/*
 * bench_hip_main.c — HIP (ROCm/AMD) GPU ray-tracing benchmark for LightRT.
 *
 * Measures build time and closest-hit / occlusion throughput (Mrays/s) of the
 * HIP backend against the CPU fp32 kernel, and verifies GPU hits against the CPU
 * oracle. Reuses the benchmark_c scene/ray generators (mandelbulb, thinspan,
 * random soup; coherent primary / incoherent / shadow workloads).
 *
 * Backends (select with --backend a,b,...; default all available):
 *   cpu-bvh8   CPU fp32 BVH8 trace (baseline / oracle)
 *   hip-fp32   GPU fp32 resident trace of a CPU-built BVH8
 *   hip-build  GPU-Morton LBVH build (Path B) + GPU fp32 resident trace
 *
 * Phase 2 will add hip-wmma-bf16 / hip-int8 / ... here for S-vs-W comparisons.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../benchmark_c/rays.h"
#include "../benchmark_c/scene_mandelbulb.h"
#include "../benchmark_c/scene_thinspan.h"
#include "../benchmark_c/timing.h"
#include "../lightrt_c_hip.h"
#include "../lightrt_c_tri.h"

/* ---- scene generation ---------------------------------------------------- */
static float *gen_scene(const char *name, size_t want_tris, size_t *ntris_out) {
    float *verts = NULL;
    size_t ntris = 0;
    if (strcmp(name, "mandelbulb") == 0) {
        int fineness = 96;
        while (fineness < 384) {
            free(verts);
            verts = NULL;
            ntris = scene_mandelbulb_generate(fineness, 8, &verts);
            if (ntris >= want_tris || !verts) break;
            fineness += 32;
        }
    } else if (strcmp(name, "thinspan") == 0) {
        ntris = scene_thinspan_generate(want_tris, 0.0f, 0.0f, 12345u, &verts);
    } else { /* random */
        ntris = want_tris;
        verts = (float *)malloc(ntris * 9 * sizeof(float));
        uint64_t rng = 0x123456789abcdef0ull;
        for (size_t i = 0; i < ntris * 9; i++) {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            float u = (float)((rng >> 32) & 0xFFFFFF) / 16777216.0f;
            size_t comp = i % 9;
            size_t axis = comp % 3;
            float center = (axis == 0 ? -2.0f : -2.0f) + 4.0f * u;
            (void)center;
            /* center per-triangle then jitter vertices a bit */
            if (comp < 3)
                verts[i] = -2.0f + 4.0f * u;
            else
                verts[i] = verts[i - (comp >= 6 ? 6 : 3)] + (u - 0.5f) * 0.3f;
        }
    }
    *ntris_out = ntris;
    return verts;
}

/* ---- timing helper ------------------------------------------------------- */
typedef struct {
    double build_ms;
    double primary_mrays;
    double incoherent_mrays;
    double shadow_mrays;
    double agree_primary; /* fraction vs CPU oracle */
    double hit_frac;
    size_t mem_bytes;
} bench_result;

static double mrays(size_t n, uint64_t ns) {
    if (ns == 0) return 0.0;
    return (double)n / ((double)ns / 1e9) / 1e6;
}

/* Best-of-iters throughput for a closure invoked through a function pointer. */
#define TIME_BEST(iters, n, body)                       \
    ({                                                  \
        double best = 0.0;                              \
        for (int _it = 0; _it < (iters); _it++) {       \
            uint64_t _t0 = bench_time_ns();             \
            body;                                       \
            uint64_t _t1 = bench_time_ns();             \
            double _m = mrays((n), _t1 - _t0);          \
            if (_m > best) best = _m;                   \
        }                                               \
        best;                                           \
    })

static double agreement(const lrt_hit *a, const lrt_hit *b, size_t n) {
    size_t ok = 0;
    for (size_t i = 0; i < n; i++) {
        int ah = a[i].prim_id != LRT_TRI_NO_HIT;
        int bh = b[i].prim_id != LRT_TRI_NO_HIT;
        if (ah != bh) continue;
        if (!ah) {
            ok++;
            continue;
        }
        if (a[i].prim_id == b[i].prim_id) {
            ok++;
        } else {
            double rel = fabs((double)a[i].t - b[i].t) / (1.0 + fabs((double)b[i].t));
            if (rel < 1e-4) ok++;
        }
    }
    return (double)ok / (double)n;
}

/* ---- Phase 2: WMMA leaf-intersection microbenchmark ---------------------- */
/* Isolates the convergent leaf inner kernel: nblocks leaves, each 16 coherent
 * rays vs T triangles, timed for scalar fp32 vs bf16/fp16/int8 WMMA, with
 * agreement vs the scalar method. This is the honest S-vs-W measurement. */
/* dir_jitter: 0 => all 16 rays in a leaf aim at the cluster center (coherent);
 * larger => divergent directions (incoherent), which exercises scalar branch
 * divergence. The S-vs-W verdict depends strongly on this, so we sweep it. */
static void leaf_regime(lrt_hip_engine *e, const char *label, uint32_t nblocks,
                        uint32_t T, int iters, float dir_jitter) {
    size_t nrays = (size_t)nblocks * 16;
    float *tris = (float *)malloc((size_t)nblocks * T * 9 * sizeof(float));
    lrt_ray *rays = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    uint64_t rng = 0xC0FFEEull;
#define NX() (rng ^= rng << 13, rng ^= rng >> 7, rng ^= rng << 17, \
              ((rng >> 32) & 0xFFFF) / 65536.0f)
    for (uint32_t b = 0; b < nblocks; b++) {
        float cx = -5 + 10 * NX(), cy = -5 + 10 * NX(), cz = -5 + 10 * NX();
        for (uint32_t i = 0; i < T; i++) {
            float *v = &tris[((size_t)b * T + i) * 9];
            for (int k = 0; k < 9; k++)
                v[k] = (k % 3 == 0 ? cx : (k % 3 == 1 ? cy : cz)) +
                       (NX() - 0.5f) * 0.8f;
        }
        for (int r = 0; r < 16; r++) {
            lrt_ray *ray = &rays[(size_t)b * 16 + r];
            float ox = cx + (NX() - 0.5f) * 6.0f;
            float oy = cy + (NX() - 0.5f) * 6.0f;
            float oz = cz + (NX() - 0.5f) * 6.0f;
            ray->org[0] = ox; ray->org[1] = oy; ray->org[2] = oz;
            float dx = cx - ox + (NX() - 0.5f) * dir_jitter;
            float dy = cy - oy + (NX() - 0.5f) * dir_jitter;
            float dz = cz - oz + (NX() - 0.5f) * dir_jitter;
            float l = sqrtf(dx * dx + dy * dy + dz * dz) + 1e-9f;
            ray->dir[0] = dx / l; ray->dir[1] = dy / l; ray->dir[2] = dz / l;
            ray->tmin = 1e-4f; ray->tmax = 1e9f;
        }
    }
#undef NX
    lrt_hit *hs = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    lrt_hit *hw = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    double tests = (double)nrays * T, dummy;
    lrt_hip_leaf_bench(e, LRT_HIP_ISECT_SCALAR, tris, nblocks, T, rays, hs,
                       &dummy, NULL);
    size_t hit = 0;
    for (size_t i = 0; i < nrays; i++)
        if (hs[i].prim_id != LRT_TRI_NO_HIT) hit++;
    printf("\n[%s] leaves=%u tris/leaf=%u tests=%.1fM hit_frac=%.3f\n", label,
           nblocks, T, tests / 1e6, (double)hit / nrays);
    printf("  %-12s %12s %10s %8s\n", "method", "Mtests/s", "agree%", "speedup");
    struct { const char *name; lrt_hip_isect_method m; } methods[] = {
        {"scalar", LRT_HIP_ISECT_SCALAR},
        {"wmma-bf16", LRT_HIP_ISECT_WMMA_BF16},
        {"wmma-fp16", LRT_HIP_ISECT_WMMA_FP16},
        {"wmma-fp8", LRT_HIP_ISECT_WMMA_FP8},
        {"wmma-int8", LRT_HIP_ISECT_WMMA_INT8},
    };
    const int nmethods = (int)(sizeof(methods) / sizeof(methods[0]));
    double scalar_rate = 0.0;
    for (int k = 0; k < nmethods; k++) {
        if (k > 0 && !lrt_hip_have_wmma()) break;
        double best_ms = 1e30;
        for (int it = 0; it < iters; it++) {
            double ms = 0.0;
            int r = lrt_hip_leaf_bench(e, methods[k].m, tris, nblocks, T, rays,
                                       hw, &ms, NULL);
            if (r != 0) { best_ms = -1; break; }
            if (ms < best_ms) best_ms = ms;
        }
        if (best_ms < 0) { printf("  %-12s   (failed)\n", methods[k].name); continue; }
        size_t agree = 0;
        for (size_t i = 0; i < nrays; i++)
            if (hw[i].prim_id == hs[i].prim_id) agree++;
        double rate = tests / (best_ms / 1e3) / 1e6;
        if (k == 0) scalar_rate = rate;
        printf("  %-12s %12.1f %9.3f%% %7.2fx\n", methods[k].name, rate,
               100.0 * agree / nrays, rate / scalar_rate);
    }
    free(tris); free(rays); free(hs); free(hw);
}

static int run_leaf_bench(uint32_t nblocks, uint32_t T, int iters) {
    lrt_result er = LRT_RESULT_OK;
    lrt_hip_engine *e = lrt_hip_engine_create(NULL, &er);
    if (!e) {
        printf("(no HIP device; skipping WMMA leaf bench)\n");
        return 0;
    }
    printf("WMMA leaf-intersection microbenchmark (16 rays/leaf, dev=%s)\n",
           lrt_hip_engine_device_name(e));
    if (!lrt_hip_have_wmma())
        printf("(rocWMMA not compiled in; only scalar kernel available)\n");
    if (T > 16) T = 16;
    leaf_regime(e, "coherent rays", nblocks, T, iters, 0.0f);
    leaf_regime(e, "incoherent rays", nblocks, T, iters, 1.5f);
    lrt_hip_engine_destroy(e);
    return 0;
}

int main(int argc, char **argv) {
    const char *scene = "mandelbulb";
    size_t want_tris = 200000;
    size_t nrays = 1000000;
    int iters = 5;
    int do_cpu = 1, do_fp32 = 1, do_build = 1, do_gpubuild = 1;
    int have_backend_filter = 0;
    int leaf_mode = 0;
    uint32_t leaf_blocks = 262144, leaf_tris = 8;

    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--leaf")) {
            leaf_mode = 1;
        } else if (!strcmp(argv[i], "--leaf-blocks") && i + 1 < argc) {
            leaf_blocks = (uint32_t)strtoul(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--leaf-tris") && i + 1 < argc) {
            leaf_tris = (uint32_t)strtoul(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--scene") && i + 1 < argc) {
            scene = argv[++i];
        } else if (!strcmp(argv[i], "--tris") && i + 1 < argc) {
            want_tris = (size_t)strtoull(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--rays") && i + 1 < argc) {
            nrays = (size_t)strtoull(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--iters") && i + 1 < argc) {
            iters = atoi(argv[++i]);
        } else if (!strcmp(argv[i], "--backend") && i + 1 < argc) {
            const char *b = argv[++i];
            do_cpu = do_fp32 = do_build = do_gpubuild = 0;
            have_backend_filter = 1;
            if (strstr(b, "cpu")) do_cpu = 1;
            if (strstr(b, "hip-fp32")) do_fp32 = 1;
            if (strstr(b, "hip-build")) do_build = 1;
            if (strstr(b, "hip-gpubuild")) do_gpubuild = 1;
        } else {
            printf("usage: %s [--scene random|mandelbulb|thinspan] [--tris N] "
                   "[--rays N] [--iters N] [--backend cpu,hip-fp32,hip-build]\n"
                   "       %s --leaf [--leaf-blocks N] [--leaf-tris N] "
                   "[--iters N]\n",
                   argv[0], argv[0]);
            return 2;
        }
    }
    (void)have_backend_filter;

    if (leaf_mode) return run_leaf_bench(leaf_blocks, leaf_tris, iters);

    size_t ntris = 0;
    float *verts = gen_scene(scene, want_tris, &ntris);
    if (!verts || ntris == 0) {
        printf("scene generation failed\n");
        return 1;
    }
    printf("scene=%s ntris=%zu rays=%zu iters=%d\n", scene, ntris, nrays, iters);

    lrt_ray *primary = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_ray *incoh = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_ray *shadow = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_hit *cpu_hits = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    lrt_hit *gpu_hits = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    uint8_t *occ = (uint8_t *)malloc(nrays * sizeof(uint8_t));
    rays_gen_primary(primary, nrays, 1u);
    rays_gen_incoherent(incoh, nrays, 1u);

    /* CPU baseline + oracle (always build it for verification). */
    lrt_tri_build_options opts;
    memset(&opts, 0, sizeof(opts));
    opts.quality = LRT_TRI_BUILD_DEFAULT;
    opts.layout = LRT_TRI_LAYOUT_BVH8;
    opts.num_threads = 1;
    uint64_t t0 = bench_time_ns();
    lrt_tri_scene *cpu = lrt_tri_scene_build(verts, ntris, &opts, NULL);
    uint64_t t1 = bench_time_ns();
    lrt_tri_stats st;
    lrt_tri_scene_stats(cpu, &st);

    /* shadow rays need primary hits first */
    lrt_tri_intersect1N(cpu, primary, cpu_hits, nrays, LRT_TRI_BATCH_COHERENT);
    rays_gen_shadow(shadow, nrays, primary, cpu_hits, verts, ntris, 1u);

    printf("\n%-12s %10s %12s %12s %12s %10s %8s\n", "backend", "build_ms",
           "primary", "incoh", "shadow", "agree%", "mem_mb");
    printf("%-12s %10s %12s %12s %12s %10s %8s\n", "", "", "Mray/s", "Mray/s",
           "Mray/s(occ)", "", "");

    if (do_cpu) {
        double pm = TIME_BEST(iters, nrays, {
            lrt_tri_intersect1N(cpu, primary, gpu_hits, nrays,
                                LRT_TRI_BATCH_COHERENT);
        });
        double im = TIME_BEST(iters, nrays, {
            lrt_tri_intersect1N(cpu, incoh, gpu_hits, nrays,
                                LRT_TRI_BATCH_INCOHERENT);
        });
        double sm = TIME_BEST(iters, nrays, {
            lrt_tri_occluded1N(cpu, shadow, occ, nrays, LRT_TRI_BATCH_INCOHERENT);
        });
        printf("%-12s %10.2f %12.1f %12.1f %12.1f %10s %8.2f\n", "cpu-bvh8",
               bench_ns_to_ms(t1 - t0), pm, im, sm, "(oracle)",
               st.memory_bytes / (1024.0 * 1024.0));
    }

    /* HIP engine (skip GPU backends gracefully if absent). */
    lrt_hip_engine *e = NULL;
    if (do_fp32 || do_build) {
        lrt_result er = LRT_RESULT_OK;
        e = lrt_hip_engine_create(NULL, &er);
        if (!e) printf("(no HIP device; skipping GPU backends)\n");
    }

    if (e && do_fp32) {
        lrt_hip_scene *gs = lrt_hip_scene_upload(e, cpu, NULL);
        if (gs) {
            /* warm up + correctness */
            lrt_hip_scene_trace(e, gs, primary, (uint32_t)nrays, gpu_hits, NULL);
            double ag = agreement(gpu_hits, cpu_hits, nrays);
            size_t hits = 0;
            for (size_t i = 0; i < nrays; i++)
                if (gpu_hits[i].prim_id != LRT_TRI_NO_HIT) hits++;
            double pm = TIME_BEST(iters, nrays, {
                lrt_hip_scene_trace(e, gs, primary, (uint32_t)nrays, gpu_hits,
                                    NULL);
            });
            double im = TIME_BEST(iters, nrays, {
                lrt_hip_scene_trace(e, gs, incoh, (uint32_t)nrays, gpu_hits,
                                    NULL);
            });
            double sm = TIME_BEST(iters, nrays, {
                lrt_hip_scene_occluded(e, gs, shadow, (uint32_t)nrays, occ,
                                       NULL);
            });
            printf("%-12s %10.2f %12.1f %12.1f %12.1f %9.3f%% %8.2f\n",
                   "hip-fp32", bench_ns_to_ms(t1 - t0), pm, im, sm, ag * 100.0,
                   st.memory_bytes / (1024.0 * 1024.0));
            (void)hits;
            /* Refit timing (dynamic/animation path): vs the full build_ms. */
            double refit_ms = 1e30;
            for (int it = 0; it < iters; it++) {
                uint64_t r0 = bench_time_ns();
                lrt_hip_scene_refit(e, gs, verts, (uint32_t)ntris, NULL);
                uint64_t r1 = bench_time_ns();
                double m = bench_ns_to_ms(r1 - r0);
                if (m < refit_ms) refit_ms = m;
            }
            printf("%-12s refit %.2f ms (%.1fx faster than the %.2f ms build)\n",
                   "hip-refit", refit_ms, bench_ns_to_ms(t1 - t0) / refit_ms,
                   bench_ns_to_ms(t1 - t0));
            lrt_hip_scene_free(e, gs);
        } else {
            printf("hip-fp32: upload failed: %s\n",
                   lrt_hip_engine_last_error(e));
        }
    }

    if (e && do_build) {
        lrt_tri_scene *gpu_scene = NULL;
        uint64_t b0 = bench_time_ns();
        int br = lrt_hip_build_scene(e, verts, (uint32_t)ntris,
                                     LRT_TRI_LAYOUT_BVH8, &gpu_scene, NULL);
        uint64_t b1 = bench_time_ns();
        if (br == 0 && gpu_scene) {
            lrt_hip_scene *gs = lrt_hip_scene_upload(e, gpu_scene, NULL);
            if (gs) {
                lrt_hip_scene_trace(e, gs, primary, (uint32_t)nrays, gpu_hits,
                                    NULL);
                double ag = agreement(gpu_hits, cpu_hits, nrays);
                lrt_tri_stats gst;
                lrt_tri_scene_stats(gpu_scene, &gst);
                double pm = TIME_BEST(iters, nrays, {
                    lrt_hip_scene_trace(e, gs, primary, (uint32_t)nrays,
                                        gpu_hits, NULL);
                });
                double im = TIME_BEST(iters, nrays, {
                    lrt_hip_scene_trace(e, gs, incoh, (uint32_t)nrays, gpu_hits,
                                        NULL);
                });
                double sm = TIME_BEST(iters, nrays, {
                    lrt_hip_scene_occluded(e, gs, shadow, (uint32_t)nrays, occ,
                                           NULL);
                });
                printf("%-12s %10.2f %12.1f %12.1f %12.1f %9.3f%% %8.2f\n",
                       "hip-build", bench_ns_to_ms(b1 - b0), pm, im, sm,
                       ag * 100.0, gst.memory_bytes / (1024.0 * 1024.0));
                lrt_hip_scene_free(e, gs);
            }
            lrt_tri_scene_free(gpu_scene);
        } else {
            printf("hip-build: failed: %s\n", lrt_hip_engine_last_error(e));
        }
    }

    if (e && do_gpubuild && lrt_hip_have_gpu_build()) {
        /* Full-GPU LBVH: build entirely on the GPU, trace the resident scene. */
        double best_build = 1e30;
        lrt_hip_scene *gs = NULL;
        for (int it = 0; it < iters; it++) {
            uint64_t b0 = bench_time_ns();
            lrt_hip_scene *g =
                lrt_hip_scene_build_gpu(e, verts, (uint32_t)ntris, NULL);
            uint64_t b1 = bench_time_ns();
            double m = bench_ns_to_ms(b1 - b0);
            if (m < best_build) best_build = m;
            if (gs) lrt_hip_scene_free(e, gs);
            gs = g;
        }
        if (gs) {
            lrt_hip_scene_trace(e, gs, primary, (uint32_t)nrays, gpu_hits, NULL);
            double ag = agreement(gpu_hits, cpu_hits, nrays);
            double pm = TIME_BEST(iters, nrays, {
                lrt_hip_scene_trace(e, gs, primary, (uint32_t)nrays, gpu_hits,
                                    NULL);
            });
            double im = TIME_BEST(iters, nrays, {
                lrt_hip_scene_trace(e, gs, incoh, (uint32_t)nrays, gpu_hits,
                                    NULL);
            });
            double sm = TIME_BEST(iters, nrays, {
                lrt_hip_scene_occluded(e, gs, shadow, (uint32_t)nrays, occ,
                                       NULL);
            });
            printf("%-12s %10.2f %12.1f %12.1f %12.1f %9.3f%% %8s\n",
                   "hip-gpubuild", best_build, pm, im, sm, ag * 100.0, "-");
            lrt_hip_scene_free(e, gs);
        }
    }

    if (e) lrt_hip_engine_destroy(e);
    lrt_tri_scene_free(cpu);
    free(verts);
    free(primary);
    free(incoh);
    free(shadow);
    free(cpu_hits);
    free(gpu_hits);
    free(occ);
    return 0;
}
