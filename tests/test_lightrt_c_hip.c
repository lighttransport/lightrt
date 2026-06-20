/*
 * test_lightrt_c_hip.c — correctness tests for the HIP (ROCm/AMD) GPU backend
 * (lightrt_c_hip.h). Pure C11.
 *
 * The GPU trace kernel is a byte-for-byte port of the scalar CPU kernel over the
 * same node/leaf memory image, so the oracle is the CPU kernel itself
 * (lrt_tri_intersect1 / lrt_tri_occluded1), not a separate brute force — we
 * expect near-exact agreement, much tighter than the brute-force test.
 *
 * Checks, for BVH4 and BVH8:
 *   1. Closest-hit agreement (prim_id + t) GPU vs CPU on random + structured
 *      scenes and degenerate rays.
 *   2. Occlusion agreement GPU vs CPU.
 *   3. Path B (GPU-Morton build) hit agreement vs a CPU FAST build.
 *
 * Degrades gracefully: if no HIP device is present, lrt_hip_engine_create()
 * returns NULL and the test passes (skipped).
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../lightrt_c_hip.h"
#include "../lightrt_c_tri.h"

/* xorshift PRNG for reproducible scenes/rays */
static uint64_t g_rng = 0x9E3779B97F4A7C15ull;
static uint32_t rnd_u32(void) {
    g_rng ^= g_rng << 13;
    g_rng ^= g_rng >> 7;
    g_rng ^= g_rng << 17;
    return (uint32_t)(g_rng >> 32);
}
static float rnd_f(float lo, float hi) {
    return lo + (hi - lo) * ((float)(rnd_u32() & 0xFFFFFF) / 16777216.0f);
}

static float *make_random_soup(size_t ntris, float scale) {
    float *verts = (float *)malloc(ntris * 9 * sizeof(float));
    if (!verts) return NULL;
    for (size_t i = 0; i < ntris; i++) {
        float cx = rnd_f(-2.0f, 2.0f), cy = rnd_f(-2.0f, 2.0f),
              cz = rnd_f(-2.0f, 2.0f);
        for (int k = 0; k < 3; k++) {
            verts[i * 9 + k * 3 + 0] = cx + rnd_f(-scale, scale);
            verts[i * 9 + k * 3 + 1] = cy + rnd_f(-scale, scale);
            verts[i * 9 + k * 3 + 2] = cz + rnd_f(-scale, scale);
        }
    }
    return verts;
}

/* A tessellated-grid scene (more BVH structure / depth than random soup). */
static float *make_grid_soup(int n, size_t *ntris_out) {
    size_t ntris = (size_t)n * n * 2;
    float *verts = (float *)malloc(ntris * 9 * sizeof(float));
    if (!verts) return NULL;
    size_t t = 0;
    float step = 4.0f / (float)n;
    for (int j = 0; j < n; j++) {
        for (int i = 0; i < n; i++) {
            float x0 = -2.0f + i * step, x1 = x0 + step;
            float z0 = -2.0f + j * step, z1 = z0 + step;
            float y = 0.2f * sinf((float)(i + j));
            /* tri A */
            float a[9] = {x0, y, z0, x1, y, z0, x0, y, z1};
            float b[9] = {x1, y, z0, x1, y, z1, x0, y, z1};
            memcpy(&verts[t * 9], a, sizeof(a));
            t++;
            memcpy(&verts[t * 9], b, sizeof(b));
            t++;
        }
    }
    *ntris_out = ntris;
    return verts;
}

static void make_random_ray(lrt_ray *r) {
    r->org[0] = rnd_f(-4.0f, 4.0f);
    r->org[1] = rnd_f(-4.0f, 4.0f);
    r->org[2] = rnd_f(-4.0f, 4.0f);
    float dx = rnd_f(-1.0f, 1.0f), dy = rnd_f(-1.0f, 1.0f), dz = rnd_f(-1.0f, 1.0f);
    uint32_t z = rnd_u32();
    if ((z & 0xFF) < 24) dx = 0.0f;
    if (((z >> 8) & 0xFF) < 24) dy = 0.0f;
    if (((z >> 16) & 0xFF) < 24) dz = 0.0f;
    if (dx == 0.0f && dy == 0.0f && dz == 0.0f) dz = 1.0f;
    float len = sqrtf(dx * dx + dy * dy + dz * dz);
    r->dir[0] = dx / len;
    r->dir[1] = dy / len;
    r->dir[2] = dz / len;
    r->tmin = ((z >> 24) & 1) ? 0.0f : 1e-5f;
    r->tmax = ((z >> 25) & 1) ? 1e10f : rnd_f(1.0f, 12.0f);
}

static int g_failures = 0;
#define CHECK(cond, ...)                  \
    do {                                  \
        if (!(cond)) {                    \
            printf("FAIL: " __VA_ARGS__); \
            printf("\n");                 \
            g_failures++;                 \
        }                                 \
    } while (0)

/* Compare a GPU trace against the CPU oracle over n rays. Returns agreement
 * fraction; mismatches near shared edges (fp ties) are tolerated. */
static void test_trace(lrt_hip_engine *e, const char *label, const float *verts,
                       size_t ntris, lrt_tri_layout layout, size_t nrays) {
    lrt_tri_build_options opts;
    memset(&opts, 0, sizeof(opts));
    opts.quality = LRT_TRI_BUILD_DEFAULT;
    opts.layout = layout;
    opts.num_threads = 1;
    lrt_tri_scene *s = lrt_tri_scene_build(verts, ntris, &opts, NULL);
    CHECK(s != NULL, "%s: scene build failed", label);
    if (!s) return;

    lrt_hip_scene *gs = lrt_hip_scene_upload(e, s, NULL);
    CHECK(gs != NULL, "%s: GPU upload failed: %s", label,
          lrt_hip_engine_last_error(e));
    if (!gs) {
        lrt_tri_scene_free(s);
        return;
    }

    lrt_ray *rays = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_hit *ghits = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    uint8_t *gocc = (uint8_t *)malloc(nrays * sizeof(uint8_t));
    for (size_t i = 0; i < nrays; i++) make_random_ray(&rays[i]);

    int r = lrt_hip_scene_trace(e, gs, rays, (uint32_t)nrays, ghits, NULL);
    CHECK(r >= 0, "%s: GPU trace failed: %s", label,
          lrt_hip_engine_last_error(e));
    int ro = lrt_hip_scene_occluded(e, gs, rays, (uint32_t)nrays, gocc, NULL);
    CHECK(ro >= 0, "%s: GPU occluded failed: %s", label,
          lrt_hip_engine_last_error(e));

    size_t agree = 0, occ_agree = 0;
    double max_rel_t = 0.0;
    for (size_t i = 0; i < nrays; i++) {
        lrt_hit cpu;
        int chit = lrt_tri_intersect1(s, &rays[i], &cpu);
        int ghit = (ghits[i].prim_id != LRT_TRI_NO_HIT);
        if (chit == ghit) {
            if (!ghit) {
                agree++;
            } else if (cpu.prim_id == ghits[i].prim_id) {
                agree++;
                double rel = fabs((double)ghits[i].t - cpu.t) /
                             (1.0 + fabs((double)cpu.t));
                if (rel > max_rel_t) max_rel_t = rel;
            } else {
                /* different prim but same distance => shared-edge fp tie */
                double rel = fabs((double)ghits[i].t - cpu.t) /
                             (1.0 + fabs((double)cpu.t));
                if (rel < 1e-4) agree++;
            }
        }

        int cocc = lrt_tri_occluded1(s, &rays[i]);
        if ((cocc != 0) == (gocc[i] != 0)) occ_agree++;
    }
    double frac = (double)agree / (double)nrays;
    double ofrac = (double)occ_agree / (double)nrays;
    printf("  %-22s closest agree %.4f%% (max_rel_t %.2e)  occ agree %.4f%%\n",
           label, frac * 100.0, max_rel_t, ofrac * 100.0);
    CHECK(frac >= 0.999, "%s: closest-hit agreement %.4f%% < 99.9%%", label,
          frac * 100.0);
    CHECK(max_rel_t < 1e-3, "%s: max_rel_t %.2e >= 1e-3", label, max_rel_t);
    CHECK(ofrac >= 0.999, "%s: occlusion agreement %.4f%% < 99.9%%", label,
          ofrac * 100.0);

    free(rays);
    free(ghits);
    free(gocc);
    lrt_hip_scene_free(e, gs);
    lrt_tri_scene_free(s);
}

/* Path B: GPU-Morton build should produce a scene whose hits match a CPU FAST
 * build over the same rays. */
static void test_build(lrt_hip_engine *e, const char *label, const float *verts,
                       size_t ntris, lrt_tri_layout layout, size_t nrays) {
    lrt_tri_scene *gpu_scene = NULL;
    int br = lrt_hip_build_scene(e, verts, (uint32_t)ntris, layout, &gpu_scene,
                                 NULL);
    CHECK(br == 0 && gpu_scene, "%s: GPU build failed: %s", label,
          lrt_hip_engine_last_error(e));
    if (br != 0 || !gpu_scene) return;

    lrt_tri_build_options opts;
    memset(&opts, 0, sizeof(opts));
    opts.quality = LRT_TRI_BUILD_FAST;
    opts.layout = layout;
    opts.num_threads = 1;
    lrt_tri_scene *cpu_scene = lrt_tri_scene_build(verts, ntris, &opts, NULL);
    CHECK(cpu_scene != NULL, "%s: CPU FAST build failed", label);
    if (!cpu_scene) {
        lrt_tri_scene_free(gpu_scene);
        return;
    }

    size_t agree = 0;
    for (size_t i = 0; i < nrays; i++) {
        lrt_ray ray;
        make_random_ray(&ray);
        lrt_hit a, b;
        int ah = lrt_tri_intersect1(gpu_scene, &ray, &a);
        int bh = lrt_tri_intersect1(cpu_scene, &ray, &b);
        if (ah == bh && (!ah || a.prim_id == b.prim_id)) agree++;
    }
    double frac = (double)agree / (double)nrays;
    printf("  %-22s GPU-build vs CPU-FAST agree %.4f%%\n", label, frac * 100.0);
    CHECK(frac >= 0.999, "%s: GPU-build agreement %.4f%% < 99.9%%", label,
          frac * 100.0);

    lrt_tri_scene_free(gpu_scene);
    lrt_tri_scene_free(cpu_scene);
}

/* Full-GPU LBVH: build entirely on the GPU, trace, compare to the CPU oracle.
 * The GPU tree differs from the CPU SAH tree (binary Karras vs collapsed SAH),
 * so we compare hits against an independent CPU scene built on the same soup. */
static void test_gpu_build(lrt_hip_engine *e, const char *label,
                           const float *verts, size_t ntris, size_t nrays) {
    lrt_result er = LRT_RESULT_OK;
    lrt_hip_scene *gs =
        lrt_hip_scene_build_gpu(e, verts, (uint32_t)ntris, &er);
    CHECK(gs != NULL, "%s: GPU build failed: %s", label,
          lrt_hip_engine_last_error(e));
    if (!gs) return;

    lrt_tri_build_options opts;
    memset(&opts, 0, sizeof(opts));
    opts.quality = LRT_TRI_BUILD_DEFAULT;
    opts.layout = LRT_TRI_LAYOUT_BVH8;
    opts.num_threads = 1;
    lrt_tri_scene *cpu = lrt_tri_scene_build(verts, ntris, &opts, NULL);

    lrt_ray *rays = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_hit *gh = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    for (size_t i = 0; i < nrays; i++) make_random_ray(&rays[i]);
    lrt_hip_scene_trace(e, gs, rays, (uint32_t)nrays, gh, NULL);

    size_t agree = 0;
    double max_rel = 0.0;
    for (size_t i = 0; i < nrays; i++) {
        lrt_hit c;
        int ch = lrt_tri_intersect1(cpu, &rays[i], &c);
        int g = gh[i].prim_id != LRT_TRI_NO_HIT;
        if (ch == g) {
            if (!g) {
                agree++;
            } else if (c.prim_id == gh[i].prim_id) {
                agree++;
                double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                if (rel > max_rel) max_rel = rel;
            } else {
                double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                if (rel < 1e-4) agree++;
            }
        }
    }
    double frac = (double)agree / (double)nrays;
    printf("  %-22s GPU-LBVH vs CPU agree %.4f%% (max_rel_t %.2e)\n", label,
           frac * 100.0, max_rel);
    CHECK(frac >= 0.999, "%s: GPU-LBVH agreement %.4f%% < 99.9%%", label,
          frac * 100.0);

    free(rays);
    free(gh);
    lrt_hip_scene_free(e, gs);
    lrt_tri_scene_free(cpu);
}

/* Fully GPU-resident dynamic pipeline: device vertex buffer -> GPU build ->
 * GPU raygen -> device trace, with a single download at the end to verify. */
static void test_device_pipeline(lrt_hip_engine *e, const float *verts,
                                 size_t ntris) {
    if (!lrt_hip_have_gpu_build()) {
        printf("== GPU-resident pipeline: hipCUB absent, skipping\n");
        return;
    }
    uint32_t W = 256, H = 256;
    uint32_t n = W * H;

    /* Resident buffers. */
    lrt_hip_dbuffer *dverts =
        lrt_hip_dbuffer_alloc(e, ntris * 9 * sizeof(float), NULL);
    lrt_hip_dbuffer *drays = lrt_hip_dbuffer_alloc(e, n * sizeof(lrt_ray), NULL);
    lrt_hip_dbuffer *dhits = lrt_hip_dbuffer_alloc(e, n * sizeof(lrt_hit), NULL);
    CHECK(dverts && drays && dhits, "dbuffer alloc failed");
    if (!dverts || !drays || !dhits) return;
    lrt_hip_dbuffer_upload(e, dverts, verts, ntris * 9 * sizeof(float), NULL);

    /* GPU build from the device vertex buffer (no H2D/D2H). */
    lrt_hip_scene *gs =
        lrt_hip_scene_build_gpu_device(e, dverts, (uint32_t)ntris, NULL);
    CHECK(gs != NULL, "build_gpu_device failed: %s",
          lrt_hip_engine_last_error(e));
    if (!gs) return;

    /* Camera that frames the [-2,2]^3 scene. */
    float origin[3] = {5, 5, 5};
    float ll[3] = {-3.5f, -3.5f, -3.5f};
    float horiz[3] = {7, 0, 0};
    float vert[3] = {0, 7, 0};
    lrt_hip_raygen_camera(e, drays, W, H, origin, ll, horiz, vert, 1e-4f, 1e9f,
                          NULL);
    int tr = lrt_hip_scene_trace_device(e, gs, drays, n, dhits, NULL);
    CHECK(tr == 0, "trace_device failed: %s", lrt_hip_engine_last_error(e));

    /* Single download to verify against a CPU re-trace of the same rays. */
    lrt_ray *hrays = (lrt_ray *)malloc(n * sizeof(lrt_ray));
    lrt_hit *hhits = (lrt_hit *)malloc(n * sizeof(lrt_hit));
    lrt_hip_dbuffer_download(e, drays, hrays, n * sizeof(lrt_ray), NULL);
    lrt_hip_dbuffer_download(e, dhits, hhits, n * sizeof(lrt_hit), NULL);

    lrt_tri_build_options opts;
    memset(&opts, 0, sizeof(opts));
    opts.quality = LRT_TRI_BUILD_DEFAULT;
    opts.layout = LRT_TRI_LAYOUT_BVH8;
    opts.num_threads = 1;
    lrt_tri_scene *cpu = lrt_tri_scene_build(verts, ntris, &opts, NULL);
    size_t agree = 0, hits = 0;
    for (uint32_t i = 0; i < n; i++) {
        lrt_hit c;
        int ch = lrt_tri_intersect1(cpu, &hrays[i], &c);
        int g = hhits[i].prim_id != LRT_TRI_NO_HIT;
        if (g) hits++;
        if (ch == g && (!ch || c.prim_id == hhits[i].prim_id))
            agree++;
        else if (ch && g) {
            double rel = fabs((double)hhits[i].t - c.t) / (1.0 + fabs(c.t));
            if (rel < 1e-4) agree++;
        }
    }
    double frac = (double)agree / (double)n;
    printf("== GPU-resident pipeline (raygen+build+trace on device) ==\n");
    printf("  %ux%u rays hit_frac=%.3f  device-vs-CPU agree %.4f%%\n", W, H,
           (double)hits / n, frac * 100.0);
    CHECK(frac >= 0.999, "device pipeline agreement %.4f%% < 99.9%%",
          frac * 100.0);

    free(hrays);
    free(hhits);
    lrt_tri_scene_free(cpu);
    lrt_hip_scene_free(e, gs);
    lrt_hip_dbuffer_free(e, dverts);
    lrt_hip_dbuffer_free(e, drays);
    lrt_hip_dbuffer_free(e, dhits);
}

/* Phase 2: WMMA leaf intersection. Verify scalar GPU leaf kernel matches a CPU
 * brute force exactly, and that the low-precision WMMA methods agree with the
 * scalar method above their expected thresholds (fp16 > bf16/int8). */
static int ref_isect(const float *tri, const lrt_ray *r, float *t, float *u,
                     float *v) {
    float e1[3] = {tri[3] - tri[0], tri[4] - tri[1], tri[5] - tri[2]};
    float e2[3] = {tri[6] - tri[0], tri[7] - tri[1], tri[8] - tri[2]};
    float px = r->dir[1] * e2[2] - r->dir[2] * e2[1];
    float py = r->dir[2] * e2[0] - r->dir[0] * e2[2];
    float pz = r->dir[0] * e2[1] - r->dir[1] * e2[0];
    float det = e1[0] * px + e1[1] * py + e1[2] * pz;
    if (det > -1e-12f && det < 1e-12f) return 0;
    float inv = 1.0f / det;
    float tvx = r->org[0] - tri[0], tvy = r->org[1] - tri[1],
          tvz = r->org[2] - tri[2];
    float uu = (tvx * px + tvy * py + tvz * pz) * inv;
    if (uu < 0.0f || uu > 1.0f) return 0;
    float qx = tvy * e1[2] - tvz * e1[1];
    float qy = tvz * e1[0] - tvx * e1[2];
    float qz = tvx * e1[1] - tvy * e1[0];
    float vv = (r->dir[0] * qx + r->dir[1] * qy + r->dir[2] * qz) * inv;
    if (vv < 0.0f || uu + vv > 1.0f) return 0;
    float tt = (e2[0] * qx + e2[1] * qy + e2[2] * qz) * inv;
    if (tt < r->tmin || tt >= r->tmax) return 0;
    *t = tt;
    *u = uu;
    *v = vv;
    return 1;
}

static double run_leaf(lrt_hip_engine *e, lrt_hip_isect_method m,
                       const float *tris, uint32_t nblk, uint32_t T,
                       const lrt_ray *rays, const lrt_hit *oracle,
                       size_t nrays) {
    lrt_hit *h = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    double ms = 0.0;
    int r = lrt_hip_leaf_bench(e, m, tris, nblk, T, rays, h, &ms, NULL);
    CHECK(r == 0, "leaf_bench method %d failed", (int)m);
    size_t agree = 0;
    for (size_t i = 0; i < nrays; i++)
        if (h[i].prim_id == oracle[i].prim_id) agree++;
    double frac = (double)agree / (double)nrays;
    free(h);
    return frac;
}

static void test_wmma(lrt_hip_engine *e) {
    if (!lrt_hip_have_wmma()) {
        printf("== WMMA leaf intersection: rocWMMA not compiled in, skipping\n");
        return;
    }
    uint32_t nblk = 8192, T = 8;
    size_t nrays = (size_t)nblk * 16;
    float *tris = (float *)malloc((size_t)nblk * T * 9 * sizeof(float));
    lrt_ray *rays = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    for (uint32_t b = 0; b < nblk; b++) {
        float cx = rnd_f(-5, 5), cy = rnd_f(-5, 5), cz = rnd_f(-5, 5);
        for (uint32_t i = 0; i < T; i++) {
            float *v = &tris[((size_t)b * T + i) * 9];
            float bx = cx + rnd_f(-0.5f, 0.5f), by = cy + rnd_f(-0.5f, 0.5f),
                  bz = cz + rnd_f(-0.5f, 0.5f);
            for (int k = 0; k < 3; k++) {
                v[k * 3 + 0] = bx + rnd_f(-0.4f, 0.4f);
                v[k * 3 + 1] = by + rnd_f(-0.4f, 0.4f);
                v[k * 3 + 2] = bz + rnd_f(-0.4f, 0.4f);
            }
        }
        for (int r = 0; r < 16; r++) {
            lrt_ray *ray = &rays[(size_t)b * 16 + r];
            float ox = cx + rnd_f(-3, 3), oy = cy + rnd_f(-3, 3),
                  oz = cz + rnd_f(-3, 3);
            ray->org[0] = ox;
            ray->org[1] = oy;
            ray->org[2] = oz;
            float dx = cx - ox + rnd_f(-0.3f, 0.3f),
                  dy = cy - oy + rnd_f(-0.3f, 0.3f),
                  dz = cz - oz + rnd_f(-0.3f, 0.3f);
            float l = sqrtf(dx * dx + dy * dy + dz * dz);
            ray->dir[0] = dx / l;
            ray->dir[1] = dy / l;
            ray->dir[2] = dz / l;
            ray->tmin = 1e-4f;
            ray->tmax = 1e9f;
        }
    }

    /* GPU scalar leaf result + a CPU brute-force oracle over the same leaves. */
    lrt_hit *gscalar = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    double ms = 0.0;
    int r = lrt_hip_leaf_bench(e, LRT_HIP_ISECT_SCALAR, tris, nblk, T, rays,
                               gscalar, &ms, NULL);
    CHECK(r == 0, "leaf_bench scalar failed");
    size_t scalar_ok = 0;
    for (uint32_t b = 0; b < nblk; b++) {
        const float *base = &tris[(size_t)b * T * 9];
        for (int rr = 0; rr < 16; rr++) {
            const lrt_ray *ray = &rays[(size_t)b * 16 + rr];
            float best = ray->tmax;
            uint32_t bp = LRT_TRI_NO_HIT;
            for (uint32_t i = 0; i < T; i++) {
                float t, u, v;
                lrt_ray q = *ray;
                q.tmax = best;
                if (ref_isect(&base[i * 9], &q, &t, &u, &v)) {
                    best = t;
                    bp = i;
                }
            }
            if (gscalar[(size_t)b * 16 + rr].prim_id == bp) scalar_ok++;
        }
    }
    double sfrac = (double)scalar_ok / (double)nrays;
    CHECK(sfrac >= 0.999, "WMMA scalar leaf vs CPU brute force %.4f%% < 99.9%%",
          sfrac * 100.0);

    double bf = run_leaf(e, LRT_HIP_ISECT_WMMA_BF16, tris, nblk, T, rays,
                         gscalar, nrays);
    double fp = run_leaf(e, LRT_HIP_ISECT_WMMA_FP16, tris, nblk, T, rays,
                         gscalar, nrays);
    double f8 = run_leaf(e, LRT_HIP_ISECT_WMMA_FP8, tris, nblk, T, rays,
                         gscalar, nrays);
    double i8 = run_leaf(e, LRT_HIP_ISECT_WMMA_INT8, tris, nblk, T, rays,
                         gscalar, nrays);
    printf("== WMMA leaf intersection (vs scalar) ==\n");
    printf("  scalar-vs-cpu %.4f%%  bf16 %.3f%%  fp16 %.3f%%  fp8 %.3f%%  "
           "int8 %.3f%%\n",
           sfrac * 100.0, bf * 100.0, fp * 100.0, f8 * 100.0, i8 * 100.0);
    CHECK(fp >= 0.98, "fp16 leaf agreement %.3f%% < 98%%", fp * 100.0);
    CHECK(bf >= 0.90, "bf16 leaf agreement %.3f%% < 90%%", bf * 100.0);
    CHECK(i8 >= 0.90, "int8 leaf agreement %.3f%% < 90%%", i8 * 100.0);
    CHECK(f8 >= 0.70, "fp8 leaf agreement %.3f%% < 70%%", f8 * 100.0);

    free(tris);
    free(rays);
    free(gscalar);

    /* Transform / motion-blur batching: GPU result must match a CPU reference. */
    uint32_t nt = 50000;
    lrt_ray *in = (lrt_ray *)malloc(nt * sizeof(lrt_ray));
    lrt_ray *gt = (lrt_ray *)malloc(nt * sizeof(lrt_ray));
    float *times = (float *)malloc(nt * sizeof(float));
    for (uint32_t i = 0; i < nt; i++) {
        for (int k = 0; k < 3; k++) {
            in[i].org[k] = rnd_f(-3, 3);
            in[i].dir[k] = rnd_f(-1, 1);
        }
        in[i].tmin = 0;
        in[i].tmax = 1e9f;
        times[i] = rnd_f(0, 1);
    }
    float m0[12] = {1, 0, 0, 0.5f, 0, 1, 0, -0.5f, 0, 0, 1, 0.25f};
    float m1[12] = {0, -1, 0, 1.0f, 1, 0, 0, 0.0f, 0, 0, 1, -0.25f};
    double tms = 0.0;
    int tr = lrt_hip_transform_bench(e, LRT_HIP_ISECT_SCALAR, in, gt, nt, m0, m1,
                                     times, &tms, NULL);
    CHECK(tr == 0, "transform_bench failed");
    size_t tok = 0;
    for (uint32_t i = 0; i < nt; i++) {
        float t = times[i], M[12];
        for (int k = 0; k < 12; k++) M[k] = (1.0f - t) * m0[k] + t * m1[k];
        float ex = M[0] * in[i].org[0] + M[1] * in[i].org[1] +
                   M[2] * in[i].org[2] + M[3];
        float ey = M[4] * in[i].org[0] + M[5] * in[i].org[1] +
                   M[6] * in[i].org[2] + M[7];
        if (fabsf(ex - gt[i].org[0]) < 1e-4f && fabsf(ey - gt[i].org[1]) < 1e-4f)
            tok++;
    }
    double tfrac = (double)tok / (double)nt;
    printf("  transform/motion-blur GPU vs CPU agree %.4f%% (%.3f ms)\n",
           tfrac * 100.0, tms);
    CHECK(tfrac >= 0.999, "transform agreement %.4f%% < 99.9%%", tfrac * 100.0);
    free(in);
    free(gt);
    free(times);
}

/* Refit: deform vertices, GPU-refit the resident scene, and check its trace
 * matches a CPU scene refitted (same topology) on the same deformed vertices. */
static void test_refit(lrt_hip_engine *e, const char *label, const float *verts,
                       size_t ntris, lrt_tri_layout layout, size_t nrays) {
    lrt_tri_build_options opts;
    memset(&opts, 0, sizeof(opts));
    opts.quality = LRT_TRI_BUILD_DEFAULT;
    opts.layout = layout;
    opts.num_threads = 1;
    lrt_tri_scene *s = lrt_tri_scene_build(verts, ntris, &opts, NULL);
    lrt_hip_scene *gs = lrt_hip_scene_upload(e, s, NULL);
    CHECK(s && gs, "%s: build/upload failed", label);
    if (!s || !gs) {
        if (gs) lrt_hip_scene_free(e, gs);
        if (s) lrt_tri_scene_free(s);
        return;
    }

    /* Deform: vertical wave displacement. */
    float *def = (float *)malloc(ntris * 9 * sizeof(float));
    for (size_t i = 0; i < ntris * 9; i += 3) {
        def[i + 0] = verts[i + 0];
        def[i + 1] = verts[i + 1] + 0.3f * sinf(verts[i + 0] * 1.7f);
        def[i + 2] = verts[i + 2];
    }

    lrt_result rr = lrt_tri_scene_refit(s, def, ntris);
    CHECK(rr == LRT_RESULT_OK, "%s: CPU refit failed", label);
    int gr = lrt_hip_scene_refit(e, gs, def, (uint32_t)ntris, NULL);
    CHECK(gr == 0, "%s: GPU refit failed: %s", label,
          lrt_hip_engine_last_error(e));

    lrt_ray *rays = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_hit *gh = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    for (size_t i = 0; i < nrays; i++) make_random_ray(&rays[i]);
    lrt_hip_scene_trace(e, gs, rays, (uint32_t)nrays, gh, NULL);

    size_t agree = 0;
    for (size_t i = 0; i < nrays; i++) {
        lrt_hit cpu;
        int ch = lrt_tri_intersect1(s, &rays[i], &cpu);
        int g = gh[i].prim_id != LRT_TRI_NO_HIT;
        if (ch == g && (!ch || cpu.prim_id == gh[i].prim_id)) agree++;
    }
    double frac = (double)agree / (double)nrays;
    printf("  %-22s GPU-refit vs CPU-refit agree %.4f%%\n", label, frac * 100.0);
    CHECK(frac >= 0.999, "%s: refit agreement %.4f%% < 99.9%%", label,
          frac * 100.0);

    free(def);
    free(rays);
    free(gh);
    lrt_hip_scene_free(e, gs);
    lrt_tri_scene_free(s);
}

/* GPU analytic primitives (sphere / point / quad / tetra): CPU build -> GPU
 * trace, compared against the CPU oracle (same scene). */
static void test_analytic(lrt_hip_engine *e, const char *label,
                          lrt_tri_scene *cpu, size_t nrays) {
    if (!cpu) {
        CHECK(0, "%s: CPU build failed", label);
        return;
    }
    lrt_hip_scene *gs = lrt_hip_scene_upload(e, cpu, NULL);
    CHECK(gs != NULL, "%s: GPU upload failed: %s", label,
          lrt_hip_engine_last_error(e));
    if (!gs) {
        lrt_tri_scene_free(cpu);
        return;
    }
    lrt_ray *rays = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_hit *gh = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    uint8_t *go = (uint8_t *)malloc(nrays * sizeof(uint8_t));
    for (size_t i = 0; i < nrays; i++) make_random_ray(&rays[i]);
    lrt_hip_scene_trace(e, gs, rays, (uint32_t)nrays, gh, NULL);
    lrt_hip_scene_occluded(e, gs, rays, (uint32_t)nrays, go, NULL);
    size_t agree = 0, oagree = 0;
    double max_rel = 0.0;
    for (size_t i = 0; i < nrays; i++) {
        lrt_hit c;
        int ch = lrt_tri_intersect1(cpu, &rays[i], &c);
        int g = gh[i].prim_id != LRT_TRI_NO_HIT;
        if (ch == g && (!g || c.prim_id == gh[i].prim_id)) {
            agree++;
            if (g) {
                double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                if (rel > max_rel) max_rel = rel;
            }
        } else if (ch && g) {
            double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
            if (rel < 1e-4) agree++;
        }
        int co = lrt_tri_occluded1(cpu, &rays[i]);
        if ((co != 0) == (go[i] != 0)) oagree++;
    }
    double f = (double)agree / nrays, of = (double)oagree / nrays;
    printf("  %-14s closest %.3f%% (max_rel_t %.2e)  occ %.3f%%\n", label,
           f * 100.0, max_rel, of * 100.0);
    CHECK(f >= 0.999, "%s: closest agreement %.3f%% < 99.9%%", label, f * 100.0);
    CHECK(of >= 0.999, "%s: occ agreement %.3f%% < 99.9%%", label, of * 100.0);
    free(rays);
    free(gh);
    free(go);
    lrt_hip_scene_free(e, gs);
    lrt_tri_scene_free(cpu);
}

static void test_gpu_curves(lrt_hip_engine *e) {
    /* random hair strands: nstr strands of pps points each */
    uint32_t nstr = 800, pps = 4;
    uint32_t npoints = nstr * pps;
    float *pts = (float *)malloc(npoints * 3 * sizeof(float));
    float *rad = (float *)malloc(npoints * sizeof(float));
    uint32_t *first = (uint32_t *)malloc(nstr * sizeof(uint32_t));
    uint32_t *cnt = (uint32_t *)malloc(nstr * sizeof(uint32_t));
    for (uint32_t s = 0; s < nstr; s++) {
        float base[3] = {rnd_f(-2, 2), rnd_f(-2, 2), rnd_f(-2, 2)};
        float dir[3] = {rnd_f(-1, 1), rnd_f(-1, 1), rnd_f(-1, 1)};
        first[s] = s * pps;
        cnt[s] = pps;
        for (uint32_t p = 0; p < pps; p++) {
            uint32_t i = s * pps + p;
            float u = (float)p / (float)(pps - 1);
            for (int k = 0; k < 3; k++)
                pts[i * 3 + k] = base[k] + dir[k] * u + rnd_f(-0.05f, 0.05f);
            rad[i] = rnd_f(0.02f, 0.06f);
        }
    }
    lrt_hair_strands hs;
    memset(&hs, 0, sizeof(hs));
    hs.points = pts;
    hs.radius = rad;
    hs.strand_first = first;
    hs.strand_count = cnt;
    hs.nstrands = nstr;
    hs.npoints = npoints;

    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    printf("== GPU curve primitives vs CPU oracle ==\n");

    struct {
        const char *name;
        lrt_tri_scene *(*build)(const lrt_hair_strands *,
                                const lrt_tri_build_options *, lrt_result *);
    } kinds[2] = {{"roundcurve", lrt_roundcurve_scene_build},
                  {"flatcurve", lrt_flatcurve_scene_build}};
    for (int kk = 0; kk < 2; kk++) {
        lrt_tri_scene *cpu = kinds[kk].build(&hs, &o, NULL);
        if (!cpu) {
            CHECK(0, "%s build", kinds[kk].name);
            continue;
        }
        lrt_hip_scene *gs = lrt_hip_scene_upload(e, cpu, NULL);
        CHECK(gs != NULL, "%s upload: %s", kinds[kk].name,
              lrt_hip_engine_last_error(e));
        if (!gs) {
            lrt_tri_scene_free(cpu);
            continue;
        }
        size_t nr = 30000, agree = 0;
        double max_rel = 0.0;
        lrt_ray *rays = (lrt_ray *)malloc(nr * sizeof(lrt_ray));
        lrt_hit *gh = (lrt_hit *)malloc(nr * sizeof(lrt_hit));
        for (size_t i = 0; i < nr; i++) make_random_ray(&rays[i]);
        lrt_hip_scene_trace(e, gs, rays, (uint32_t)nr, gh, NULL);
        for (size_t i = 0; i < nr; i++) {
            lrt_hit c;
            int ch = lrt_tri_intersect1(cpu, &rays[i], &c);
            int g = gh[i].prim_id != LRT_TRI_NO_HIT;
            if (ch == g && (!g || c.prim_id == gh[i].prim_id)) {
                agree++;
                if (g) {
                    double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                    if (rel > max_rel) max_rel = rel;
                }
            } else if (ch && g) {
                double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                if (rel < 1e-3) agree++;
            }
        }
        double f = (double)agree / nr;
        printf("  %-12s closest %.3f%% (max_rel_t %.2e)\n", kinds[kk].name,
               f * 100.0, max_rel);
        CHECK(f >= 0.995, "%s agreement %.3f%% < 99.5%%", kinds[kk].name,
              f * 100.0);
        free(rays);
        free(gh);
        lrt_hip_scene_free(e, gs);
        lrt_tri_scene_free(cpu);
    }
    free(pts);
    free(rad);
    free(first);
    free(cnt);
}

static void test_gpu_sdf(lrt_hip_engine *e) {
    size_t N = 2000;
    uint32_t *types = (uint32_t *)malloc(N * sizeof(uint32_t));
    float *ctr = (float *)malloc(N * 3 * sizeof(float));
    float *par = (float *)malloc(N * 3 * sizeof(float));
    for (size_t i = 0; i < N; i++) {
        types[i] = (uint32_t)(rnd_u32() % 3u); /* sphere/box/torus */
        for (int k = 0; k < 3; k++) ctr[i * 3 + k] = rnd_f(-2, 2);
        if (types[i] == LRT_SDF_SPHERE) {
            par[i * 3 + 0] = rnd_f(0.1f, 0.3f);
            par[i * 3 + 1] = par[i * 3 + 2] = 0;
        } else if (types[i] == LRT_SDF_BOX) {
            par[i * 3 + 0] = rnd_f(0.1f, 0.25f);
            par[i * 3 + 1] = rnd_f(0.1f, 0.25f);
            par[i * 3 + 2] = rnd_f(0.1f, 0.25f);
        } else {
            par[i * 3 + 0] = rnd_f(0.15f, 0.3f); /* R */
            par[i * 3 + 1] = rnd_f(0.04f, 0.1f); /* r */
            par[i * 3 + 2] = 0;
        }
    }
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    lrt_tri_scene *cpu = lrt_sdfprim_scene_build(types, ctr, par, N, &o, NULL);
    printf("== GPU built-in SDF primitives vs CPU oracle ==\n");
    if (!cpu) {
        CHECK(0, "sdf build");
        free(types); free(ctr); free(par);
        return;
    }
    lrt_hip_scene *gs = lrt_hip_scene_upload(e, cpu, NULL);
    CHECK(gs != NULL, "sdf upload: %s", lrt_hip_engine_last_error(e));
    if (gs) {
        size_t nr = 30000, agree = 0, hits = 0;
        double max_rel = 0.0;
        lrt_ray *rays = (lrt_ray *)malloc(nr * sizeof(lrt_ray));
        lrt_hit *gh = (lrt_hit *)malloc(nr * sizeof(lrt_hit));
        for (size_t i = 0; i < nr; i++) make_random_ray(&rays[i]);
        lrt_hip_scene_trace(e, gs, rays, (uint32_t)nr, gh, NULL);
        for (size_t i = 0; i < nr; i++) {
            lrt_hit c;
            int ch = lrt_tri_intersect1(cpu, &rays[i], &c);
            int g = gh[i].prim_id != LRT_TRI_NO_HIT;
            if (g) hits++;
            if (ch == g && (!g || c.prim_id == gh[i].prim_id)) {
                agree++;
                if (g) {
                    double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                    if (rel > max_rel) max_rel = rel;
                }
            } else if (ch && g) {
                double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                if (rel < 1e-3) agree++;
            }
        }
        double f = (double)agree / nr;
        printf("  sdf          closest %.3f%% (hit_frac %.3f, max_rel_t %.2e)\n",
               f * 100.0, (double)hits / nr, max_rel);
        CHECK(f >= 0.999, "sdf agreement %.3f%% < 99.9%%", f * 100.0);
        free(rays);
        free(gh);
        lrt_hip_scene_free(e, gs);
    }
    lrt_tri_scene_free(cpu);
    free(types); free(ctr); free(par);
}

static void test_gpu_bezier(lrt_hip_engine *e) {
    uint32_t nseg = 1500;
    float *cps = (float *)malloc(nseg * 16 * sizeof(float));
    for (uint32_t s = 0; s < nseg; s++) {
        float c[3] = {rnd_f(-2, 2), rnd_f(-2, 2), rnd_f(-2, 2)};
        float d[3] = {rnd_f(-0.6f, 0.6f), rnd_f(-0.6f, 0.6f), rnd_f(-0.6f, 0.6f)};
        float *cp = &cps[s * 16];
        for (int k = 0; k < 4; k++) {
            float u = (float)k / 3.0f;
            cp[k * 4 + 0] = c[0] + d[0] * u + rnd_f(-0.1f, 0.1f);
            cp[k * 4 + 1] = c[1] + d[1] * u + rnd_f(-0.1f, 0.1f);
            cp[k * 4 + 2] = c[2] + d[2] * u + rnd_f(-0.1f, 0.1f);
            cp[k * 4 + 3] = rnd_f(0.02f, 0.06f);
        }
    }
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    lrt_tri_scene *cpu = lrt_bezcurve_scene_build(cps, nseg, &o, NULL);
    printf("== GPU Bezier curves vs CPU oracle ==\n");
    if (!cpu) {
        CHECK(0, "bezier build");
        free(cps);
        return;
    }
    lrt_hip_scene *gs = lrt_hip_scene_upload(e, cpu, NULL);
    CHECK(gs != NULL, "bezier upload: %s", lrt_hip_engine_last_error(e));
    if (gs) {
        size_t nr = 40000, agree = 0, hits = 0;
        double max_rel = 0.0;
        lrt_ray *rays = (lrt_ray *)malloc(nr * sizeof(lrt_ray));
        lrt_hit *gh = (lrt_hit *)malloc(nr * sizeof(lrt_hit));
        for (size_t i = 0; i < nr; i++) make_random_ray(&rays[i]);
        lrt_hip_scene_trace(e, gs, rays, (uint32_t)nr, gh, NULL);
        for (size_t i = 0; i < nr; i++) {
            lrt_hit c;
            int ch = lrt_tri_intersect1(cpu, &rays[i], &c);
            int g = gh[i].prim_id != LRT_TRI_NO_HIT;
            if (g) hits++;
            if (ch == g && (!g || c.prim_id == gh[i].prim_id)) {
                agree++;
                if (g) {
                    double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                    if (rel > max_rel) max_rel = rel;
                }
            } else if (ch && g) {
                double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                if (rel < 1e-3) agree++;
            }
        }
        double f = (double)agree / nr;
        printf("  bezier       closest %.3f%% (hit_frac %.3f, max_rel_t %.2e)\n",
               f * 100.0, (double)hits / nr, max_rel);
        /* GPU mirrors the scalar adaptive sweep; CPU intersect1 uses the SSE
         * adaptive sweep -> tiny silhouette differences. */
        CHECK(f >= 0.99, "bezier agreement %.3f%% < 99%%", f * 100.0);
        free(rays);
        free(gh);
        lrt_hip_scene_free(e, gs);
    }
    lrt_tri_scene_free(cpu);
    free(cps);
}

/* GPU parametric surfaces (bilinear / Bézier / NURBS): CPU build -> GPU trace,
 * compared against the CPU oracle (same scene). */
static void test_gpu_surfaces(lrt_hip_engine *e) {
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    size_t N = 2000;
    printf("== GPU parametric surfaces vs CPU oracle ==\n");

    /* bilinear + bezier-patch from random control data */
    float *corners = (float *)malloc(N * 12 * sizeof(float));
    float *bcps = (float *)malloc(N * 48 * sizeof(float));
    for (size_t p = 0; p < N; p++) {
        float c[3] = {rnd_f(-2, 2), rnd_f(-2, 2), rnd_f(-2, 2)};
        float ax[3] = {rnd_f(-1, 1), rnd_f(-1, 1), rnd_f(-1, 1)};
        float ay[3] = {rnd_f(-1, 1), rnd_f(-1, 1), rnd_f(-1, 1)};
        float *q = &corners[p * 12];
        for (int k = 0; k < 3; k++) {
            float w = rnd_f(-0.25f, 0.25f);
            q[0 + k] = c[k] - 0.3f * ax[k] - 0.3f * ay[k];
            q[3 + k] = c[k] + 0.3f * ax[k] - 0.3f * ay[k] + (k == 2 ? w : 0);
            q[6 + k] = c[k] + 0.3f * ax[k] + 0.3f * ay[k];
            q[9 + k] = c[k] - 0.3f * ax[k] + 0.3f * ay[k] - (k == 2 ? w : 0);
        }
        float *cp = &bcps[p * 48];
        for (int j = 0; j < 4; j++)
            for (int i = 0; i < 4; i++) {
                float fu = (float)i / 3 - 0.5f, fv = (float)j / 3 - 0.5f;
                for (int k = 0; k < 3; k++)
                    cp[(j * 4 + i) * 3 + k] = c[k] + 0.5f * fu * ax[k] +
                                              0.5f * fv * ay[k] +
                                              rnd_f(-0.1f, 0.1f);
            }
    }
    /* one NURBS surface (its own scene) */
    const float U[9] = {0, 0, 0, 0, 0.5f, 1, 1, 1, 1};
    float net[25 * 3], w[25];
    for (int j = 0; j < 5; j++)
        for (int i = 0; i < 5; i++) {
            int idx = j * 5 + i;
            for (int k = 0; k < 3; k++)
                net[idx * 3 + k] = (k == 0 ? -1 : 0) + 0.5f * i * (k == 0) +
                                   0.5f * j * (k == 1) + rnd_f(-0.15f, 0.15f);
            w[idx] = rnd_f(0.6f, 1.8f);
        }

    struct {
        const char *name;
        lrt_tri_scene *s;
    } cases[3] = {
        {"bilinear", lrt_bilinear_scene_build(corners, N, &o, NULL)},
        {"bezpatch", lrt_bezpatch_scene_build(bcps, N, &o, NULL)},
        {"nurbs", lrt_nurbs_scene_build(net, 4, 4, U, U, w, 3, 3, &o, NULL)},
    };
    for (int ci = 0; ci < 3; ci++) {
        lrt_tri_scene *cpu = cases[ci].s;
        CHECK(cpu != NULL, "%s build", cases[ci].name);
        if (!cpu) continue;
        lrt_hip_scene *gs = lrt_hip_scene_upload(e, cpu, NULL);
        CHECK(gs != NULL, "%s upload: %s", cases[ci].name,
              lrt_hip_engine_last_error(e));
        if (!gs) {
            lrt_tri_scene_free(cpu);
            continue;
        }
        size_t nr = (ci == 2) ? 60000 : 20000, agree = 0, hits = 0;
        double max_rel = 0.0;
        lrt_ray *rays = (lrt_ray *)malloc(nr * sizeof(lrt_ray));
        lrt_hit *gh = (lrt_hit *)malloc(nr * sizeof(lrt_hit));
        for (size_t i = 0; i < nr; i++) {
            if (ci == 2) { /* NURBS near origin: aim rays at it */
                float org[3] = {rnd_f(-3, 3), rnd_f(-3, 3), rnd_f(-3, 3)};
                float d[3] = {-org[0] + rnd_f(-0.5f, 0.5f),
                              -org[1] + rnd_f(-0.5f, 0.5f),
                              -org[2] + rnd_f(-0.5f, 0.5f)};
                float l = sqrtf(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]) + 1e-9f;
                for (int k = 0; k < 3; k++) {
                    rays[i].org[k] = org[k];
                    rays[i].dir[k] = d[k] / l;
                }
                rays[i].tmin = 1e-4f;
                rays[i].tmax = 1e9f;
            } else {
                make_random_ray(&rays[i]);
            }
        }
        lrt_hip_scene_trace(e, gs, rays, (uint32_t)nr, gh, NULL);
        for (size_t i = 0; i < nr; i++) {
            lrt_hit c;
            int ch = lrt_tri_intersect1(cpu, &rays[i], &c);
            int g = gh[i].prim_id != LRT_TRI_NO_HIT;
            if (g) hits++;
            if (ch == g && (!g || c.prim_id == gh[i].prim_id)) {
                agree++;
                if (g) {
                    double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                    if (rel > max_rel) max_rel = rel;
                }
            } else if (ch && g) {
                double rel = fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                if (rel < 1e-3) agree++;
            }
        }
        double f = (double)agree / nr;
        printf("  %-10s closest %.3f%% (hit_frac %.3f, max_rel_t %.2e)\n",
               cases[ci].name, f * 100.0, (double)hits / nr, max_rel);
        CHECK(f >= 0.999, "%s GPU agreement %.3f%% < 99.9%%", cases[ci].name,
              f * 100.0);
        free(rays);
        free(gh);
        lrt_hip_scene_free(e, gs);
        lrt_tri_scene_free(cpu);
    }
    /* trimmed NURBS: GPU trace must match the CPU trimmed oracle */
    {
        int NG = 40;
        float tp[40 * 2];
        uint32_t ll[1] = {(uint32_t)NG};
        for (int i = 0; i < NG; i++) {
            float a = 6.2831853f * i / NG;
            tp[i * 2] = 0.5f + 0.3f * cosf(a);
            tp[i * 2 + 1] = 0.5f + 0.3f * sinf(a);
        }
        lrt_tri_scene *cpu = lrt_trimnurbs_scene_build(net, 4, 4, U, U, w, 3, 3,
                                                       tp, ll, 1, &o, NULL);
        CHECK(cpu != NULL, "trimnurbs build");
        if (cpu) {
            lrt_hip_scene *gs = lrt_hip_scene_upload(e, cpu, NULL);
            CHECK(gs != NULL, "trimnurbs upload: %s",
                  lrt_hip_engine_last_error(e));
            if (gs) {
                size_t nr = 60000, agree = 0, hits = 0;
                lrt_ray *rays = (lrt_ray *)malloc(nr * sizeof(lrt_ray));
                lrt_hit *gh = (lrt_hit *)malloc(nr * sizeof(lrt_hit));
                for (size_t i = 0; i < nr; i++) {
                    float og[3] = {rnd_f(-3, 3), rnd_f(-3, 3), rnd_f(-3, 3)};
                    float d[3] = {-og[0] + rnd_f(-0.5f, 0.5f),
                                  -og[1] + rnd_f(-0.5f, 0.5f),
                                  -og[2] + rnd_f(-0.5f, 0.5f)};
                    float l = sqrtf(d[0]*d[0]+d[1]*d[1]+d[2]*d[2]) + 1e-9f;
                    for (int k = 0; k < 3; k++) {
                        rays[i].org[k] = og[k];
                        rays[i].dir[k] = d[k] / l;
                    }
                    rays[i].tmin = 1e-4f;
                    rays[i].tmax = 1e9f;
                }
                lrt_hip_scene_trace(e, gs, rays, (uint32_t)nr, gh, NULL);
                for (size_t i = 0; i < nr; i++) {
                    lrt_hit c;
                    int ch = lrt_tri_intersect1(cpu, &rays[i], &c);
                    int g = gh[i].prim_id != LRT_TRI_NO_HIT;
                    if (g) hits++;
                    if (ch == g && (!g || c.prim_id == gh[i].prim_id)) {
                        agree++;
                    } else if (ch && g) {
                        double rel =
                            fabs((double)gh[i].t - c.t) / (1.0 + fabs(c.t));
                        if (rel < 1e-3) agree++;
                    }
                }
                double f = (double)agree / nr;
                printf("  %-10s closest %.3f%% (hit_frac %.3f)\n", "trimnurbs",
                       f * 100.0, (double)hits / nr);
                CHECK(f >= 0.999, "trimnurbs GPU agreement %.3f%%", f * 100.0);
                free(rays);
                free(gh);
                lrt_hip_scene_free(e, gs);
            }
            lrt_tri_scene_free(cpu);
        }
    }

    free(corners);
    free(bcps);
}

/* GPU per-hit shading normals (lrt_hip_scene_trace_normals) vs the CPU oracle
 * (lrt_tri_surface_normal for surfaces, the radial frame for round-linear). */
static void test_gpu_normals(lrt_hip_engine *e) {
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    printf("== GPU shading normals vs CPU oracle ==\n");
    const float U[9] = {0, 0, 0, 0, 0.5f, 1, 1, 1, 1};
    const size_t N = 1500;

    /* bilinear + bezpatch control data */
    float *corners = (float *)malloc(N * 12 * sizeof(float));
    float *bcps = (float *)malloc(N * 48 * sizeof(float));
    for (size_t p = 0; p < N; p++) {
        float c[3] = {rnd_f(-2, 2), rnd_f(-2, 2), rnd_f(-2, 2)};
        float ax[3] = {rnd_f(-1, 1), rnd_f(-1, 1), rnd_f(-1, 1)};
        float ay[3] = {rnd_f(-1, 1), rnd_f(-1, 1), rnd_f(-1, 1)};
        float *q = &corners[p * 12];
        for (int k = 0; k < 3; k++) {
            float wv = rnd_f(-0.25f, 0.25f);
            q[0 + k] = c[k] - 0.3f * ax[k] - 0.3f * ay[k];
            q[3 + k] = c[k] + 0.3f * ax[k] - 0.3f * ay[k] + (k == 2 ? wv : 0);
            q[6 + k] = c[k] + 0.3f * ax[k] + 0.3f * ay[k];
            q[9 + k] = c[k] - 0.3f * ax[k] + 0.3f * ay[k] - (k == 2 ? wv : 0);
        }
        float *cp = &bcps[p * 48];
        for (int j = 0; j < 4; j++)
            for (int i = 0; i < 4; i++) {
                float fu = (float)i / 3 - 0.5f, fv = (float)j / 3 - 0.5f;
                for (int k = 0; k < 3; k++)
                    cp[(j * 4 + i) * 3 + k] =
                        c[k] + 0.5f * fu * ax[k] + 0.5f * fv * ay[k] +
                        rnd_f(-0.1f, 0.1f);
            }
    }
    float net[25 * 3], w[25];
    for (int j = 0; j < 5; j++)
        for (int i = 0; i < 5; i++) {
            int idx = j * 5 + i;
            for (int k = 0; k < 3; k++)
                net[idx * 3 + k] = (k == 0 ? -1 : 0) + 0.5f * i * (k == 0) +
                                   0.5f * j * (k == 1) + rnd_f(-0.15f, 0.15f);
            w[idx] = rnd_f(0.6f, 1.8f);
        }

    /* round-linear hair strands */
    enum { NSTR = 200, PTS = 5 };
    size_t npts = (size_t)NSTR * PTS;
    float *hpts = (float *)malloc(npts * 3 * sizeof(float));
    float *hrad = (float *)malloc(npts * sizeof(float));
    uint32_t *sf = (uint32_t *)malloc(NSTR * sizeof(uint32_t));
    uint32_t *sc = (uint32_t *)malloc(NSTR * sizeof(uint32_t));
    for (int st = 0; st < NSTR; st++) {
        sf[st] = (uint32_t)(st * PTS);
        sc[st] = PTS;
        float px = rnd_f(-2, 2), py = rnd_f(-2, 2), pz = rnd_f(-2, 2);
        for (int p = 0; p < PTS; p++) {
            size_t idx = (size_t)st * PTS + p;
            px += rnd_f(-0.7f, 0.7f); py += rnd_f(-0.7f, 0.7f); pz += rnd_f(-0.7f, 0.7f);
            hpts[idx * 3 + 0] = px; hpts[idx * 3 + 1] = py; hpts[idx * 3 + 2] = pz;
            hrad[idx] = rnd_f(0.02f, 0.05f);
        }
    }
    lrt_hair_strands hs = {0};
    hs.points = hpts; hs.radius = hrad; hs.strand_first = sf;
    hs.strand_count = sc; hs.nstrands = NSTR; hs.npoints = npts;

    struct { const char *name; lrt_tri_scene *s; int curve; } cases[4] = {
        {"bilinear", lrt_bilinear_scene_build(corners, N, &o, NULL), 0},
        {"bezpatch", lrt_bezpatch_scene_build(bcps, N, &o, NULL), 0},
        {"nurbs", lrt_nurbs_scene_build(net, 4, 4, U, U, w, 3, 3, &o, NULL), 0},
        {"roundcurve", lrt_roundcurve_scene_build(&hs, NULL, NULL), 1},
    };
    for (int ci = 0; ci < 4; ci++) {
        lrt_tri_scene *cpu = cases[ci].s;
        CHECK(cpu != NULL, "%s build", cases[ci].name);
        if (!cpu) continue;
        lrt_hip_scene *gs = lrt_hip_scene_upload(e, cpu, NULL);
        CHECK(gs != NULL, "%s upload: %s", cases[ci].name,
              lrt_hip_engine_last_error(e));
        if (!gs) { lrt_tri_scene_free(cpu); continue; }
        size_t nr = 40000, hits = 0, agree = 0;
        double max_dot = 1.0;
        lrt_ray *rays = (lrt_ray *)malloc(nr * sizeof(lrt_ray));
        lrt_hit *gh = (lrt_hit *)malloc(nr * sizeof(lrt_hit));
        float *gn = (float *)malloc(nr * 3 * sizeof(float));
        for (size_t i = 0; i < nr; i++) {
            if (ci == 2) { /* aim at the NURBS near origin */
                float org[3] = {rnd_f(-3, 3), rnd_f(-3, 3), rnd_f(-3, 3)};
                float d[3] = {-org[0] + rnd_f(-0.5f, 0.5f),
                              -org[1] + rnd_f(-0.5f, 0.5f),
                              -org[2] + rnd_f(-0.5f, 0.5f)};
                float l = sqrtf(d[0]*d[0]+d[1]*d[1]+d[2]*d[2]) + 1e-9f;
                for (int k = 0; k < 3; k++) { rays[i].org[k]=org[k]; rays[i].dir[k]=d[k]/l; }
                rays[i].tmin = 1e-4f; rays[i].tmax = 1e9f;
            } else {
                make_random_ray(&rays[i]);
            }
        }
        lrt_result er = LRT_RESULT_OK;
        int rc = lrt_hip_scene_trace_normals(e, gs, rays, (uint32_t)nr, gh, gn, &er);
        CHECK(rc >= 0 && er == LRT_RESULT_OK, "%s trace_normals err=%d",
              cases[ci].name, (int)er);
        for (size_t i = 0; i < nr; i++) {
            if (gh[i].prim_id == LRT_TRI_NO_HIT) continue;
            hits++;
            float Ncpu[3];
            if (cases[ci].curve) {
                /* round-linear: radial normal from the centerline frame + hit P */
                float C[3], T[3], rr;
                if (lrt_tri_curve_frame(cpu, gh[i].prim_id, gh[i].u, C, T, &rr) !=
                    LRT_RESULT_OK)
                    continue;
                float P[3];
                for (int k = 0; k < 3; k++) P[k] = rays[i].org[k] + gh[i].t * rays[i].dir[k];
                float d[3] = {P[0]-C[0], P[1]-C[1], P[2]-C[2]};
                float tt = T[0]*T[0]+T[1]*T[1]+T[2]*T[2];
                float pr = (d[0]*T[0]+d[1]*T[1]+d[2]*T[2])/(tt>1e-20f?tt:1e-20f);
                for (int k = 0; k < 3; k++) Ncpu[k] = d[k] - pr * T[k];
            } else {
                if (lrt_tri_surface_normal(cpu, gh[i].prim_id, gh[i].u, gh[i].v,
                                           NULL, Ncpu, NULL, NULL) != LRT_RESULT_OK)
                    continue;
            }
            float lc = sqrtf(Ncpu[0]*Ncpu[0]+Ncpu[1]*Ncpu[1]+Ncpu[2]*Ncpu[2]);
            const float *Ng = &gn[i * 3];
            float lg = sqrtf(Ng[0]*Ng[0]+Ng[1]*Ng[1]+Ng[2]*Ng[2]);
            if (lc < 1e-12f || lg < 1e-12f) { agree++; continue; } /* degenerate */
            float dot = (Ncpu[0]*Ng[0]+Ncpu[1]*Ng[1]+Ncpu[2]*Ng[2]) / (lc*lg);
            if (dot > 0.999f) agree++;
            if (dot < max_dot) max_dot = dot;
        }
        double f = hits ? (double)agree / hits : 1.0;
        printf("  %-10s normals %.3f%% (hits %zu, min cos %.5f)\n",
               cases[ci].name, f * 100.0, hits, max_dot);
        CHECK(hits > nr / 100, "%s: too few hits", cases[ci].name);
        CHECK(f >= 0.999, "%s: GPU normal agreement %.3f%%", cases[ci].name,
              f * 100.0);

        /* Device-resident path (lrt_hip_scene_trace_normals_device): same kernel
         * over dbuffer in/out — must produce bit-identical normals to the host
         * D2H path above. */
        lrt_hip_dbuffer *drays = lrt_hip_dbuffer_alloc(e, nr * sizeof(lrt_ray), NULL);
        lrt_hip_dbuffer *dhits = lrt_hip_dbuffer_alloc(e, nr * sizeof(lrt_hit), NULL);
        lrt_hip_dbuffer *dnrm = lrt_hip_dbuffer_alloc(e, nr * 3 * sizeof(float), NULL);
        CHECK(drays && dhits && dnrm, "%s: dbuffer alloc", cases[ci].name);
        if (drays && dhits && dnrm) {
            lrt_hip_dbuffer_upload(e, drays, rays, nr * sizeof(lrt_ray), NULL);
            lrt_result de = LRT_RESULT_OK;
            int dr = lrt_hip_scene_trace_normals_device(e, gs, drays, (uint32_t)nr,
                                                        dhits, dnrm, &de);
            CHECK(dr == 0 && de == LRT_RESULT_OK,
                  "%s: trace_normals_device err=%d", cases[ci].name, (int)de);
            float *dn = (float *)malloc(nr * 3 * sizeof(float));
            lrt_hip_dbuffer_download(e, dnrm, dn, nr * 3 * sizeof(float), NULL);
            size_t mism = 0;
            for (size_t i = 0; i < nr * 3; i++)
                if (dn[i] != gn[i]) mism++; /* same kernel -> exact match */
            CHECK(mism == 0, "%s: device-resident normals differ from host (%zu)",
                  cases[ci].name, mism);
            free(dn);
        }
        lrt_hip_dbuffer_free(e, drays);
        lrt_hip_dbuffer_free(e, dhits);
        lrt_hip_dbuffer_free(e, dnrm);

        free(rays); free(gh); free(gn);
        lrt_hip_scene_free(e, gs);
        lrt_tri_scene_free(cpu);
    }

    /* a triangle scene has no shade data -> UNSUPPORTED */
    {
        float tri[9] = {0, 0, 0, 1, 0, 0, 0, 1, 0};
        lrt_tri_scene *ts = lrt_tri_scene_build(tri, 1, &o, NULL);
        lrt_hip_scene *gs = ts ? lrt_hip_scene_upload(e, ts, NULL) : NULL;
        if (gs) {
            lrt_ray r;
            make_random_ray(&r);
            lrt_hit h;
            float nrm[3];
            lrt_result er = LRT_RESULT_OK;
            int rc = lrt_hip_scene_trace_normals(e, gs, &r, 1, &h, nrm, &er);
            CHECK(rc < 0 && er == LRT_RESULT_UNSUPPORTED,
                  "triangle trace_normals should be UNSUPPORTED (rc=%d err=%d)",
                  rc, (int)er);
            lrt_hip_scene_free(e, gs);
        }
        if (ts) lrt_tri_scene_free(ts);
    }
    free(corners); free(bcps);
    free(hpts); free(hrad); free(sf); free(sc);
}

static void test_gpu_analytics(lrt_hip_engine *e) {
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    size_t N = 3000;
    printf("== GPU analytic primitives vs CPU oracle ==\n");

    float *sph = (float *)malloc(N * 4 * sizeof(float));
    for (size_t i = 0; i < N; i++) {
        sph[i * 4 + 0] = rnd_f(-2, 2);
        sph[i * 4 + 1] = rnd_f(-2, 2);
        sph[i * 4 + 2] = rnd_f(-2, 2);
        sph[i * 4 + 3] = rnd_f(0.05f, 0.25f);
    }
    test_analytic(e, "sphere", lrt_sphere_scene_build(sph, N, &o, NULL), 20000);
    free(sph);

    float *ctr = (float *)malloc(N * 3 * sizeof(float));
    float *rad = (float *)malloc(N * sizeof(float));
    float *nrm = (float *)malloc(N * 3 * sizeof(float));
    for (size_t i = 0; i < N; i++) {
        for (int k = 0; k < 3; k++) {
            ctr[i * 3 + k] = rnd_f(-2, 2);
            nrm[i * 3 + k] = rnd_f(-1, 1);
        }
        rad[i] = rnd_f(0.05f, 0.2f);
    }
    test_analytic(e, "point/sphere",
                  lrt_points_scene_build(ctr, rad, NULL, LRT_POINT_SPHERE, N,
                                         &o, NULL),
                  20000);
    test_analytic(e, "point/disc",
                  lrt_points_scene_build(ctr, rad, NULL, LRT_POINT_DISC, N, &o,
                                         NULL),
                  20000);
    test_analytic(e, "point/odisc",
                  lrt_points_scene_build(ctr, rad, nrm, LRT_POINT_ORIENTED_DISC,
                                         N, &o, NULL),
                  20000);
    free(ctr);
    free(rad);
    free(nrm);

    float *quads = (float *)malloc(N * 12 * sizeof(float));
    float *tets = (float *)malloc(N * 12 * sizeof(float));
    for (size_t i = 0; i < N; i++) {
        float c[3] = {rnd_f(-2, 2), rnd_f(-2, 2), rnd_f(-2, 2)};
        float a[3] = {rnd_f(-1, 1), rnd_f(-1, 1), rnd_f(-1, 1)};
        float b[3] = {rnd_f(-1, 1), rnd_f(-1, 1), rnd_f(-1, 1)};
        float *q = &quads[i * 12];
        for (int k = 0; k < 3; k++) {
            q[0 + k] = c[k] - 0.3f * a[k] - 0.3f * b[k];
            q[3 + k] = c[k] + 0.3f * a[k] - 0.3f * b[k];
            q[6 + k] = c[k] + 0.3f * a[k] + 0.3f * b[k];
            q[9 + k] = c[k] - 0.3f * a[k] + 0.3f * b[k];
        }
        float *t = &tets[i * 12];
        for (int vtx = 0; vtx < 4; vtx++)
            for (int k = 0; k < 3; k++)
                t[vtx * 3 + k] = c[k] + rnd_f(-0.3f, 0.3f);
    }
    test_analytic(e, "quad", lrt_quad_scene_build(quads, N, &o, NULL), 20000);
    test_analytic(e, "tetra", lrt_tetra_scene_build(tets, N, &o, NULL), 20000);
    free(quads);
    free(tets);
}

int main(void) {
    lrt_result err = LRT_RESULT_OK;
    lrt_hip_engine *e = lrt_hip_engine_create(NULL, &err);
    if (!e) {
        printf("lightrt_c_hip: no HIP device available (skipping). reason=%d\n",
               (int)err);
        return 0; /* graceful skip */
    }
    printf("HIP device: %s  caps=0x%x\n", lrt_hip_engine_device_name(e),
           lrt_hip_engine_caps(e));

    size_t ntris = 4000;
    float *soup = make_random_soup(ntris, 0.15f);
    size_t grid_n = 0;
    float *grid = make_grid_soup(48, &grid_n);

    printf("== closest-hit + occlusion vs CPU oracle ==\n");
    test_trace(e, "random/BVH4", soup, ntris, LRT_TRI_LAYOUT_BVH4, 20000);
    test_trace(e, "random/BVH8", soup, ntris, LRT_TRI_LAYOUT_BVH8, 20000);
    test_trace(e, "grid/BVH4", grid, grid_n, LRT_TRI_LAYOUT_BVH4, 20000);
    test_trace(e, "grid/BVH8", grid, grid_n, LRT_TRI_LAYOUT_BVH8, 20000);

    printf("== Path B (GPU-Morton build) vs CPU FAST ==\n");
    test_build(e, "build/BVH4", soup, ntris, LRT_TRI_LAYOUT_BVH4, 20000);
    test_build(e, "build/BVH8", grid, grid_n, LRT_TRI_LAYOUT_BVH8, 20000);

    printf("== Full-GPU LBVH (lrt_hip_scene_build_gpu) vs CPU oracle ==\n");
    if (lrt_hip_have_gpu_build()) {
        test_gpu_build(e, "gpu-lbvh/random", soup, ntris, 20000);
        test_gpu_build(e, "gpu-lbvh/grid", grid, grid_n, 20000);
    } else {
        printf("  (hipCUB not compiled in, skipping)\n");
    }

    printf("== GPU refit (animation) vs CPU refit ==\n");
    test_refit(e, "refit/BVH4", soup, ntris, LRT_TRI_LAYOUT_BVH4, 20000);
    test_refit(e, "refit/BVH8", grid, grid_n, LRT_TRI_LAYOUT_BVH8, 20000);

    test_device_pipeline(e, soup, ntris);

    test_gpu_analytics(e);

    test_gpu_curves(e);

    test_gpu_bezier(e);

    test_gpu_sdf(e);

    test_gpu_surfaces(e);

    test_gpu_normals(e);

    test_wmma(e);

    free(soup);
    free(grid);
    lrt_hip_engine_destroy(e);

    if (g_failures) {
        printf("\n%d FAILURES\n", g_failures);
        return 1;
    }
    printf("\nAll HIP tests passed.\n");
    return 0;
}
