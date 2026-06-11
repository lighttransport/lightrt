/*
 * bench_main.c — LightRT C11 ray tracing benchmark harness.
 *
 * Generates a procedural scene (mandelbulb via marching cubes), builds it with
 * one or more backends (lightrt C11 callback API, lightrt fp32 triangle API,
 * Embree), and measures BVH build time and ray throughput for coherent
 * primary, incoherent random, and shadow/occlusion workloads, single- or
 * multi-threaded. Results go to stdout and optionally a CSV.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(__linux__)
#include <sys/prctl.h>
#endif

#include "backend.h"
#include "rays.h"
#include "scene_mandelbulb.h"
#include "timing.h"

#define MAX_BACKENDS 16
#define MAX_THREADS 256

typedef struct {
    const char *scene;
    int fineness;
    int power;
    const char *backends; /* comma list or "all" */
    const char *workloads; /* comma list or "all" */
    size_t nrays;
    int threads;
    int repeat;
    uint32_t seed;
    const char *csv_path;
    int verify;
} bench_config;

static void usage(const char *argv0) {
    fprintf(stderr,
            "usage: %s [options]\n"
            "  --scene mandelbulb     procedural scene (default mandelbulb)\n"
            "  --fineness N           marching-cubes grid resolution (default 128)\n"
            "  --power N              mandelbulb power (default 8)\n"
            "  --backend LIST         all | comma list of: c11-cb,c11-bvh4,c11-bvh8,\n"
            "                         c11-lbvh4,c11-lbvh8 (Morton fast build),\n"
            "                         c11-bvh8q (quantized nodes), c11-sbvh4 (spatial\n"
            "                         splits), embree, tinybvh, mm-bvh\n"
            "  --rays LIST            all | comma list of: primary,incoherent,shadow\n"
            "  --nrays N              rays per workload (default 4000000)\n"
            "  --threads N            worker threads (default 1)\n"
            "  --repeat N             timed repetitions, median reported (default 5)\n"
            "  --seed N               workload RNG seed (default 1234)\n"
            "  --csv PATH             append results to CSV (header written if new)\n"
            "  --verify               cross-check hits against the c11-cb fp64 oracle\n",
            argv0);
}

/* ------------------------------------------------------------------------- */
/* Multithreaded ray dispatch.                                               */
/* ------------------------------------------------------------------------- */

typedef struct {
    const bench_backend *bk;
    void *scene;
    int thread_idx;
    const lrt_ray *rays;
    lrt_hit *hits;
    uint8_t *occ;
    size_t n;
    int occlusion;
    int coherent;
} worker_args;

static void *worker_main(void *p) {
    worker_args *w = (worker_args *)p;
    if (w->n == 0) return NULL;
    if (w->occlusion) {
        w->bk->occluded1N(w->scene, w->thread_idx, w->rays, w->occ, w->n,
                          w->coherent);
    } else {
        w->bk->intersect1N(w->scene, w->thread_idx, w->rays, w->hits, w->n,
                           w->coherent);
    }
    return NULL;
}

/* Runs the workload across `threads` workers; returns wall seconds. */
static double run_rays(const bench_backend *bk, void *scene, int threads,
                       const lrt_ray *rays, lrt_hit *hits, uint8_t *occ,
                       size_t n, int occlusion, int coherent) {
    uint64_t t0 = bench_time_ns();
    if (threads <= 1) {
        worker_args w = {bk, scene, 0, rays, hits, occ, n, occlusion, coherent};
        worker_main(&w);
    } else {
        pthread_t tid[MAX_THREADS];
        worker_args wa[MAX_THREADS];
        size_t chunk = (n + (size_t)threads - 1) / (size_t)threads;
        int spawned = 0;
        for (int t = 0; t < threads; t++) {
            size_t lo = (size_t)t * chunk;
            if (lo >= n) break;
            size_t cnt = chunk < n - lo ? chunk : n - lo;
            wa[t] = (worker_args){bk,
                                  scene,
                                  t,
                                  rays + lo,
                                  hits ? hits + lo : NULL,
                                  occ ? occ + lo : NULL,
                                  cnt,
                                  occlusion,
                                  coherent};
            pthread_create(&tid[t], NULL, worker_main, &wa[t]);
            spawned++;
        }
        for (int t = 0; t < spawned; t++) pthread_join(tid[t], NULL);
    }
    uint64_t t1 = bench_time_ns();
    return bench_ns_to_s(t1 - t0);
}

static int cmp_double(const void *a, const void *b) {
    double da = *(const double *)a, db = *(const double *)b;
    return (da > db) - (da < db);
}

/* ------------------------------------------------------------------------- */
/* Verification against the fp64 callback oracle.                            */
/* ------------------------------------------------------------------------- */

static int verify_backend(const bench_backend *bk, void *scene,
                          const bench_backend *oracle_bk, void *oracle_scene,
                          const lrt_ray *rays, size_t n, const char *workload) {
    size_t sample = n < 100000 ? n : 100000;
    lrt_hit *h = (lrt_hit *)malloc(sample * sizeof(lrt_hit));
    lrt_hit *ho = (lrt_hit *)malloc(sample * sizeof(lrt_hit));
    if (!h || !ho) {
        free(h);
        free(ho);
        return 0;
    }
    bk->intersect1N(scene, 0, rays, h, sample, 0);
    oracle_bk->intersect1N(oracle_scene, 0, rays, ho, sample, 0);

    /* A mismatch is a hit/miss disagreement or a hit whose distance differs
     * beyond fp32 noise. A handful of edge rays legitimately differ between
     * the fp32 traversals and the fp64 oracle (Embree shows the same rate),
     * so the criterion is an agreement fraction, not zero mismatches. */
    size_t mismatch = 0;
    double max_rel = 0.0;
    for (size_t i = 0; i < sample; i++) {
        int hit_a = h[i].prim_id != LRT_TRI_NO_HIT;
        int hit_b = ho[i].prim_id != LRT_TRI_NO_HIT;
        if (hit_a != hit_b) {
            mismatch++;
            continue;
        }
        if (hit_a) {
            double denom = fabs((double)ho[i].t) > 1e-12 ? fabs((double)ho[i].t) : 1e-12;
            double rel = fabs((double)h[i].t - (double)ho[i].t) / denom;
            if (rel > max_rel) max_rel = rel;
            if (rel > 1e-3) mismatch++;
        }
    }
    double agree_frac = 1.0 - (double)mismatch / (double)sample;
    int pass = agree_frac >= 0.999;
    printf("  verify %-10s %-10s: agreement %.4f%% max_rel_t %.3e %s\n",
           bk->name, workload, agree_frac * 100.0, max_rel,
           pass ? "PASS" : "FAIL");
    free(h);
    free(ho);
    return pass;
}

/* ------------------------------------------------------------------------- */

static FILE *open_csv(const char *path) {
    if (!path) return NULL;
    FILE *probe = fopen(path, "r");
    int need_header = probe == NULL;
    if (probe) fclose(probe);
    FILE *f = fopen(path, "a");
    if (f && need_header) {
        fprintf(f, "backend,scene,ntris,build_ms,build_mtris_s,mem_mb,workload,"
                   "threads,mrays_s,hit_frac\n");
    }
    return f;
}

int main(int argc, char **argv) {
#if defined(__linux__) && defined(PR_SET_THP_DISABLE)
    /* Some launch environments disable transparent huge pages per process
     * (THP_enabled: 0 in /proc/self/status), which silently defeats both our
     * MADV_HUGEPAGE arenas and Embree's huge-page allocator and inflates dTLB
     * misses on incoherent workloads. Re-enable for a level playing field. */
    (void)prctl(PR_SET_THP_DISABLE, 0, 0, 0, 0);
#endif
    bench_config cfg = {
        .scene = "mandelbulb",
        .fineness = 128,
        .power = 8,
        .backends = "all",
        .workloads = "all",
        .nrays = 4000000,
        .threads = 1,
        .repeat = 5,
        .seed = 1234,
        .csv_path = NULL,
        .verify = 0,
    };

    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        const char *next = (i + 1 < argc) ? argv[i + 1] : NULL;
        if (!strcmp(a, "--scene") && next) cfg.scene = argv[++i];
        else if (!strcmp(a, "--fineness") && next) cfg.fineness = atoi(argv[++i]);
        else if (!strcmp(a, "--power") && next) cfg.power = atoi(argv[++i]);
        else if (!strcmp(a, "--backend") && next) cfg.backends = argv[++i];
        else if (!strcmp(a, "--rays") && next) cfg.workloads = argv[++i];
        else if (!strcmp(a, "--nrays") && next) cfg.nrays = (size_t)atoll(argv[++i]);
        else if (!strcmp(a, "--threads") && next) cfg.threads = atoi(argv[++i]);
        else if (!strcmp(a, "--repeat") && next) cfg.repeat = atoi(argv[++i]);
        else if (!strcmp(a, "--seed") && next) cfg.seed = (uint32_t)strtoul(argv[++i], NULL, 10);
        else if (!strcmp(a, "--csv") && next) cfg.csv_path = argv[++i];
        else if (!strcmp(a, "--verify")) cfg.verify = 1;
        else if (!strcmp(a, "--help") || !strcmp(a, "-h")) { usage(argv[0]); return 0; }
        else { fprintf(stderr, "unknown option: %s\n", a); usage(argv[0]); return 1; }
    }
    if (cfg.threads < 1) cfg.threads = 1;
    if (cfg.threads > MAX_THREADS) cfg.threads = MAX_THREADS;
    if (cfg.repeat < 1) cfg.repeat = 1;
    if (cfg.nrays < 1024) cfg.nrays = 1024;

    if (strcmp(cfg.scene, "mandelbulb") != 0) {
        fprintf(stderr, "unknown scene: %s\n", cfg.scene);
        return 1;
    }

    /* --- Scene generation --- */
    float *verts = NULL;
    uint64_t g0 = bench_time_ns();
    size_t ntris = scene_mandelbulb_generate(cfg.fineness, cfg.power, &verts);
    uint64_t g1 = bench_time_ns();
    if (ntris == 0) {
        fprintf(stderr, "scene generation failed\n");
        return 1;
    }
    printf("scene: %s fineness=%d power=%d -> %zu triangles (%.1f ms)\n",
           cfg.scene, cfg.fineness, cfg.power, ntris, bench_ns_to_ms(g1 - g0));

    /* --- Resolve backends --- */
    const bench_backend *all_bk[MAX_BACKENDS];
    int nbk = 0;
    {
        const struct {
            const char *name;
            const bench_backend *(*get)(void);
        } registry[] = {
            {"c11-cb", backend_lightrt_cb},
            {"c11-bvh4", backend_lightrt_bvh4},
            {"c11-bvh8", backend_lightrt_bvh8},
            {"c11-lbvh4", backend_lightrt_lbvh4},
            {"c11-lbvh8", backend_lightrt_lbvh8},
            {"c11-bvh8q", backend_lightrt_bvh8q},
            {"c11-sbvh4", backend_lightrt_sbvh4},
            {"embree", backend_embree},
            {"tinybvh", backend_tinybvh},
            {"mm-bvh", backend_madmann},
        };
        int want_all = !strcmp(cfg.backends, "all");
        for (size_t r = 0; r < sizeof(registry) / sizeof(registry[0]); r++) {
            int wanted = want_all;
            if (!wanted) {
                char buf[256];
                snprintf(buf, sizeof(buf), ",%s,", cfg.backends);
                char pat[64];
                snprintf(pat, sizeof(pat), ",%s,", registry[r].name);
                wanted = strstr(buf, pat) != NULL;
            }
            if (!wanted) continue;
            const bench_backend *bk = registry[r].get();
            if (bk) {
                all_bk[nbk++] = bk;
            } else if (!want_all) {
                fprintf(stderr, "backend %s not available in this build\n",
                        registry[r].name);
                return 1;
            }
        }
    }
    if (nbk == 0) {
        fprintf(stderr, "no backends selected\n");
        return 1;
    }

    int want_primary = !strcmp(cfg.workloads, "all") || strstr(cfg.workloads, "primary");
    int want_incoherent = !strcmp(cfg.workloads, "all") || strstr(cfg.workloads, "incoherent");
    int want_shadow = !strcmp(cfg.workloads, "all") || strstr(cfg.workloads, "shadow");

    /* --- Ray sets (identical across backends) --- */
    size_t n = cfg.nrays;
    lrt_ray *primary = (lrt_ray *)malloc(n * sizeof(lrt_ray));
    lrt_ray *incoherent = (lrt_ray *)malloc(n * sizeof(lrt_ray));
    lrt_ray *shadow = (lrt_ray *)malloc(n * sizeof(lrt_ray));
    lrt_hit *hits = (lrt_hit *)malloc(n * sizeof(lrt_hit));
    uint8_t *occ = (uint8_t *)malloc(n * sizeof(uint8_t));
    if (!primary || !incoherent || !shadow || !hits || !occ) {
        fprintf(stderr, "out of memory for ray buffers\n");
        return 1;
    }
    rays_gen_primary(primary, n, cfg.seed);
    rays_gen_incoherent(incoherent, n, cfg.seed);
    int shadow_ready = 0; /* derived from the first backend's primary hits */

    FILE *csv = open_csv(cfg.csv_path);

    /* Oracle for --verify */
    void *oracle_scene = NULL;
    const bench_backend *oracle_bk = backend_lightrt_cb();
    if (cfg.verify) {
        double oracle_ms;
        oracle_scene = oracle_bk->build(verts, ntris, 1, &oracle_ms);
        if (!oracle_scene) {
            fprintf(stderr, "oracle build failed\n");
            return 1;
        }
    }

    int verify_failures = 0;

    for (int b = 0; b < nbk; b++) {
        const bench_backend *bk = all_bk[b];
        double build_ms = 0.0;
        void *scene = bk->build(verts, ntris, cfg.threads, &build_ms);
        if (!scene) {
            fprintf(stderr, "%s: build failed\n", bk->name);
            continue;
        }
        double build_mtris_s = build_ms > 0.0 ? (double)ntris / build_ms / 1e3 : 0.0;
        double mem_mb = (double)bk->memory_bytes(scene) / (1024.0 * 1024.0);
        printf("%-10s build %8.1f ms (%6.2f Mtris/s)  mem %7.2f MB\n", bk->name,
               build_ms, build_mtris_s, mem_mb);

        /* Derive shadow rays once, from the first backend processed. */
        if (want_shadow && !shadow_ready) {
            bk->intersect1N(scene, 0, primary, hits, n, 1);
            rays_gen_shadow(shadow, n, primary, hits, verts, ntris, cfg.seed);
            shadow_ready = 1;
        }

        struct {
            const char *name;
            const lrt_ray *rays;
            int occlusion;
            int enabled;
            int coherent;
        } workloads[] = {
            {"primary", primary, 0, want_primary, 1},
            {"incoherent", incoherent, 0, want_incoherent, 0},
            {"shadow", shadow, 1, want_shadow, 1},
        };

        for (size_t w = 0; w < sizeof(workloads) / sizeof(workloads[0]); w++) {
            if (!workloads[w].enabled) continue;
            const lrt_ray *rays = workloads[w].rays;
            int occlusion = workloads[w].occlusion;
            int coherent = workloads[w].coherent;

            /* Warm-up, also produces hit_frac. */
            run_rays(bk, scene, cfg.threads, rays, hits, occ, n, occlusion,
                     coherent);
            size_t nhit = 0;
            if (occlusion) {
                for (size_t i = 0; i < n; i++) nhit += occ[i];
            } else {
                for (size_t i = 0; i < n; i++) nhit += hits[i].prim_id != LRT_TRI_NO_HIT;
            }
            double hit_frac = (double)nhit / (double)n;

            double samples[64];
            int reps = cfg.repeat < 64 ? cfg.repeat : 64;
            for (int rep = 0; rep < reps; rep++) {
                double secs = run_rays(bk, scene, cfg.threads, rays, hits, occ,
                                       n, occlusion, coherent);
                samples[rep] = secs > 0.0 ? (double)n / secs / 1e6 : 0.0;
            }
            qsort(samples, (size_t)reps, sizeof(double), cmp_double);
            double mrays = samples[reps / 2];

            printf("%-10s %-10s threads=%-3d %9.2f Mrays/s  hit %.4f\n", bk->name,
                   workloads[w].name, cfg.threads, mrays, hit_frac);
            if (csv) {
                fprintf(csv, "%s,%s,%zu,%.3f,%.3f,%.3f,%s,%d,%.3f,%.5f\n", bk->name,
                        cfg.scene, ntris, build_ms, build_mtris_s, mem_mb,
                        workloads[w].name, cfg.threads, mrays, hit_frac);
            }

            if (cfg.verify && bk != oracle_bk && !occlusion) {
                if (!verify_backend(bk, scene, oracle_bk, oracle_scene, rays, n,
                                    workloads[w].name)) {
                    verify_failures++;
                }
            }
        }

        bk->destroy(scene);
    }

    if (oracle_scene) oracle_bk->destroy(oracle_scene);
    if (csv) fclose(csv);
    free(primary);
    free(incoherent);
    free(shadow);
    free(hits);
    free(occ);
    free(verts);

    if (cfg.verify) {
        printf("verify: %s\n", verify_failures == 0 ? "ALL PASS" : "FAILURES");
        return verify_failures == 0 ? 0 : 2;
    }
    return 0;
}
