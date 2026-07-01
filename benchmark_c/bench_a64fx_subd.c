/*
 * bench_a64fx_subd.c — A64FX throughput for parametric "subd" surfaces:
 * bicubic Bézier patches and a NURBS surface, intersected directly (no
 * tessellation) by the C11 kernel. These prim_kinds run the SCALAR path on
 * A64FX today (the NEON/SVE leaves are triangle-only), so this measures the
 * direct-patch intersector's scalar throughput and how it scales to 48 cores.
 *
 * Build (A64FX):
 *   fcc -Nclang -march=armv8.2-a+sve -O3 -std=gnu11 -D_POSIX_C_SOURCE=200809L \
 *       -I. -I.. benchmark_c/bench_a64fx_subd.c benchmark_c/rays.c \
 *       lightrt_c_tri.c -o bench_subd -lpthread -lm
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../lightrt_c_tri.h"
#include "rays.h"
#include "timing.h"

/* Wavy heightfield z = h(x,y) sampled for control points. */
static float hfield(float x, float y) {
    return 0.6f * sinf(1.7f * x) * cosf(1.3f * y) + 0.2f * sinf(3.1f * x + y);
}

/* GxG grid of bicubic Bézier patches over [-2,2]^2 (xy), height in z.
 * cps layout: 48 floats/patch, point k=j*4+i -> cps[k*3+axis]. */
static float *gen_bezpatch(int G, size_t *npatch_out) {
    size_t np = (size_t)G * G;
    float *cps = malloc(np * 48 * sizeof(float));
    float span = 4.0f / G;
    size_t p = 0;
    for (int gy = 0; gy < G; gy++)
        for (int gx = 0; gx < G; gx++) {
            float x0 = -2.0f + gx * span, y0 = -2.0f + gy * span;
            for (int j = 0; j < 4; j++)
                for (int i = 0; i < 4; i++) {
                    int k = j * 4 + i;
                    float x = x0 + span * (i / 3.0f);
                    float y = y0 + span * (j / 3.0f);
                    cps[(p * 16 + k) * 3 + 0] = x;
                    cps[(p * 16 + k) * 3 + 1] = y;
                    cps[(p * 16 + k) * 3 + 2] = hfield(x, y);
                }
            p++;
        }
    *npatch_out = np;
    return cps;
}

/* Single bicubic NURBS surface over an (n+1)x(n+1) control net, clamped uniform
 * knots, unit weights. net index (j*(n+1)+i)*3+axis. */
static float *gen_nurbs_net(int n, float **ku_out, float **kv_out) {
    int N = n + 1;
    float *net = malloc((size_t)N * N * 3 * sizeof(float));
    for (int j = 0; j < N; j++)
        for (int i = 0; i < N; i++) {
            float x = -2.0f + 4.0f * i / (N - 1);
            float y = -2.0f + 4.0f * j / (N - 1);
            net[(j * N + i) * 3 + 0] = x;
            net[(j * N + i) * 3 + 1] = y;
            net[(j * N + i) * 3 + 2] = hfield(x, y);
        }
    int deg = 3;
    int nk = n + deg + 2; /* knots length */
    float *ku = malloc(nk * sizeof(float)), *kv = malloc(nk * sizeof(float));
    int interior = nk - 2 * (deg + 1);
    for (int t = 0; t < nk; t++) {
        float v;
        if (t <= deg) v = 0.0f;
        else if (t >= nk - deg - 1) v = 1.0f;
        else v = (float)(t - deg) / (float)(interior + 1);
        ku[t] = v; kv[t] = v;
    }
    *ku_out = ku; *kv_out = kv;
    return net;
}

typedef struct {
    lrt_tri_scene *s;
    const lrt_ray *rays;
    size_t lo, hi;
    size_t hits;
} job_t;

static void *worker(void *arg) {
    job_t *j = arg;
    size_t h = 0;
    lrt_hit hit;
    for (size_t i = j->lo; i < j->hi; i++)
        if (lrt_tri_intersect1(j->s, &j->rays[i], &hit)) h++;
    j->hits = h;
    return NULL;
}

static double run(lrt_tri_scene *s, const lrt_ray *rays, size_t n, int nt,
                  double *hitfrac) {
    pthread_t th[256];
    job_t jobs[256];
    if (nt > 256) nt = 256;
    size_t per = (n + nt - 1) / nt;
    uint64_t t0 = bench_time_ns();
    for (int t = 0; t < nt; t++) {
        jobs[t].s = s; jobs[t].rays = rays;
        jobs[t].lo = (size_t)t * per;
        jobs[t].hi = jobs[t].lo + per; if (jobs[t].hi > n) jobs[t].hi = n;
        if (jobs[t].lo > n) jobs[t].lo = n;
        pthread_create(&th[t], NULL, worker, &jobs[t]);
    }
    size_t hits = 0;
    for (int t = 0; t < nt; t++) { pthread_join(th[t], NULL); hits += jobs[t].hits; }
    double secs = bench_ns_to_s(bench_time_ns() - t0);
    if (hitfrac) *hitfrac = (double)hits / (double)n;
    return secs;
}

static void bench_scene(const char *name, lrt_tri_scene *s, double build_ms,
                        const lrt_ray *prim, const lrt_ray *inc, size_t n,
                        int nt, int rep) {
    if (!s) { printf("  %-10s BUILD FAILED\n", name); return; }
    printf("  %-10s build %8.1f ms   kernel=%s\n", name, build_ms,
           lrt_tri_kernel_name(s));
    const lrt_ray *sets[2] = {prim, inc};
    const char *wl[2] = {"primary", "incoherent"};
    for (int w = 0; w < 2; w++) {
        double best = 1e30, hf = 0;
        for (int r = 0; r < rep; r++) {
            double hh, sc = run(s, sets[w], n, nt, &hh);
            if (sc < best) { best = sc; hf = hh; }
        }
        printf("  %-10s %-11s threads=%d  %8.3f Mrays/s  hit %.4f\n",
               name, wl[w], nt, (double)n / best / 1e6, hf);
    }
}

int main(int argc, char **argv) {
    int G = 40, nrays = 4000000, nt = 48, rep = 3, nurbs_n = 24;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--patches") && i + 1 < argc) G = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--nrays") && i + 1 < argc) nrays = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--threads") && i + 1 < argc) nt = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--repeat") && i + 1 < argc) rep = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--nurbs") && i + 1 < argc) nurbs_n = atoi(argv[++i]);
    }
    printf("A64FX parametric-surface (subd) benchmark: %dx%d bezpatch grid, "
           "NURBS %dx%d net, %d rays, %d threads\n",
           G, G, nurbs_n + 1, nurbs_n + 1, nrays, nt);

    lrt_ray *prim = malloc((size_t)nrays * sizeof(lrt_ray));
    lrt_ray *inc = malloc((size_t)nrays * sizeof(lrt_ray));
    rays_gen_primary(prim, nrays, 1234);
    rays_gen_incoherent(inc, nrays, 1234);

    /* Bicubic Bézier patches. */
    size_t np;
    float *cps = gen_bezpatch(G, &np);
    uint64_t b0 = bench_time_ns();
    lrt_tri_scene *bez = lrt_bezpatch_scene_build(cps, np, NULL, NULL);
    double bez_ms = bench_ns_to_ms(bench_time_ns() - b0);
    printf("\nbezpatch: %zu patches\n", np);
    bench_scene("bezpatch", bez, bez_ms, prim, inc, nrays, nt, rep);

    /* NURBS surface. */
    float *ku, *kv;
    float *net = gen_nurbs_net(nurbs_n, &ku, &kv);
    b0 = bench_time_ns();
    lrt_tri_scene *nb = lrt_nurbs_scene_build(net, nurbs_n, nurbs_n, ku, kv, NULL,
                                              3, 3, NULL, NULL);
    double nb_ms = bench_ns_to_ms(bench_time_ns() - b0);
    printf("\nnurbs: %dx%d control net (bicubic)\n", nurbs_n + 1, nurbs_n + 1);
    bench_scene("nurbs", nb, nb_ms, prim, inc, nrays, nt, rep);

    printf("\nNote: parametric surfaces use the SCALAR path on A64FX (NEON/SVE\n"
           "leaves are triangle-only); these are direct ray-patch intersections,\n"
           "not tessellation. SVE-vectorizing the Newton/subdivision leaf is\n"
           "future work.\n");
    return 0;
}
