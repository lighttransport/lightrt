/*
 * bench_a64fx_volume.c — A64FX dense-grid VOLUME RAYMARCH microbenchmark.
 *
 * Unlike the analytic SDF path (compute-bound), this marches a real N^3 float
 * density grid with trilinear sampling + front-to-back compositing — the
 * classic memory-bandwidth-bound workload. It reports Mrays/s, Msamples/s and
 * the *effective* HBM2 bandwidth (GB/s) so you can see where A64FX's ~1 TB/s
 * HBM2 saturates, and how coherent (primary) vs incoherent (random 3D gather)
 * rays differ once the grid spills out of cache.
 *
 * No BVH/intersector — pure raymarch — so it isolates the bandwidth question.
 *
 * Build (A64FX):
 *   fcc -Nclang -march=armv8.2-a+sve -O3 -std=gnu11 -D_POSIX_C_SOURCE=200809L \
 *       -I. -I.. benchmark_c/bench_a64fx_volume.c benchmark_c/rays.c \
 *       -o bench_volume -lpthread -lm
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../lightrt_c_tri.h" /* lrt_ray */
#include "rays.h"
#include "timing.h"

static int N;            /* grid resolution (N^3) */
static float *g_vol;     /* density grid, N^3 floats */
static int g_steps;      /* march steps across the box */
/* volume occupies world [-1,1]^3 */

static inline float sample(float x, float y, float z) {
    /* world [-1,1] -> grid [0,N-1] */
    float gx = (x + 1.0f) * 0.5f * (N - 1);
    float gy = (y + 1.0f) * 0.5f * (N - 1);
    float gz = (z + 1.0f) * 0.5f * (N - 1);
    int ix = (int)gx, iy = (int)gy, iz = (int)gz;
    if (ix < 0 || iy < 0 || iz < 0 || ix >= N - 1 || iy >= N - 1 || iz >= N - 1)
        return 0.0f;
    float fx = gx - ix, fy = gy - iy, fz = gz - iz;
    size_t st = (size_t)N, st2 = st * st;
    const float *b = g_vol + (size_t)iz * st2 + (size_t)iy * st + ix;
    float c000 = b[0],        c100 = b[1];
    float c010 = b[st],       c110 = b[st + 1];
    float c001 = b[st2],      c101 = b[st2 + 1];
    float c011 = b[st2 + st], c111 = b[st2 + st + 1];
    float c00 = c000 + fx * (c100 - c000), c01 = c001 + fx * (c101 - c001);
    float c10 = c010 + fx * (c110 - c010), c11 = c011 + fx * (c111 - c011);
    float c0 = c00 + fy * (c10 - c00), c1 = c01 + fy * (c11 - c01);
    return c0 + fz * (c1 - c0);
}

/* ray-box [-1,1]^3 entry/exit; returns 1 if it hits. */
static inline int box(const float o[3], const float d[3], float *t0, float *t1) {
    float tmin = 0.0f, tmax = 1e30f;
    for (int a = 0; a < 3; a++) {
        float inv = 1.0f / (d[a] == 0 ? 1e-30f : d[a]);
        float ta = (-1.0f - o[a]) * inv, tb = (1.0f - o[a]) * inv;
        if (ta > tb) { float s = ta; ta = tb; tb = s; }
        if (ta > tmin) tmin = ta;
        if (tb < tmax) tmax = tb;
    }
    if (tmax < tmin) return 0;
    *t0 = tmin; *t1 = tmax;
    return 1;
}

typedef struct {
    const lrt_ray *rays;
    size_t lo, hi;
    double accum;     /* sink */
    uint64_t samples; /* trilinear samples taken */
} job_t;

static void *worker(void *arg) {
    job_t *j = arg;
    double sink = 0;
    uint64_t ns = 0;
    int steps = g_steps;
    for (size_t i = j->lo; i < j->hi; i++) {
        const float *o = j->rays[i].org, *d = j->rays[i].dir;
        float t0, t1;
        if (!box(o, d, &t0, &t1)) continue;
        float dt = (t1 - t0) / steps;
        float T = 1.0f, acc = 0.0f, t = t0;
        for (int s = 0; s < steps; s++, t += dt) {
            float x = o[0] + t * d[0], y = o[1] + t * d[1], z = o[2] + t * d[2];
            float dens = sample(x, y, z);
            ns++;
            float a = 1.0f - expf(-dens * dt * 8.0f);
            acc += T * a;
            T *= (1.0f - a);
            if (T < 0.003f) break; /* front-to-back early-out */
        }
        sink += acc;
    }
    j->accum = sink;
    j->samples = ns;
    return NULL;
}

static void run(const char *label, const lrt_ray *rays, size_t n, int nt, int rep) {
    pthread_t th[256];
    job_t jobs[256];
    if (nt > 256) nt = 256;
    size_t per = (n + nt - 1) / nt;
    double best = 1e30;
    uint64_t samples = 0;
    for (int r = 0; r < rep; r++) {
        uint64_t t0 = bench_time_ns();
        for (int t = 0; t < nt; t++) {
            jobs[t].rays = rays;
            jobs[t].lo = (size_t)t * per;
            jobs[t].hi = jobs[t].lo + per; if (jobs[t].hi > n) jobs[t].hi = n;
            if (jobs[t].lo > n) jobs[t].lo = n;
            pthread_create(&th[t], NULL, worker, &jobs[t]);
        }
        samples = 0;
        for (int t = 0; t < nt; t++) { pthread_join(th[t], NULL); samples += jobs[t].samples; }
        double sc = bench_ns_to_s(bench_time_ns() - t0);
        if (sc < best) best = sc;
    }
    double mray = (double)n / best / 1e6;
    double msamp = (double)samples / best / 1e6;
    /* trilinear touches 8 floats = 32 bytes/sample (effective; cache reuse for
     * coherent rays makes this an upper bound on DRAM traffic). */
    double gbs = (double)samples * 32.0 / best / 1e9;
    printf("  %-11s threads=%d  %7.2f Mrays/s  %8.1f Msamp/s  %7.1f GB/s (eff)\n",
           label, nt, mray, msamp, gbs);
}

int main(int argc, char **argv) {
    N = 256; g_steps = 512;
    int nrays = 2000000, nt = 48, rep = 3;
    int sizes_argc = 0; int sizes[8];
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--n") && i + 1 < argc) N = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--steps") && i + 1 < argc) g_steps = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--nrays") && i + 1 < argc) nrays = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--threads") && i + 1 < argc) nt = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--repeat") && i + 1 < argc) rep = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--sizes") && i + 1 < argc) {
            char *p = strtok(argv[++i], ",");
            while (p && sizes_argc < 8) { sizes[sizes_argc++] = atoi(p); p = strtok(NULL, ","); }
        }
    }
    if (sizes_argc == 0) { sizes[0] = N; sizes_argc = 1; }

    lrt_ray *prim = malloc((size_t)nrays * sizeof(lrt_ray));
    lrt_ray *inc = malloc((size_t)nrays * sizeof(lrt_ray));
    rays_gen_primary(prim, nrays, 1234);
    rays_gen_incoherent(inc, nrays, 1234);

    printf("A64FX dense-grid volume raymarch: steps=%d, %d rays, %d threads\n",
           g_steps, nrays, nt);
    printf("(effective GB/s assumes 32 B/sample; coherent rays reuse cache, so\n"
           " their GB/s is an upper bound on real DRAM traffic — the gap between\n"
           " primary and incoherent shows where HBM2 bandwidth/latency bites.)\n");

    for (int si = 0; si < sizes_argc; si++) {
        N = sizes[si];
        size_t cells = (size_t)N * N * N;
        g_vol = malloc(cells * sizeof(float));
        if (!g_vol) { printf("N=%d: alloc failed\n", N); continue; }
        /* procedural density: a couple of gaussian blobs + noise. */
        for (int z = 0; z < N; z++)
            for (int y = 0; y < N; y++)
                for (int x = 0; x < N; x++) {
                    float fx = 2.0f * x / (N - 1) - 1, fy = 2.0f * y / (N - 1) - 1,
                          fz = 2.0f * z / (N - 1) - 1;
                    float r1 = fx*fx + fy*fy + fz*fz;
                    float r2 = (fx-0.3f)*(fx-0.3f) + (fy+0.2f)*(fy+0.2f) + fz*fz;
                    float v = expf(-3.0f*r1) + 0.7f*expf(-8.0f*r2);
                    g_vol[(size_t)z*N*N + (size_t)y*N + x] = v;
                }
        printf("\n--- N=%d  (%zu cells, %.1f MB) ---\n", N, cells,
               cells * sizeof(float) / 1048576.0);
        run("primary", prim, nrays, nt, rep);
        run("incoherent", inc, nrays, nt, rep);
        free(g_vol);
    }
    return 0;
}
