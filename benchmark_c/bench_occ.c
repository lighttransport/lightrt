/* Item-14 benchmark: BVH8 any-hit interleaved pipeline vs per-ray, on a
 * large cache-cold scene. Build without the watertight leaf so the
 * interleaved pipeline is eligible. */
#define _POSIX_C_SOURCE 200809L
#include "lightrt_c_tri.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static uint64_t rs = 0x123456789abcdefULL;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)(rs >> 16); }
static float fr(void) { return (float)(rnd() & 0xffffff) / 16777216.0f; }

int main(int argc, char **argv) {
    int g = argc > 1 ? atoi(argv[1]) : 700;
    size_t nrays = argc > 2 ? (size_t)atol(argv[2]) : 1000000;
    size_t ntris = (size_t)2 * (size_t)g * (size_t)g;
    float *v = malloc(ntris * 9 * sizeof(float));
    size_t k = 0;
    for (int y = 0; y < g; y++)
        for (int x = 0; x < g; x++) {
            float P[4][3];
            for (int c = 0; c < 4; c++) {
                int xx = x + (c & 1), yy = y + (c >> 1);
                P[c][0] = (float)xx / g * 2.0f - 1.0f;
                P[c][1] = (float)yy / g * 2.0f - 1.0f;
                P[c][2] = 0.15f * (float)((xx * 7919 + yy * 104729) % 1000) / 1000.0f;
            }
            int T[2][3] = {{0, 1, 3}, {0, 3, 2}};
            for (int t = 0; t < 2; t++)
                for (int c = 0; c < 3; c++)
                    for (int a = 0; a < 3; a++) v[k++] = P[T[t][c]][a];
        }
    lrt_tri_build_options o = {LRT_TRI_BUILD_FAST, LRT_TRI_LAYOUT_BVH8, 0, 0};
    lrt_result e;
    lrt_tri_scene *s = lrt_tri_scene_build(v, ntris, &o, &e);
    if (!s) { fprintf(stderr, "build failed %d\n", (int)e); return 1; }
    printf("scene: %zu tris, BVH8\n", ntris);

    lrt_ray *rays = malloc(nrays * sizeof(lrt_ray));
    uint8_t *occ = malloc(nrays), *occ2 = malloc(nrays);
    for (size_t i = 0; i < nrays; i++) {
        /* origin above/around the patch, direction at a random scene point */
        rays[i].org[0] = fr() * 3.0f - 1.5f;
        rays[i].org[1] = fr() * 3.0f - 1.5f;
        rays[i].org[2] = 1.5f + fr() * 2.0f;
        float tx = fr() * 2.0f - 1.0f, ty = fr() * 2.0f - 1.0f;
        rays[i].dir[0] = tx - rays[i].org[0];
        rays[i].dir[1] = ty - rays[i].org[1];
        rays[i].dir[2] = -0.3f - fr() - rays[i].org[2];
        rays[i].tmin = 0.0f;
        rays[i].tmax = 1e30f;
    }

    /* warm-up + equality check */
    lrt_tri_occluded1N(s, rays, occ, nrays, LRT_TRI_BATCH_COHERENT);
    lrt_tri_occluded1N(s, rays, occ2, nrays, LRT_TRI_BATCH_AUTO);
    size_t diff = 0, nocc = 0;
    for (size_t i = 0; i < nrays; i++) { nocc += occ[i] ? 1 : 0; if (occ[i] != occ2[i]) diff++; }
    printf("occluded %zu/%zu, interleaved bits differ %zu\n", nocc, nrays, diff);

    double bestC = 1e30, bestD = 1e30;
    for (int it = 0; it < 9; it++) {
        double t0 = now();
        lrt_tri_occluded1N(s, rays, occ, nrays, LRT_TRI_BATCH_COHERENT);
        double t1 = now();
        lrt_tri_occluded1N(s, rays, occ2, nrays, LRT_TRI_BATCH_AUTO);
        double t2 = now();
        if (t1 - t0 < bestC) bestC = t1 - t0;
        if (t2 - t1 < bestD) bestD = t2 - t1;
    }
    printf("per-ray  %.1f Mray/s (%.3f s)\n", nrays / bestC / 1e6, bestC);
    printf("interlv  %.1f Mray/s (%.3f s)\n", nrays / bestD / 1e6, bestD);
    printf("interleaved vs per-ray: %+.1f%%\n", (bestC / bestD - 1.0) * 100.0);
    lrt_tri_scene_free(s);
    free(v); free(rays); free(occ); free(occ2);
    return 0;
}
