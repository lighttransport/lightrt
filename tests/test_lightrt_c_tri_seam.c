/* Seam (watertightness) test for the main triangle leaf.
 *
 * A jittered heightfield mesh (adjacent triangles share exact vertices) is shot
 * with rays aimed at points ON shared edges (interior edges and diagonals).
 * Every such ray hits the mesh in exact arithmetic, so a miss is a leak through
 * a crack between two triangles. Built with -DLRT_TRI_WATERTIGHT_TRI the leaf
 * runs the proved-watertight Woop test (formal/LightRT/C/Proofs/WoopWatertight
 * .lean) and the test requires 0 leaks; otherwise it reports the default
 * Moller-Trumbore leak count. Exit 0 = pass. */
#include "lightrt_c_tri.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

static unsigned long long rs = 88172645463325252ull;
static double frand(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return (double)(rs >> 11) * (1.0 / 9007199254740992.0);
}

int main(void) {
    const int g = 48;
    float *h = malloc(sizeof(float) * (g + 1) * (g + 1));
    for (int i = 0; i < (g + 1) * (g + 1); i++) h[i] = (float)(0.5 / g * frand()); /* slope <= ~1: no silhouette edges for near-vertical rays */
    size_t n = (size_t)2 * g * g;
    float *v = malloc(sizeof(float) * 9 * n);
    float P[(g + 1) * (g + 1)][3];
    for (int y = 0; y <= g; y++) for (int x = 0; x <= g; x++) {
        float *p = P[y * (g + 1) + x];
        p[0] = (float)x / g + (float)(0.3 / g * (frand() - 0.5)) * (x > 0 && x < g);
        p[1] = h[y * (g + 1) + x];
        p[2] = (float)y / g + (float)(0.3 / g * (frand() - 0.5)) * (y > 0 && y < g);
    }
    size_t k = 0;
    for (int y = 0; y < g; y++) for (int x = 0; x < g; x++) {
        int a = y * (g + 1) + x, b = a + 1, c = a + g + 1, d = c + 1;
        int T[2][3] = {{a, b, d}, {a, d, c}};
        for (int t = 0; t < 2; t++) for (int j = 0; j < 3; j++) for (int q = 0; q < 3; q++)
            v[k++] = P[T[t][j]][q];
    }
    int fails = 0;
    for (int layout = 4; layout <= 8; layout += 4) {
        lrt_tri_build_options o = {LRT_TRI_BUILD_DEFAULT, (lrt_tri_layout)layout, 0, 0};
        lrt_result err;
        lrt_tri_scene *s = lrt_tri_scene_build(v, n, &o, &err);
        if (!s) { printf("build failed\n"); return 1; }
        int rays = 0, leaks = 0;
        for (int r = 0; r < 200000; r++) {
            /* a random interior edge: diagonal a-d of a cell, or its right/top edge */
            int x = 1 + (int)(frand() * (g - 2)), y = 1 + (int)(frand() * (g - 2));
            int a = y * (g + 1) + x, e;
            int kind = r % 3;
            e = kind == 0 ? a + g + 2 : kind == 1 ? a + 1 : a + g + 1;
            double s_ = 0.05 + 0.9 * frand();
            double tgt[3];
            for (int q = 0; q < 3; q++) tgt[q] = P[a][q] + s_ * ((double)P[e][q] - P[a][q]);
            lrt_ray ray;
            double dir[3] = {0.4 * (frand() - 0.5), -1.0, 0.4 * (frand() - 0.5)};
            for (int q = 0; q < 3; q++) {
                ray.org[q] = (float)(tgt[q] - 2.0 * dir[q]);
                ray.dir[q] = (float)dir[q];
            }
            ray.tmin = 0.0f; ray.tmax = 1e30f;
            lrt_hit hit;
            rays++;
            if (!lrt_tri_intersect1(s, &ray, &hit)) leaks++;
        }
        printf("BVH%d: %d edge rays, %d leaks [%s]\n", layout, rays, leaks,
#ifdef LRT_TRI_WATERTIGHT_TRI
               "watertight"
#else
               "default MT"
#endif
        );
#ifdef LRT_TRI_WATERTIGHT_TRI
        if (leaks) fails++;
#endif
        lrt_tri_scene_free(s);
    }
    free(v); free(h);
    printf("RESULT: %s\n", fails ? "FAIL" : "PASS");
    return fails ? 1 : 0;
}
