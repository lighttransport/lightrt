/*
 * test_lightrt_c_quadtetra.c — correctness tests for the planar-quad and
 * solid-tetra primitives (lrt_quad_scene_build / lrt_tetra_scene_build) vs a
 * brute-force oracle. Pure C11.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../lightrt_c_tri.h"

static uint64_t g_rng = 0x1234567deadbeefull;
static uint32_t rnd_u32(void) {
    g_rng ^= g_rng << 13;
    g_rng ^= g_rng >> 7;
    g_rng ^= g_rng << 17;
    return (uint32_t)(g_rng >> 32);
}
static float rf(float lo, float hi) {
    return lo + (hi - lo) * ((float)(rnd_u32() & 0xFFFFFF) / 16777216.0f);
}

/* Scalar MT against an explicit triangle. */
static int mt(const float *o, const float *d, const float *v0, const float *v1,
              const float *v2, float tmin, float tmax, float *tout) {
    float e1[3] = {v1[0] - v0[0], v1[1] - v0[1], v1[2] - v0[2]};
    float e2[3] = {v2[0] - v0[0], v2[1] - v0[1], v2[2] - v0[2]};
    float px = d[1] * e2[2] - d[2] * e2[1], py = d[2] * e2[0] - d[0] * e2[2],
          pz = d[0] * e2[1] - d[1] * e2[0];
    float det = e1[0] * px + e1[1] * py + e1[2] * pz;
    if (det > -1e-12f && det < 1e-12f) return 0;
    float inv = 1.0f / det;
    float tv[3] = {o[0] - v0[0], o[1] - v0[1], o[2] - v0[2]};
    float u = (tv[0] * px + tv[1] * py + tv[2] * pz) * inv;
    if (u < 0.0f || u > 1.0f) return 0;
    float qx = tv[1] * e1[2] - tv[2] * e1[1], qy = tv[2] * e1[0] - tv[0] * e1[2],
          qz = tv[0] * e1[1] - tv[1] * e1[0];
    float v = (d[0] * qx + d[1] * qy + d[2] * qz) * inv;
    if (v < 0.0f || u + v > 1.0f) return 0;
    float t = (e2[0] * qx + e2[1] * qy + e2[2] * qz) * inv;
    if (t < tmin || t >= tmax) return 0;
    *tout = t;
    return 1;
}

static int g_fail = 0;
#define CHECK(c, ...)                     \
    do {                                  \
        if (!(c)) {                       \
            printf("FAIL: " __VA_ARGS__); \
            printf("\n");                 \
            g_fail++;                     \
        }                                 \
    } while (0)

static void make_ray(lrt_ray *r) {
    for (int k = 0; k < 3; k++) r->org[k] = rf(-4, 4);
    float d[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
    if (d[0] == 0 && d[1] == 0 && d[2] == 0) d[2] = 1;
    float l = sqrtf(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]);
    for (int k = 0; k < 3; k++) r->dir[k] = d[k] / l;
    r->tmin = 1e-4f;
    r->tmax = 1e9f;
}

int main(void) {
    const size_t N = 3000, NR = 30000;

    /* ---- Quad: random planar quads (build from a triangle + 4th coplanar pt) */
    float *quads = (float *)malloc(N * 12 * sizeof(float));
    for (size_t i = 0; i < N; i++) {
        float c[3] = {rf(-2, 2), rf(-2, 2), rf(-2, 2)};
        /* basis in a random plane */
        float a[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float b[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float s = 0.4f;
        float *q = &quads[i * 12];
        /* v0,v1,v2,v3 around the quad (parallelogram is planar+convex) */
        for (int k = 0; k < 3; k++) {
            q[0 + k] = c[k] - s * a[k] - s * b[k];
            q[3 + k] = c[k] + s * a[k] - s * b[k];
            q[6 + k] = c[k] + s * a[k] + s * b[k];
            q[9 + k] = c[k] - s * a[k] + s * b[k];
        }
    }
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    lrt_tri_scene *qs = lrt_quad_scene_build(quads, N, &o, NULL);
    CHECK(qs != NULL, "quad build");

    size_t qagree = 0, qocc = 0;
    for (size_t i = 0; i < NR; i++) {
        lrt_ray r;
        make_ray(&r);
        float best = r.tmax;
        int found = 0;
        for (size_t p = 0; p < N; p++) {
            const float *q = &quads[p * 12];
            float t;
            if (mt(r.org, r.dir, &q[0], &q[3], &q[6], r.tmin, best, &t)) {
                best = t;
                found = 1;
            }
            if (mt(r.org, r.dir, &q[0], &q[6], &q[9], r.tmin, best, &t)) {
                best = t;
                found = 1;
            }
        }
        lrt_hit h;
        int g = lrt_tri_intersect1(qs, &r, &h);
        if (g == found &&
            (!found || fabsf(h.t - best) <= 1e-3f * (1.0f + best)))
            qagree++;
        int occ = lrt_tri_occluded1(qs, &r);
        if ((occ != 0) == (found != 0)) qocc++;
    }
    printf("quad : closest %.3f%%  occ %.3f%%  (%zu quads, %zu rays)\n",
           100.0 * qagree / NR, 100.0 * qocc / NR, N, NR);
    CHECK(qagree >= NR * 999 / 1000, "quad closest agreement");
    CHECK(qocc >= NR * 999 / 1000, "quad occlusion agreement");

    /* ---- Tetra: random tetrahedra ---- */
    float *tet = (float *)malloc(N * 12 * sizeof(float));
    for (size_t i = 0; i < N; i++) {
        float c[3] = {rf(-2, 2), rf(-2, 2), rf(-2, 2)};
        float *t = &tet[i * 12];
        for (int vtx = 0; vtx < 4; vtx++)
            for (int k = 0; k < 3; k++) t[vtx * 3 + k] = c[k] + rf(-0.35f, 0.35f);
    }
    lrt_tri_scene *ts = lrt_tetra_scene_build(tet, N, &o, NULL);
    CHECK(ts != NULL, "tetra build");
    static const int F[4][3] = {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}};
    size_t tagree = 0, tocc = 0;
    for (size_t i = 0; i < NR; i++) {
        lrt_ray r;
        make_ray(&r);
        float best = r.tmax;
        int found = 0;
        for (size_t p = 0; p < N; p++) {
            const float *t = &tet[p * 12];
            for (int f = 0; f < 4; f++) {
                float tt;
                if (mt(r.org, r.dir, &t[F[f][0] * 3], &t[F[f][1] * 3],
                       &t[F[f][2] * 3], r.tmin, best, &tt)) {
                    best = tt;
                    found = 1;
                }
            }
        }
        lrt_hit h;
        int g = lrt_tri_intersect1(ts, &r, &h);
        if (g == found &&
            (!found || fabsf(h.t - best) <= 1e-3f * (1.0f + best)))
            tagree++;
        int occ = lrt_tri_occluded1(ts, &r);
        if ((occ != 0) == (found != 0)) tocc++;
    }
    printf("tetra: closest %.3f%%  occ %.3f%%  (%zu tetra, %zu rays)\n",
           100.0 * tagree / NR, 100.0 * tocc / NR, N, NR);
    CHECK(tagree >= NR * 999 / 1000, "tetra closest agreement");
    CHECK(tocc >= NR * 999 / 1000, "tetra occlusion agreement");

    /* Batch path (intersect1N/occluded1N) must match single-ray for these
     * non-triangle kinds (regression guard: they must NOT take the
     * triangle-only pipeline). */
    {
        size_t nb = 5000;
        lrt_ray *br = (lrt_ray *)malloc(nb * sizeof(lrt_ray));
        lrt_hit *h1 = (lrt_hit *)malloc(nb * sizeof(lrt_hit));
        lrt_hit *hN = (lrt_hit *)malloc(nb * sizeof(lrt_hit));
        uint8_t *o1 = (uint8_t *)malloc(nb);
        uint8_t *oN = (uint8_t *)malloc(nb);
        lrt_tri_scene *scenes[2] = {qs, ts};
        const char *nm[2] = {"quad", "tetra"};
        for (int sc = 0; sc < 2; sc++) {
            for (size_t i = 0; i < nb; i++) make_ray(&br[i]);
            for (size_t i = 0; i < nb; i++) {
                if (!lrt_tri_intersect1(scenes[sc], &br[i], &h1[i]))
                    h1[i].prim_id = LRT_TRI_NO_HIT;
                o1[i] = (uint8_t)lrt_tri_occluded1(scenes[sc], &br[i]);
            }
            lrt_tri_intersect1N(scenes[sc], br, hN, nb, LRT_TRI_BATCH_INCOHERENT);
            lrt_tri_occluded1N(scenes[sc], br, oN, nb, LRT_TRI_BATCH_INCOHERENT);
            size_t a = 0, ao = 0;
            for (size_t i = 0; i < nb; i++) {
                if (h1[i].prim_id == hN[i].prim_id) a++;
                if ((o1[i] != 0) == (oN[i] != 0)) ao++;
            }
            CHECK(a == nb, "%s intersect1N != intersect1 (%zu/%zu)", nm[sc], a,
                  nb);
            CHECK(ao == nb, "%s occluded1N != occluded1 (%zu/%zu)", nm[sc], ao,
                  nb);
        }
        free(br); free(h1); free(hN); free(o1); free(oN);
    }

    free(quads);
    free(tet);
    lrt_tri_scene_free(qs);
    lrt_tri_scene_free(ts);
    if (g_fail) {
        printf("\n%d FAILURES\n", g_fail);
        return 1;
    }
    printf("\nAll quad/tetra tests passed.\n");
    return 0;
}
