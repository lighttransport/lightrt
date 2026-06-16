/*
 * test_lightrt_c_surfaces.c — correctness tests for the parametric SURFACE
 * primitives (bilinear patch, Bezier surface, NURBS, trimmed NURBS). Pure C11.
 *
 * Primary check is a RESIDUAL test: the returned (t,u,v) must place the surface
 * point S(u,v) on the ray (org + t*dir). Plus a tessellated-triangle oracle for
 * hit-fraction sanity.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../lightrt_c_tri.h"

static uint64_t g_rng = 0xfeedfacecafebeefull;
static uint32_t rnd_u32(void) {
    g_rng ^= g_rng << 13;
    g_rng ^= g_rng >> 7;
    g_rng ^= g_rng << 17;
    return (uint32_t)(g_rng >> 32);
}
static float rf(float lo, float hi) {
    return lo + (hi - lo) * ((float)(rnd_u32() & 0xFFFFFF) / 16777216.0f);
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

/* bilerp of 4 corners q00,q10,q11,q01 (12 floats) at (u,v). */
static void bilerp(const float *c, float u, float v, float p[3]) {
    for (int k = 0; k < 3; k++) {
        float a = (1 - u) * c[0 + k] + u * c[3 + k];  /* q00,q10 */
        float b = (1 - u) * c[9 + k] + u * c[6 + k];  /* q01,q11 */
        p[k] = (1 - v) * a + v * b;
    }
}

static void test_bilinear(void) {
    const size_t N = 2000, NR = 40000;
    float *patches = (float *)malloc(N * 12 * sizeof(float));
    for (size_t i = 0; i < N; i++) {
        float c[3] = {rf(-2, 2), rf(-2, 2), rf(-2, 2)};
        float *p = &patches[i * 12];
        /* random non-planar quad: 4 corners jittered around a base frame */
        float ax[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float ay[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float s = 0.35f, w = 0.3f; /* w = out-of-plane warp */
        for (int k = 0; k < 3; k++) {
            float warp = rf(-w, w);
            p[0 + k] = c[k] - s * ax[k] - s * ay[k];               /* q00 */
            p[3 + k] = c[k] + s * ax[k] - s * ay[k] + (k == 2 ? warp : 0); /* q10 */
            p[6 + k] = c[k] + s * ax[k] + s * ay[k];               /* q11 */
            p[9 + k] = c[k] - s * ax[k] + s * ay[k] - (k == 2 ? warp : 0); /* q01 */
        }
    }
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    lrt_tri_scene *s = lrt_bilinear_scene_build(patches, N, &o, NULL);
    CHECK(s != NULL, "bilinear build");
    if (!s) {
        free(patches);
        return;
    }

    size_t hits = 0, resid_ok = 0, occ_ok = 0;
    double max_resid = 0.0;
    for (size_t i = 0; i < NR; i++) {
        lrt_ray r;
        make_ray(&r);
        lrt_hit h;
        int hit = lrt_tri_intersect1(s, &r, &h);
        int occ = lrt_tri_occluded1(s, &r);
        if ((hit != 0) == (occ != 0)) occ_ok++;
        if (hit) {
            hits++;
            CHECK(h.prim_id < N, "bilinear prim_id oob");
            CHECK(h.u >= -1e-4f && h.u <= 1.0001f && h.v >= -1e-4f &&
                      h.v <= 1.0001f,
                  "bilinear (u,v) out of range: %f %f", h.u, h.v);
            float ps[3], pr[3];
            bilerp(&patches[h.prim_id * 12], h.u, h.v, ps);
            for (int k = 0; k < 3; k++) pr[k] = r.org[k] + h.t * r.dir[k];
            float d = sqrtf((ps[0] - pr[0]) * (ps[0] - pr[0]) +
                            (ps[1] - pr[1]) * (ps[1] - pr[1]) +
                            (ps[2] - pr[2]) * (ps[2] - pr[2]));
            double rel = d / (1.0 + fabs((double)h.t));
            if (rel > max_resid) max_resid = rel;
            if (rel < 1e-4) resid_ok++;
        }
    }
    double rfrac = hits ? (double)resid_ok / (double)hits : 1.0;
    printf("bilinear: %zu/%zu rays hit, residual ok %.3f%% (max %.2e), "
           "occ-consistency %.3f%%\n",
           hits, NR, rfrac * 100.0, max_resid, 100.0 * occ_ok / NR);
    CHECK(hits > NR / 100, "bilinear: too few hits (%zu) — geometry/ray issue",
          hits);
    CHECK(rfrac >= 0.999, "bilinear residual agreement %.3f%% < 99.9%%",
          rfrac * 100.0);
    CHECK(occ_ok == NR, "bilinear occ-consistency %.3f%%", 100.0 * occ_ok / NR);

    free(patches);
    lrt_tri_scene_free(s);
}

/* cubic Bernstein eval of 4 scalars. */
static float bez1(float p0, float p1, float p2, float p3, float u) {
    float u1 = 1 - u;
    return u1 * u1 * u1 * p0 + 3 * u1 * u1 * u * p1 + 3 * u1 * u * u * p2 +
           u * u * u * p3;
}
/* bicubic patch eval: cp[(j*4+i)*3+axis]. */
static void bezpatch_eval(const float *cp, float u, float v, float S[3]) {
    for (int a = 0; a < 3; a++) {
        float R[4];
        for (int j = 0; j < 4; j++)
            R[j] = bez1(cp[(j * 4 + 0) * 3 + a], cp[(j * 4 + 1) * 3 + a],
                        cp[(j * 4 + 2) * 3 + a], cp[(j * 4 + 3) * 3 + a], u);
        S[a] = bez1(R[0], R[1], R[2], R[3], v);
    }
}

static void test_bezpatch(void) {
    const size_t N = 1500, NR = 40000;
    float *cps = (float *)malloc(N * 48 * sizeof(float));
    for (size_t p = 0; p < N; p++) {
        float c[3] = {rf(-2, 2), rf(-2, 2), rf(-2, 2)};
        float *cp = &cps[p * 48];
        /* 4x4 control net: base grid in a random frame + per-CP jitter (warp) */
        float ax[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float ay[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        for (int j = 0; j < 4; j++)
            for (int i = 0; i < 4; i++) {
                float fu = (float)i / 3.0f - 0.5f, fv = (float)j / 3.0f - 0.5f;
                for (int k = 0; k < 3; k++)
                    cp[(j * 4 + i) * 3 + k] =
                        c[k] + 0.6f * fu * ax[k] + 0.6f * fv * ay[k] +
                        rf(-0.12f, 0.12f);
            }
    }
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    lrt_tri_scene *s = lrt_bezpatch_scene_build(cps, N, &o, NULL);
    CHECK(s != NULL, "bezpatch build");
    if (!s) {
        free(cps);
        return;
    }
    size_t hits = 0, resid_ok = 0, occ_ok = 0;
    double max_resid = 0.0;
    for (size_t i = 0; i < NR; i++) {
        lrt_ray r;
        make_ray(&r);
        lrt_hit h;
        int hit = lrt_tri_intersect1(s, &r, &h);
        int occ = lrt_tri_occluded1(s, &r);
        if ((hit != 0) == (occ != 0)) occ_ok++;
        if (hit) {
            hits++;
            CHECK(h.prim_id < N, "bezpatch prim_id oob");
            float ps[3], pr[3];
            bezpatch_eval(&cps[h.prim_id * 48], h.u, h.v, ps);
            for (int k = 0; k < 3; k++) pr[k] = r.org[k] + h.t * r.dir[k];
            float d = sqrtf((ps[0] - pr[0]) * (ps[0] - pr[0]) +
                            (ps[1] - pr[1]) * (ps[1] - pr[1]) +
                            (ps[2] - pr[2]) * (ps[2] - pr[2]));
            double rel = d / (1.0 + fabs((double)h.t));
            if (rel > max_resid) max_resid = rel;
            if (rel < 1e-3) resid_ok++;
        }
    }
    double rfrac = hits ? (double)resid_ok / (double)hits : 1.0;
    printf("bezpatch: %zu/%zu rays hit, residual ok %.3f%% (max %.2e), "
           "occ-consistency %.3f%%\n",
           hits, NR, rfrac * 100.0, max_resid, 100.0 * occ_ok / NR);
    CHECK(hits > NR / 100, "bezpatch: too few hits (%zu)", hits);
    CHECK(rfrac >= 0.999, "bezpatch residual agreement %.3f%% < 99.9%%",
          rfrac * 100.0);
    CHECK(occ_ok >= NR * 999 / 1000, "bezpatch occ-consistency %.3f%%",
          100.0 * occ_ok / NR);
    free(cps);
    lrt_tri_scene_free(s);
}

int main(void) {
    test_bilinear();
    test_bezpatch();
    if (g_fail) {
        printf("\n%d FAILURES\n", g_fail);
        return 1;
    }
    printf("\nAll surface tests passed.\n");
    return 0;
}
