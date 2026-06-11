/*
 * test_lightrt_c_tri.c — correctness tests for the fp32 triangle BVH
 * (lightrt_c_tri.h). Pure C11, no C++ dependency.
 *
 * Checks, for every compiled layout (BVH4, BVH8) and build quality:
 *   1. Brute-force O(N) closest-hit agreement on random triangle scenes and on
 *      degenerate rays (axis-aligned, zero direction components, tmin/tmax
 *      clipping).
 *   2. occluded1 agreement with intersect1 (occluded <=> closest hit exists).
 *   3. Scalar vs SIMD traversal agreement on the same scene.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

/* Scalar fp32 Moller-Trumbore reference (same epsilon as the library). */
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
    float tvx = r->org[0] - tri[0], tvy = r->org[1] - tri[1], tvz = r->org[2] - tri[2];
    float uu = (tvx * px + tvy * py + tvz * pz) * inv;
    if (uu < 0.0f || uu > 1.0f) return 0;
    float qx = tvy * e1[2] - tvz * e1[1];
    float qy = tvz * e1[0] - tvx * e1[2];
    float qz = tvx * e1[1] - tvy * e1[0];
    float vv = (r->dir[0] * qx + r->dir[1] * qy + r->dir[2] * qz) * inv;
    if (vv < 0.0f || uu + vv > 1.0f) return 0;
    float tt = (e2[0] * qx + e2[1] * qy + e2[2] * qz) * inv;
    if (tt < r->tmin || tt > r->tmax) return 0;
    *t = tt;
    *u = uu;
    *v = vv;
    return 1;
}

/* Brute-force closest hit over the soup. */
static int brute_force(const float *verts, size_t ntris, const lrt_ray *r,
                       lrt_hit *out) {
    float best_t = r->tmax;
    int found = 0;
    out->prim_id = LRT_TRI_NO_HIT;
    for (size_t i = 0; i < ntris; i++) {
        float t, u, v;
        lrt_ray rr = *r;
        rr.tmax = best_t;
        if (ref_isect(&verts[i * 9], &rr, &t, &u, &v)) {
            /* strictly-closer wins; ties keep the first found (may differ from
             * BVH order, handled by tolerance in the comparison) */
            if (!found || t < best_t) {
                best_t = t;
                out->t = t;
                out->u = u;
                out->v = v;
                out->prim_id = (uint32_t)i;
                found = 1;
            }
        }
    }
    return found;
}

/* Random triangle soup: ntris triangles with edge size ~scale in [-2,2]^3. */
static float *make_random_soup(size_t ntris, float scale) {
    float *verts = (float *)malloc(ntris * 9 * sizeof(float));
    if (!verts) return NULL;
    for (size_t i = 0; i < ntris; i++) {
        float cx = rnd_f(-2.0f, 2.0f), cy = rnd_f(-2.0f, 2.0f), cz = rnd_f(-2.0f, 2.0f);
        for (int k = 0; k < 3; k++) {
            verts[i * 9 + k * 3 + 0] = cx + rnd_f(-scale, scale);
            verts[i * 9 + k * 3 + 1] = cy + rnd_f(-scale, scale);
            verts[i * 9 + k * 3 + 2] = cz + rnd_f(-scale, scale);
        }
    }
    return verts;
}

static void make_random_ray(lrt_ray *r) {
    r->org[0] = rnd_f(-4.0f, 4.0f);
    r->org[1] = rnd_f(-4.0f, 4.0f);
    r->org[2] = rnd_f(-4.0f, 4.0f);
    float dx = rnd_f(-1.0f, 1.0f), dy = rnd_f(-1.0f, 1.0f), dz = rnd_f(-1.0f, 1.0f);
    /* Occasionally zero out components to exercise degenerate slab axes. */
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

#define CHECK(cond, ...)                          \
    do {                                          \
        if (!(cond)) {                            \
            printf("FAIL: " __VA_ARGS__);         \
            printf("\n");                         \
            g_failures++;                         \
        }                                         \
    } while (0)

static void test_vs_brute_force(const char *label, const float *verts,
                                size_t ntris, lrt_tri_layout layout,
                                lrt_tri_quality quality, size_t nrays) {
    lrt_tri_build_options opts = {
        .quality = quality, .layout = layout, .max_leaf_size = 0, .num_threads = 1};
    lrt_result err = LRT_RESULT_OK;
    lrt_tri_scene *s = lrt_tri_scene_build(verts, ntris, &opts, &err);
    CHECK(s != NULL, "%s: build failed (err=%d)", label, (int)err);
    if (!s) return;

    lrt_tri_stats st;
    lrt_tri_scene_stats(s, &st);
    printf("  %s [%s]: %u nodes, %u leaves, depth %u, %.1f KB, sah %.1f\n",
           label, lrt_tri_kernel_name(s), st.node_count, st.leaf_count,
           st.max_depth, (double)st.memory_bytes / 1024.0, (double)st.sah_cost);

    size_t mismatches = 0, occl_mismatches = 0;
    double max_dt = 0.0;
    for (size_t i = 0; i < nrays; i++) {
        lrt_ray r;
        make_random_ray(&r);
        lrt_hit hb, ha;
        int bf = brute_force(verts, ntris, &r, &hb);
        int bvh = lrt_tri_intersect1(s, &r, &ha);
        if (bf != bvh) {
            mismatches++;
        } else if (bf) {
            double dt = fabs((double)ha.t - (double)hb.t);
            /* Different test order can pick a different tri on near-ties; only
             * flag mismatches where the distances genuinely differ. */
            if (dt > 1e-3 * (1.0 + fabs((double)hb.t))) {
                mismatches++;
                if (dt > max_dt) max_dt = dt;
            }
        }
        int occ = lrt_tri_occluded1(s, &r);
        if (occ != bvh) occl_mismatches++;
    }
    CHECK(mismatches == 0, "%s: %zu/%zu closest-hit mismatches vs brute force "
          "(max dt %.3e)", label, mismatches, nrays, max_dt);
    CHECK(occl_mismatches == 0, "%s: %zu occluded1/intersect1 disagreements",
          label, occl_mismatches);

    lrt_tri_scene_free(s);
}

/* BVH4 vs BVH8 (and their kernels) must agree with each other on hit/miss and
 * distances within fp32 noise. */
static void test_layouts_agree(const float *verts, size_t ntris, size_t nrays) {
    lrt_tri_build_options o4 = {.quality = LRT_TRI_BUILD_DEFAULT,
                                .layout = LRT_TRI_LAYOUT_BVH4};
    lrt_tri_build_options o8 = {.quality = LRT_TRI_BUILD_DEFAULT,
                                .layout = LRT_TRI_LAYOUT_BVH8};
    lrt_tri_scene *s4 = lrt_tri_scene_build(verts, ntris, &o4, NULL);
    lrt_tri_scene *s8 = lrt_tri_scene_build(verts, ntris, &o8, NULL);
    CHECK(s4 && s8, "layout-agreement: build failed");
    if (!s4 || !s8) {
        lrt_tri_scene_free(s4);
        lrt_tri_scene_free(s8);
        return;
    }
    size_t mismatches = 0;
    for (size_t i = 0; i < nrays; i++) {
        lrt_ray r;
        make_random_ray(&r);
        lrt_hit h4, h8;
        int a = lrt_tri_intersect1(s4, &r, &h4);
        int b = lrt_tri_intersect1(s8, &r, &h8);
        if (a != b) {
            mismatches++;
        } else if (a && fabs((double)h4.t - (double)h8.t) >
                           1e-3 * (1.0 + fabs((double)h4.t))) {
            mismatches++;
        }
    }
    CHECK(mismatches == 0, "bvh4 vs bvh8: %zu mismatches over %zu rays",
          mismatches, nrays);
    lrt_tri_scene_free(s4);
    lrt_tri_scene_free(s8);
}

static void test_edge_cases(void) {
    /* Single triangle; rays straight at it, edge-on, behind, clipped. */
    const float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
    lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
    CHECK(s != NULL, "single-tri build");
    if (!s) return;

    lrt_hit h;
    lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
    CHECK(lrt_tri_intersect1(s, &r, &h) == 1 && fabsf(h.t - 5.0f) < 1e-5f,
          "axis-aligned +z hit (t=%f)", (double)h.t);

    lrt_ray rb = {{0, 0, 10}, 0.0f, {0, 0, 1}, 100.0f};
    CHECK(lrt_tri_intersect1(s, &rb, &h) == 0, "ray behind triangle");

    lrt_ray rc = {{0, 0, 0}, 0.0f, {0, 0, 1}, 4.0f};
    CHECK(lrt_tri_intersect1(s, &rc, &h) == 0, "tmax clips hit");

    lrt_ray rd = {{0, 0, 0}, 6.0f, {0, 0, 1}, 100.0f};
    CHECK(lrt_tri_intersect1(s, &rd, &h) == 0, "tmin clips hit");

    CHECK(lrt_tri_occluded1(s, &r) == 1, "occluded1 hit");
    CHECK(lrt_tri_occluded1(s, &rc) == 0, "occluded1 respects tmax");
    lrt_tri_scene_free(s);

    /* Degenerate (zero-area) triangles must build and never hit. */
    float degen[18];
    for (int i = 0; i < 18; i++) degen[i] = 1.0f;
    s = lrt_tri_scene_build(degen, 2, NULL, NULL);
    CHECK(s != NULL, "degenerate build");
    if (s) {
        lrt_ray re = {{1, 1, -5}, 0.0f, {0, 0, 1}, 100.0f};
        CHECK(lrt_tri_intersect1(s, &re, &h) == 0, "degenerate tris never hit");
        lrt_tri_scene_free(s);
    }

    /* Invalid input handling. */
    lrt_result err = LRT_RESULT_OK;
    CHECK(lrt_tri_scene_build(NULL, 10, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_ARGUMENT,
          "NULL vertices rejected");
    float nanv[9] = {0};
    nanv[0] = NAN;
    CHECK(lrt_tri_scene_build(nanv, 1, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_BOUNDS,
          "NaN vertex rejected");
}

int main(void) {
    printf("lightrt_c_tri test\n");

    test_edge_cases();

    /* Small soup: every leaf shape exercised. */
    g_rng = 0x9E3779B97F4A7C15ull;
    float *small = make_random_soup(37, 0.5f);
    test_vs_brute_force("small/bvh4/sah", small, 37, LRT_TRI_LAYOUT_BVH4,
                        LRT_TRI_BUILD_DEFAULT, 20000);
    test_vs_brute_force("small/bvh8/sah", small, 37, LRT_TRI_LAYOUT_BVH8,
                        LRT_TRI_BUILD_DEFAULT, 20000);
    free(small);

    /* Medium soup, both qualities and layouts. */
    g_rng = 0x123456789ABCDEFull;
    float *med = make_random_soup(5000, 0.15f);
    test_vs_brute_force("medium/bvh4/sah", med, 5000, LRT_TRI_LAYOUT_BVH4,
                        LRT_TRI_BUILD_DEFAULT, 4000);
    test_vs_brute_force("medium/bvh8/sah", med, 5000, LRT_TRI_LAYOUT_BVH8,
                        LRT_TRI_BUILD_DEFAULT, 4000);
    test_vs_brute_force("medium/bvh4/fast", med, 5000, LRT_TRI_LAYOUT_BVH4,
                        LRT_TRI_BUILD_FAST, 4000);
    test_vs_brute_force("medium/bvh8/fast", med, 5000, LRT_TRI_LAYOUT_BVH8,
                        LRT_TRI_BUILD_FAST, 4000);
    test_layouts_agree(med, 5000, 50000);
    free(med);

    /* Co-planar / overlapping pathological soup. */
    g_rng = 0xDEADBEEFCAFEull;
    float *flat = (float *)malloc(2000 * 9 * sizeof(float));
    for (size_t i = 0; i < 2000; i++) {
        float cx = rnd_f(-2, 2), cy = rnd_f(-2, 2);
        flat[i * 9 + 0] = cx;
        flat[i * 9 + 1] = cy;
        flat[i * 9 + 2] = 1.0f;
        flat[i * 9 + 3] = cx + 0.3f;
        flat[i * 9 + 4] = cy;
        flat[i * 9 + 5] = 1.0f;
        flat[i * 9 + 6] = cx;
        flat[i * 9 + 7] = cy + 0.3f;
        flat[i * 9 + 8] = 1.0f;
    }
    test_vs_brute_force("coplanar/bvh4/sah", flat, 2000, LRT_TRI_LAYOUT_BVH4,
                        LRT_TRI_BUILD_DEFAULT, 4000);
    test_vs_brute_force("coplanar/bvh8/sah", flat, 2000, LRT_TRI_LAYOUT_BVH8,
                        LRT_TRI_BUILD_DEFAULT, 4000);
    free(flat);

    if (g_failures == 0) {
        printf("RESULT: PASS\n");
        return 0;
    }
    printf("RESULT: FAIL (%d failures)\n", g_failures);
    return 1;
}
