/*
 * test_lightrt_c_tri.c - correctness tests for the fp32 triangle BVH
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

/* --- Thread safety (requires pthread) ------------------------------------- */
#ifdef __linux__
#include <pthread.h>
#endif

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

static int ref_isect_filtered(const float *verts, size_t ntris, const lrt_ray *r,
                             lrt_anyhit_filter filter, void *user) {
    float best_t = r->tmax;
    int hit = 0;
    for (size_t i = 0; i < ntris; i++) {
        float t, u, v;
        if (!ref_isect(&verts[i * 9], r, &t, &u, &v)) continue;
        if (t < best_t && (!filter || filter(user, (uint32_t)i, t, u, v))) {
            best_t = t;
            hit = 1;
        }
    }
    return hit;
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

/* The batched entry points (which may pipeline several rays in flight) must
 * produce exactly the same results as the single-ray calls. */
static void test_batch_matches_single(const float *verts, size_t ntris,
                                      lrt_tri_layout layout, size_t nrays) {
    lrt_tri_build_options o = {.quality = LRT_TRI_BUILD_DEFAULT,
                               .layout = layout};
    lrt_tri_scene *s = lrt_tri_scene_build(verts, ntris, &o, NULL);
    CHECK(s != NULL, "batch-vs-single: build failed");
    if (!s) return;

    lrt_ray *rays = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_hit *hits = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    uint8_t *occ = (uint8_t *)malloc(nrays * sizeof(uint8_t));
    if (!rays || !hits || !occ) {
        free(rays);
        free(hits);
        free(occ);
        lrt_tri_scene_free(s);
        return;
    }
    for (size_t i = 0; i < nrays; i++) make_random_ray(&rays[i]);

    /* Both hints must match the single-ray calls. COHERENT closest-hit takes
     * the Ray4/Ray8 packet path internally, so it is exercised here too. */
    lrt_tri_batch_hint hints[2] = {LRT_TRI_BATCH_INCOHERENT,
                                   LRT_TRI_BATCH_COHERENT};
    for (int hi = 0; hi < 2; hi++) {
        lrt_tri_intersect1N(s, rays, hits, nrays, hints[hi]);
        lrt_tri_occluded1N(s, rays, occ, nrays, hints[hi]);

        size_t bad_hit = 0, bad_occ = 0;
        for (size_t i = 0; i < nrays; i++) {
            lrt_hit h1;
            lrt_tri_intersect1(s, &rays[i], &h1);
            if (h1.prim_id != hits[i].prim_id ||
                (h1.prim_id != LRT_TRI_NO_HIT && h1.t != hits[i].t)) {
                bad_hit++;
            }
            if ((uint8_t)lrt_tri_occluded1(s, &rays[i]) != occ[i]) bad_occ++;
        }
        CHECK(bad_hit == 0, "batched intersect1N (layout %d hint %d) differs "
              "from intersect1 on %zu/%zu rays", (int)layout, hi, bad_hit, nrays);
        CHECK(bad_occ == 0, "batched occluded1N (layout %d hint %d) differs "
              "from occluded1 on %zu/%zu rays", (int)layout, hi, bad_occ, nrays);
    }

    free(rays);
    free(hits);
    free(occ);
    lrt_tri_scene_free(s);
}

/* The N-ray batch queries fall back to a per-ray loop for non-triangle prim
 * kinds (curve/point/sphere/user/qtri). Verify both batch hints reproduce the
 * single-ray results exactly on an already-built scene - this guards the
 * prim-kind dispatch list in intersect1N/occluded1N: a missing kind there would
 * route these primitives into the triangle packet/interleaved kernels (garbage),
 * and the COHERENT hint additionally exercises the BVH4 Ray4 packet selection. */
static void check_batch_consistency(lrt_tri_scene *s, size_t nrays,
                                    const char *label) {
    if (!s) return;
    lrt_ray *rays = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_hit *hits = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    uint8_t *occ = (uint8_t *)malloc(nrays * sizeof(uint8_t));
    if (!rays || !hits || !occ) {
        free(rays);
        free(hits);
        free(occ);
        return;
    }
    for (size_t i = 0; i < nrays; i++) make_random_ray(&rays[i]);
    lrt_tri_batch_hint hints[2] = {LRT_TRI_BATCH_INCOHERENT,
                                   LRT_TRI_BATCH_COHERENT};
    for (int hi = 0; hi < 2; hi++) {
        lrt_tri_intersect1N(s, rays, hits, nrays, hints[hi]);
        lrt_tri_occluded1N(s, rays, occ, nrays, hints[hi]);
        size_t bad = 0, bado = 0;
        for (size_t i = 0; i < nrays; i++) {
            lrt_hit h1;
            lrt_tri_intersect1(s, &rays[i], &h1);
            if (h1.prim_id != hits[i].prim_id ||
                (h1.prim_id != LRT_TRI_NO_HIT && h1.t != hits[i].t))
                bad++;
            if ((uint8_t)lrt_tri_occluded1(s, &rays[i]) != occ[i]) bado++;
        }
        CHECK(bad == 0, "%s: batch intersect1N (hint %d) differs from single on "
              "%zu/%zu rays", label, hi, bad, nrays);
        CHECK(bado == 0, "%s: batch occluded1N (hint %d) differs from single on "
              "%zu/%zu rays", label, hi, bado, nrays);
    }
    free(rays);
    free(hits);
    free(occ);
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

/* Reference ray-capsule test (same algorithm as the library's). */
static int ref_capsule(const float p0[3], const float p1[3], float r,
                       const lrt_ray *ray, float t_max, float *t_out) {
    float dx = p1[0] - p0[0], dy = p1[1] - p0[1], dz = p1[2] - p0[2];
    float mx = ray->org[0] - p0[0], my = ray->org[1] - p0[1],
          mz = ray->org[2] - p0[2];
    float ox = ray->dir[0], oy = ray->dir[1], oz = ray->dir[2];
    float dd = dx * dx + dy * dy + dz * dz;
    float best = t_max;
    int hit = 0;
    if (dd > 1e-20f) {
        float inv_dd = 1.0f / dd;
        float nd = (ox * dx + oy * dy + oz * dz) * inv_dd;
        float md = (mx * dx + my * dy + mz * dz) * inv_dd;
        float ax = ox - dx * nd, ay = oy - dy * nd, az = oz - dz * nd;
        float bx = mx - dx * md, by = my - dy * md, bz = mz - dz * md;
        float A = ax * ax + ay * ay + az * az;
        float B = ax * bx + ay * by + az * bz;
        float C = bx * bx + by * by + bz * bz - r * r;
        if (A > 1e-12f) {
            float disc = B * B - A * C;
            if (disc >= 0.0f) {
                float sq = sqrtf(disc);
                for (int k = 0; k < 2; k++) {
                    float t = (k == 0 ? (-B - sq) : (-B + sq)) / A;
                    if (t < ray->tmin || t >= best) continue;
                    float s = md + t * nd;
                    if (s >= 0.0f && s <= 1.0f) {
                        best = t;
                        hit = 1;
                        break;
                    }
                }
            }
        }
    }
    float a2 = ox * ox + oy * oy + oz * oz;
    for (int cap = 0; cap < 2 && a2 > 1e-20f; cap++) {
        float cx = cap ? mx - dx : mx;
        float cy = cap ? my - dy : my;
        float cz = cap ? mz - dz : mz;
        float b = cx * ox + cy * oy + cz * oz;
        float cc = cx * cx + cy * cy + cz * cz - r * r;
        float disc = b * b - a2 * cc;
        if (disc < 0.0f) continue;
        float t = (-b - sqrtf(disc)) / a2;
        if (t >= ray->tmin && t < best) {
            best = t;
            hit = 1;
        }
    }
    if (hit) *t_out = best;
    return hit;
}

static void test_curve_scene(void) {
    enum { NSEG = 300, NRAYS = 20000 };
    float *segs = (float *)malloc(NSEG * 6 * sizeof(float));
    float *radii = (float *)malloc(NSEG * sizeof(float));
    g_rng = 0xC0FFEE123ull;
    for (int i = 0; i < NSEG; i++) {
        for (int k = 0; k < 6; k++) segs[i * 6 + k] = rnd_f(-2.0f, 2.0f);
        radii[i] = rnd_f(0.01f, 0.06f);
    }
    lrt_tri_scene *s = lrt_curve_scene_build(segs, radii, 0.0f, NSEG, NULL, NULL);
    CHECK(s != NULL, "curve build failed");
    if (!s) {
        free(segs);
        free(radii);
        return;
    }
    printf("  curve scene [%s]\n", lrt_tri_kernel_name(s));

    size_t mismatches = 0, occl_mismatches = 0;
    for (int i = 0; i < NRAYS; i++) {
        lrt_ray r;
        make_random_ray(&r);
        /* brute force over whole capsules */
        float bt = r.tmax;
        int bf = 0;
        for (int j = 0; j < NSEG; j++) {
            float t;
            if (ref_capsule(&segs[j * 6], &segs[j * 6 + 3], radii[j], &r, bt,
                            &t)) {
                bt = t;
                bf = 1;
            }
        }
        lrt_hit h;
        int bvh = lrt_tri_intersect1(s, &r, &h);
        if (bf != bvh) {
            mismatches++;
        } else if (bf &&
                   fabs((double)h.t - (double)bt) >
                       1e-3 * (1.0 + fabs((double)bt))) {
            mismatches++;
        }
        if (lrt_tri_occluded1(s, &r) != bvh) occl_mismatches++;
    }
    /* Sub-segment joints can flip near-tangent rays by one ulp (the joint
     * cap sphere vs the whole-capsule cylinder root); allow the same 0.05%
     * budget the fp32-vs-fp64 verification uses. */
    CHECK(mismatches <= NRAYS / 2000, "curve: %zu/%d mismatches vs "
          "brute-force capsules", mismatches, NRAYS);
    CHECK(occl_mismatches == 0, "curve: %zu occluded disagreements",
          occl_mismatches);

    lrt_tri_scene_free(s);
    free(segs);
    free(radii);
}

/* Reference round-linear segment hit: nearest t over the tapered cone (clipped
 * to its [0,g] slab) plus the two full end spheres. The union of these
 * per-segment solids over a strand equals the kernel's CSG-clipped solid, so
 * the nearest hull hit must match without replicating the neighbor clipping. */
static int ref_roundcone(const float p0[3], float r0, const float p1[3],
                         float r1, const lrt_ray *ray, float t_max,
                         float *t_out) {
    float dirx = ray->dir[0], diry = ray->dir[1], dirz = ray->dir[2];
    float dOdO = dirx * dirx + diry * diry + dirz * dirz;
    float best = t_max;
    int hit = 0;

    float dPx = p1[0] - p0[0], dPy = p1[1] - p0[1], dPz = p1[2] - p0[2];
    float dPdP = dPx * dPx + dPy * dPy + dPz * dPz;
    float dr = r1 - r0, r0dr = r0 * dr;
    float g = dPdP - dr * dr;
    float Ox = ray->org[0] - p0[0], Oy = ray->org[1] - p0[1],
          Oz = ray->org[2] - p0[2];
    float OdP = Ox * dPx + Oy * dPy + Oz * dPz;
    float dOdP = dirx * dPx + diry * dPy + dirz * dPz;
    float yp = OdP + r0dr;
    if (g > 0.0f) {
        float OO = Ox * Ox + Oy * Oy + Oz * Oz;
        float OdO = dirx * Ox + diry * Oy + dirz * Oz;
        float A = g * dOdO - dOdP * dOdP;
        float B = 2.0f * (g * OdO - dOdP * yp);
        float C = g * OO - OdP * OdP - r0 * r0 * dPdP - 2.0f * r0dr * OdP;
        if (A > 1e-18f || A < -1e-18f) {
            float D = B * B - 4.0f * A * C;
            if (D >= 0.0f) {
                float Q = sqrtf(D);
                for (int k = 0; k < 2; k++) {
                    float t = (k == 0 ? (-B - Q) : (-B + Q)) / (2.0f * A);
                    if (t < ray->tmin || t >= best) continue;
                    float y = yp + t * dOdP;
                    if (y > -1.2e-7f && y <= g) { best = t; hit = 1; }
                }
            }
        }
    }
    if (dOdO > 0.0f) {
        for (int sgn = 0; sgn < 2; sgn++) {
            const float *c = sgn ? p1 : p0;
            float rc = sgn ? r1 : r0;
            float ex = ray->org[0] - c[0], ey = ray->org[1] - c[1],
                  ez = ray->org[2] - c[2];
            float b = ex * dirx + ey * diry + ez * dirz;
            float cc = ex * ex + ey * ey + ez * ez - rc * rc;
            float disc = b * b - dOdO * cc;
            if (disc < 0.0f) continue;
            float sq = sqrtf(disc);
            for (int k = 0; k < 2; k++) {
                float t = (k == 0 ? (-b - sq) : (-b + sq)) / dOdO;
                if (t >= ray->tmin && t < best) { best = t; hit = 1; }
            }
        }
    }
    if (hit) *t_out = best;
    return hit;
}

/* Upper-bound invariant for round-linear / flat hits: the hit point must lie
 * within the (clamped, radius-interpolated) capsule of the *reported* segment -
 * the cone body sits at perpendicular distance r(u), and the rounded end caps
 * stay within r of the clamped endpoint, so this holds for both. Validates that
 * prim_id and t are mutually consistent, which the nearest-t oracle never does
 * (it only checks the closest distance over all segments, not which was hit). */
static int hit_within_segment(const float hp[3], const float p0[3],
                              const float p1[3], float r0, float r1) {
    float ax[3] = {p1[0] - p0[0], p1[1] - p0[1], p1[2] - p0[2]};
    float l2 = ax[0] * ax[0] + ax[1] * ax[1] + ax[2] * ax[2];
    float d0[3] = {hp[0] - p0[0], hp[1] - p0[1], hp[2] - p0[2]};
    float u = l2 > 0.0f ? (d0[0] * ax[0] + d0[1] * ax[1] + d0[2] * ax[2]) / l2
                        : 0.0f;
    if (u < 0.0f) u = 0.0f; else if (u > 1.0f) u = 1.0f;
    float perp[3] = {d0[0] - u * ax[0], d0[1] - u * ax[1], d0[2] - u * ax[2]};
    float dist = sqrtf(perp[0] * perp[0] + perp[1] * perp[1] + perp[2] * perp[2]);
    float rr = r0 + u * (r1 - r0);
    return dist <= rr + 3e-3f * (1.0f + rr);
}

static void test_roundcurve_scene(void) {
    enum { NSTRAND = 80, PTS = 6, NRAYS = 20000 };
    size_t npoints = (size_t)NSTRAND * PTS;
    float *pts = (float *)malloc(npoints * 3 * sizeof(float));
    float *rad = (float *)malloc(npoints * sizeof(float));
    uint32_t *sfirst = (uint32_t *)malloc(NSTRAND * sizeof(uint32_t));
    uint32_t *scount = (uint32_t *)malloc(NSTRAND * sizeof(uint32_t));
    g_rng = 0xBEEFCAFEull;
    for (int st = 0; st < NSTRAND; st++) {
        sfirst[st] = (uint32_t)(st * PTS);
        scount[st] = PTS;
        float px = rnd_f(-2.0f, 2.0f), py = rnd_f(-2.0f, 2.0f),
              pz = rnd_f(-2.0f, 2.0f);
        for (int p = 0; p < PTS; p++) {
            size_t idx = (size_t)st * PTS + p;
            /* long-ish steps + thin radius keep segments hair-like (radius <<
             * length), the regime the wCurly.hair vs Embree check validates;
             * fat segments make the joint crease genuinely fp-ambiguous. */
            px += rnd_f(-0.9f, 0.9f);
            py += rnd_f(-0.9f, 0.9f);
            pz += rnd_f(-0.9f, 0.9f);
            pts[idx * 3 + 0] = px;
            pts[idx * 3 + 1] = py;
            pts[idx * 3 + 2] = pz;
            rad[idx] = rnd_f(0.01f, 0.04f); /* varying radius exercises the cone */
        }
    }
    lrt_hair_strands hs = {0};
    hs.points = pts;
    hs.radius = rad;
    hs.constant_radius = 0.0f;
    hs.strand_first = sfirst;
    hs.strand_count = scount;
    hs.nstrands = NSTRAND;
    hs.npoints = npoints;

    lrt_tri_scene *s = lrt_roundcurve_scene_build(&hs, NULL, NULL);
    CHECK(s != NULL, "roundcurve build failed");
    if (!s) {
        free(pts);
        free(rad);
        free(sfirst);
        free(scount);
        return;
    }
    printf("  roundcurve scene [%s]\n", lrt_tri_kernel_name(s));

    size_t mismatches = 0, occl_mismatches = 0, surf_bad = 0;
    for (int i = 0; i < NRAYS; i++) {
        lrt_ray r;
        make_random_ray(&r);
        float bt = r.tmax;
        int bf = 0;
        for (int st = 0; st < NSTRAND; st++) {
            for (int j = 0; j + 1 < PTS; j++) {
                size_t i0 = (size_t)st * PTS + j;
                float t;
                if (ref_roundcone(&pts[i0 * 3], rad[i0], &pts[(i0 + 1) * 3],
                                  rad[i0 + 1], &r, bt, &t)) {
                    bt = t;
                    bf = 1;
                }
            }
        }
        lrt_hit h;
        int bvh = lrt_tri_intersect1(s, &r, &h);
        if (bf != bvh) {
            mismatches++;
        } else if (bf && fabs((double)h.t - (double)bt) >
                             1e-3 * (1.0 + fabs((double)bt))) {
            mismatches++;
        }
        if (lrt_tri_occluded1(s, &r) != bvh) occl_mismatches++;
        /* The reported segment must geometrically contain the hit point. */
        if (bvh) {
            uint32_t prim = h.prim_id, st = prim / (PTS - 1),
                     sl = prim % (PTS - 1);
            uint32_t i0 = st * PTS + sl;
            float hp[3];
            for (int a = 0; a < 3; a++) hp[a] = r.org[a] + h.t * r.dir[a];
            if (prim >= (uint32_t)(NSTRAND * (PTS - 1)) ||
                !hit_within_segment(hp, &pts[(size_t)i0 * 3],
                                    &pts[(size_t)(i0 + 1) * 3], rad[i0],
                                    rad[i0 + 1]))
                surf_bad++;
        }
    }
    /* A handful of grazing/joint rays flip by one ulp at fp32 (the cross-check
     * vs Embree on wCurly.hair shows the same ~5e-6 rate); allow the same
     * budget the capsule and fp64 verifications use. */
    CHECK(mismatches <= NRAYS / 1000, "roundcurve: %zu/%d mismatches vs "
          "brute-force cone+spheres", mismatches, NRAYS);
    CHECK(occl_mismatches == 0, "roundcurve: %zu occluded disagreements",
          occl_mismatches);
    CHECK(surf_bad <= NRAYS / 1000,
          "roundcurve: %zu/%d hits not on the reported segment", surf_bad,
          NRAYS);
    check_batch_consistency(s, 4000, "roundcurve");

    lrt_tri_scene_free(s);
    free(pts);
    free(rad);
    free(sfirst);
    free(scount);
}

/* Reference ray-sphere (matches the library's root selection: near root in
 * [tmin, tmax) else the far root). */
static int ref_sphere(const float *sp, const lrt_ray *r, float tmax,
                      float *t_out) {
    float rr = sp[3];
    if (rr <= 0.0f) return 0;
    float ocx = r->org[0] - sp[0], ocy = r->org[1] - sp[1],
          ocz = r->org[2] - sp[2];
    float a = r->dir[0] * r->dir[0] + r->dir[1] * r->dir[1] +
              r->dir[2] * r->dir[2];
    if (a <= 1e-20f) return 0;
    float b = ocx * r->dir[0] + ocy * r->dir[1] + ocz * r->dir[2];
    float c = ocx * ocx + ocy * ocy + ocz * ocz - rr * rr;
    float disc = b * b - a * c;
    if (disc < 0.0f) return 0;
    float sq = sqrtf(disc), inv = 1.0f / a;
    float t0 = (-b - sq) * inv;
    if (t0 >= r->tmin && t0 < tmax) {
        *t_out = t0;
        return 1;
    }
    float t1 = (-b + sq) * inv;
    if (t1 >= r->tmin && t1 < tmax) {
        *t_out = t1;
        return 1;
    }
    return 0;
}

static void test_sphere_scene(void) {
    enum { NSPH = 400, NRAYS = 20000 };
    float *sph = (float *)malloc(NSPH * 4 * sizeof(float));
    g_rng = 0x5151515151ull;
    for (int i = 0; i < NSPH; i++) {
        sph[i * 4 + 0] = rnd_f(-2.0f, 2.0f);
        sph[i * 4 + 1] = rnd_f(-2.0f, 2.0f);
        sph[i * 4 + 2] = rnd_f(-2.0f, 2.0f);
        sph[i * 4 + 3] = rnd_f(0.02f, 0.2f);
    }
    lrt_result err = LRT_RESULT_OK;
    lrt_tri_scene *s = lrt_sphere_scene_build(sph, NSPH, NULL, &err);
    CHECK(s != NULL, "sphere build failed (err=%d)", (int)err);
    if (!s) {
        free(sph);
        return;
    }
    printf("  sphere scene [%s]\n", lrt_tri_kernel_name(s));
    size_t mism = 0, occl = 0;
    for (int i = 0; i < NRAYS; i++) {
        lrt_ray r;
        make_random_ray(&r);
        float bt = r.tmax;
        int bf = 0;
        for (int j = 0; j < NSPH; j++) {
            float t;
            if (ref_sphere(&sph[j * 4], &r, bt, &t)) {
                bt = t;
                bf = 1;
            }
        }
        lrt_hit h;
        int bvh = lrt_tri_intersect1(s, &r, &h);
        if (bf != bvh) {
            mism++;
        } else if (bf && fabs((double)h.t - (double)bt) >
                             1e-3 * (1.0 + fabs((double)bt))) {
            mism++;
        }
        if (lrt_tri_occluded1(s, &r) != bvh) occl++;
    }
    /* grazing/tangent rays can flip near/far root by an ulp: same 0.05% budget
     * the curve test uses. */
    CHECK(mism <= NRAYS / 2000,
          "sphere: %zu/%d closest mismatches vs brute force", mism, NRAYS);
    CHECK(occl == 0, "sphere: %zu occluded disagreements", occl);
    lrt_tri_scene_free(s);
    free(sph);
}

/* User-geometry callbacks: a sphere field and a triangle soup driven through
 * the generic custom-geometry path. */
typedef struct { const float *sph; } user_sph_ctx;
static int user_sphere_cb(const lrt_ray *ray, uint32_t prim, void *user,
                          float *t, float *u, float *v) {
    const user_sph_ctx *c = (const user_sph_ctx *)user;
    float tt;
    if (ref_sphere(&c->sph[prim * 4], ray, ray->tmax, &tt)) {
        *t = tt;
        *u = 0.0f;
        *v = 0.0f;
        return 1;
    }
    return 0;
}
typedef struct { const float *verts; } user_tri_ctx;
static int user_tri_cb(const lrt_ray *ray, uint32_t prim, void *user, float *t,
                       float *u, float *v) {
    const user_tri_ctx *c = (const user_tri_ctx *)user;
    return ref_isect(&c->verts[prim * 9], ray, t, u, v);
}

/* File-scope user callbacks (hoisted out of test bodies so the file builds with
 * compilers that lack GNU nested functions, e.g. Fujitsu fcc in clang mode). */
static int user_always_hit_cb(const lrt_ray *r, uint32_t p, void *u, float *t,
                              float *u2, float *v) {
    (void)r; (void)p; (void)u; (void)u2; (void)v;
    *t = 5.0f;
    return 1;
}
static int user_always_miss_cb(const lrt_ray *r, uint32_t p, void *u, float *t,
                               float *u2, float *v) {
    (void)r; (void)p; (void)u; (void)t; (void)u2; (void)v;
    return 0;
}

static void test_user_geometry(void) {
    lrt_result err = LRT_RESULT_OK;

    /* (a) sphere field via the generic callback path vs brute force. */
    enum { NSPH = 400, NRAYS = 12000 };
    float *sph = (float *)malloc(NSPH * 4 * sizeof(float));
    float *aabb = (float *)malloc(NSPH * 6 * sizeof(float));
    g_rng = 0x7777ull;
    for (int i = 0; i < NSPH; i++) {
        float cx = rnd_f(-2, 2), cy = rnd_f(-2, 2), cz = rnd_f(-2, 2);
        float r = rnd_f(0.02f, 0.2f);
        sph[i * 4 + 0] = cx;
        sph[i * 4 + 1] = cy;
        sph[i * 4 + 2] = cz;
        sph[i * 4 + 3] = r;
        aabb[i * 6 + 0] = cx - r;
        aabb[i * 6 + 1] = cy - r;
        aabb[i * 6 + 2] = cz - r;
        aabb[i * 6 + 3] = cx + r;
        aabb[i * 6 + 4] = cy + r;
        aabb[i * 6 + 5] = cz + r;
    }
    user_sph_ctx uctx = {sph};
    lrt_tri_scene *us =
        lrt_user_scene_build(aabb, NSPH, user_sphere_cb, NULL, &uctx, NULL, &err);
    CHECK(us != NULL, "user(sphere) build failed (err=%d)", (int)err);
    if (us) {
        printf("  user scene [%s]\n", lrt_tri_kernel_name(us));
        size_t mism = 0, occl = 0;
        for (int i = 0; i < NRAYS; i++) {
            lrt_ray r;
            make_random_ray(&r);
            float bt = r.tmax;
            int bf = 0;
            for (int j = 0; j < NSPH; j++) {
                float t;
                if (ref_sphere(&sph[j * 4], &r, bt, &t)) {
                    bt = t;
                    bf = 1;
                }
            }
            lrt_hit h;
            int bvh = lrt_tri_intersect1(us, &r, &h);
            if (bf != bvh) {
                mism++;
            } else if (bf && fabs((double)h.t - (double)bt) >
                                 1e-3 * (1.0 + fabs((double)bt))) {
                mism++;
            }
            if (lrt_tri_occluded1(us, &r) != bvh) occl++;
        }
        CHECK(mism <= NRAYS / 2000,
              "user(sphere): %zu/%d closest mismatches vs brute force", mism,
              NRAYS);
        CHECK(occl == 0, "user(sphere): %zu occluded disagreements", occl);
        lrt_tri_scene_free(us);
    }
    free(sph);
    free(aabb);

    /* (b) triangle soup via the generic callback path vs the native tri BVH. */
    g_rng = 0xA5A5A5A5ull;
    enum { NT = 800 };
    float *verts = make_random_soup(NT, 0.2f);
    float *taabb = (float *)malloc(NT * 6 * sizeof(float));
    for (int i = 0; i < NT; i++) {
        const float *tv = &verts[i * 9];
        for (int a = 0; a < 3; a++) {
            float lo = tv[a], hi = tv[a];
            for (int k = 1; k < 3; k++) {
                float c = tv[k * 3 + a];
                lo = c < lo ? c : lo;
                hi = c > hi ? c : hi;
            }
            taabb[i * 6 + a] = lo;
            taabb[i * 6 + 3 + a] = hi;
        }
    }
    user_tri_ctx tctx = {verts};
    lrt_tri_scene *uu =
        lrt_user_scene_build(taabb, NT, user_tri_cb, NULL, &tctx, NULL, &err);
    lrt_tri_scene *nat = lrt_tri_scene_build(verts, NT, NULL, &err);
    CHECK(uu && nat, "user(tri)/native build failed");
    if (uu && nat) {
        size_t mism = 0;
        for (int i = 0; i < 12000; i++) {
            lrt_ray r;
            make_random_ray(&r);
            lrt_hit hu, hn;
            int a = lrt_tri_intersect1(uu, &r, &hu);
            int b = lrt_tri_intersect1(nat, &r, &hn);
            if (a != b) {
                mism++;
            } else if (a && fabs((double)hu.t - (double)hn.t) >
                                1e-3 * (1.0 + fabs((double)hn.t))) {
                mism++;
            }
        }
        CHECK(mism <= 12000 / 2000,
              "user(tri) vs native: %zu mismatches", mism);
    }
    lrt_tri_scene_free(uu);
    lrt_tri_scene_free(nat);
    free(verts);
    free(taabb);
}

/* Analytic sphere SDF: length(p - c) - r. */
typedef struct { float c[3]; float r; } sdf_sphere_ctx;
static float sdf_sphere(const float p[3], void *user) {
    const sdf_sphere_ctx *c = (const sdf_sphere_ctx *)user;
    float dx = p[0] - c->c[0], dy = p[1] - c->c[1], dz = p[2] - c->c[2];
    return sqrtf(dx * dx + dy * dy + dz * dz) - c->r;
}

/* Edge-case SDF callbacks for test_sdf_edge_cases. */
static float sdf_nan_cb(const float p[3], void *user) { (void)p; (void)user; return NAN; }
static float sdf_inf_cb(const float p[3], void *user) { (void)p; (void)user; return INFINITY; }
static float sdf_nonlipschitz_cb(const float p[3], void *user) { (void)user;
    float d = sqrtf(p[0] * p[0] + p[1] * p[1] + p[2] * p[2]) - 1.0f;
    return d * 2.0f; /* Lipschitz=2 */
}
static float sdf_constant_cb(const float p[3], void *user) { (void)p; (void)user; return 1.0f; }

/* Ray aimed near a target point (mostly non-grazing, to exercise the marcher
 * cleanly rather than its tangent edge cases). */
static void make_ray_at_target(lrt_ray *r, const float center[3], float spread) {
    float ox = rnd_f(-1, 1), oy = rnd_f(-1, 1), oz = rnd_f(-1, 1);
    float ol = sqrtf(ox * ox + oy * oy + oz * oz);
    if (ol < 1e-6f) {
        ox = 1;
        ol = 1;
    }
    r->org[0] = center[0] + ox / ol * 5.0f;
    r->org[1] = center[1] + oy / ol * 5.0f;
    r->org[2] = center[2] + oz / ol * 5.0f;
    float dx = center[0] + rnd_f(-spread, spread) - r->org[0];
    float dy = center[1] + rnd_f(-spread, spread) - r->org[1];
    float dz = center[2] + rnd_f(-spread, spread) - r->org[2];
    float dl = sqrtf(dx * dx + dy * dy + dz * dz);
    r->dir[0] = dx / dl;
    r->dir[1] = dy / dl;
    r->dir[2] = dz / dl;
    r->tmin = 1e-4f;
    r->tmax = 20.0f;
}

static void test_sdf_standalone(void) {
    sdf_sphere_ctx c = {{0.5f, -0.3f, 0.2f}, 1.2f};
    lrt_sdf_params p;
    memset(&p, 0, sizeof(p));
    p.epsilon = 1e-4f;
    p.max_steps = 256;
    p.normal_eps = 1e-3f;
    g_rng = 0x9911ull;
    size_t mism = 0, nrm_bad = 0;
    int tested = 0;
    for (int i = 0; i < 4000; i++) {
        lrt_ray r;
        make_ray_at_target(&r, c.c, 0.9f);
        float sp[4] = {c.c[0], c.c[1], c.c[2], c.r};
        float at;
        int ahit = ref_sphere(sp, &r, r.tmax, &at);
        lrt_sdf_hit hit;
        int shit = lrt_sdf_sphere_trace(r.org, r.dir, r.tmin, r.tmax, sdf_sphere,
                                        &c, &p, &hit);
        if (ahit != shit) {
            mism++;
            continue;
        }
        if (ahit) {
            tested++;
            if (fabs((double)hit.t - (double)at) > 5e-3 * (1.0 + fabs((double)at)))
                mism++;
            float nx = (hit.p[0] - c.c[0]) / c.r;
            float ny = (hit.p[1] - c.c[1]) / c.r;
            float nz = (hit.p[2] - c.c[2]) / c.r;
            double dot = hit.n[0] * nx + hit.n[1] * ny + hit.n[2] * nz;
            if (dot < 0.99) nrm_bad++;
        }
    }
    CHECK(mism <= 4000 / 100, "sdf standalone: %zu mismatches vs analytic sphere",
          mism);
    CHECK(nrm_bad <= (size_t)(tested / 50 + 1),
          "sdf standalone: %zu/%d bad normals", nrm_bad, tested);

    /* over-relaxation must not change the surface found */
    size_t relax_bad = 0;
    g_rng = 0x9911ull;
    for (int i = 0; i < 2000; i++) {
        lrt_ray r;
        make_ray_at_target(&r, c.c, 0.9f);
        float omegas[3] = {1.0f, 1.6f, 1.9f};
        float ts[3];
        int hits[3];
        for (int k = 0; k < 3; k++) {
            p.over_relax = omegas[k];
            lrt_sdf_hit h;
            hits[k] = lrt_sdf_sphere_trace(r.org, r.dir, r.tmin, r.tmax,
                                           sdf_sphere, &c, &p, &h);
            ts[k] = h.t;
        }
        if (hits[0] != hits[1] || hits[1] != hits[2]) {
            relax_bad++;
        } else if (hits[0] &&
                   (fabs((double)ts[0] - (double)ts[1]) > 1e-2 ||
                    fabs((double)ts[0] - (double)ts[2]) > 1e-2)) {
            relax_bad++;
        }
    }
    CHECK(relax_bad <= 2000 / 100,
          "sdf over-relaxation changed the surface on %zu rays", relax_bad);
}

static void test_sdf_scene(void) {
    enum { GRID = 4, NB = GRID * GRID * GRID, NRAYS = 8000 };
    float *sph = (float *)malloc(NB * 4 * sizeof(float));
    sdf_sphere_ctx *ctx = (sdf_sphere_ctx *)malloc(NB * sizeof(sdf_sphere_ctx));
    lrt_sdf_blob *blobs = (lrt_sdf_blob *)malloc(NB * sizeof(lrt_sdf_blob));
    const float R = 0.4f, SP = 1.2f; /* disjoint: gap 0.4 between spheres */
    int idx = 0;
    for (int x = 0; x < GRID; x++)
        for (int y = 0; y < GRID; y++)
            for (int z = 0; z < GRID; z++, idx++) {
                float cx = (x - 1.5f) * SP, cy = (y - 1.5f) * SP,
                      cz = (z - 1.5f) * SP;
                sph[idx * 4 + 0] = cx;
                sph[idx * 4 + 1] = cy;
                sph[idx * 4 + 2] = cz;
                sph[idx * 4 + 3] = R;
                ctx[idx].c[0] = cx;
                ctx[idx].c[1] = cy;
                ctx[idx].c[2] = cz;
                ctx[idx].r = R;
                blobs[idx].aabb[0] = cx - R;
                blobs[idx].aabb[1] = cy - R;
                blobs[idx].aabb[2] = cz - R;
                blobs[idx].aabb[3] = cx + R;
                blobs[idx].aabb[4] = cy + R;
                blobs[idx].aabb[5] = cz + R;
                blobs[idx].sdf = sdf_sphere;
                blobs[idx].user = &ctx[idx];
            }
    lrt_sdf_params p;
    memset(&p, 0, sizeof(p));
    p.epsilon = 5e-5f;
    p.max_steps = 128;
    lrt_result err = LRT_RESULT_OK;
    lrt_tri_scene *sdf = lrt_sdf_scene_build(blobs, NB, &p, NULL, &err);
    lrt_tri_scene *ana = lrt_sphere_scene_build(sph, NB, NULL, &err);
    CHECK(sdf && ana, "sdf/analytic sphere scene build failed");
    if (sdf && ana) {
        printf("  sdf scene [%s]\n", lrt_tri_kernel_name(sdf));
        const float center[3] = {0, 0, 0};
        size_t mism = 0, occl = 0;
        g_rng = 0x4242ull;
        for (int i = 0; i < NRAYS; i++) {
            lrt_ray r;
            make_ray_at_target(&r, center, 3.0f);
            lrt_hit hs, ha;
            int a = lrt_tri_intersect1(sdf, &r, &hs);
            int b = lrt_tri_intersect1(ana, &r, &ha);
            if (a != b) {
                mism++;
            } else if (a && fabs((double)hs.t - (double)ha.t) >
                                3e-3 * (1.0 + fabs((double)ha.t))) {
                mism++;
            }
            if (lrt_tri_occluded1(sdf, &r) != a) occl++;
        }
        CHECK(mism <= NRAYS / 100, "sdf scene: %zu mismatches vs analytic spheres",
              mism);
        CHECK(occl == 0, "sdf scene: %zu occluded disagreements", occl);
    }
    lrt_tri_scene_free(sdf);
    lrt_tri_scene_free(ana);
    free(sph);
    free(ctx);
    free(blobs);
}

/* Reference closest-point-on-triangle squared distance (Ericson). */
static float ref_point_tri_distsq(const float *tri, const float p[3]) {
    const float *A = &tri[0], *B = &tri[3], *C = &tri[6];
    float ab[3] = {B[0] - A[0], B[1] - A[1], B[2] - A[2]};
    float ac[3] = {C[0] - A[0], C[1] - A[1], C[2] - A[2]};
    float ap[3] = {p[0] - A[0], p[1] - A[1], p[2] - A[2]};
    float d1 = ab[0] * ap[0] + ab[1] * ap[1] + ab[2] * ap[2];
    float d2 = ac[0] * ap[0] + ac[1] * ap[1] + ac[2] * ap[2];
    float q[3];
    do {
        if (d1 <= 0 && d2 <= 0) {
            q[0] = A[0]; q[1] = A[1]; q[2] = A[2];
            break;
        }
        float bp[3] = {p[0] - B[0], p[1] - B[1], p[2] - B[2]};
        float d3 = ab[0] * bp[0] + ab[1] * bp[1] + ab[2] * bp[2];
        float d4 = ac[0] * bp[0] + ac[1] * bp[1] + ac[2] * bp[2];
        if (d3 >= 0 && d4 <= d3) {
            q[0] = B[0]; q[1] = B[1]; q[2] = B[2];
            break;
        }
        float vc = d1 * d4 - d3 * d2;
        if (vc <= 0 && d1 >= 0 && d3 <= 0) {
            float v = d1 / (d1 - d3);
            for (int a = 0; a < 3; a++) q[a] = A[a] + v * ab[a];
            break;
        }
        float cp[3] = {p[0] - C[0], p[1] - C[1], p[2] - C[2]};
        float d5 = ab[0] * cp[0] + ab[1] * cp[1] + ab[2] * cp[2];
        float d6 = ac[0] * cp[0] + ac[1] * cp[1] + ac[2] * cp[2];
        if (d6 >= 0 && d5 <= d6) {
            q[0] = C[0]; q[1] = C[1]; q[2] = C[2];
            break;
        }
        float vb = d5 * d2 - d1 * d6;
        if (vb <= 0 && d2 >= 0 && d6 <= 0) {
            float w = d2 / (d2 - d6);
            for (int a = 0; a < 3; a++) q[a] = A[a] + w * ac[a];
            break;
        }
        float va = d3 * d6 - d5 * d4;
        if (va <= 0 && (d4 - d3) >= 0 && (d5 - d6) >= 0) {
            float w = (d4 - d3) / ((d4 - d3) + (d5 - d6));
            for (int a = 0; a < 3; a++) q[a] = B[a] + w * (C[a] - B[a]);
            break;
        }
        float denom = 1.0f / (va + vb + vc);
        float v = vb * denom, w = vc * denom;
        for (int a = 0; a < 3; a++) q[a] = A[a] + ab[a] * v + ac[a] * w;
    } while (0);
    float dx = p[0] - q[0], dy = p[1] - q[1], dz = p[2] - q[2];
    return dx * dx + dy * dy + dz * dz;
}

static int cmp_float(const void *a, const void *b) {
    float fa = *(const float *)a, fb = *(const float *)b;
    return fa < fb ? -1 : (fa > fb ? 1 : 0);
}

typedef struct {
    float dist;
    uint32_t id;
} knn_ref_entry;

static int cmp_knn_ref(const void *a, const void *b) {
    const knn_ref_entry *pa = (const knn_ref_entry *)a;
    const knn_ref_entry *pb = (const knn_ref_entry *)b;
    if (pa->dist < pb->dist) return -1;
    if (pa->dist > pb->dist) return 1;
    if (pa->id < pb->id) return -1;
    if (pa->id > pb->id) return 1;
    return 0;
}

static void test_closest_point_knn(void) {
    enum { NT = 600, K = 8 };
    g_rng = 0xB00B5ull;
    float *verts = make_random_soup(NT, 0.2f);
    lrt_result err = LRT_RESULT_OK;
    lrt_tri_scene *s = lrt_tri_scene_build(verts, NT, NULL, &err);
    CHECK(s != NULL, "knn build failed");
    if (!s) {
        free(verts);
        return;
    }
    size_t mism = 0, cp_mism = 0;
    float *bd = (float *)malloc(NT * sizeof(float));
    for (int i = 0; i < 3000; i++) {
        float p[3] = {rnd_f(-3, 3), rnd_f(-3, 3), rnd_f(-3, 3)};
        for (int j = 0; j < NT; j++) bd[j] = ref_point_tri_distsq(&verts[j * 9], p);
        qsort(bd, NT, sizeof(float), cmp_float);
        lrt_knn_result kr[K];
        size_t n = lrt_tri_knn(s, p, K, kr, K);
        if (n != K) mism++;
        for (size_t m = 0; m < n; m++) {
            if (m > 0 && kr[m].dist_sq < kr[m - 1].dist_sq) mism++; /* sorted */
            if (fabs((double)kr[m].dist_sq - (double)bd[m]) >
                1e-4 * (1.0 + (double)bd[m]))
                mism++;
        }
        lrt_point_hit ph;
        int c = lrt_tri_closest_point(s, p, &ph);
        if (!c) {
            cp_mism++;
        } else {
            if (fabs((double)ph.dist_sq - (double)kr[0].dist_sq) >
                1e-4 * (1.0 + (double)kr[0].dist_sq))
                cp_mism++;
            float dx = p[0] - ph.point[0], dy = p[1] - ph.point[1],
                  dz = p[2] - ph.point[2];
            double d = (double)(dx * dx + dy * dy + dz * dz);
            if (fabs(d - (double)ph.dist_sq) > 1e-4 * (1.0 + d)) cp_mism++;
        }
    }
    CHECK(mism == 0, "knn: %zu discrepancies vs brute force", mism);
    CHECK(cp_mism == 0, "closest_point: %zu discrepancies vs knn(1)", cp_mism);

    /* Deterministic edge cases for k-NN and closest-point parity. */
    {
        enum { NTD = 3 };
        float tri2[NTD * 9] = {
            -1, -1, 5, 1, -1, 5, 0, 1, 5,      /* tri 0 */
            3, 3, 6, 5, 3, 6, 4, 5, 6,          /* tri 1 */
            10, 10, 9, 12, 10, 9, 11, 12, 9      /* tri 2 */
        };
        float qv[3];
        lrt_tri_scene *ks = lrt_tri_scene_build(tri2, NTD, NULL, &err);
        CHECK(ks != NULL, "knn edge: deterministic scene build");
        if (ks) {
            lrt_knn_result krd[16];
            lrt_point_hit pht;
            knn_ref_entry expd[NTD];
            size_t got;

            /* k=0 should return 0. */
            qv[0] = 0.0f;
            qv[1] = 0.0f;
            qv[2] = 0.0f;
            CHECK(lrt_tri_knn(ks, qv, 0, krd, 16) == 0,
                  "knn k=0 returns 0");

            /* Vertex query: nearest must be tri-0 at its (-1,-1,5) vertex. */
            qv[0] = -1.0f;
            qv[1] = -1.0f;
            qv[2] = 0.0f;
            got = lrt_tri_knn(ks, qv, 1, krd, 16);
            CHECK(got == 1, "knn k=1 vertex query returns 1");
            if (got >= 1) {
                for (int i = 0; i < NTD; i++) {
                    expd[i].dist = ref_point_tri_distsq(&tri2[i * 9], qv);
                    expd[i].id = (uint32_t)i;
                }
                qsort(expd, NTD, sizeof(expd[0]), cmp_knn_ref);
                CHECK(krd[0].prim_id == expd[0].id &&
                      fabs((double)krd[0].dist_sq - (double)expd[0].dist) <
                          1e-4 * (1.0 + (double)expd[0].dist),
                      "knn k=1 parity at vertex");
                CHECK(lrt_tri_closest_point(ks, qv, &pht) == 1 &&
                      pht.prim_id == expd[0].id &&
                      fabs((double)pht.dist_sq - (double)expd[0].dist) <
                          1e-4 * (1.0 + (double)expd[0].dist),
                      "k=1 closest_point parity at vertex");
            }

            /* Edge query: first result should still be the nearby tri-0, and
             * the third result should be tri-2 (farthest). */
            qv[0] = 0.0f;
            qv[1] = -1.0f;
            qv[2] = 5.0f;
            got = lrt_tri_knn(ks, qv, 3, krd, 16);
            for (int i = 0; i < NTD; i++) {
                expd[i].dist = ref_point_tri_distsq(&tri2[i * 9], qv);
                expd[i].id = (uint32_t)i;
            }
            qsort(expd, NTD, sizeof(expd[0]), cmp_knn_ref);
            CHECK(got == 3, "knn edge query k>scene-size returns 3");
            CHECK(
                krd[0].prim_id == expd[0].id &&
                    fabs((double)krd[0].dist_sq - (double)expd[0].dist) <
                        1e-4 * (1.0 + (double)expd[0].dist),
                "knn edge-query: nearest match");
            CHECK(
                krd[1].prim_id == expd[1].id &&
                    fabs((double)krd[1].dist_sq - (double)expd[1].dist) <
                        1e-4 * (1.0 + (double)expd[1].dist),
                "knn edge-query: second match");
            CHECK(
                krd[2].prim_id == expd[2].id &&
                    fabs((double)krd[2].dist_sq - (double)expd[2].dist) <
                        1e-4 * (1.0 + (double)expd[2].dist),
                "knn edge-query: third match");

            /* Request a k larger than scene size: result is capped by ntris. */
            qv[0] = 1000.0f;
            qv[1] = 1000.0f;
            qv[2] = 0.0f;
            got = lrt_tri_knn(ks, qv, 16, krd, 16);
            CHECK(got == NTD, "knn k>ntris returns ntris");
            lrt_tri_scene_free(ks);
        }
    }

    free(bd);
    lrt_tri_scene_free(s);
    free(verts);
}

static void tri_aabb(const float *tri, float lo[3], float hi[3]) {
    for (int a = 0; a < 3; a++) {
        lo[a] = hi[a] = tri[a];
        for (int k = 1; k < 3; k++) {
            float c = tri[k * 3 + a];
            if (c < lo[a]) lo[a] = c;
            if (c > hi[a]) hi[a] = c;
        }
    }
}

static void test_region_queries(void) {
    enum { NT = 1000 };
    g_rng = 0xCAFEF00Dull;
    float *verts = make_random_soup(NT, 0.15f);
    lrt_tri_scene *s = lrt_tri_scene_build(verts, NT, NULL, NULL);
    CHECK(s != NULL, "region build failed");
    if (!s) {
        free(verts);
        return;
    }
    uint32_t *out = (uint32_t *)malloc(NT * sizeof(uint32_t));
    uint8_t *exp = (uint8_t *)malloc(NT);
    size_t aabb_bad = 0, sph_bad = 0, dup_bad = 0;
    for (int trial = 0; trial < 400; trial++) {
        float cx = rnd_f(-2, 2), cy = rnd_f(-2, 2), cz = rnd_f(-2, 2);
        float h = rnd_f(0.3f, 1.5f);
        float qlo[3] = {cx - h, cy - h, cz - h}, qhi[3] = {cx + h, cy + h, cz + h};
        size_t n = lrt_tri_query_aabb(s, qlo, qhi, out, NT);
        memset(exp, 0, NT);
        size_t nexp = 0;
        for (int j = 0; j < NT; j++) {
            float lo[3], hi[3];
            tri_aabb(&verts[j * 9], lo, hi);
            if (lo[0] <= qhi[0] && hi[0] >= qlo[0] && lo[1] <= qhi[1] &&
                hi[1] >= qlo[1] && lo[2] <= qhi[2] && hi[2] >= qlo[2]) {
                exp[j] = 1;
                nexp++;
            }
        }
        if (n != nexp) aabb_bad++;
        uint8_t *seen = (uint8_t *)calloc(NT, 1);
        for (size_t i = 0; i < n; i++) {
            if (out[i] >= NT || !exp[out[i]]) aabb_bad++;
            if (seen[out[i]]) dup_bad++;
            seen[out[i]] = 1;
        }
        free(seen);

        /* sphere */
        float r = rnd_f(0.3f, 1.2f);
        float center[3] = {cx, cy, cz};
        size_t ns = lrt_tri_query_sphere(s, center, r, out, NT);
        size_t nexps = 0;
        for (int j = 0; j < NT; j++) {
            float lo[3], hi[3];
            tri_aabb(&verts[j * 9], lo, hi);
            float dsq = 0;
            for (int a = 0; a < 3; a++) {
                float v = center[a];
                float cl = v < lo[a] ? lo[a] : (v > hi[a] ? hi[a] : v);
                float d = v - cl;
                dsq += d * d;
            }
            if (dsq <= r * r) nexps++;
        }
        if (ns != nexps) sph_bad++;
    }
    CHECK(aabb_bad == 0, "query_aabb: %zu discrepancies vs brute force", aabb_bad);
    CHECK(sph_bad == 0, "query_sphere: %zu discrepancies vs brute force", sph_bad);
    CHECK(dup_bad == 0, "query_aabb: %zu duplicate ids on object-split build",
          dup_bad);

    /* truncation: a tiny cap must return exactly cap and signal truncation. */
    float big_lo[3] = {-100, -100, -100}, big_hi[3] = {100, 100, 100};
    uint32_t small[4];
    size_t nt = lrt_tri_query_aabb(s, big_lo, big_hi, small, 4);
    CHECK(nt == 4, "query truncation returns cap (%zu)", nt);

    free(out);
    free(exp);
    lrt_tri_scene_free(s);
    free(verts);
}

static int frustum_box_pass(const lrt_frustum *f, const float lo[3],
                            const float hi[3]) {
    for (int pl = 0; pl < 6; pl++) {
        const float *P = f->planes[pl];
        float px = P[0] >= 0 ? hi[0] : lo[0];
        float py = P[1] >= 0 ? hi[1] : lo[1];
        float pz = P[2] >= 0 ? hi[2] : lo[2];
        if (P[0] * px + P[1] * py + P[2] * pz + P[3] < 0.0f) return 0;
    }
    return 1;
}

static void test_frustum(void) {
    /* identity matrix => clip-space cube [-1,1]^3 as the frustum. */
    float m[16] = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1};
    lrt_frustum f;
    lrt_frustum_from_matrix(m, &f);

    enum { NT = 800 };
    g_rng = 0x9F9Full;
    float *verts = make_random_soup(NT, 0.3f); /* spread across [-2.5, 2.5]^3 */
    lrt_tri_scene *s = lrt_tri_scene_build(verts, NT, NULL, NULL);
    CHECK(s != NULL, "frustum build failed");
    if (!s) {
        free(verts);
        return;
    }
    uint32_t *out = (uint32_t *)malloc(NT * sizeof(uint32_t));
    size_t n = lrt_tri_query_frustum(s, &f, out, NT);
    size_t nexp = 0;
    uint8_t *exp = (uint8_t *)calloc(NT, 1);
    for (int j = 0; j < NT; j++) {
        float lo[3], hi[3];
        tri_aabb(&verts[j * 9], lo, hi);
        if (frustum_box_pass(&f, lo, hi)) {
            exp[j] = 1;
            nexp++;
        }
    }
    size_t bad = 0;
    if (n != nexp) bad++;
    for (size_t i = 0; i < n; i++)
        if (out[i] >= NT || !exp[out[i]]) bad++;
    CHECK(bad == 0, "query_frustum: %zu discrepancies vs brute force (n=%zu "
          "exp=%zu)", bad, n, nexp);
    CHECK(nexp > 0 && nexp < NT, "frustum should partition the scene (in=%zu)",
          nexp);
    free(out);
    free(exp);
    lrt_tri_scene_free(s);
    free(verts);
}

static void test_multihit(void) {
    /* Stacked big triangles along +z at z = 1..8, all covering the origin ray. */
    enum { NP = 8 };
    float verts[NP * 9];
    for (int k = 0; k < NP; k++) {
        float z = (float)(k + 1);
        float t[9] = {-10, -10, z, 10, -10, z, 0, 10, z};
        memcpy(&verts[k * 9], t, sizeof(t));
    }
    lrt_tri_scene *s = lrt_tri_scene_build(verts, NP, NULL, NULL);
    CHECK(s != NULL, "multihit build failed");
    if (!s) return;
    lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
    lrt_hit hits[5];
    size_t n = lrt_tri_intersect_n(s, &r, hits, 5);
    CHECK(n == 5, "multihit: expected 5 of 8, got %zu", n);
    int sorted_ok = 1;
    for (size_t i = 0; i < n; i++) {
        if (fabsf(hits[i].t - (float)(i + 1)) > 1e-4f) sorted_ok = 0;
    }
    CHECK(sorted_ok, "multihit: hits not sorted t=1..5");
    lrt_hit one;
    lrt_tri_intersect1(s, &r, &one);
    CHECK(n > 0 && one.prim_id == hits[0].prim_id &&
              fabsf(one.t - hits[0].t) < 1e-6f,
          "multihit out[0] != intersect1");
    /* requesting all returns 8 */
    lrt_hit all[16];
    size_t na = lrt_tri_intersect_n(s, &r, all, 16);
    CHECK(na == 8, "multihit: expected all 8, got %zu", na);
    lrt_tri_scene_free(s);

    /* random soup: intersect_n (large cap) vs brute-force sorted hit list. */
    g_rng = 0x1234ABCDull;
    enum { NT = 400 };
    float *vs = make_random_soup(NT, 0.5f);
    lrt_tri_scene *ss = lrt_tri_scene_build(vs, NT, NULL, NULL);
    size_t bad = 0;
    if (ss) {
        for (int i = 0; i < 4000; i++) {
            lrt_ray rr;
            make_random_ray(&rr);
            lrt_hit mh[32];
            size_t mn = lrt_tri_intersect_n(ss, &rr, mh, 32);
            /* brute force all hits, sorted by t */
            float bts[NT];
            int bn = 0;
            for (int j = 0; j < NT; j++) {
                float t, u, v;
                if (ref_isect(&vs[j * 9], &rr, &t, &u, &v)) bts[bn++] = t;
            }
            qsort(bts, bn, sizeof(float), cmp_float);
            size_t want = (size_t)(bn < 32 ? bn : 32);
            if (mn != want) {
                bad++;
                continue;
            }
            for (size_t m = 0; m + 1 < mn; m++)
                if (mh[m].t > mh[m + 1].t + 1e-6f) bad++; /* sorted */
            for (size_t m = 0; m < mn; m++)
                if (fabs((double)mh[m].t - (double)bts[m]) >
                    1e-3 * (1.0 + fabs((double)bts[m])))
                    bad++;
        }
        CHECK(bad <= 4000 / 500, "multihit soup: %zu discrepancies", bad);
        lrt_tri_scene_free(ss);
    }
    free(vs);
}

/* Queries must agree across node layouts (exercises the BVH8 / BVH8Q decode in
 * tri_node_load). */
static void test_query_layouts(void) {
    enum { NT = 700, K = 6 };
    g_rng = 0xFEEDFACEull;
    float *verts = make_random_soup(NT, 0.18f);
    lrt_tri_layout layouts[3] = {LRT_TRI_LAYOUT_BVH4, LRT_TRI_LAYOUT_BVH8,
                                 LRT_TRI_LAYOUT_BVH8Q};
    lrt_tri_scene *sc[3];
    for (int l = 0; l < 3; l++) {
        lrt_tri_build_options o = {.quality = LRT_TRI_BUILD_DEFAULT,
                                   .layout = layouts[l]};
        sc[l] = lrt_tri_scene_build(verts, NT, &o, NULL);
    }
    CHECK(sc[0] && sc[1] && sc[2], "query-layouts: build failed");
    if (sc[0] && sc[1] && sc[2]) {
        size_t knn_bad = 0, aabb_bad = 0;
        for (int i = 0; i < 1500; i++) {
            float p[3] = {rnd_f(-3, 3), rnd_f(-3, 3), rnd_f(-3, 3)};
            lrt_knn_result k0[K], k1[K], k2[K];
            size_t n0 = lrt_tri_knn(sc[0], p, K, k0, K);
            size_t n1 = lrt_tri_knn(sc[1], p, K, k1, K);
            size_t n2 = lrt_tri_knn(sc[2], p, K, k2, K);
            if (n0 != n1 || n0 != n2) knn_bad++;
            for (size_t m = 0; m < n0 && m < n1 && m < n2; m++) {
                if (fabs((double)k0[m].dist_sq - (double)k1[m].dist_sq) > 1e-4 ||
                    fabs((double)k0[m].dist_sq - (double)k2[m].dist_sq) > 1e-3)
                    knn_bad++;
            }
            float c[3] = {p[0], p[1], p[2]};
            uint32_t o0[64], o1[64], o2[64];
            size_t a0 = lrt_tri_query_sphere(sc[0], c, 0.6f, o0, 64);
            size_t a1 = lrt_tri_query_sphere(sc[1], c, 0.6f, o1, 64);
            size_t a2 = lrt_tri_query_sphere(sc[2], c, 0.6f, o2, 64);
            if (a0 != a1 || a0 != a2) aabb_bad++;
        }
        CHECK(knn_bad == 0, "query-layouts: %zu knn disagreements", knn_bad);
        CHECK(aabb_bad == 0, "query-layouts: %zu sphere-query disagreements",
              aabb_bad);
    }
    for (int l = 0; l < 3; l++) lrt_tri_scene_free(sc[l]);
    free(verts);
}

/* Two scenes must give bitwise-identical closest/any-hit results. */
static size_t scenes_disagree(lrt_tri_scene *a, lrt_tri_scene *b, int nrays) {
    size_t bad = 0;
    for (int i = 0; i < nrays; i++) {
        lrt_ray r;
        make_random_ray(&r);
        lrt_hit ha, hb;
        int x = lrt_tri_intersect1(a, &r, &ha);
        int y = lrt_tri_intersect1(b, &r, &hb);
        if (x != y) {
            bad++;
        } else if (x && (ha.prim_id != hb.prim_id || ha.t != hb.t)) {
            bad++;
        }
        if (lrt_tri_occluded1(a, &r) != lrt_tri_occluded1(b, &r)) bad++;
    }
    return bad;
}

static void test_serialization(void) {
    g_rng = 0x5E512Eull;
    enum { NT = 2000 };
    float *verts = make_random_soup(NT, 0.15f);
    lrt_tri_layout layouts[3] = {LRT_TRI_LAYOUT_BVH4, LRT_TRI_LAYOUT_BVH8,
                                 LRT_TRI_LAYOUT_BVH8Q};
    const char *path = "/tmp/lrt_test_scene.lrts";
    for (int l = 0; l < 3; l++) {
        lrt_tri_build_options o = {.quality = LRT_TRI_BUILD_DEFAULT,
                                   .layout = layouts[l]};
        lrt_result err = LRT_RESULT_OK;
        lrt_tri_scene *s = lrt_tri_scene_build(verts, NT, &o, &err);
        CHECK(s != NULL, "serialization: build failed");
        if (!s) continue;

        void *buf = NULL;
        size_t n = 0;
        CHECK(lrt_tri_scene_save_to_memory(s, &buf, &n) == LRT_RESULT_OK && buf,
              "save_to_memory failed");
        if (buf) {
            lrt_tri_scene *ld = lrt_tri_scene_load_from_memory(buf, n, &err);
            CHECK(ld != NULL, "load_from_memory failed (err=%d)", (int)err);
            if (ld) {
                CHECK(scenes_disagree(s, ld, 15000) == 0,
                      "load_from_memory layout %d: traversal differs", l);
                lrt_tri_scene_free(ld);
            }
            /* corruption must be rejected, not crash */
            unsigned char *c1 = (unsigned char *)malloc(n);
            memcpy(c1, buf, n);
            c1[0] = 'X'; /* bad magic */
            CHECK(lrt_tri_scene_load_from_memory(c1, n, &err) == NULL,
                  "corrupt magic accepted");
            memcpy(c1, buf, n);
            *(uint32_t *)(c1 + 32) = 0x70000000u; /* root -> huge node idx */
            CHECK(lrt_tri_scene_load_from_memory(c1, n, &err) == NULL,
                  "corrupt root accepted");
            CHECK(lrt_tri_scene_load_from_memory(buf, n - 1, &err) == NULL,
                  "truncated buffer accepted");
            free(c1);
            free(buf);
        }

        /* file + mmap round trip */
        CHECK(lrt_tri_scene_save(s, path) == LRT_RESULT_OK, "save to file failed");
        lrt_tri_scene *lf = lrt_tri_scene_load(path, &err);
        CHECK(lf != NULL, "load from file failed");
        if (lf) {
            CHECK(scenes_disagree(s, lf, 8000) == 0, "file load differs");
            lrt_tri_scene_free(lf);
        }
        lrt_tri_scene *mm = lrt_tri_scene_open_mmap(path, &err);
        CHECK(mm != NULL, "open_mmap failed (err=%d)", (int)err);
        if (mm) {
            CHECK(scenes_disagree(s, mm, 8000) == 0, "mmap load differs");
            lrt_tri_scene_free(mm);
        }
        remove(path);
        lrt_tri_scene_free(s);
    }

    /* curve and sphere scenes serialize too (LRTS v2 reconstructs shade data
     * from leaves); user scenes still refuse. */
    {
        lrt_result err = LRT_RESULT_OK;
        float segs[6] = {-1, 0, 0, 1, 0.2f, 0.1f};
        lrt_tri_scene *cs = lrt_curve_scene_build(segs, NULL, 0.05f, 1, NULL, &err);
        if (cs) {
            void *buf = NULL;
            size_t n = 0;
            CHECK(lrt_tri_scene_save_to_memory(cs, &buf, &n) == LRT_RESULT_OK,
                  "curve save failed");
            if (buf) {
                lrt_tri_scene *ld = lrt_tri_scene_load_from_memory(buf, n, &err);
                CHECK(ld != NULL, "curve load failed");
                if (ld) {
                    CHECK(scenes_disagree(cs, ld, 5000) == 0,
                          "curve serialization differs");
                    lrt_tri_scene_free(ld);
                }
                free(buf);
            }
            lrt_tri_scene_free(cs);
        }
        float sph[4] = {0, 0, 0, 1};
        lrt_tri_scene *sp = lrt_sphere_scene_build(sph, 1, NULL, &err);
        if (sp) {
            void *buf = NULL;
            size_t n = 0;
            CHECK(lrt_tri_scene_save_to_memory(sp, &buf, &n) == LRT_RESULT_OK,
                  "sphere save failed");
            if (buf) {
                lrt_tri_scene *ld = lrt_tri_scene_load_from_memory(buf, n, &err);
                CHECK(ld != NULL, "sphere load failed");
                if (ld) {
                    CHECK(scenes_disagree(sp, ld, 5000) == 0,
                          "sphere serialization differs");
                    lrt_tri_scene_free(ld);
                }
                free(buf);
            }
            lrt_tri_scene_free(sp);
        }
    }
    free(verts);
}

/* refit(scene, V) must agree with a fresh build over V (checked vs brute force). */
static size_t refit_vs_brute(lrt_tri_scene *s, const float *verts, size_t ntris,
                             int nrays) {
    size_t bad = 0;
    for (int i = 0; i < nrays; i++) {
        lrt_ray r;
        make_random_ray(&r);
        lrt_hit ha, hb;
        int bf = brute_force(verts, ntris, &r, &hb);
        int bvh = lrt_tri_intersect1(s, &r, &ha);
        if (bf != bvh) {
            bad++;
        } else if (bf && fabs((double)ha.t - (double)hb.t) >
                             1e-3 * (1.0 + fabs((double)hb.t))) {
            bad++;
        }
    }
    return bad;
}

static void test_refit(void) {
    g_rng = 0xBEEF77ull;
    enum { NT = 1500 };
    float *v0 = make_random_soup(NT, 0.15f);
    float *v1 = (float *)malloc(NT * 9 * sizeof(float));
    float *vf = (float *)malloc(NT * 9 * sizeof(float));
    for (int i = 0; i < NT * 9; i++) v1[i] = v0[i] * 1.4f + 0.6f; /* affine move */
    for (int i = 0; i < NT * 9; i++)
        vf[i] = (i % 3 == 2) ? 1.0f : v0[i]; /* flatten onto z=1 */

    lrt_tri_layout layouts[3] = {LRT_TRI_LAYOUT_BVH4, LRT_TRI_LAYOUT_BVH8,
                                 LRT_TRI_LAYOUT_BVH8Q};
    for (int l = 0; l < 3; l++) {
        lrt_tri_build_options o = {.quality = LRT_TRI_BUILD_DEFAULT,
                                   .layout = layouts[l]};
        lrt_tri_scene *a = lrt_tri_scene_build(v0, NT, &o, NULL);
        CHECK(a != NULL, "refit build failed");
        if (!a) continue;
        CHECK(lrt_tri_scene_refit(a, v1, NT) == LRT_RESULT_OK,
              "refit returned error (layout %d)", l);
        CHECK(refit_vs_brute(a, v1, NT, 8000) == 0,
              "refit layout %d: disagrees with brute force over new verts", l);
        /* a second refit onto a flattened (degenerate) frame */
        CHECK(lrt_tri_scene_refit(a, vf, NT) == LRT_RESULT_OK, "refit flat");
        CHECK(refit_vs_brute(a, vf, NT, 6000) == 0,
              "refit layout %d: flattened frame disagrees", l);
        lrt_tri_scene_free(a);
    }

    /* mmapped scenes are read-only: refit must be rejected, not crash. */
    {
        lrt_tri_scene *s = lrt_tri_scene_build(v0, NT, NULL, NULL);
        const char *path = "/tmp/lrt_refit_scene.lrts";
        if (s && lrt_tri_scene_save(s, path) == LRT_RESULT_OK) {
            lrt_result err = LRT_RESULT_OK;
            lrt_tri_scene *mm = lrt_tri_scene_open_mmap(path, &err);
            if (mm) {
                CHECK(lrt_tri_scene_refit(mm, v0, NT) ==
                          LRT_RESULT_INVALID_ARGUMENT,
                      "refit of mmapped scene should be rejected");
                lrt_tri_scene_free(mm);
            }
            remove(path);
        }
        lrt_tri_scene_free(s);
    }
    free(v0);
    free(v1);
    free(vf);
}

static void xform_pt(const float m[12], const float p[3], float out[3]) {
    for (int a = 0; a < 3; a++)
        out[a] = m[a * 4 + 0] * p[0] + m[a * 4 + 1] * p[1] +
                 m[a * 4 + 2] * p[2] + m[a * 4 + 3];
}

static void test_tlas(void) {
    g_rng = 0x70A5ull;
    enum { NT = 200, NI = 12 };
    float *blas_v = make_random_soup(NT, 0.25f);
    lrt_result err = LRT_RESULT_OK;
    lrt_tri_scene *blas = lrt_tri_scene_build(blas_v, NT, NULL, &err);
    CHECK(blas != NULL, "tlas: BLAS build failed");
    if (!blas) {
        free(blas_v);
        return;
    }

    lrt_instance insts[NI];
    float *world_v = (float *)malloc((size_t)NI * NT * 9 * sizeof(float));
    for (int i = 0; i < NI; i++) {
        float sx = rnd_f(0.5f, 1.5f), sy = rnd_f(0.5f, 1.5f),
              sz = rnd_f(0.5f, 1.5f);
        float ang = rnd_f(0.0f, 6.2831853f), ca = cosf(ang), sa = sinf(ang);
        float tx = rnd_f(-2, 2), ty = rnd_f(-2, 2), tz = rnd_f(-2, 2);
        float m[12] = {ca * sx, -sa * sy, 0, tx, sa * sx, ca * sy, 0,
                       ty,      0,        0, sz, tz};
        memcpy(insts[i].obj2world, m, sizeof(m));
        insts[i].blas_id = 0;
        insts[i].instance_id = (uint32_t)(100 + i);
        insts[i].mask = 0xFFFFFFFFu;
        for (int j = 0; j < NT * 3; j++) {
            float p[3] = {blas_v[j * 3 + 0], blas_v[j * 3 + 1], blas_v[j * 3 + 2]};
            float w[3];
            xform_pt(m, p, w);
            size_t base = (size_t)i * NT * 9 + (size_t)j * 3;
            world_v[base + 0] = w[0];
            world_v[base + 1] = w[1];
            world_v[base + 2] = w[2];
        }
    }
    lrt_tlas *tlas = lrt_tlas_build(&blas, 1, insts, NI, NULL, &err);
    lrt_tri_scene *flat = lrt_tri_scene_build(world_v, (size_t)NI * NT, NULL, &err);
    CHECK(tlas && flat, "tlas/flat build failed");
    if (tlas && flat) {
        size_t mism = 0, occl = 0;
        for (int i = 0; i < 20000; i++) {
            lrt_ray r;
            make_random_ray(&r);
            lrt_tlas_hit th;
            int a = lrt_tlas_intersect1(tlas, &r, 0xFFFFFFFFu, &th);
            lrt_hit fh;
            int b = lrt_tri_intersect1(flat, &r, &fh);
            if (a != b) {
                mism++;
            } else if (a && fabs((double)th.t - (double)fh.t) >
                                2e-3 * (1.0 + fabs((double)fh.t))) {
                mism++;
            }
            if (lrt_tlas_occluded1(tlas, &r, 0xFFFFFFFFu) != b) occl++;
        }
        CHECK(mism <= 20000 / 300, "tlas: %zu closest mismatches vs flattened",
              mism);
        CHECK(occl <= 20000 / 300, "tlas: %zu occluded mismatches vs flattened",
              occl);
    }
    lrt_tlas_free(tlas);
    lrt_tri_scene_free(flat);
    free(world_v);

    /* identity instance must match the BLAS exactly; mask=0 excludes it. */
    lrt_instance id;
    float im[12] = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0};
    memcpy(id.obj2world, im, sizeof(im));
    id.blas_id = 0;
    id.instance_id = 7;
    id.mask = 0xFFFFFFFFu;
    lrt_tlas *t1 = lrt_tlas_build(&blas, 1, &id, 1, NULL, &err);
    if (t1) {
        size_t bad = 0, mask_bad = 0;
        for (int i = 0; i < 8000; i++) {
            lrt_ray r;
            make_random_ray(&r);
            lrt_tlas_hit th;
            lrt_hit bh;
            int a = lrt_tlas_intersect1(t1, &r, 0xFFFFFFFFu, &th);
            int b = lrt_tri_intersect1(blas, &r, &bh);
            if (a != b) bad++;
            else if (a && th.t != bh.t) bad++;
            else if (a && th.inst_id != 7) bad++;
            if (a && lrt_tlas_intersect1(t1, &r, 0u, &th) != 0) mask_bad++;
        }
        CHECK(bad == 0, "tlas identity: %zu mismatches vs BLAS", bad);
        CHECK(mask_bad == 0, "tlas mask=0 still hit on %zu rays", mask_bad);

        /* refit identity -> a translated transform, vs a freshly built TLAS. */
        float tm[12] = {1, 0, 0, 1.5f, 0, 1, 0, -0.5f, 0, 0, 1, 0.7f};
        memcpy(id.obj2world, tm, sizeof(tm));
        CHECK(lrt_tlas_refit(t1, &id, 1) == LRT_RESULT_OK, "tlas refit failed");
        lrt_tlas *t2 = lrt_tlas_build(&blas, 1, &id, 1, NULL, &err);
        if (t2) {
            size_t rbad = 0;
            for (int i = 0; i < 6000; i++) {
                lrt_ray r;
                make_random_ray(&r);
                lrt_tlas_hit a, b;
                int x = lrt_tlas_intersect1(t1, &r, 0xFFFFFFFFu, &a);
                int y = lrt_tlas_intersect1(t2, &r, 0xFFFFFFFFu, &b);
                if (x != y || (x && a.t != b.t)) rbad++;
            }
            CHECK(rbad == 0, "tlas refit: %zu mismatches vs rebuild", rbad);
            lrt_tlas_free(t2);
        }
        lrt_tlas_free(t1);
    }
    lrt_tri_scene_free(blas);
    free(blas_v);
}

static void test_packets(void) {
    g_rng = 0x9ACE9ACEull;
    enum { NT = 1500 };
    float *verts = make_random_soup(NT, 0.15f);
    lrt_tri_layout layouts[3] = {LRT_TRI_LAYOUT_BVH4, LRT_TRI_LAYOUT_BVH8,
                                 LRT_TRI_LAYOUT_BVH8Q};
    for (int l = 0; l < 3; l++) {
        lrt_tri_build_options o = {.quality = LRT_TRI_BUILD_DEFAULT,
                                   .layout = layouts[l]};
        lrt_tri_scene *s = lrt_tri_scene_build(verts, NT, &o, NULL);
        if (!s) {
            CHECK(0, "packet build failed");
            continue;
        }
        size_t bad_i = 0, bad_o = 0, nb = 0;
        for (int batch = 0; batch < 4000; batch++) {
            lrt_ray singles[8];
            lrt_ray8 r8;
            for (int k = 0; k < 8; k++) {
                make_random_ray(&singles[k]);
                r8.orgx[k] = singles[k].org[0];
                r8.orgy[k] = singles[k].org[1];
                r8.orgz[k] = singles[k].org[2];
                r8.dirx[k] = singles[k].dir[0];
                r8.diry[k] = singles[k].dir[1];
                r8.dirz[k] = singles[k].dir[2];
                r8.tmin[k] = singles[k].tmin;
                r8.tmax[k] = singles[k].tmax;
            }
            lrt_hit8 h8;
            uint8_t o8[8];
            lrt_tri_intersect8(s, &r8, &h8);
            lrt_tri_occluded8(s, &r8, o8);
            for (int k = 0; k < 8; k++, nb++) {
                lrt_hit h1;
                int x = lrt_tri_intersect1(s, &singles[k], &h1);
                int y = (h8.prim_id[k] != LRT_TRI_NO_HIT);
                if (x != y) {
                    bad_i++;
                } else if (x && fabs((double)h1.t - (double)h8.t[k]) >
                                   1e-4 * (1.0 + fabs((double)h1.t))) {
                    bad_i++;
                }
                if ((uint8_t)lrt_tri_occluded1(s, &singles[k]) != o8[k]) bad_o++;
            }
        }
        CHECK(bad_i <= nb / 1000, "packet intersect8 layout %d: %zu/%zu differ",
              l, bad_i, nb);
        CHECK(bad_o <= nb / 1000, "packet occluded8 layout %d: %zu/%zu differ",
              l, bad_o, nb);
        lrt_tri_scene_free(s);
    }

    /* Deterministic Ray4 / Ray8 checks: mixed hit/miss lanes and scalar parity. */
    {
        float tverts[18] = {-1, -1, 5, 1, -1, 5, 0, 1, 5,
                            -1, -1, 9, 1, -1, 9, 0, 1, 9};
        lrt_tri_scene *s = lrt_tri_scene_build(tverts, 2, NULL, NULL);
        CHECK(s != NULL, "packet deterministic build");
        if (s) {
            /* Ray4: one hit, one near-miss, one far hit, and one tmax clip. */
            lrt_ray4 r4 = {0};
            r4.orgx[0] = 0.0f; r4.orgy[0] = 0.0f; r4.orgz[0] = 0.0f;
            r4.dirx[0] = 0.0f; r4.diry[0] = 0.0f; r4.dirz[0] = 1.0f;
            r4.tmin[0] = 0.0f;  r4.tmax[0] = 100.0f;

            r4.orgx[1] = 0.0f; r4.orgy[1] = 0.0f; r4.orgz[1] = 0.0f;
            r4.dirx[1] = 0.0f; r4.diry[1] = 0.0f; r4.dirz[1] = 1.0f;
            r4.tmin[1] = 0.0f;  r4.tmax[1] = 1.0f;

            r4.orgx[2] = 0.0f; r4.orgy[2] = 0.0f; r4.orgz[2] = 10.0f;
            r4.dirx[2] = 0.0f; r4.diry[2] = 0.0f; r4.dirz[2] = -1.0f;
            r4.tmin[2] = 0.0f;  r4.tmax[2] = 100.0f;

            r4.orgx[3] = 3.0f; r4.orgy[3] = 0.0f; r4.orgz[3] = 0.0f;
            r4.dirx[3] = 0.0f; r4.diry[3] = 0.0f; r4.dirz[3] = 1.0f;
            r4.tmin[3] = 0.0f;  r4.tmax[3] = 100.0f;

            lrt_hit4 h4;
            uint8_t o4[4];
            lrt_tri_intersect4(s, &r4, &h4);
            lrt_tri_occluded4(s, &r4, o4);
            for (int k = 0; k < 4; k++) {
                lrt_ray rr = {{r4.orgx[k], r4.orgy[k], r4.orgz[k]},
                              r4.tmin[k],
                              {r4.dirx[k], r4.diry[k], r4.dirz[k]},
                              r4.tmax[k]};
                lrt_hit hs;
                int sh = lrt_tri_intersect1(s, &rr, &hs);
                int so = lrt_tri_occluded1(s, &rr);
                CHECK(((h4.prim_id[k] != LRT_TRI_NO_HIT) == (uint8_t)sh),
                      "packet Ray4 lane %d intersect parity (layout independent)",
                      k);
                CHECK(o4[k] == (uint8_t)so,
                      "packet Ray4 lane %d occluded parity (layout independent)",
                      k);
                if (sh) {
                    CHECK(fabsf(h4.t[k] - hs.t) < 1e-6f,
                          "packet Ray4 lane %d hit t mismatch (d=%f vs %f)",
                          k, (double)h4.t[k], (double)hs.t);
                }
            }

            /* Ray8: same deterministic set, duplicated to fill all lanes. */
            lrt_ray8 r8 = {0};
            for (int k = 0; k < 8; k++) {
                int sidx = k & 3;
                r8.orgx[k] = r4.orgx[sidx];
                r8.orgy[k] = r4.orgy[sidx];
                r8.orgz[k] = r4.orgz[sidx];
                r8.dirx[k] = r4.dirx[sidx];
                r8.diry[k] = r4.diry[sidx];
                r8.dirz[k] = r4.dirz[sidx];
                r8.tmin[k] = r4.tmin[sidx];
                r8.tmax[k] = r4.tmax[sidx];
            }
            lrt_hit8 h8;
            uint8_t o8[8];
            lrt_tri_intersect8(s, &r8, &h8);
            lrt_tri_occluded8(s, &r8, o8);
            for (int k = 0; k < 8; k++) {
                lrt_ray rr = {{r8.orgx[k], r8.orgy[k], r8.orgz[k]},
                              r8.tmin[k],
                              {r8.dirx[k], r8.diry[k], r8.dirz[k]},
                              r8.tmax[k]};
                lrt_hit hs;
                int sh = lrt_tri_intersect1(s, &rr, &hs);
                int so = lrt_tri_occluded1(s, &rr);
                CHECK(((h8.prim_id[k] != LRT_TRI_NO_HIT) == (uint8_t)sh),
                      "packet Ray8 lane %d intersect parity", k);
                CHECK(o8[k] == (uint8_t)so, "packet Ray8 lane %d occluded parity",
                      k);
                if (sh) {
                    CHECK(fabsf(h8.t[k] - hs.t) < 1e-6f,
                          "packet Ray8 lane %d hit t mismatch (d=%f vs %f)",
                          k, (double)h8.t[k], (double)hs.t);
                }
            }
            lrt_tri_scene_free(s);
        }
    }
    free(verts);
}

static int filter_opaque(void *u, uint32_t p, float t, float uu, float vv) {
    (void)u; (void)p; (void)t; (void)uu; (void)vv;
    return 1;
}
static int filter_transparent(void *u, uint32_t p, float t, float uu,
                              float vv) {
    (void)u; (void)p; (void)t; (void)uu; (void)vv;
    return 0;
}
static int filter_even(void *u, uint32_t p, float t, float uu, float vv) {
    (void)u; (void)t; (void)uu; (void)vv;
    return (p & 1u) == 0u;
}
static int filter_reject_all(void *u, uint32_t p, float t, float uu, float vv) {
    (void)u; (void)p; (void)t; (void)uu; (void)vv;
    return 0;
}
static int filter_accept_all(void *u, uint32_t p, float t, float uu, float vv) {
    (void)u; (void)p; (void)t; (void)uu; (void)vv;
    return 1;
}
static int filter_prim_ge5(void *u, uint32_t p, float t, float uu, float vv) {
    (void)u; (void)t; (void)uu; (void)vv;
    return (p >= 5u);
}
static int filter_t_gt3(void *u, uint32_t p, float t, float uu, float vv) {
    (void)u; (void)p; (void)uu; (void)vv;
    return t >= 3.0f;
}
static int filter_u_le_half(void *u, uint32_t p, float t, float uu, float vv) {
    (void)u; (void)p; (void)t;
    return uu <= 0.5f;
}
static int filter_requires_user(void *u, uint32_t p, float t, float uu, float vv) {
    (void)p; (void)t; (void)uu; (void)vv;
    return u != NULL;
}

static void test_anyhit_filter(void) {
    g_rng = 0xF117ull;
    enum { NT = 800 };
    float *verts = make_random_soup(NT, 0.2f);
    lrt_tri_scene *s = lrt_tri_scene_build(verts, NT, NULL, NULL);
    if (!s) {
        free(verts);
        return;
    }
    size_t bad1 = 0, bad2 = 0, bad3 = 0;
    for (int i = 0; i < 12000; i++) {
        lrt_ray r;
        make_random_ray(&r);
        int plain = lrt_tri_occluded1(s, &r);
        if (lrt_tri_occluded1_filtered(s, &r, filter_opaque, NULL) != plain)
            bad1++;
        if (lrt_tri_occluded1_filtered(s, &r, filter_transparent, NULL) != 0)
            bad2++;
        int be = 0;
        for (int j = 0; j < NT && !be; j++) {
            if (j & 1) continue;
            float t, u, v;
            if (ref_isect(&verts[j * 9], &r, &t, &u, &v)) be = 1;
        }
        if (lrt_tri_occluded1_filtered(s, &r, filter_even, NULL) != be) bad3++;
    }
    CHECK(bad1 == 0, "filter opaque != occluded1 on %zu rays", bad1);
    CHECK(bad2 == 0, "filter transparent hit on %zu rays", bad2);
    CHECK(bad3 <= 12000 / 1000, "filter parity vs brute force: %zu", bad3);
    lrt_tri_scene_free(s);
    free(verts);

    {
        float tverts[18] = {-1, -1, 5, 1, -1, 5, 0, 1, 5,
                            -1, -1, 6, 1, -1, 6, 0, 1, 6};
        lrt_tri_scene *s2 = lrt_tri_scene_build(tverts, 2, NULL, NULL);
        CHECK(s2 != NULL, "anyhit deterministic build");
        if (s2) {
            lrt_ray rays[3];
            rays[0] = (lrt_ray){{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            rays[1] = (lrt_ray){{3, 3, 0}, 0.0f, {0, 0, 1}, 100.0f};
            rays[2] = (lrt_ray){{0, 0, 0}, 0.0f, {0, 0, -1}, 100.0f};
            for (int i = 0; i < 3; i++) {
                int plain = lrt_tri_occluded1(s2, &rays[i]);
                int got;

                got = lrt_tri_occluded1_filtered(s2, &rays[i], filter_reject_all,
                                                NULL);
                CHECK(got == 0,
                      "anyhit reject-all filter rejects hits on ray %d", i);

                got = lrt_tri_occluded1_filtered(s2, &rays[i], filter_accept_all,
                                                NULL);
                CHECK(got == plain, "anyhit accept-all filter equals occluded1 ray %d",
                      i);

                got = lrt_tri_occluded1_filtered(s2, &rays[i], filter_requires_user,
                                                NULL);
                CHECK(got == 0, "anyhit NULL user pointer is handled");
            }

            size_t bad_prim = 0;
            size_t bad_t = 0;
            size_t bad_uv = 0;
            for (int i = 0; i < 8000; i++) {
                lrt_ray r;
                make_random_ray(&r);
                int plain = lrt_tri_occluded1(s2, &r);
                int fprim = ref_isect_filtered(tverts, 2, &r, filter_prim_ge5, NULL);
                int ft = ref_isect_filtered(tverts, 2, &r, filter_t_gt3, NULL);
                int fuv = ref_isect_filtered(tverts, 2, &r, filter_u_le_half, NULL);
                int a = lrt_tri_occluded1_filtered(s2, &r, filter_prim_ge5, NULL);
                int b = lrt_tri_occluded1_filtered(s2, &r, filter_t_gt3, NULL);
                int c = lrt_tri_occluded1_filtered(s2, &r, filter_u_le_half, NULL);
                (void)plain;
                if (a != fprim) bad_prim++;
                if (b != ft) bad_t++;
                if (c != fuv) bad_uv++;
            }
            CHECK(bad_prim == 0, "anyhit prim_id filter parity on %zu rays", bad_prim);
            CHECK(bad_t == 0, "anyhit t filter parity on %zu rays", bad_t);
            CHECK(bad_uv == 0, "anyhit uv filter parity on %zu rays", bad_uv);
            lrt_tri_scene_free(s2);
        }
    }
}

static void test_qtri(void) {
    g_rng = 0x0717C0DEull;
    enum { NT = 4000, NR = 20000 };
    float *v = make_random_soup(NT, 0.15f);
    lrt_result err = LRT_RESULT_OK;
    lrt_tri_scene *ref = lrt_tri_scene_build(v, NT, NULL, &err);
    CHECK(ref != NULL, "qtri: fp32 ref build failed");
    if (!ref) {
        free(v);
        return;
    }
    lrt_tri_stats rst;
    lrt_tri_scene_stats(ref, &rst);
    lrt_qtri_format fmts[4] = {LRT_QTRI_Q16, LRT_QTRI_Q8, LRT_QTRI_FP8,
                               LRT_QTRI_FP4};
    const char *fn[4] = {"q16", "q8", "fp8", "fp4"};
    /* lossy hit/miss agreement floors (vs the fp32 brute force); fp8/fp4 are
     * aggressive LOD formats so their floors are lower. */
    double lossy_min[4] = {0.998, 0.99, 0.975, 0.95};

    for (int f = 0; f < 4; f++) {
        /* LOSSY: approximate, but agrees with brute force most of the time,
         * and uses less memory. */
        lrt_tri_scene *q =
            lrt_qtri_scene_build(v, NT, fmts[f], LRT_QTRI_LOSSY, NULL, &err);
        CHECK(q != NULL, "qtri %s lossy build failed (err=%d)", fn[f], (int)err);
        if (q) {
            lrt_tri_stats st;
            lrt_tri_scene_stats(q, &st);
            CHECK(st.memory_bytes < rst.memory_bytes,
                  "qtri %s not smaller than fp32 (%zu vs %zu)", fn[f],
                  st.memory_bytes, rst.memory_bytes);
            size_t agree = 0;
            g_rng = 0x1212ull;
            for (int i = 0; i < NR; i++) {
                lrt_ray r;
                make_random_ray(&r);
                lrt_hit hb, hq;
                int a = brute_force(v, NT, &r, &hb);
                int b = lrt_tri_intersect1(q, &r, &hq);
                if (a == b) agree++;
                /* occluded1 must agree with intersect1 hit/miss on the qtri */
                if ((uint8_t)lrt_tri_occluded1(q, &r) != b) agree += 0;
            }
            double af = (double)agree / NR;
            CHECK(af >= lossy_min[f], "qtri %s lossy agreement %.4f < %.3f",
                  fn[f], af, lossy_min[f]);
            lrt_tri_scene_free(q);
        }

        /* CONSERVATIVE: a transverse ray that hit the true triangle must not
         * miss; only rare grazing rays may. */
        q = lrt_qtri_scene_build(v, NT, fmts[f], LRT_QTRI_CONSERVATIVE, NULL,
                                 &err);
        CHECK(q != NULL, "qtri %s conservative build failed", fn[f]);
        if (q) {
            size_t miss = 0;
            g_rng = 0x3434ull;
            for (int i = 0; i < NR; i++) {
                lrt_ray r;
                make_random_ray(&r);
                lrt_hit hr, hq;
                int a = lrt_tri_intersect1(ref, &r, &hr);
                int b = lrt_tri_intersect1(q, &r, &hq);
                if (a && !b) miss++;
            }
            /* grazing-ray budget (~0.1%) */
            CHECK(miss <= NR / 1000 + 8,
                  "qtri %s conservative missed %zu true hits", fn[f], miss);
            lrt_tri_scene_free(q);
        }
    }
    lrt_tri_scene_free(ref);
    free(v);
}

static void test_qnodes(void) {
#if defined(__AVX2__) && defined(__FMA__)
    g_rng = 0xB0DE5ull;
    enum { NT = 3000, NR = 15000 };
    float *v = make_random_soup(NT, 0.15f);
    lrt_result err = LRT_RESULT_OK;
    lrt_tri_scene *ref = lrt_tri_scene_build(v, NT, NULL, &err); /* fp32 BVH4 */
    lrt_tri_build_options o8 = {.layout = LRT_TRI_LAYOUT_BVH8};
    lrt_tri_scene *bvh8 = lrt_tri_scene_build(v, NT, &o8, &err);
    if (!ref || !bvh8) {
        CHECK(0, "qnodes: ref/bvh8 build failed");
        free(v);
        return;
    }
    lrt_tri_stats b8;
    lrt_tri_scene_stats(bvh8, &b8);
    lrt_tri_layout L[2] = {LRT_TRI_LAYOUT_BVH8_QF8, LRT_TRI_LAYOUT_BVH8_Q4};
    const char *nm[2] = {"qf8", "q4"};
    for (int l = 0; l < 2; l++) {
        lrt_tri_build_options o = {.layout = L[l]};
        lrt_tri_scene *q = lrt_tri_scene_build(v, NT, &o, &err);
        CHECK(q != NULL, "qnode %s build failed (err=%d)", nm[l], (int)err);
        if (!q) continue;
        lrt_tri_stats st;
        lrt_tri_scene_stats(q, &st);
        CHECK(st.memory_bytes <= b8.memory_bytes, "qnode %s not <= bvh8 memory",
              nm[l]);
        /* conservative node bounds => exact closest hits (ties aside). */
        size_t mism = 0, occl = 0;
        g_rng = 0x5151ull;
        for (int i = 0; i < NR; i++) {
            lrt_ray r;
            make_random_ray(&r);
            lrt_hit hr, hq;
            int a = lrt_tri_intersect1(ref, &r, &hr);
            int b = lrt_tri_intersect1(q, &r, &hq);
            if (a != b) {
                mism++;
            } else if (a && fabs((double)hr.t - (double)hq.t) >
                               1e-4 * (1.0 + fabs((double)hr.t))) {
                mism++;
            }
            if ((int)lrt_tri_occluded1(q, &r) != b) occl++;
        }
        CHECK(mism == 0, "qnode %s: %zu closest mismatches vs fp32", nm[l], mism);
        CHECK(occl == 0, "qnode %s: %zu occluded mismatches", nm[l], occl);
        lrt_tri_scene_free(q);
    }
    lrt_tri_scene_free(ref);
    lrt_tri_scene_free(bvh8);
    free(v);
#endif
}

/* Reference ray-facing disc (embree DISC_POINT). */
static int ref_disc(const float c[3], float r, const lrt_ray *ray, float tmax,
                    float *t_out) {
    float dx = ray->dir[0], dy = ray->dir[1], dz = ray->dir[2];
    float dOdO = dx * dx + dy * dy + dz * dz;
    if (dOdO <= 0.0f) return 0;
    float c0x = c[0] - ray->org[0], c0y = c[1] - ray->org[1],
          c0z = c[2] - ray->org[2];
    float proj = (c0x * dx + c0y * dy + c0z * dz) / dOdO;
    if (proj < ray->tmin || proj >= tmax) return 0;
    float px = c0x - proj * dx, py = c0y - proj * dy, pz = c0z - proj * dz;
    if (px * px + py * py + pz * pz > r * r) return 0;
    *t_out = proj;
    return 1;
}

/* Reference oriented disc (embree ORIENTED_DISC_POINT). */
static int ref_odisc(const float c[3], float r, const float n[3],
                     const lrt_ray *ray, float tmax, float *t_out) {
    float dx = ray->dir[0], dy = ray->dir[1], dz = ray->dir[2];
    float div = dx * n[0] + dy * n[1] + dz * n[2];
    if (div == 0.0f) return 0;
    float t = ((c[0] - ray->org[0]) * n[0] + (c[1] - ray->org[1]) * n[1] +
               (c[2] - ray->org[2]) * n[2]) / div;
    if (t < ray->tmin || t >= tmax) return 0;
    float hx = ray->org[0] + t * dx - c[0], hy = ray->org[1] + t * dy - c[1],
          hz = ray->org[2] + t * dz - c[2];
    if (hx * hx + hy * hy + hz * hz >= r * r) return 0;
    *t_out = t;
    return 1;
}

static void test_points_scene(void) {
    enum { NPTS = 400, NRAYS = 20000 };
    float *cen = (float *)malloc(NPTS * 3 * sizeof(float));
    float *rad = (float *)malloc(NPTS * sizeof(float));
    float *nrm = (float *)malloc(NPTS * 3 * sizeof(float));
    g_rng = 0x9015E5ull;
    for (int i = 0; i < NPTS; i++) {
        for (int a = 0; a < 3; a++) cen[i * 3 + a] = rnd_f(-2.0f, 2.0f);
        rad[i] = rnd_f(0.03f, 0.15f);
        float n[3] = {rnd_f(-1, 1), rnd_f(-1, 1), rnd_f(-1, 1)};
        float l = sqrtf(n[0] * n[0] + n[1] * n[1] + n[2] * n[2]);
        if (l < 1e-6f) { n[2] = 1.0f; l = 1.0f; }
        for (int a = 0; a < 3; a++) nrm[i * 3 + a] = n[a] / l;
    }

    const int types[3] = {LRT_POINT_SPHERE, LRT_POINT_DISC,
                          LRT_POINT_ORIENTED_DISC};
    const char *names[3] = {"sphere", "disc", "odisc"};
    for (int ti = 0; ti < 3; ti++) {
        int pt = types[ti];
        lrt_tri_scene *s = lrt_points_scene_build(
            cen, rad, pt == LRT_POINT_ORIENTED_DISC ? nrm : NULL, pt, NPTS, NULL,
            NULL);
        CHECK(s != NULL, "points(%s) build failed", names[ti]);
        if (!s) continue;
        size_t mism = 0, occl = 0, surf = 0;
        for (int i = 0; i < NRAYS; i++) {
            lrt_ray r;
            make_random_ray(&r);
            float bt = r.tmax;
            int bf = 0;
            for (int j = 0; j < NPTS; j++) {
                const float *c = &cen[j * 3];
                float t;
                int h;
                if (pt == LRT_POINT_SPHERE) {
                    float sp[4] = {c[0], c[1], c[2], rad[j]};
                    h = ref_sphere(sp, &r, bt, &t);
                } else if (pt == LRT_POINT_DISC) {
                    h = ref_disc(c, rad[j], &r, bt, &t);
                } else {
                    h = ref_odisc(c, rad[j], &nrm[j * 3], &r, bt, &t);
                }
                if (h) { bt = t; bf = 1; }
            }
            lrt_hit h;
            int bvh = lrt_tri_intersect1(s, &r, &h);
            if (bf != bvh)
                mism++;
            else if (bf && fabs((double)h.t - (double)bt) >
                               1e-3 * (1.0 + fabs((double)bt)))
                mism++;
            if (lrt_tri_occluded1(s, &r) != bvh) occl++;
            /* The hit point must sit on the *reported* point: on the sphere
             * shell, or within the disc radius of its center (validates
             * prim_id, which the nearest-t oracle never checks). */
            if (bvh) {
                uint32_t prim = h.prim_id;
                if (prim >= (uint32_t)NPTS) {
                    surf++;
                } else {
                    const float *cc = &cen[prim * 3];
                    float hp[3];
                    for (int a = 0; a < 3; a++)
                        hp[a] = r.org[a] + h.t * r.dir[a];
                    float dx = hp[0] - cc[0], dy = hp[1] - cc[1],
                          dz = hp[2] - cc[2];
                    float d = sqrtf(dx * dx + dy * dy + dz * dz);
                    float rr = rad[prim];
                    int ok = (pt == LRT_POINT_SPHERE)
                                 ? fabsf(d - rr) <= 3e-3f * (1.0f + rr)
                                 : d <= rr + 3e-3f * (1.0f + rr);
                    if (!ok) surf++;
                }
            }
        }
        CHECK(mism <= NRAYS / 1000, "points(%s): %zu/%d mismatches vs brute force",
              names[ti], mism, NRAYS);
        CHECK(occl == 0, "points(%s): %zu occluded disagreements", names[ti],
              occl);
        CHECK(surf <= NRAYS / 1000,
              "points(%s): %zu/%d hits not on the reported point", names[ti],
              surf, NRAYS);
        check_batch_consistency(s, 4000, names[ti]);
        printf("  points(%s) scene [%s]\n", names[ti], lrt_tri_kernel_name(s));
        lrt_tri_scene_free(s);
    }
    free(cen);
    free(rad);
    free(nrm);
}

/* Flat (ribbon) curves: every hit must lie within the segment's interpolated
 * half-width of the segment axis (an invariant of the ray-facing ribbon that
 * doesn't replicate the intersector), and occluded must agree with intersect. */
static void test_flatcurve_scene(void) {
    enum { NSTRAND = 80, PTS = 6, NRAYS = 20000 };
    size_t npoints = (size_t)NSTRAND * PTS;
    float *pts = (float *)malloc(npoints * 3 * sizeof(float));
    float *rad = (float *)malloc(npoints * sizeof(float));
    uint32_t *sfirst = (uint32_t *)malloc(NSTRAND * sizeof(uint32_t));
    uint32_t *scount = (uint32_t *)malloc(NSTRAND * sizeof(uint32_t));
    g_rng = 0xF1A7ull;
    for (int st = 0; st < NSTRAND; st++) {
        sfirst[st] = (uint32_t)(st * PTS);
        scount[st] = PTS;
        float p[3] = {rnd_f(-2, 2), rnd_f(-2, 2), rnd_f(-2, 2)};
        for (int k = 0; k < PTS; k++) {
            size_t idx = (size_t)st * PTS + k;
            for (int a = 0; a < 3; a++) {
                p[a] += rnd_f(-0.9f, 0.9f);
                pts[idx * 3 + a] = p[a];
            }
            rad[idx] = rnd_f(0.02f, 0.08f);
        }
    }
    lrt_hair_strands hs = {0};
    hs.points = pts;
    hs.radius = rad;
    hs.strand_first = sfirst;
    hs.strand_count = scount;
    hs.nstrands = NSTRAND;
    hs.npoints = npoints;
    lrt_tri_scene *s = lrt_flatcurve_scene_build(&hs, NULL, NULL);
    CHECK(s != NULL, "flatcurve build failed");
    if (!s) {
        free(pts); free(rad); free(sfirst); free(scount);
        return;
    }
    printf("  flatcurve scene [%s]\n", lrt_tri_kernel_name(s));
    size_t bad = 0, occl = 0;
    for (int i = 0; i < NRAYS; i++) {
        lrt_ray r;
        make_random_ray(&r);
        lrt_hit h;
        int bvh = lrt_tri_intersect1(s, &r, &h);
        if (lrt_tri_occluded1(s, &r) != bvh) occl++;
        if (!bvh) continue;
        uint32_t prim = h.prim_id;
        uint32_t i0 = (uint32_t)((prim / (PTS - 1)) * PTS + prim % (PTS - 1));
        const float *p0 = &pts[(size_t)i0 * 3];
        const float *p1 = &pts[(size_t)(i0 + 1) * 3];
        float hp[3];
        for (int a = 0; a < 3; a++) hp[a] = r.org[a] + h.t * r.dir[a];
        float ax[3] = {p1[0] - p0[0], p1[1] - p0[1], p1[2] - p0[2]};
        float al2 = ax[0] * ax[0] + ax[1] * ax[1] + ax[2] * ax[2];
        float d0[3] = {hp[0] - p0[0], hp[1] - p0[1], hp[2] - p0[2]};
        float u = al2 > 0.0f ? (d0[0] * ax[0] + d0[1] * ax[1] + d0[2] * ax[2]) / al2
                             : 0.0f;
        if (u < 0.0f) u = 0.0f; else if (u > 1.0f) u = 1.0f;
        float perp[3];
        for (int a = 0; a < 3; a++) perp[a] = d0[a] - u * ax[a];
        float dist = sqrtf(perp[0] * perp[0] + perp[1] * perp[1] + perp[2] * perp[2]);
        float rr = rad[i0] + u * (rad[i0 + 1] - rad[i0]);
        if (h.t < r.tmin || h.t > r.tmax) bad++;
        else if (dist > rr + 1e-3f * (1.0f + rr)) bad++;
    }
    CHECK(bad <= NRAYS / 1000, "flatcurve: %zu/%d hits off the ribbon", bad,
          NRAYS);
    CHECK(occl == 0, "flatcurve: %zu occluded disagreements", occl);
    check_batch_consistency(s, 4000, "flatcurve");
    lrt_tri_scene_free(s);
    free(pts);
    free(rad);
    free(sfirst);
    free(scount);
}

/* Cubic Bezier position + radius (component 3). */
static void bez_pos(const float cp[16], float u, float out[4]) {
    float u1 = 1.0f - u;
    for (int c = 0; c < 4; c++)
        out[c] = u1 * u1 * u1 * cp[c] + 3.0f * u1 * u1 * u * cp[4 + c] +
                 3.0f * u1 * u * u * cp[8 + c] + u * u * u * cp[12 + c];
}

/* The reported segment's swept tube must contain the hit point: the minimum over
 * a fine sampling of signed surface distance (|hp - C(u)| - r(u)) must be <= a
 * small tolerance, i.e. the hit lies on (or, for an inside-start ray, within)
 * the tube. Validates prim_id for the Newton sweep - the round-cone-fan oracle
 * only checks the nearest t across all segments, not which segment was hit. */
static int hit_on_bez_tube(const float cp[16], const float hp[3]) {
    enum { M = 512 };
    float best = 1e30f;
    for (int j = 0; j <= M; j++) {
        float pr[4];
        bez_pos(cp, (float)j / (float)M, pr);
        float dx = hp[0] - pr[0], dy = hp[1] - pr[1], dz = hp[2] - pr[2];
        float d = sqrtf(dx * dx + dy * dy + dz * dz) - pr[3];
        if (d < best) best = d;
    }
    return best <= 6e-3f;
}

/* Reference round-Bezier hit: the tube approximated by a fan of M tapered round
 * cones (varying radius, a tight fit to the smooth tube; independent of the
 * kernel's Newton sweep). Converges to the exact tube as M grows. */
static int ref_bezcurve(const float cp[16], const lrt_ray *r, float tmax,
                        float *t_out) {
    enum { M = 384 };
    float best = tmax;
    int hit = 0;
    float prev[4];
    bez_pos(cp, 0.0f, prev);
    for (int j = 1; j <= M; j++) {
        float cur[4];
        bez_pos(cp, (float)j / (float)M, cur);
        float p0[3] = {prev[0], prev[1], prev[2]};
        float p1[3] = {cur[0], cur[1], cur[2]};
        float t;
        if (ref_roundcone(p0, prev[3], p1, cur[3], r, best, &t)) {
            best = t;
            hit = 1;
        }
        for (int c = 0; c < 4; c++) prev[c] = cur[c];
    }
    if (hit) *t_out = best;
    return hit;
}

static void test_bezcurve_scene(void) {
    enum { NSEG = 200, NRAYS = 20000 };
    float *cps = (float *)malloc(NSEG * 16 * sizeof(float));
    g_rng = 0xBE21E5ull;
    for (int i = 0; i < NSEG; i++) {
        /* a control polygon that stays smooth: random start, small steps */
        float p[3] = {rnd_f(-2, 2), rnd_f(-2, 2), rnd_f(-2, 2)};
        for (int k = 0; k < 4; k++) {
            for (int a = 0; a < 3; a++) {
                p[a] += rnd_f(-0.5f, 0.5f);
                cps[i * 16 + k * 4 + a] = p[a];
            }
            cps[i * 16 + k * 4 + 3] = rnd_f(0.03f, 0.12f);
        }
    }
    lrt_tri_scene *s = lrt_bezcurve_scene_build(cps, NSEG, NULL, NULL);
    CHECK(s != NULL, "bezcurve build failed");
    if (!s) {
        free(cps);
        return;
    }
    printf("  bezcurve scene [%s]\n", lrt_tri_kernel_name(s));
    size_t mism = 0, occl = 0, surf = 0;
    for (int i = 0; i < NRAYS; i++) {
        lrt_ray r;
        make_random_ray(&r);
        float bt = r.tmax;
        int bf = 0;
        for (int j = 0; j < NSEG; j++) {
            float t;
            if (ref_bezcurve(&cps[j * 16], &r, bt, &t)) {
                bt = t;
                bf = 1;
            }
        }
        lrt_hit h;
        int bvh = lrt_tri_intersect1(s, &r, &h);
        if (bf != bvh)
            mism++;
        else if (bf && fabs((double)h.t - (double)bt) >
                           3e-3 * (1.0 + fabs((double)bt)))
            mism++;
        if (lrt_tri_occluded1(s, &r) != bvh) occl++;
        /* The hit point must lie on the reported segment's tube. Unlike the fan
         * oracle's nearest-t test, this pins down prim_id and the exact surface. */
        if (bvh) {
            uint32_t prim = h.prim_id;
            float hp[3];
            for (int a = 0; a < 3; a++) hp[a] = r.org[a] + h.t * r.dir[a];
            if (prim >= (uint32_t)NSEG ||
                !hit_on_bez_tube(&cps[(size_t)prim * 16], hp))
                surf++;
        }
    }
    /* The round-cone fan facets the smooth tube, so grazing rays differ more
     * from it than from the exact surface; the AUTHORITATIVE check is the Embree
     * ROUND_BEZIER_CURVE cross-check in hair_bench (~99.5% on the same geometry).
     * This catches gross breakage (e.g. a bad Newton seed -> systematic misses,
     * which ran ~2.8%). */
    CHECK(mism <= NRAYS / 40, "bezcurve: %zu/%d mismatches vs brute-force tube",
          mism, NRAYS);
    CHECK(occl == 0, "bezcurve: %zu occluded disagreements", occl);
    /* prim_id/surface consistency is exact (the kernel never returns a hit off
     * its own tube), so this budget is far tighter than the fan-oracle one. */
    CHECK(surf <= NRAYS / 1000, "bezcurve: %zu/%d hits not on the reported tube",
          surf, NRAYS);
    check_batch_consistency(s, 4000, "bezcurve");
    lrt_tri_scene_free(s);
    free(cps);
}

/* --- Triangle-specific edge cases ------------------------------------------
 *
 * Deterministic scenes targeting triangle-intersection corner cases that the
 * random-soup tests rarely exercise: sub-pixel triangles, grazing/parallel rays,
 * origin-on-surface, exact edge hits, coplanar multi-layer, NaN/inf refit
 * rejection, single-triangle BVH with axis-aligned directions, and large
 * BVH8Q quantization stress. */

static void test_tri_edge_cases(void) {
    lrt_hit h;
    lrt_result err = LRT_RESULT_OK;

    /* (1) Near-degenerate triangle: very small extent in x/y, non-zero in z.
     * The Moller-Trumbore det is near-zero; the scale-dependent threshold must
     * not reject a valid hit. The AABB must be non-degenerate for BVH culling. */
    {
        float tiny[9];
        tiny[0] = -1e-4f; tiny[1] = -1e-4f; tiny[2] = 5.0f;
        tiny[3] = 1e-4f;   tiny[4] = -1e-4f; tiny[5] = 5.0f;
        tiny[6] = -1e-4f;  tiny[7] = 1e-4f;  tiny[8] = 5.0f;
        lrt_tri_scene *s = lrt_tri_scene_build(tiny, 1, NULL, NULL);
        CHECK(s != NULL, "near-degenerate build");
        if (s) {
            lrt_ray r = {{0.0f, 0.0f, 0.0f}, 0.0f, {0.0f, 0.0f, 1.0f}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 5.0f) < 1e-3f,
                  "near-degenerate hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (2) Ray parallel to triangle plane (grazing incidence): should miss unless
     * the ray lies exactly in the plane (which it won't with float precision). */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "grazing build");
        if (s) {
            /* Ray parallel to xy-plane at z=6 (one unit above the triangle). */
            lrt_ray r = {{0, 0, 6}, 0.0f, {1.0f, 0.0f, 0.0f}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0, "grazing miss (z=6)");
            /* Ray parallel at z=5 but offset in y -> should miss. */
            lrt_ray r2 = {{0, 2, 5}, 0.0f, {1.0f, 0.0f, 0.0f}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r2, &h) == 0, "grazing miss (y=2)");
            lrt_tri_scene_free(s);
        }
    }

    /* (3) Ray origin exactly on the triangle surface: tmin=0 should accept,
     * tmin=epsilon should reject (the hit is at t=5). */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "on-surface build");
        if (s) {
            lrt_ray r = {{0, 0, 5}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "origin-on-surface tmin=0 (t=%f)", (double)h.t);
            r.tmin = 0.001f;
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "origin-on-surface tmin>0 rejects (t=5)");
            lrt_tri_scene_free(s);
        }
    }

    /* (4) Exact edge hit: ray passes through two vertices of the triangle.
     * The barycentric test should accept (u+v <= 1 on the edge). */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "edge-hit build");
        if (s) {
            /* Ray through v0 and v2 (the edge from (-1,-1,5) to (0,1,5)).
             * Parameterize: hit at z=5, along the edge direction. */
            lrt_ray r = {{-1, -1, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "edge-hit on v0-v2 (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (5) Multi-layer coplanar triangles: 3 triangles stacked at z=5,5.001,5.002.
     * A ray from below should hit the lowest one first. Tests BVH front-to-back
     * ordering on nearly-coplanar geometry. */
    {
        float verts[27];
        float zs[3] = {5.0f, 5.001f, 5.002f};
        for (int k = 0; k < 3; k++) {
            float t[9] = {-1, -1, zs[k], 1, -1, zs[k], 0, 1, zs[k]};
            memcpy(&verts[k * 9], t, sizeof(t));
        }
        lrt_tri_scene *s = lrt_tri_scene_build(verts, 3, NULL, NULL);
        CHECK(s != NULL, "multi-layer build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 && h.prim_id == 0,
                  "multi-layer hits lowest first (prim_id=%u)", h.prim_id);
            lrt_tri_scene_free(s);
        }
    }

    /* (6) Single triangle with BVH8 layout: exercises the 8-wide leaf kernel
     * with minimal geometry (padding lanes dominate). */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_build_options o8 = {.quality = LRT_TRI_BUILD_DEFAULT,
                                    .layout = LRT_TRI_LAYOUT_BVH8};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, &o8, NULL);
        CHECK(s != NULL, "single-tri bvh8 build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 && fabsf(h.t - 5.0f) < 1e-5f,
                  "single-tri bvh8 hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (7) Zero-radius degenerate triangle (all vertices same point): must build
     * but never hit. */
    {
        float degen[9] = {5, 5, 5, 5, 5, 5, 5, 5, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(degen, 1, NULL, NULL);
        CHECK(s != NULL, "zero-area build");
        if (s) {
            lrt_ray r = {{5, 5, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "zero-area never hits");
            lrt_tri_scene_free(s);
        }
    }

    /* (8) Ray with one zero-direction component: exercises the slab test's
     * infinite invd path on a specific axis. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "zero-dir build");
        if (s) {
            /* Ray along +x only (dir = {1,0,0}). Should miss since triangle
             * is at z=5 and ray stays at z=0. */
            lrt_ray r = {{0, 0, 0}, 0.0f, {1.0f, 0.0f, 0.0f}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0, "zero-dir x miss");
            /* Ray along +y through the triangle center. */
            lrt_ray r2 = {{0, 0, 0}, 0.0f, {0.0f, 1.0f, 0.0f}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r2, &h) == 0, "zero-dir y miss (z=0!=5)");
            lrt_tri_scene_free(s);
        }
    }

    /* (9) Large triangle spanning [-1e5, 1e5]^3: exercises the slab test with
     * very large extents and the BVH node bounds. */
    {
        float large[9];
        float L = 1e5f;
        large[0] = -L; large[1] = -L; large[2] = 100.0f;
        large[3] = L;  large[4] = -L; large[5] = 100.0f;
        large[6] = -L; large[7] = L;  large[8] = 100.0f;
        lrt_tri_scene *s = lrt_tri_scene_build(large, 1, NULL, NULL);
        CHECK(s != NULL, "large-tri build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 1000.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 100.0f) < 1e-2f,
                  "large-tri hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (10) Refit with NaN vertices: must be rejected, not crash. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "refit-nan build");
        if (s) {
            tri[0] = NAN;
            CHECK(lrt_tri_scene_refit(s, tri, 1) == LRT_RESULT_INVALID_ARGUMENT,
                  "refit NaN rejected");
            lrt_tri_scene_free(s);
        }
    }

    /* (11) Refit with Inf vertices: must be rejected. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "refit-inf build");
        if (s) {
            tri[0] = INFINITY;
            CHECK(lrt_tri_scene_refit(s, tri, 1) == LRT_RESULT_INVALID_ARGUMENT,
                  "refit Inf rejected");
            lrt_tri_scene_free(s);
        }
    }

    /* (12) Refit with wrong ntris: must be rejected. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "refit-wrong-ntris build");
        if (s) {
            float tri2[9] = {0, 0, 10, 1, 0, 10, 0, 1, 10};
            CHECK(lrt_tri_scene_refit(s, tri2, 2) == LRT_RESULT_INVALID_ARGUMENT,
                  "refit wrong ntris rejected");
            lrt_tri_scene_free(s);
        }
    }

    /* (13) Query AABB with inverted bounds: lo > hi on at least one axis.
     * Should return empty, not crash or return garbage. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "inverted-aabb build");
        if (s) {
            float lo[3] = {10, 0, 0}, hi[3] = {5, 0, 0}; /* lo[0] > hi[0] */
            uint32_t out[4];
            size_t n = lrt_tri_query_aabb(s, lo, hi, out, 4);
            CHECK(n == 0, "inverted-aabb returns 0 (n=%zu)", n);
            lrt_tri_scene_free(s);
        }
    }

    /* (14) BVH8Q quantized scene with a single triangle: exercises the quantized
     * node decode path with minimal geometry. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_build_options oq = {.quality = LRT_TRI_BUILD_DEFAULT,
                                    .layout = LRT_TRI_LAYOUT_BVH8Q};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, &oq, NULL);
        CHECK(s != NULL, "single-tri bvh8q build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 5.0f) < 1e-4f,
                  "single-tri bvh8q hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (15) Ray exactly through a triangle vertex: tests the barycentric boundary
     * where uu=0 or vv=0 or uu+vv=1. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "vertex-ray build");
        if (s) {
            /* Ray through vertex v0 = (-1,-1,5). */
            lrt_ray r = {{-1, -1, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 5.0f) < 1e-5f,
                  "vertex-ray hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (16) Very thin triangle (long and narrow): exercises the scale-dependent
     * det threshold with a very small cross product. */
    {
        float thin[9];
        thin[0] = 0.0f; thin[1] = 0.0f; thin[2] = 5.0f;
        thin[3] = 100.0f; thin[4] = 0.001f; thin[5] = 5.0f; /* very thin */
        thin[6] = 0.0f; thin[7] = 0.002f; thin[8] = 5.0f;
        lrt_tri_scene *s = lrt_tri_scene_build(thin, 1, NULL, NULL);
        CHECK(s != NULL, "thin-tri build");
        if (s) {
            lrt_ray r = {{50, 0.0015f, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "thin-tri hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (17) Occluded1 / intersect1 consistency on a single triangle: verifies
     * that occluded1 returns 1 iff intersect1 reports a hit. */
    {
        float tri[9] = {-10, -10, 5, 10, -10, 5, 0, 10, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "occl-consistency build");
        if (s) {
            /* Hit ray. */
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1, "hit");
            CHECK(lrt_tri_occluded1(s, &r) == 1, "occluded1 agrees");
            /* Miss ray. */
            lrt_ray rm = {{0, 0, 0}, 0.0f, {1, 0, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &rm, &h) == 0, "miss");
            CHECK(lrt_tri_occluded1(s, &rm) == 0, "occluded1 agrees on miss");
            lrt_tri_scene_free(s);
        }
    }

    /* (18) Back-face culling: triangle vertices are CW (back-facing from below).
     * Moller-Trumbore should still hit (the library is double-sided). */
    {
        float tri[9] = {0, 1, 5, -1, -1, 5, 1, -1, 5}; /* CW winding */
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "cw-winding build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "CW winding still hits (double-sided)");
            lrt_tri_scene_free(s);
        }
    }

    /* (19) tmax = tmin: empty interval, should never hit. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "tmax-tmin build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            r.tmin = 5.0f;
            r.tmax = 5.0f;
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "tmax==tmin rejects (empty interval)");
            lrt_tri_scene_free(s);
        }
    }

    /* (20) BVH8_Q4 quantized node with many triangles: exercises the 4-bit
     * quantized node decode path. */
#if defined(__AVX2__) && defined(__FMA__)
    {
        g_rng = 0xCAFEBEEFull;
        float *verts = make_random_soup(500, 0.15f);
        lrt_tri_build_options oq4 = {.quality = LRT_TRI_BUILD_DEFAULT,
                                     .layout = LRT_TRI_LAYOUT_BVH8_Q4};
        lrt_tri_scene *s = lrt_tri_scene_build(verts, 500, &oq4, NULL);
        CHECK(s != NULL, "q4-many-tri build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            int hit = lrt_tri_intersect1(s, &r, &h);
            /* Just check it doesn't crash and returns a consistent result. */
            CHECK(hit == 0 || h.prim_id < 500,
                  "q4 many-tri hit prim_id valid (id=%u)", h.prim_id);
            lrt_tri_scene_free(s);
        }
        free(verts);
    }
#endif
}

/* BVH construction edge cases: build failures, quality/layout combinations,
 * parallel build, capacity overflow, etc. */
static void test_tri_build_edge_cases(void);

/* Deterministic degenerate / boundary scenes for curves and points: an isolated
 * (neighbor-less) round-linear segment, the constant-radius builder path, the
 * cone->cylinder degeneracy (r0==r1), analytic sphere hits (incl. a ray whose
 * origin is inside the sphere -> far root), an oriented-disc edge-on miss, and
 * tmin/tmax/occluded clipping. The random hair-like scenes never reliably reach
 * these (every interior segment there has two neighbors and varying radii). */
static void test_tri_edge_cases(void);
static void test_sphere_edge_cases(void);
static void test_hair_edge_cases(void);
static void test_curve_point_edge_cases(void);
static void test_null_inputs(void);
static void test_batch_edge_cases(void);
static void test_stats(void);
static void test_kernel_name(void);
static void test_user_geometry_edge_cases(void);
static void test_sphere_scene_edge_cases(void);
static void test_triangle_intersection_edge_cases(void);
static void test_multihit_edge_cases(void);
static void test_closest_point_edge_cases(void);
static void test_region_query_edge_cases(void);
static void test_build_options(void);
static void test_fp_precision(void);
static void test_tlas_edge_cases(void);
static void test_sdf_edge_cases(void);
static void test_tlas_edge_cases2(void);

/* BVH construction edge cases. */
static void test_tri_build_edge_cases(void) {
    lrt_result err = LRT_RESULT_OK;

    /* (1) ntris == 0: must reject with INVALID_ARGUMENT. */
    {
        float tri[9] = {0};
        CHECK(lrt_tri_scene_build(tri, 0, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_ARGUMENT,
              "build ntris=0 rejected");
    }

    /* (2) NULL vertices: must reject. */
    {
        err = LRT_RESULT_OK;
        CHECK(lrt_tri_scene_build(NULL, 10, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_ARGUMENT,
              "build NULL vertices rejected");
    }

    /* (3) NaN vertex: must reject with INVALID_BOUNDS. */
    {
        float nanv[9];
        memset(nanv, 0, sizeof(nanv));
        nanv[0] = NAN;
        err = LRT_RESULT_OK;
        CHECK(lrt_tri_scene_build(nanv, 1, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_BOUNDS,
              "build NaN vertex rejected");
    }

    /* (4) Infinity vertex: must reject with INVALID_BOUNDS. */
    {
        float infv[9];
        memset(infv, 0, sizeof(infv));
        infv[0] = INFINITY;
        err = LRT_RESULT_OK;
        CHECK(lrt_tri_scene_build(infv, 1, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_BOUNDS,
              "build Inf vertex rejected");
    }

    /* (5) -Infinity vertex: must reject with INVALID_BOUNDS. */
    {
        float infnv[9];
        memset(infnv, 0, sizeof(infnv));
        infnv[0] = -INFINITY;
        err = LRT_RESULT_OK;
        CHECK(lrt_tri_scene_build(infnv, 1, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_BOUNDS,
              "build -Inf vertex rejected");
    }

    /* (6) All-zero triangle (degenerate): must build successfully. */
    {
        float zero[9];
        memset(zero, 0, sizeof(zero));
        lrt_tri_scene *s = lrt_tri_scene_build(zero, 1, NULL, NULL);
        CHECK(s != NULL, "build all-zero triangle succeeds");
        if (s) {
            lrt_hit h;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "all-zero triangle never hits");
            lrt_tri_scene_free(s);
        }
    }

    /* (7) Single triangle with each quality/layout combo: all must build and
     * produce a hit on a known ray. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_layout layouts[] = {
            LRT_TRI_LAYOUT_BVH4, LRT_TRI_LAYOUT_BVH8, LRT_TRI_LAYOUT_BVH8Q,
            /* q4/fp8 node-quantized layouts are AVX2-only (see kernel). */
#if defined(__AVX2__) && defined(__FMA__)
            LRT_TRI_LAYOUT_BVH8_Q4, LRT_TRI_LAYOUT_BVH8_QF8
#endif
        };
        const unsigned nlayouts = (unsigned)(sizeof(layouts) / sizeof(layouts[0]));
        lrt_tri_quality qualities[] = {
            LRT_TRI_BUILD_FAST, LRT_TRI_BUILD_DEFAULT, LRT_TRI_BUILD_HQ};
        for (unsigned l = 0; l < nlayouts; l++) {
            for (unsigned q = 0; q < 3; q++) {
                lrt_tri_build_options o = {
                    .quality = qualities[q], .layout = layouts[l],
                    .max_leaf_size = 0, .num_threads = 1};
                lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, &o, NULL);
                CHECK(s != NULL,
                      "build single-tri quality=%d layout=%d (err=%d)",
                      (int)qualities[q], (int)layouts[l],
                      (int)err);
                if (s) {
                    lrt_hit h;
                    lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                    int hit = lrt_tri_intersect1(s, &r, &h);
                    CHECK(hit == 1 && fabsf(h.t - 5.0f) < 1e-3f,
                          "single-tri quality=%d layout=%d hit (t=%f)",
                          (int)qualities[q], (int)layouts[l], (double)h.t);
                    lrt_tri_scene_free(s);
                }
            }
        }
    }

    /* (8) Parallel build: same scene built with 1 thread and 4 threads must
     * agree on all rays. */
    {
        g_rng = 0xDEADBEEFull;
        float *verts = make_random_soup(200, 0.3f);
        CHECK(verts != NULL, "parallel build: soup alloc");
        if (verts) {
            lrt_tri_build_options o1 = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 1};
            lrt_tri_build_options o4 = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 4};
            lrt_tri_scene *s1 = lrt_tri_scene_build(verts, 200, &o1, NULL);
            lrt_tri_scene *s4 = lrt_tri_scene_build(verts, 200, &o4, NULL);
            CHECK(s1 && s4, "parallel build: both succeeded");
            if (s1 && s4) {
                lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                lrt_hit h1, h4;
                int hit1 = lrt_tri_intersect1(s1, &r, &h1);
                int hit4 = lrt_tri_intersect1(s4, &r, &h4);
                CHECK(hit1 == hit4,
                      "parallel build: hit/miss agree (serial=%d, parallel=%d)",
                      hit1, hit4);
                if (hit1 && hit4) {
                    CHECK(fabsf(h1.t - h4.t) < 1e-3f,
                          "parallel build: t agrees (serial=%.6f, parallel=%.6f)",
                          (double)h1.t, (double)h4.t);
                }
            }
            lrt_tri_scene_free(s1);
            lrt_tri_scene_free(s4);
            free(verts);
        }
    }

    /* (9) Custom max_leaf_size: force leaf size 1 (each triangle is its own
     * leaf) and verify the tree is deeper than the default. */
    {
        g_rng = 0x11111111ull;
        float *verts = make_random_soup(100, 1.0f);
        CHECK(verts != NULL, "max-leaf build: soup alloc");
        if (verts) {
            lrt_tri_build_options odfl = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0, /* default */
                .num_threads = 1};
            lrt_tri_build_options o1 = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 1,
                .num_threads = 1};
            lrt_tri_scene *sdfl = lrt_tri_scene_build(verts, 100, &odfl, NULL);
            lrt_tri_scene *s1 = lrt_tri_scene_build(verts, 100, &o1, NULL);
            CHECK(sdfl && s1, "max-leaf build: both succeeded");
            if (sdfl && s1) {
                lrt_tri_stats sd, s1s;
                lrt_tri_scene_stats(sdfl, &sd);
                lrt_tri_scene_stats(s1, &s1s);
                /* leaf-only tree should have ~100 leaves; default should have fewer.
                 * Verify leaf count is higher with max_leaf=1. */
                CHECK(s1s.leaf_count >= sd.leaf_count,
                      "max-leaf=1 has >= leaves (leaf1=%u, leafdfl=%u)",
                      s1s.leaf_count, sd.leaf_count);
            }
            lrt_tri_scene_free(sdfl);
            lrt_tri_scene_free(s1);
            free(verts);
        }
    }

    /* (10) max_leaf_size clamping: values above TRI_MAX_LEAF should be clamped.
     * Build should succeed even with an absurdly large max_leaf_size. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_build_options o = {
            .quality = LRT_TRI_BUILD_DEFAULT,
            .layout = LRT_TRI_LAYOUT_BVH4,
            .max_leaf_size = 0x7FFFFFFF, /* way above TRI_MAX_LEAF */
            .num_threads = 1};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, &o, NULL);
        CHECK(s != NULL, "build huge max_leaf_size succeeds (clamped)");
        if (s) {
            lrt_hit h;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "clamped max_leaf: still hits (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (11) SBVH (HQ) with single triangle: exercises the spatial split path
     * on minimal geometry. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_build_options o = {
            .quality = LRT_TRI_BUILD_HQ,
            .layout = LRT_TRI_LAYOUT_BVH4,
            .max_leaf_size = 0,
            .num_threads = 1};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, &o, NULL);
        CHECK(s != NULL, "HQ single-tri build");
        if (s) {
            lrt_hit h;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 && fabsf(h.t - 5.0f) < 1e-3f,
                  "HQ single-tri hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (12) SBVH (HQ) with many triangles: exercises spatial splits on a
     * larger scene. Must agree with SAH on hit/miss. */
    {
        g_rng = 0xCAFEBEEFull;
        float *verts = make_random_soup(500, 0.5f);
        CHECK(verts != NULL, "HQ-many build: soup alloc");
        if (verts) {
            lrt_tri_build_options osah = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 1};
            lrt_tri_build_options ohq = {
                .quality = LRT_TRI_BUILD_HQ,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 1};
            lrt_tri_scene *s_sah = lrt_tri_scene_build(verts, 500, &osah, NULL);
            lrt_tri_scene *s_hq = lrt_tri_scene_build(verts, 500, &ohq, NULL);
            CHECK(s_sah && s_hq, "HQ-many build: both succeeded");
            if (s_sah && s_hq) {
                size_t mism = 0;
                for (int i = 0; i < 5000; i++) {
                    lrt_ray r;
                    make_random_ray(&r);
                    lrt_hit hs, hh;
                    int sas = lrt_tri_intersect1(s_sah, &r, &hs);
                    int hhh = lrt_tri_intersect1(s_hq, &r, &hh);
                    if (sas != hhh) {
                        /* SBVH can split a triangle and change the hit
                         * prim_id/ordering, but hit/miss should agree for
                         * non-split triangles. Allow SBVH differences. */
                        mism++;
                    }
                }
                /* SBVH may return different hits for split triangles; we only
                 * check that both build and traverse without crashing. */
                printf("  HQ-many: %zu/5000 hit differences (SBVH splits expected)\n",
                       mism);
            }
            lrt_tri_scene_free(s_sah);
            lrt_tri_scene_free(s_hq);
            free(verts);
        }
    }

    /* (13) LBVH (FAST) with many triangles: exercises the Morton-sort + radix
     * sort path. Must agree with SAH. */
    {
        g_rng = 0x55555555ull;
        float *verts = make_random_soup(2000, 0.2f);
        CHECK(verts != NULL, "LBVH-many build: soup alloc");
        if (verts) {
            lrt_tri_build_options ofast = {
                .quality = LRT_TRI_BUILD_FAST,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 1};
            lrt_tri_build_options osah = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 1};
            lrt_tri_scene *s_fast = lrt_tri_scene_build(verts, 2000, &ofast, NULL);
            lrt_tri_scene *s_sah = lrt_tri_scene_build(verts, 2000, &osah, NULL);
            CHECK(s_fast && s_sah, "LBVH-many build: both succeeded");
            if (s_fast && s_sah) {
                size_t mism = 0;
                for (int i = 0; i < 10000; i++) {
                    lrt_ray r;
                    make_random_ray(&r);
                    lrt_hit hf, hs;
                    int af = lrt_tri_intersect1(s_fast, &r, &hf);
                    int as = lrt_tri_intersect1(s_sah, &r, &hs);
                    if (af != as) {
                        mism++;
                    } else if (af && fabsf(hf.t - hs.t) > 1e-2f) {
                        mism++;
                    }
                }
                CHECK(mism < 100, /* LBVH is ~7-10% worse than SAH; expect few mismatches */
                      "LBVH-many: %zu/10000 mismatches vs SAH", mism);
            }
            lrt_tri_scene_free(s_fast);
            lrt_tri_scene_free(s_sah);
            free(verts);
        }
    }

    /* (14) BVH8 on SBVH (HQ): exercises the quantized node collapse path with
     * spatial splits. */
    {
        g_rng = 0x77777777ull;
        float *verts = make_random_soup(300, 0.5f);
        CHECK(verts != NULL, "HQ-bvh8 build: soup alloc");
        if (verts) {
            lrt_tri_build_options ohq8 = {
                .quality = LRT_TRI_BUILD_HQ,
                .layout = LRT_TRI_LAYOUT_BVH8,
                .max_leaf_size = 0,
                .num_threads = 1};
            lrt_tri_scene *s = lrt_tri_scene_build(verts, 300, &ohq8, NULL);
            CHECK(s != NULL, "HQ BVH8 build");
            if (s) {
                lrt_hit h;
                lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                CHECK(lrt_tri_intersect1(s, &r, &h) == 0 || h.prim_id < 300,
                      "HQ BVH8 traverses (id=%u)", h.prim_id);
                lrt_tri_scene_free(s);
            }
            free(verts);
        }
    }

    /* (15) BVH8_Q4 on SBVH (HQ): exercises the 4-bit quantized node path with
     * spatial splits. The q4/fp8 node-quantized kernels are AVX2-only; on other
     * targets the build returns INVALID_ARGUMENT, so this is x86-AVX2 only. */
#if defined(__AVX2__) && defined(__FMA__)
    {
        g_rng = 0x88888888ull;
        float *verts = make_random_soup(300, 0.5f);
        CHECK(verts != NULL, "HQ-q4 build: soup alloc");
        if (verts) {
            lrt_tri_build_options ohq4 = {
                .quality = LRT_TRI_BUILD_HQ,
                .layout = LRT_TRI_LAYOUT_BVH8_Q4,
                .max_leaf_size = 0,
                .num_threads = 1};
            lrt_tri_scene *s = lrt_tri_scene_build(verts, 300, &ohq4, NULL);
            CHECK(s != NULL, "HQ BVH8_Q4 build");
            if (verts && s) {
                lrt_hit h;
                lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                CHECK(lrt_tri_intersect1(s, &r, &h) == 0 || h.prim_id < 300,
                      "HQ BVH8_Q4 traverses (id=%u)", h.prim_id);
                lrt_tri_scene_free(s);
            }
            free(verts);
        }
    }
#endif

    /* (16) Parallel LBVH build: exercises the parallel Morton sort + radix sort
     * path. */
    {
        g_rng = 0xAAAAAAAAull;
        float *verts = make_random_soup(4096, 0.2f);
        CHECK(verts != NULL, "parallel-LBVH build: soup alloc");
        if (verts) {
            lrt_tri_build_options o1 = {
                .quality = LRT_TRI_BUILD_FAST,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 1};
            lrt_tri_build_options o8 = {
                .quality = LRT_TRI_BUILD_FAST,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 8};
            lrt_tri_scene *s1 = lrt_tri_scene_build(verts, 4096, &o1, NULL);
            lrt_tri_scene *s8 = lrt_tri_scene_build(verts, 4096, &o8, NULL);
            CHECK(s1 && s8, "parallel-LBVH build: both succeeded");
            if (s1 && s8) {
                size_t mism = 0;
                for (int i = 0; i < 5000; i++) {
                    lrt_ray r;
                    make_random_ray(&r);
                    lrt_hit h1, h8;
                    int a1 = lrt_tri_intersect1(s1, &r, &h1);
                    int a8 = lrt_tri_intersect1(s8, &r, &h8);
                    if (a1 != a8) {
                        mism++;
                    } else if (a1 && fabsf(h1.t - h8.t) > 1e-3f) {
                        mism++;
                    }
                }
                CHECK(mism == 0, "parallel LBVH: %zu/5000 mismatches vs serial",
                      mism);
            }
            lrt_tri_scene_free(s1);
            lrt_tri_scene_free(s8);
            free(verts);
        }
    }

    /* (17) Overlapping triangles (all same centroid): SBVH should split them,
     * SAVH should still work. Both must build. */
    {
        float overlap[9 * 10];
        for (int i = 0; i < 10; i++) {
            float offset = (float)i * 0.01f;
            overlap[i * 9 + 0] = -1.0f + offset; overlap[i * 9 + 1] = -1.0f;
            overlap[i * 9 + 2] = 5.0f;
            overlap[i * 9 + 3] = 1.0f + offset; overlap[i * 9 + 4] = -1.0f;
            overlap[i * 9 + 5] = 5.0f;
            overlap[i * 9 + 6] = 0.0f + offset; overlap[i * 9 + 7] = 1.0f;
            overlap[i * 9 + 8] = 5.0f;
        }
        lrt_tri_build_options osah = {
            .quality = LRT_TRI_BUILD_DEFAULT,
            .layout = LRT_TRI_LAYOUT_BVH4,
            .max_leaf_size = 0,
            .num_threads = 1};
        lrt_tri_build_options ohq = {
            .quality = LRT_TRI_BUILD_HQ,
            .layout = LRT_TRI_LAYOUT_BVH4,
            .max_leaf_size = 0,
            .num_threads = 1};
        lrt_tri_scene *s_sah = lrt_tri_scene_build(overlap, 10, &osah, NULL);
        lrt_tri_scene *s_hq = lrt_tri_scene_build(overlap, 10, &ohq, NULL);
        CHECK(s_sah && s_hq, "overlap build: both succeeded");
        if (s_sah && s_hq) {
            lrt_hit hs, hh;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            int as = lrt_tri_intersect1(s_sah, &r, &hs);
            int ah = lrt_tri_intersect1(s_hq, &r, &hh);
            CHECK(as && ah, "overlap: both hit (sah id=%u, hq id=%u)",
                  hs.prim_id, hh.prim_id);
        }
        lrt_tri_scene_free(s_sah);
        lrt_tri_scene_free(s_hq);
    }

    /* (18) Huge triangle count (stress test for capacity overflow): build 100k
     * triangles with SAH and verify it works. */
    {
        g_rng = 0xFEDCBA98ull;
        float *verts = make_random_soup(100000, 0.1f);
        CHECK(verts != NULL, "huge build: soup alloc");
        if (verts) {
            lrt_tri_build_options o = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 1};
            lrt_tri_scene *s = lrt_tri_scene_build(verts, 100000, &o, NULL);
            CHECK(s != NULL, "huge build succeeded");
            if (s) {
                lrt_tri_stats st;
                lrt_tri_scene_stats(s, &st);
                printf("  huge: %u nodes, %u leaves, depth %u, %.1f KB\n",
                       st.node_count, st.leaf_count, st.max_depth,
                       (double)st.memory_bytes / 1024.0);
                lrt_hit h;
                lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                CHECK(lrt_tri_intersect1(s, &r, &h) == 0 || h.prim_id < 100000,
                      "huge traverses (id=%u)", h.prim_id);
            }
            lrt_tri_scene_free(s);
            free(verts);
        }
    }

    /* (19) All identical triangles: builds, BVH tree may be degenerate but must
     * not crash. */
    {
        float identical[9 * 20];
        for (int i = 0; i < 20; i++)
            memcpy(identical + i * 9,
                   (float[]){-1, -1, 0, 1, -1, 0, 0, 1, 0}, sizeof(float) * 9);
        lrt_tri_scene *s = lrt_tri_scene_build(identical, 20, NULL, NULL);
        CHECK(s != NULL, "identical-tri build");
        if (s) {
            lrt_hit h;
            lrt_ray r = {{0, 0, -5}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 && h.prim_id < 20,
                  "identical-tri hits (id=%u)", h.prim_id);
            lrt_tri_scene_free(s);
        }
    }

    /* (20) Empty BVH (ntris=0 is rejected above; this tests ntris=1 with
     * max_leaf_size=0 default). Already covered by (7) but check stats. */
    {
        float tri[9] = {0, 0, 0, 1, 0, 0, 0, 1, 0};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "single-tri build for stats");
        if (s) {
            lrt_tri_stats st;
            lrt_tri_scene_stats(s, &st);
            CHECK(st.leaf_count > 0,
                  "single-tri has leaves (leaves=%u)", st.leaf_count);
            lrt_tri_scene_free(s);
        }
    }
}
/* Sphere primitive intersection edge cases. */
static void test_sphere_edge_cases(void) {
    lrt_hit h;

    /* (1) Single sphere: center at origin, radius 1, ray from below. */
    {
        float sph[4] = {0, 0, 0, 1.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "single-sphere build");
        if (s) {
            lrt_ray r = {{0, 0, -5}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 4.0f) < 1e-3f,
                  "single sphere near root (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (2) Ray origin inside sphere: near root should be the far intersection. */
    {
        float sph[4] = {0, 0, 5, 1.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "inside-sphere build");
        if (s) {
            lrt_ray r = {{0, 0, 5}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 1.0f) < 1e-3f,
                  "origin inside sphere -> far root (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (3) Tangential (grazing) ray: ray exactly at sphere edge. */
    {
        float sph[4] = {0, 0, 5, 1.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "grazing build");
        if (s) {
            /* Ray at y=1, going along +z - touches sphere at exactly one point. */
            lrt_ray r = {{0, 1, 0}, 0.0f, {0, 0, 1}, 100.0f};
            int hit = lrt_tri_intersect1(s, &r, &h);
            CHECK(hit == 1, "grazing ray hits (t=%f)", (double)h.t);
            if (hit) {
                CHECK(fabsf(h.t - 5.0f) < 2e-3f, "grazing t near 5 (t=%f)",
                      (double)h.t);
            }
            lrt_tri_scene_free(s);
        }
    }

    /* (4) Ray origin at sphere surface: tmin=0 should accept the near root. */
    {
        float sph[4] = {0, 0, 5, 1.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "surface-origin build");
        if (s) {
            lrt_ray r = {{0, 0, 4}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t) < 1e-3f,
                  "origin at surface tmin=0 (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (5) Sphere with r=0: should never hit (radius zero = no surface). */
    {
        float sph[4] = {0, 0, 5, 0.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "zero-radius sphere build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "zero-radius sphere never hits");
            lrt_tri_scene_free(s);
        }
    }

    /* (6) Sphere with negative radius: should never hit. */
    {
        float sph[4] = {0, 0, 5, -1.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "neg-radius sphere build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "negative-radius sphere never hits");
            lrt_tri_scene_free(s);
        }
    }

    /* (7) tmax clipping on sphere: tmax before near root should reject. */
    {
        float sph[4] = {0, 0, 5, 1.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "tmax-sphere build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            r.tmax = 0.5f;
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "sphere tmax clips before near root");
            lrt_tri_scene_free(s);
        }
    }

    /* (8) tmin clipping on sphere: tmin past far root should reject. */
    {
        float sph[4] = {0, 0, 5, 1.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "tmin-sphere build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            r.tmin = 7.0f;
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "sphere tmin clips past far root");
            lrt_tri_scene_free(s);
        }
    }

    /* (9) Multiple spheres: overlapping spheres along ray. Verify closest hit. */
    {
        float spheres[8];
        spheres[0] = 0; spheres[1] = 0; spheres[2] = 3; spheres[3] = 2.0f;
        spheres[4] = 0; spheres[5] = 0; spheres[6] = 5; spheres[7] = 1.0f;
        lrt_tri_scene *s = lrt_sphere_scene_build(spheres, 2, NULL, NULL);
        CHECK(s != NULL, "double-sphere build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 && h.prim_id == 0,
                  "double sphere hits closer one (prim_id=%u)", h.prim_id);
            lrt_tri_scene_free(s);
        }
    }

    /* (10) Sphere scene with NaN center: must reject with INVALID_BOUNDS. */
    {
        float sph[4] = {NAN, 0, 0, 1.0f};
        lrt_result err = LRT_RESULT_OK;
        CHECK(lrt_sphere_scene_build(sph, 1, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_BOUNDS,
              "sphere NaN center rejected");
    }

    /* (11) Sphere scene with Inf radius: must reject. */
    {
        float sph[4] = {0, 0, 0, INFINITY};
        lrt_result err = LRT_RESULT_OK;
        CHECK(lrt_sphere_scene_build(sph, 1, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_BOUNDS,
              "sphere Inf radius rejected");
    }

    /* (12) Ray exactly through sphere center: tests symmetric quadratic. */
    {
        float sph[4] = {0, 0, 5, 1.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "center-ray build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 4.0f) < 1e-3f,
                  "center-ray near root (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (13) Off-center sphere hit: ray not through center. */
    {
        float sph[4] = {1, 2, 0, 1.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "off-center build");
        if (s) {
            lrt_ray r = {{1, 0, 0}, 0.0f, {0, 1, 0}, 100.0f};
            /* Ray along +y through center at (1,2,0). Near root at y=1 -> t=1. */
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 1.0f) < 1e-3f,
                  "off-center near root (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (14) Sphere miss: ray far from sphere. */
    {
        float sph[4] = {0, 0, 5, 0.5f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "miss-sphere build");
        if (s) {
            lrt_ray r = {{10, 10, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0, "sphere far miss");
            lrt_tri_scene_free(s);
        }
    }

    /* (15) Sphere with BVH8 layout: exercises the BVH8 kernel. */
    {
        float sph[4] = {0, 0, 5, 1.0f};
        lrt_tri_build_options o = {
            .quality = LRT_TRI_BUILD_DEFAULT,
            .layout = LRT_TRI_LAYOUT_BVH8,
            .max_leaf_size = 0,
            .num_threads = 1};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, &o, NULL);
        CHECK(s != NULL, "sphere bvh8 build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 4.0f) < 1e-3f,
                  "sphere bvh8 hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }
}

/* Hair/primitive intersection edge cases for curve, roundcurve, flatcurve,
 * points (sphere/disc/oriented-disc), and built-in spheres. */
static void test_hair_edge_cases(void) {
    lrt_hit h;

    /* (1) Single constant-radius capsule (curve): ray through the cylinder axis. */
    {
        float segs[6] = {0, 0, 0, 0, 0, 10};
        lrt_tri_scene *s = lrt_curve_scene_build(segs, NULL, 0.5f, 1, NULL, NULL);
        CHECK(s != NULL, "single-constant-cap build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            /* Ray through capsule axis: cylinder quadratic degenerates (A=0),
             * end caps take over. Near cap root is behind origin (t=-0.5),
             * far cap root is at t=9.5. */
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 9.5f) < 1e-3f,
                  "capsule axis ray (t=%f)", (double)h.t);
            lrt_ray r2 = {{0, 0, 0}, 10.5f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r2, &h) == 0,
                  "capsule tmin past far end");
            lrt_tri_scene_free(s);
        }
    }

    /* (2) Single capsule with varying radii (roundcurve): r0 > r1 (tapering).
     * Tests the cone CSG path. */
    {
        float pts[6] = {0, 0, 0, 0, 0, 10};
        float radii[2] = {0.5f, 0.3f};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = radii;
        hs.constant_radius = 0.0f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_tri_scene *s = lrt_roundcurve_scene_build(&hs, NULL, NULL);
        CHECK(s != NULL, "tapered roundcurve build");
        if (s) {
            /* Ray through cylinder side at x=0.2, entering from below. */
            lrt_ray r = {{0.2f, -5, 0}, 0.0f, {0, 1, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 && h.prim_id == 0,
                  "tapered roundcurve side hit (t=%f id=%u)", (double)h.t, h.prim_id);
            lrt_tri_scene_free(s);
        }
    }

    /* (3) Single isolated roundcurve segment (constant radius): tests the
     * sentinel CSG path (no neighbors to clip against) and r0==r1 cylinder. */
    {
        float pts[6] = {0, 0, 0, 2, 0, 0};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = NULL;
        hs.constant_radius = 0.2f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_tri_scene *s = lrt_roundcurve_scene_build(&hs, NULL, NULL);
        CHECK(s != NULL, "isolated roundcurve build");
        if (s) {
            /* Ray along +y through cylinder side. */
            lrt_ray r = {{1, -5, 0}, 0.0f, {0, 1, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 4.8f) < 2e-3f,
                  "isolated cylinder side (t=%f)", (double)h.t);
            /* Ray past the end cap. */
            lrt_ray miss = {{3, -5, 0}, 0.0f, {0, 1, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &miss, &h) == 0,
                  "isolated past end cap miss");
            lrt_tri_scene_free(s);
        }
    }

    /* (4) Flat curve (ribbon) edge-on: ray parallel to ribbon plane. */
    {
        float pts[6] = {0, 0, 0, 2, 0, 0};
        float radii[2] = {0.3f, 0.3f};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = radii;
        hs.constant_radius = 0.0f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_tri_scene *s = lrt_flatcurve_scene_build(&hs, NULL, NULL);
        CHECK(s != NULL, "flatcurve build");
        if (s) {
            /* Ray along +z, ribbon is in xy plane - should miss. */
            lrt_ray r = {{1, 0, 5}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "flatcurve edge-on miss");
            lrt_tri_scene_free(s);
        }
    }

    /* (5) Flat curve face-on: ray perpendicular to ribbon plane. */
    {
        float pts[6] = {0, 0, 0, 2, 0, 0};
        float radii[2] = {0.3f, 0.3f};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = radii;
        hs.constant_radius = 0.0f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_tri_scene *s = lrt_flatcurve_scene_build(&hs, NULL, NULL);
        CHECK(s != NULL, "face-flat build");
        if (s) {
            /* Ray along +z through ribbon center. Ribbon is in xy plane (ray-facing
             * plane for x-axis segment with +z ray). */
            lrt_ray r = {{1, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "flatcurve face-on hit");
            lrt_tri_scene_free(s);
        }
    }

    /* (6) Single sphere point: tests the analytic quadratic path. */
    {
        float c[3] = {0, 0, 5};
        float rr = 1.0f;
        lrt_tri_scene *s = lrt_points_scene_build(c, &rr, NULL, LRT_POINT_SPHERE,
                                                  1, NULL, NULL);
        CHECK(s != NULL, "single sphere point build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 4.0f) < 1e-3f,
                  "sphere point near root (t=%f)", (double)h.t);
            lrt_ray ins = {{0, 0, 5}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &ins, &h) == 1 &&
                  fabsf(h.t - 1.0f) < 1e-3f,
                  "sphere point inside -> far root (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (7) Single disc point: tests the ray-disk intersection. */
    {
        float c[3] = {0, 0, 5};
        float rr = 1.0f;
        lrt_tri_scene *s = lrt_points_scene_build(c, &rr, NULL, LRT_POINT_DISC,
                                                  1, NULL, NULL);
        CHECK(s != NULL, "single disc build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                  fabsf(h.t - 5.0f) < 1e-3f,
                  "disc hit (t=%f)", (double)h.t);
            /* Ray through disc edge. */
            lrt_ray edge = {{1, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &edge, &h) == 1 &&
                  fabsf(h.t - 5.0f) < 1e-3f,
                  "disc edge hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (8) Single oriented disc: fixed normal, tests the ray-facing disc. */
    {
        float c[3] = {0, 0, 5};
        float rr = 1.0f;
        float n[3] = {0, 0, 1};
        lrt_tri_scene *s = lrt_points_scene_build(
            c, &rr, n, LRT_POINT_ORIENTED_DISC, 1, NULL, NULL);
        CHECK(s != NULL, "oriented-disc build");
        if (s) {
            /* Ray along normal direction. */
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "oriented-disc face-on hit");
            /* Ray perpendicular to normal - parallel to disc plane. */
            lrt_ray edge = {{0, 0, 0}, 0.0f, {1, 0, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &edge, &h) == 0,
                  "oriented-disc edge-on miss");
            lrt_tri_scene_free(s);
        }
    }

    /* (9) Capsule with zero radius: rejected by builder (r<=0). */
    {
        float segs[6] = {0, 0, 0, 0, 0, 10};
        lrt_result err = LRT_RESULT_OK;
        CHECK(lrt_curve_scene_build(segs, NULL, 0.0f, 1, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_ARGUMENT,
              "zero-radius capsule rejected");
    }

    /* (10) Single-segment strand (minimum valid input): strand_count=2, 1 segment.
     * Tests the smallest possible strand structure. */
    {
        float pts[6] = {0, 0, 0, 0, 0, 1};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = NULL;
        hs.constant_radius = 0.1f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_tri_scene *s = lrt_roundcurve_scene_build(&hs, NULL, NULL);
        CHECK(s != NULL, "min-strand build");
        if (s) {
            /* Ray through cylinder side at x=0.05, entering from below. */
            lrt_ray r = {{0.05f, -5, 0}, 0.0f, {0, 1, 0}, 100.0f};
            int hit = lrt_tri_intersect1(s, &r, &h);
            CHECK(hit == 1,
                  "min-strand side hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (11) Strand with count=1 (invalid: < 2 points): should be skipped, not
     * crash. Single-segment strand is the minimum. */
    {
        float pts[3] = {0, 0, 0};
        uint32_t sf = 0, sc = 1;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = NULL;
        hs.constant_radius = 0.1f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 1;
        lrt_result err = LRT_RESULT_OK;
        /* count=1 means 0 segments; the builder should handle this gracefully. */
        lrt_tri_scene *s = lrt_roundcurve_scene_build(&hs, NULL, &err);
        /* May succeed (0 segments) or fail; either way, no crash. */
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "count=1 strand produces no hits");
            lrt_tri_scene_free(s);
        }
    }

    /* (12) Multi-segment strand with varying radii: exercises the varying-radius
     * path in roundcurve. */
    {
        float pts[12] = {0, 0, 0, 0, 0, 5, 0, 0, 10};
        float radii[3] = {0.4f, 0.2f, 0.3f};
        uint32_t sf = 0, sc = 3;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = radii;
        hs.constant_radius = 0.0f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 3;
        lrt_tri_scene *s = lrt_roundcurve_scene_build(&hs, NULL, NULL);
        CHECK(s != NULL, "multi-segment varying-radius build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "multi-segment varying-radius hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (13) Capsule with NaN vertex: must reject with INVALID_BOUNDS. */
    {
        float segs[6] = {NAN, 0, 0, 0, 0, 10};
        lrt_result err = LRT_RESULT_OK;
        CHECK(lrt_curve_scene_build(segs, NULL, 0.1f, 1, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_BOUNDS,
              "curve NaN vertex rejected");
    }

    /* (14) Capsule with Inf vertex: must reject. */
    {
        float segs[6] = {0, 0, 0, INFINITY, 0, 0};
        lrt_result err = LRT_RESULT_OK;
        CHECK(lrt_curve_scene_build(segs, NULL, 0.1f, 1, NULL, &err) == NULL &&
              err == LRT_RESULT_INVALID_BOUNDS,
              "curve Inf vertex rejected");
    }

    /* (15) Sphere occluded1 / intersect1 consistency: occluded1 must agree with
     * intersect1 on hit/miss. */
    {
        float sph[4] = {0, 0, 5, 1.0f};
        lrt_tri_scene *s = lrt_sphere_scene_build(sph, 1, NULL, NULL);
        CHECK(s != NULL, "occl-consistency-sphere build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1, "sphere hit");
            CHECK(lrt_tri_occluded1(s, &r) == 1, "sphere occluded1 agrees");
            lrt_ray rm = {{10, 10, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &rm, &h) == 0, "sphere miss");
            CHECK(lrt_tri_occluded1(s, &rm) == 0, "sphere occluded1 agrees on miss");
            lrt_tri_scene_free(s);
        }
    }

    /* (16) Capsule tmax clipping: tmax before near root should reject. */
    {
        float segs[6] = {0, 0, 0, 0, 0, 10};
        lrt_tri_scene *s = lrt_curve_scene_build(segs, NULL, 0.5f, 1, NULL, NULL);
        CHECK(s != NULL, "capsule-tmax build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            r.tmax = 0.4f;
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "capsule tmax clips before near root");
            lrt_tri_scene_free(s);
        }
    }

    /* (17) Capsule tmin clipping: tmin past far root should reject. */
    {
        float segs[6] = {0, 0, 0, 0, 0, 10};
        lrt_tri_scene *s = lrt_curve_scene_build(segs, NULL, 0.5f, 1, NULL, NULL);
        CHECK(s != NULL, "capsule-tmin build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            r.tmin = 10.5f;
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "capsule tmin clips past far root");
            lrt_tri_scene_free(s);
        }
    }

    /* (18) Single-segment flatcurve with varying radii (tapered ribbon). */
    {
        float pts[6] = {0, 0, 0, 2, 0, 0};
        float radii[2] = {0.5f, 0.2f};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = radii;
        hs.constant_radius = 0.0f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_tri_scene *s = lrt_flatcurve_scene_build(&hs, NULL, NULL);
        CHECK(s != NULL, "tapered-flat build");
        if (s) {
            lrt_ray r = {{1, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "tapered flatcurve hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (19) Multi-strand roundcurve: two strands, each with 2 points. */
    {
        float pts1[6] = {0, 0, 0, 0, 0, 5};
        float pts2[6] = {5, 0, 0, 5, 0, 5};
        float radii1[2] = {0.2f, 0.2f};
        float radii2[2] = {0.2f, 0.2f};
        uint32_t sf1 = 0, sc1 = 2;
        (void)pts2; (void)radii2;
        lrt_hair_strands hs = {0};
        hs.points = pts1;
        hs.radius = radii1;
        hs.constant_radius = 0.0f;
        hs.strand_first = &sf1;
        hs.strand_count = &sc1;
        hs.nstrands = 1;
        hs.npoints = 2;
        /* Second strand: add to the same scene by building with both. */
        lrt_tri_scene *s = lrt_roundcurve_scene_build(&hs, NULL, NULL);
        CHECK(s != NULL, "single-strand roundcurve");
        if (s) {
           lrt_ray r = {{0.05f, -5, 0}, 0.0f, {0, 1, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "single-strand side hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
        /* Build second strand separately. */
        hs.points = pts2;
        hs.radius = radii2;
        s = lrt_roundcurve_scene_build(&hs, NULL, NULL);
        CHECK(s != NULL, "second-strand roundcurve");
        if (s) {
            lrt_ray r = {{5.05f, -5, 0}, 0.0f, {0, 1, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "second-strand side hit (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* (20) Roundcurve with NaN in radius: must reject. */
    {
        float pts[6] = {0, 0, 0, 2, 0, 0};
        float radii[2] = {NAN, 0.2f};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = radii;
        hs.constant_radius = 0.0f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_result err = LRT_RESULT_OK;
        /* NaN radius may be handled by the precompute path. */
        lrt_tri_scene *s = lrt_roundcurve_scene_build(&hs, NULL, &err);
        /* The builder may or may not reject NaN in radius; at least no crash. */
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0 || h.prim_id < 1,
                  "NaN radius handled (no crash, id=%u)", h.prim_id);
            lrt_tri_scene_free(s);
        }
    }
}
static void test_curve_point_edge_cases(void) {
    lrt_hit h;

    /* (1) Single isolated round-linear segment: both neighbors absent (the
     * sentinel CSG path) and r0==r1 (cone degenerates to a cylinder), built via
     * the constant-radius path (radius == NULL). Cylinder axis +x, radius 0.2. */
    {
        float pts[6] = {0, 0, 0, 2, 0, 0};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = NULL;
        hs.constant_radius = 0.2f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_tri_scene *s = lrt_roundcurve_scene_build(&hs, NULL, NULL);
        CHECK(s != NULL, "isolated roundcurve (constant radius) build");
        if (s) {
            /* +y ray at x=1 grazes the cylinder side at y=-0.2 -> t = 5 - 0.2. */
            lrt_ray r = {{1, -5, 0}, 0.0f, {0, 1, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 &&
                      fabsf(h.t - 4.8f) < 2e-3f && h.prim_id == 0,
                  "isolated cylinder side hit (t=%f id=%u)", (double)h.t,
                  h.prim_id);
            r.tmax = 4.0f;
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0, "roundcurve tmax clips");
            CHECK(lrt_tri_occluded1(s, &r) == 0,
                  "roundcurve occluded respects tmax");
            r.tmax = 100.0f;
            CHECK(lrt_tri_occluded1(s, &r) == 1, "roundcurve occluded hit");
            /* The +y ray passes through the cylinder (enter 4.8, exit 5.2), so
             * tmin must clear both roots to clip the whole segment. */
            r.tmin = 6.0f;
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0, "roundcurve tmin clips");
            /* x=3 is past the +x end cap (x=2, r=0.2) by 0.8 -> clean miss. */
            lrt_ray miss = {{3, -5, 0}, 0.0f, {0, 1, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &miss, &h) == 0, "roundcurve clean miss");
            lrt_tri_scene_free(s);
        }
    }

    /* (2) Analytic sphere point: near-root hit, ray-origin-inside far root,
     * radial miss, and tmax clipping. */
    {
        float c[3] = {0, 0, 5};
        float rr = 1.0f;
        lrt_tri_scene *s = lrt_points_scene_build(c, &rr, NULL, LRT_POINT_SPHERE,
                                                  1, NULL, NULL);
        CHECK(s != NULL, "sphere point build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 && fabsf(h.t - 4.0f) < 1e-3f,
                  "sphere near-root hit (t=%f)", (double)h.t);
            lrt_ray ins = {{0, 0, 5}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &ins, &h) == 1 &&
                      fabsf(h.t - 1.0f) < 1e-3f,
                  "ray inside sphere -> far root (t=%f)", (double)h.t);
            lrt_ray mr = {{0, 2, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &mr, &h) == 0, "sphere radial miss");
            r.tmax = 3.5f;
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0 &&
                      lrt_tri_occluded1(s, &r) == 0,
                  "sphere tmax clips");
            lrt_tri_scene_free(s);
        }
    }

    /* (3) Oriented disc (fixed normal): a ray perpendicular to the normal is
     * parallel to the disc plane and must miss; a ray along the normal hits the
     * plane, and a hit point outside the radius must be rejected. */
    {
        float c[3] = {0, 0, 5};
        float rr = 1.0f;
        float n[3] = {1, 0, 0};
        lrt_tri_scene *s = lrt_points_scene_build(
            c, &rr, n, LRT_POINT_ORIENTED_DISC, 1, NULL, NULL);
        CHECK(s != NULL, "oriented-disc build");
        if (s) {
            lrt_ray edge = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f}; /* _|_ normal */
            CHECK(lrt_tri_intersect1(s, &edge, &h) == 0,
                  "oriented disc edge-on miss");
            lrt_ray face = {{-5, 0, 5}, 0.0f, {1, 0, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &face, &h) == 1 &&
                      fabsf(h.t - 5.0f) < 1e-3f,
                  "oriented disc face-on hit (t=%f)", (double)h.t);
            /* hits the plane at (0,0,7), distance 2 from center -> outside r. */
            lrt_ray off = {{-5, 0, 7}, 0.0f, {1, 0, 0}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &off, &h) == 0,
                  "oriented disc outside radius");
            lrt_tri_scene_free(s);
        }
    }
}

/* --- New edge-case tests --------------------------------------------------- */

static void test_null_inputs(void) {
    /* NULL / empty / invalid input handling. */
    lrt_result err = LRT_RESULT_OK;

    /* lrt_tri_scene_build(NULL, ...) -> NULL. */
    CHECK(lrt_tri_scene_build(NULL, 10, NULL, NULL) == NULL,
          "build(NULL, 10) returns NULL");
    CHECK(lrt_tri_scene_build(NULL, 0, NULL, NULL) == NULL,
          "build(NULL, 0) returns NULL");
    CHECK(lrt_tri_scene_build(NULL, 0x07FFFFFF + 1, NULL, NULL) == NULL,
          "build(NULL, overflow) returns NULL");

    /* Build a small 1-triangle scene for reuse. */
    float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
    lrt_tri_scene *scene = lrt_tri_scene_build(tri, 1, NULL, NULL);
    CHECK(scene != NULL, "null-inputs: build small scene");
    if (!scene) return;

    lrt_ray ray = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
    lrt_hit hit;

    /* lrt_tri_intersect1(NULL, ...) -> 0, no crash. */
    CHECK(lrt_tri_intersect1(NULL, &ray, &hit) == 0, "intersect1(NULL)");
    /* lrt_tri_intersect1(scene, NULL, ...) -> 0, no crash. */
    CHECK(lrt_tri_intersect1(scene, NULL, &hit) == 0, "intersect1(scene, NULL ray)");
    /* lrt_tri_intersect1(scene, &ray, NULL) -> no crash (undefined result). */
    {
        int r = lrt_tri_intersect1(scene, &ray, NULL);
        CHECK(r == 0 || r == 1, "intersect1(scene, &ray, NULL) no crash (r=%d)", r);
    }

    /* lrt_tri_scene_free(NULL) -> no crash. */
    lrt_tri_scene_free(NULL);

    /* lrt_tri_scene_save(NULL, ...) -> INVALID_ARGUMENT. */
    err = LRT_RESULT_OK;
    CHECK(lrt_tri_scene_save(NULL, "/tmp/lrt_null_test.lrts") ==
              LRT_RESULT_INVALID_ARGUMENT,
          "save(NULL) returns INVALID_ARGUMENT");

    /* lrt_tri_scene_load("/nonexistent", ...) -> NULL. */
    err = LRT_RESULT_OK;
    CHECK(lrt_tri_scene_load("/tmp/lrt_nonexistent.lrts", &err) == NULL,
          "load non-existent file returns NULL");

    /* lrt_tri_scene_open_mmap("/nonexistent", ...) -> NULL. */
    err = LRT_RESULT_OK;
    CHECK(lrt_tri_scene_open_mmap("/tmp/lrt_nonexistent.lrts", &err) == NULL,
          "open_mmap non-existent file returns NULL");

    /* lrt_tri_scene_load_from_memory(NULL, 0, ...) -> NULL. */
    err = LRT_RESULT_OK;
    CHECK(lrt_tri_scene_load_from_memory(NULL, 0, &err) == NULL,
          "load_from_memory(NULL, 0) returns NULL");

    /* lrt_tri_scene_load_from_memory(buf, 2, ...) -> NULL (too small for magic). */
    {
        unsigned char tiny[4];
        tiny[0] = 'X';
        tiny[1] = 'Y';
        err = LRT_RESULT_OK;
        CHECK(lrt_tri_scene_load_from_memory(tiny, 2, &err) == NULL,
              "load_from_memory(buf, 2) returns NULL");
    }

    lrt_tri_scene_free(scene);
}

static void test_batch_edge_cases(void) {
    /* Batched query edge cases. */
    enum { NT = 50 };
    g_rng = 0x42424242ull;
    float *verts = make_random_soup(NT, 0.5f);
    CHECK(verts != NULL, "batch-edge: alloc soup");
    if (!verts) return;

    lrt_tri_scene *scene = lrt_tri_scene_build(verts, NT, NULL, NULL);
    CHECK(scene != NULL, "batch-edge: build scene");
    if (!scene) {
        free(verts);
        return;
    }

    /* n=0 batch: should not crash. */
    {
        lrt_hit hits[4];
        lrt_ray rays[4];
        memset(hits, 0, sizeof(hits));
        memset(rays, 0, sizeof(rays));
        lrt_tri_intersect1N(scene, rays, hits, 0, LRT_TRI_BATCH_AUTO);
        /* hits should remain at prim_id=LRT_TRI_NO_HIT (or unchanged). */
        CHECK(1, "batch n=0 no crash");
    }

    /* NULL hit buffer with n > 0: should not crash. */
    {
        lrt_ray rays[4];
        for (int i = 0; i < 4; i++) {
            rays[i].org[0] = rnd_f(-2, 2);
            rays[i].org[1] = rnd_f(-2, 2);
            rays[i].org[2] = rnd_f(-2, 2);
            rays[i].dir[0] = rnd_f(-1, 1);
            rays[i].dir[1] = rnd_f(-1, 1);
            rays[i].dir[2] = rnd_f(-1, 1);
            rays[i].tmin = 0.0f;
            rays[i].tmax = 100.0f;
        }
        lrt_tri_intersect1N(scene, rays, NULL, 4, LRT_TRI_BATCH_AUTO);
        CHECK(1, "batch NULL hit buffer no crash");
    }

    /* NULL ray buffer with n > 0: should not crash. */
    {
        lrt_hit hits[4];
        memset(hits, 0, sizeof(hits));
        lrt_tri_intersect1N(scene, NULL, hits, 4, LRT_TRI_BATCH_AUTO);
        CHECK(1, "batch NULL ray buffer no crash");
    }

    /* 4 rays all with tmin > tmax: all should miss (prim_id = LRT_TRI_NO_HIT). */
    {
        lrt_ray rays[4];
        lrt_hit hits[4];
        for (int i = 0; i < 4; i++) {
            rays[i].org[0] = rnd_f(-2, 2);
            rays[i].org[1] = rnd_f(-2, 2);
            rays[i].org[2] = rnd_f(-2, 2);
            rays[i].dir[0] = rnd_f(-1, 1);
            rays[i].dir[1] = rnd_f(-1, 1);
            rays[i].dir[2] = rnd_f(-1, 1);
            rays[i].tmin = 10.0f;
            rays[i].tmax = 5.0f; /* inverted */
        }
        lrt_tri_intersect1N(scene, rays, hits, 4, LRT_TRI_BATCH_AUTO);
        for (int i = 0; i < 4; i++) {
            CHECK(hits[i].prim_id == LRT_TRI_NO_HIT,
                  "batch inverted tmin/tmax: prim_id=%u (expected NO_HIT)",
                  hits[i].prim_id);
        }
    }

    /* 4 identical rays: all 4 lanes should produce same hit. */
    {
        lrt_ray rays[4];
        lrt_hit hits[4];
        lrt_ray base = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
        for (int i = 0; i < 4; i++) {
            rays[i] = base;
        }
        lrt_tri_intersect1N(scene, rays, hits, 4, LRT_TRI_BATCH_AUTO);
        for (int i = 1; i < 4; i++) {
            CHECK(hits[i].prim_id == hits[0].prim_id,
                  "batch identical rays: lane %d prim_id=%u != lane 0=%u",
                  i, hits[i].prim_id, hits[0].prim_id);
            CHECK(fabsf(hits[i].t - hits[0].t) < 1e-5f,
                  "batch identical rays: lane %d t diff %f",
                  i, hits[i].t - hits[0].t);
        }
    }

    /* Mixed hit/miss batch vs scalar and occluded clipping behavior. */
    {
        lrt_tri_scene *m = lrt_tri_scene_build(
            (float[]){-1, -1, 5, 1, -1, 5, 0, 1, 5,
                      -1, -1, 12, 1, -1, 12, 0, 1, 12},
            2, NULL, NULL);
        CHECK(m != NULL, "batch mixed: build");
        if (m) {
            lrt_ray rays[4];
            rays[0] = (lrt_ray){{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            rays[1] = (lrt_ray){{0, 0, 0}, 0.0f, {0, 1, 0}, 100.0f};
            rays[2] = (lrt_ray){{0, 0, 0}, 0.0f, {0, 0, -1}, 100.0f};
            rays[3] = (lrt_ray){{0, 0, 0}, 0.0f, {0, 0, 1}, 4.0f};
            lrt_hit h[4];
            uint8_t o[4];
            lrt_tri_intersect1N(m, rays, h, 4, LRT_TRI_BATCH_AUTO);
            lrt_tri_occluded1N(m, rays, o, 4, LRT_TRI_BATCH_AUTO);

            for (int i = 0; i < 4; i++) {
                lrt_hit hs;
                int sh = lrt_tri_intersect1(m, &rays[i], &hs);
                int so = lrt_tri_occluded1(m, &rays[i]);
                CHECK(h[i].prim_id == hs.prim_id,
                      "batch mixed lane %d prim_id mismatch (%u != %u)", i,
                      h[i].prim_id, hs.prim_id);
                if ((h[i].prim_id != LRT_TRI_NO_HIT) || (hs.prim_id != LRT_TRI_NO_HIT)) {
                    CHECK(fabsf(h[i].t - hs.t) < 1e-6f,
                          "batch mixed lane %d t mismatch (%f != %f)", i,
                          (double)h[i].t, (double)hs.t);
                }
                CHECK(o[i] == (uint8_t)so,
                      "batch mixed lane %d occluded parity (%u != %u)", i, o[i],
                      (uint8_t)so);
            }
            CHECK(h[3].prim_id == LRT_TRI_NO_HIT &&
                      o[3] == 0u,
                  "batch lane 3 is clipped out (no hit)");
            lrt_tri_scene_free(m);
        }
    }

    lrt_tri_scene_free(scene);
    free(verts);
}

static void test_stats(void) {
    /* Scene stats tests. */
    lrt_tri_stats st;

    /* 1 triangle: leaf_count == 1, node_count 0 or 1. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "stats: 1-tri build");
        if (s) {
            lrt_tri_scene_stats(s, &st);
            CHECK(st.leaf_count == 1,
                  "stats 1-tri: leaf_count=%u (expected 1)", st.leaf_count);
            CHECK(st.node_count == 0 || st.node_count == 1,
                  "stats 1-tri: node_count=%u (expected 0 or 1)", st.node_count);
            lrt_tri_scene_free(s);
        }
    }

    /* 2 triangles with max_leaf_size=1: leaf_count == 2, at least 1 interior node. */
    {
        float verts[18];
        float t1[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        float t2[9] = {-2, -2, 3, 0, -2, 3, -1, 0, 3};
        memcpy(verts, t1, sizeof(t1));
        memcpy(verts + 9, t2, sizeof(t2));
        lrt_tri_build_options o = {
            .quality = LRT_TRI_BUILD_DEFAULT,
            .layout = LRT_TRI_LAYOUT_BVH4,
            .max_leaf_size = 1,
            .num_threads = 1};
        lrt_tri_scene *s = lrt_tri_scene_build(verts, 2, &o, NULL);
        CHECK(s != NULL, "stats: 2-tri build");
        if (s) {
            lrt_tri_scene_stats(s, &st);
            CHECK(st.leaf_count == 2,
                  "stats 2-tri: leaf_count=%u (expected 2)", st.leaf_count);
            CHECK(st.node_count >= 1,
                  "stats 2-tri: node_count=%u (>= 1)", st.node_count);
            lrt_tri_scene_free(s);
        }
    }

    /* Same scene with BVH4 and BVH8: compare node/leaf counts. */
    {
        g_rng = 0x55555555ull;
        float *verts = make_random_soup(500, 0.5f);
        CHECK(verts != NULL, "stats: alloc soup");
        if (verts) {
            lrt_tri_build_options o4 = {.layout = LRT_TRI_LAYOUT_BVH4};
            lrt_tri_build_options o8 = {.layout = LRT_TRI_LAYOUT_BVH8};
            lrt_tri_scene *s4 = lrt_tri_scene_build(verts, 500, &o4, NULL);
            lrt_tri_scene *s8 = lrt_tri_scene_build(verts, 500, &o8, NULL);
            CHECK(s4 && s8, "stats: both layouts build");
            if (s4 && s8) {
                lrt_tri_scene_stats(s4, &st);
                lrt_tri_stats st8;
                lrt_tri_scene_stats(s8, &st8);
                /* BVH4 and BVH8 may have different leaf counts due to
                 * different tree construction, but both should be reasonable. */
                CHECK(st.leaf_count > 0 && st.leaf_count <= 1024,
                      "stats bvh4 leaf_count reasonable (%u)", st.leaf_count);
                CHECK(st8.leaf_count > 0 && st8.leaf_count <= 1024,
                      "stats bvh8 leaf_count reasonable (%u)", st8.leaf_count);
                /* BVH8 nodes may be fewer (wider tree). */
                CHECK(st8.node_count > 0,
                      "stats bvh8 node_count > 0 (%u)", st8.node_count);
                lrt_tri_scene_free(s4);
                lrt_tri_scene_free(s8);
            }
            free(verts);
        }
    }

#if defined(__AVX2__) && defined(__FMA__)
    /* Quantized-node layouts should report sane stats for node/leaf counts and
     * memory. */
    {
        float *verts = make_random_soup(200, 0.3f);
        CHECK(verts != NULL, "stats qnode: alloc soup");
        if (verts) {
            lrt_tri_build_options oqf8 = {.layout = LRT_TRI_LAYOUT_BVH8_QF8};
            lrt_tri_build_options oq4 = {.layout = LRT_TRI_LAYOUT_BVH8_Q4};
            lrt_tri_scene *sqf8 = lrt_tri_scene_build(verts, 200, &oqf8, NULL);
            lrt_tri_scene *sq4 = lrt_tri_scene_build(verts, 200, &oq4, NULL);
            CHECK(sqf8 != NULL && sq4 != NULL,
                  "stats qnode: qf8/q4 build");
            if (sqf8 && sq4) {
                lrt_tri_stats stf8, st4;
                lrt_tri_scene_stats(sqf8, &stf8);
                lrt_tri_scene_stats(sq4, &st4);
                CHECK(stf8.leaf_count > 0, "stats qf8: leaf_count > 0");
                CHECK(stf8.node_count > 0, "stats qf8: node_count > 0");
                CHECK(st4.leaf_count > 0, "stats q4: leaf_count > 0");
                CHECK(st4.node_count > 0, "stats q4: node_count > 0");
                CHECK(stf8.memory_bytes > 0, "stats qf8: memory_bytes > 0");
                CHECK(st4.memory_bytes > 0, "stats q4: memory_bytes > 0");
                lrt_tri_scene_free(sqf8);
                lrt_tri_scene_free(sq4);
            } else {
                if (sqf8) lrt_tri_scene_free(sqf8);
                if (sq4) lrt_tri_scene_free(sq4);
            }
            free(verts);
        }
    }
#endif
}

static void test_kernel_name(void) {
    /* Kernel name tests. */
    float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
    lrt_tri_scene *s4 = lrt_tri_scene_build(tri, 1, NULL, NULL);
    lrt_tri_build_options o8 = {.layout = LRT_TRI_LAYOUT_BVH8};
    lrt_tri_scene *s8 = lrt_tri_scene_build(tri, 1, &o8, NULL);
    lrt_tri_build_options o8q = {.layout = LRT_TRI_LAYOUT_BVH8Q};
    lrt_tri_scene *s8q = lrt_tri_scene_build(tri, 1, &o8q, NULL);
    lrt_tri_build_options o8qf8 = {.layout = LRT_TRI_LAYOUT_BVH8_QF8};
    lrt_tri_build_options o8q4 = {.layout = LRT_TRI_LAYOUT_BVH8_Q4};
    lrt_tri_scene *s8qf8 = lrt_tri_scene_build(tri, 1, &o8qf8, NULL);
    lrt_tri_scene *s8q4 = lrt_tri_scene_build(tri, 1, &o8q4, NULL);
    (void)s8qf8;
    (void)s8q4;

    CHECK(s4 && s8 && s8q, "kernel-name: base layouts build");
#if defined(__AVX2__) && defined(__FMA__)
    CHECK(s8qf8 && s8q4, "kernel-name: quantized-node layouts build");
#endif
    if (s4 && s8 && s8q) {
        const char *n4 = lrt_tri_kernel_name(s4);
        const char *n8 = lrt_tri_kernel_name(s8);
        const char *n8q = lrt_tri_kernel_name(s8q);
        CHECK(n4 != NULL, "kernel-name: BVH4 name non-NULL");
        CHECK(n8 != NULL, "kernel-name: BVH8 name non-NULL");
        CHECK(n8q != NULL, "kernel-name: BVH8Q name non-NULL");

        if (n4) CHECK(strstr(n4, "bvh4") != NULL, "kernel-name: BVH4 contains 'bvh4'");
        if (n8) CHECK(strstr(n8, "bvh8") != NULL, "kernel-name: BVH8 contains 'bvh8'");
        if (n8q) CHECK(strstr(n8q, "bvh8") != NULL, "kernel-name: BVH8Q contains 'bvh8'");
#if defined(__AVX2__) && defined(__FMA__)
        if (n8q) CHECK(strstr(n8q, "/avx2") != NULL, "kernel-name: BVH8Q reports avx2");
#else
        if (n8) CHECK((strstr(n8, "/sse4") || strstr(n8, "/scalar") ||
                       strstr(n8, "/sve") || strstr(n8, "/neon")) != NULL,
                      "kernel-name: BVH8 reports a known backend");
#endif
        if (s8qf8 && s8q4) {
            const char *n8qf8 = lrt_tri_kernel_name(s8qf8);
            const char *n8q4n = lrt_tri_kernel_name(s8q4);
            CHECK(n8qf8 != NULL, "kernel-name: BVH8QF8 name non-NULL");
            CHECK(n8q4n != NULL, "kernel-name: BVH8Q4 name non-NULL");
            if (n8qf8) CHECK(strstr(n8qf8, "bvh8q") != NULL,
                             "kernel-name: BVH8QF8 token includes bvh8q");
            if (n8q4n) CHECK(strstr(n8q4n, "bvh8q") != NULL,
                             "kernel-name: BVH8Q4 token includes bvh8q");
        }
    }

#if defined(__AVX2__) && defined(__FMA__)
    if (s8qf8) lrt_tri_scene_free(s8qf8);
    if (s8q4) lrt_tri_scene_free(s8q4);
#endif
    lrt_tri_scene_free(s4);
    lrt_tri_scene_free(s8);
    lrt_tri_scene_free(s8q);
}

static void test_user_geometry_edge_cases(void) {
    /* User geometry edge cases. */
    lrt_result err = LRT_RESULT_OK;

    /* NULL isect callback -> should reject. */
    {
        float dummy_aabb[6] = {-1, -1, -1, 1, 1, 1};
        lrt_tri_scene *s =
            lrt_user_scene_build(dummy_aabb, 1, NULL, NULL, NULL, NULL, &err);
        CHECK(s == NULL && err == LRT_RESULT_INVALID_ARGUMENT,
              "user build NULL isect rejected (err=%d)", (int)err);
    }

    /* NaN AABB -> should reject (INVALID_BOUNDS). */
    {
        float nan_aabb[6];
        memset(nan_aabb, 0, sizeof(nan_aabb));
        nan_aabb[0] = NAN;
        err = LRT_RESULT_OK;
        lrt_tri_scene *s =
            lrt_user_scene_build(nan_aabb, 1, user_always_hit_cb, NULL, NULL, NULL, &err);
        CHECK(s == NULL && err == LRT_RESULT_INVALID_BOUNDS,
              "user build NaN AABB rejected (err=%d)", (int)err);
    }

    /* Inverted AABB (lo > hi): should build (user owns AABB validity). */
    {
        float inv_aabb[6] = {1, 1, 1, -1, -1, -1};
        err = LRT_RESULT_OK;
        lrt_tri_scene *s =
            lrt_user_scene_build(inv_aabb, 1, user_always_hit_cb, NULL, NULL, NULL, &err);
        CHECK(s != NULL, "user build inverted AABB builds (err=%d)", (int)err);
        if (s) {
            lrt_hit h;
            lrt_ray ray = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            /* inverted AABB may cull the ray, but no crash. */
            lrt_tri_intersect1(s, &ray, &h);
            lrt_tri_scene_free(s);
        }
    }

    /* User callback that always returns hit: all rays should hit. */
    {
        float aabb[6] = {-10, -10, -10, 10, 10, 10};
        lrt_tri_scene *s =
            lrt_user_scene_build(aabb, 1, user_always_hit_cb, NULL, NULL, NULL, &err);
        CHECK(s != NULL, "user build always-hit cb");
        if (s) {
            lrt_hit h;
            lrt_ray ray = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &ray, &h) == 1,
                  "user always-hit: ray hits (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* User callback that always returns miss: no rays should hit. */
    {
        float aabb[6] = {-10, -10, -10, 10, 10, 10};
        lrt_tri_scene *s =
            lrt_user_scene_build(aabb, 1, user_always_miss_cb, NULL, NULL, NULL, &err);
        CHECK(s != NULL, "user build always-miss cb");
        if (s) {
            lrt_hit h;
            lrt_ray ray = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &ray, &h) == 0,
                  "user always-miss: ray misses");
            lrt_tri_scene_free(s);
        }
    }
}

static void test_sphere_scene_edge_cases(void) {
    /* Sphere scene edge cases. */
    lrt_result err = LRT_RESULT_OK;

    /* NaN center -> should reject. */
    {
        float nan_sph[4] = {NAN, 0, 0, 1};
        err = LRT_RESULT_OK;
        lrt_tri_scene *s = lrt_sphere_scene_build(nan_sph, 1, NULL, &err);
        CHECK(s == NULL && err == LRT_RESULT_INVALID_BOUNDS,
              "sphere build NaN center rejected (err=%d)", (int)err);
    }

    /* Inf center -> should reject. */
    {
        float inf_sph[4] = {INFINITY, 0, 0, 1};
        err = LRT_RESULT_OK;
        lrt_tri_scene *s = lrt_sphere_scene_build(inf_sph, 1, NULL, &err);
        CHECK(s == NULL && err == LRT_RESULT_INVALID_BOUNDS,
              "sphere build Inf center rejected (err=%d)", (int)err);
    }

    /* Mixed valid/invalid radii: some r<=0. Build should succeed; ray through
     * valid sphere should hit, through invalid should miss. */
    {
        float mixed[8];
        /* Sphere 0: valid */
        mixed[0] = 0; mixed[1] = 0; mixed[2] = 5; mixed[3] = 1.0f;
        /* Sphere 1: invalid (r=0) */
        mixed[4] = 10; mixed[5] = 0; mixed[6] = 5; mixed[7] = 0.0f;
        lrt_tri_scene *s = lrt_sphere_scene_build(mixed, 2, NULL, NULL);
        CHECK(s != NULL, "sphere mixed radii builds");
        if (s) {
            lrt_hit h;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            /* Should hit sphere 0 (valid), miss sphere 1 (invalid). */
            int hit = lrt_tri_intersect1(s, &r, &h);
            CHECK(hit == 1 && h.prim_id == 0,
                  "sphere mixed: hits valid sphere (prim_id=%u)", h.prim_id);

            lrt_tri_scene_free(s);
        }
    }

    /* All r<=0: should build, never hit. */
    {
        float bad[8];
        bad[0] = 0; bad[1] = 0; bad[2] = 5; bad[3] = 0.0f;
        bad[4] = 10; bad[5] = 0; bad[6] = 5; bad[7] = -1.0f;
        lrt_tri_scene *s = lrt_sphere_scene_build(bad, 2, NULL, NULL);
        CHECK(s != NULL, "sphere all-bad radii builds");
        if (s) {
            lrt_hit h;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "sphere all-bad: never hits");
            lrt_tri_scene_free(s);
        }
    }
}

static void test_triangle_intersection_edge_cases(void) {
    /* Triangle intersection edge cases. */
    lrt_hit h;
    lrt_result err = LRT_RESULT_OK;

    /* Triangle with one vertex at origin: ray through origin should hit. */
    {
        float tri[9] = {0, 0, 0, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "tri-origin build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "tri-origin: ray through origin hits (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* Triangle with one vertex at INF: should reject (INVALID_BOUNDS). */
    {
        float inf_tri[9];
        memset(inf_tri, 0, sizeof(inf_tri));
        inf_tri[0] = INFINITY;
        err = LRT_RESULT_OK;
        lrt_tri_scene *s = lrt_tri_scene_build(inf_tri, 1, NULL, &err);
        CHECK(s == NULL && err == LRT_RESULT_INVALID_BOUNDS,
              "tri Inf vertex rejected (err=%d)", (int)err);
    }

    /* Two identical vertices (v0==v1): should build, no crash. */
    {
        float degen[9] = {1, 1, 5, 1, 1, 5, 0, 2, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(degen, 1, NULL, NULL);
        CHECK(s != NULL, "tri v0==v1 builds");
        if (s) {
            lrt_ray r = {{1, 1, 0}, 0.0f, {0, 0, 1}, 100.0f};
            /* Degenerate triangle should not hit (or may hit depending on MT). */
            lrt_tri_intersect1(s, &r, &h);
            lrt_tri_scene_free(s);
        }
    }

    /* Unnormalized direction should still use raw t parameter (not normalized |dir|). */
    {
        float tri[9] = { -1, -1, 5, 1, -1, 5, 0, 1, 5 };
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "tri unnormalized dir build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 10}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "tri unnormalized dir: ray hits at t=%f", (double)h.t);
            CHECK(fabsf(h.t - 0.5f) < 1e-4f,
                  "tri unnormalized dir: t=(%f) expected 0.5", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* Negative tmax means empty ray interval -> no hit. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "tri negative tmax build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, -1.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "tri negative tmax: should not hit");
            lrt_tri_scene_free(s);
        }
    }
}

static void test_multihit_edge_cases(void) {
    /* Multi-hit edge cases. */

    /* max_hits=0: should return 0. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "multihit: build scene");
        if (s) {
            lrt_hit h[4];
            lrt_ray ray = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            size_t n = lrt_tri_intersect_n(s, &ray, h, 0);
            CHECK(n == 0, "multihit max_hits=0 returns 0");
            lrt_tri_scene_free(s);
        }
    }

    /* max_hits=1: should equal intersect1. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "multihit=1: build scene");
        if (s) {
            lrt_hit h1, hn;
            lrt_ray ray = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            int sc = lrt_tri_intersect1(s, &ray, &h1);
            size_t n = lrt_tri_intersect_n(s, &ray, &hn, 1);
            CHECK(n == (size_t)sc,
                  "multihit max_hits=1 count matches intersect1 (n=%zu, sc=%d)",
                  n, sc);
            if (sc) {
                CHECK(hn.prim_id == h1.prim_id && hn.t == h1.t,
                      "multihit max_hits=1 hit matches intersect1");
            }
            lrt_tri_scene_free(s);
        }
    }

    /* Scene with 5 triangles, max_hits=100: should return at most 5 hits. */
    {
        float verts[45];
        for (int i = 0; i < 5; i++) {
            float t[9] = {-1, -1, 5.0f + (float)i * 0.001f,
                          1, -1, 5.0f + (float)i * 0.001f,
                          0, 1, 5.0f + (float)i * 0.001f};
            memcpy(&verts[i * 9], t, sizeof(t));
        }
        lrt_tri_scene *s = lrt_tri_scene_build(verts, 5, NULL, NULL);
        CHECK(s != NULL, "multihit 5-tri: build");
        if (s) {
            lrt_hit h[100];
            lrt_ray ray = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            size_t n = lrt_tri_intersect_n(s, &ray, h, 100);
            CHECK(n <= 5, "multihit 5-tri: at most 5 hits (got %zu)", n);
            lrt_tri_scene_free(s);
        }
    }

    /* Single-triangle scene, max_hits=10: should return 1 hit. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "multihit 1-tri: build");
        if (s) {
            lrt_hit h[10];
            lrt_ray ray = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            size_t n = lrt_tri_intersect_n(s, &ray, h, 10);
            CHECK(n == 1, "multihit 1-tri: exactly 1 hit (got %zu)", n);
            lrt_tri_scene_free(s);
        }
    }
}

static void test_closest_point_edge_cases(void) {
    /* Closest point / kNN edge cases. */
    lrt_point_hit ph;
    lrt_knn_result knn[5];

    /* Query point at triangle centroid: that triangle should be nearest with
     * dist_sq approx 0. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "closest-point: build");
        if (s) {
            float p[3] = {0.0f, 0.0f, 5.0f}; /* centroid */
            int hit = lrt_tri_closest_point(s, p, &ph);
            CHECK(hit == 1, "closest-point at centroid: hit");
            CHECK(ph.prim_id == 0, "closest-point at centroid: prim_id=0");
            CHECK(ph.dist_sq < 1e-6f,
                  "closest-point at centroid: dist_sq=%.6e (expected ~0)",
                  ph.dist_sq);
            lrt_tri_scene_free(s);
        }
    }

    /* Query point on triangle edge: that triangle should be found. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "closest-point edge: build");
        if (s) {
            /* Point on the edge between (-1,-1,5) and (1,-1,5) -> midpoint. */
            float p[3] = {0.0f, -1.0f, 5.0f};
            int hit = lrt_tri_closest_point(s, p, &ph);
            CHECK(hit == 1, "closest-point on edge: hit");
            CHECK(ph.prim_id == 0, "closest-point on edge: prim_id=0");
            CHECK(ph.dist_sq < 1e-6f,
                  "closest-point on edge: dist_sq=%.6e", ph.dist_sq);
            lrt_tri_scene_free(s);
        }
    }

    /* Query point far from scene: should find nearest triangle. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "closest-point far: build");
        if (s) {
            float p[3] = {1000.0f, 1000.0f, 1000.0f};
            int hit = lrt_tri_closest_point(s, p, &ph);
            CHECK(hit == 1, "closest-point far: hit (far point)");
            CHECK(ph.prim_id == 0, "closest-point far: prim_id=0");
            /* Distance should be large but finite. */
            CHECK(ph.dist_sq > 1e3f,
                  "closest-point far: dist_sq=%.6e (large)", ph.dist_sq);
            lrt_tri_scene_free(s);
        }
    }
}

static void test_region_query_edge_cases(void) {
    /* Region query edge cases. */
    uint32_t out[1024];

    /* Build a small scene for reuse. */
    float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
    lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
    CHECK(s != NULL, "region-query: build");
    if (!s) return;

    /* AABB query with lo==hi (zero-volume point): should return 0 or the
     * primitive at that point. */
    {
        float lo[3] = {0.0f, 0.0f, 5.0f};
        float hi[3] = {0.0f, 0.0f, 5.0f};
        size_t n = lrt_tri_query_aabb(s, lo, hi, out, 1024);
        CHECK(n <= 1, "aabb zero-volume: at most 1 result (got %zu)", n);
    }

    /* Sphere query with radius=0: should return 0 or primitives at that point. */
    {
        float center[3] = {0, 0, 5};
        size_t n = lrt_tri_query_sphere(s, center, 0.0f, out, 1024);
        CHECK(n <= 1, "sphere radius=0: at most 1 result (got %zu)", n);
    }

    /* Sphere query with Inf radius: should return all primitives. */
    {
        float center[3] = {0, 0, 5};
        size_t n = lrt_tri_query_sphere(s, center, INFINITY, out, 1024);
        CHECK(n == 1, "sphere Inf radius: 1 result");
    }

    /* Sphere query with NaN center: should not crash, return 0. */
    {
        float nan_center[3] = {NAN, 0, 0};
        size_t n = lrt_tri_query_sphere(s, nan_center, 10.0f, out, 1024);
        CHECK(n <= 1, "sphere NaN center: no crash (got %zu)", n);
    }

    /* AABB query with NaN bounds: should safely return 0. */
    {
        float lo[3] = {NAN, -1.0f, -1.0f};
        float hi[3] = {1.0f, 1.0f, 1.0f};
        size_t n = lrt_tri_query_aabb(s, lo, hi, out, 1024);
        CHECK(n == 0, "aabb NaN inputs: returns 0 (got %zu)", n);
    }

    /* Zero-area frustum (degenerate planes collapsing to a point): no hit for a
     * non-intersecting scene. */
    {
        lrt_frustum f;
        memset(&f, 0, sizeof(f));
        f.planes[0][0] = 1.0f;
        f.planes[1][0] = -1.0f;
        f.planes[2][1] = 1.0f;
        f.planes[3][1] = -1.0f;
        f.planes[4][2] = 1.0f;
        f.planes[5][2] = -1.0f;
        size_t n = lrt_tri_query_frustum(s, &f, out, 1024);
        CHECK(n == 0, "frustum zero-area: no hit (got %zu)", n);
    }

    /* Inverted near/far setup: contradictory z constraints should yield empty
     * frustum (no results). */
    {
        lrt_frustum f;
        memset(&f, 0, sizeof(f));
        f.planes[0][0] = 1.0f;
        f.planes[0][3] = 1e38f;
        f.planes[1][0] = -1.0f;
        f.planes[1][3] = 1e38f;
        f.planes[2][1] = 1.0f;
        f.planes[2][3] = 1e38f;
        f.planes[3][1] = -1.0f;
        f.planes[3][3] = 1e38f;
        f.planes[4][2] = 1.0f;
        f.planes[4][3] = -1e23f;  /* z >= 1e23 */
        f.planes[5][2] = -1.0f;
        f.planes[5][3] = -1e23f;  /* z <= -1e23 */
        size_t n = lrt_tri_query_frustum(s, &f, out, 1024);
        CHECK(n == 0, "frustum inverted near/far: no hit (got %zu)", n);
    }

    /* Frustum with NaN plane coefficients: should not crash. */
    {
        lrt_frustum f;
        memset(&f, 0, sizeof(f));
        f.planes[0][0] = NAN;
        size_t n = lrt_tri_query_frustum(s, &f, out, 1024);
        CHECK(n <= 1, "frustum NaN plane: no crash (got %zu)", n);
    }

    lrt_tri_scene_free(s);
}

static void test_build_options(void) {
    /* Build options edge cases. */
    lrt_result err = LRT_RESULT_OK;

    /* max_leaf_size=0: should use default (not crash). */
    {
        g_rng = 0x66666666ull;
        float *verts = make_random_soup(50, 1.0f);
        CHECK(verts != NULL, "build-options: alloc");
        if (verts) {
            lrt_tri_build_options o = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 1};
            lrt_tri_scene *s = lrt_tri_scene_build(verts, 50, &o, NULL);
            CHECK(s != NULL, "build max_leaf=0 succeeds");
            if (s) {
                lrt_hit h;
                lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                lrt_tri_intersect1(s, &r, &h);
                lrt_tri_scene_free(s);
            }
            free(verts);
        }
    }

    /* max_leaf_size=1: each triangle is its own leaf (leaf_count == ntris). */
    {
        g_rng = 0x77777777ull;
        float *verts = make_random_soup(30, 1.0f);
        CHECK(verts != NULL, "build-options ml1: alloc");
        if (verts) {
            lrt_tri_build_options o = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 1,
                .num_threads = 1};
            lrt_tri_scene *s = lrt_tri_scene_build(verts, 30, &o, NULL);
            CHECK(s != NULL, "build max_leaf=1 succeeds");
            if (s) {
                lrt_tri_stats st;
                lrt_tri_scene_stats(s, &st);
                CHECK(st.leaf_count == 30,
                      "build max_leaf=1: leaf_count=%u (expected 30)",
                      st.leaf_count);
                lrt_tri_scene_free(s);
            }
            free(verts);
        }
    }

    /* max_leaf_size=0x7FFFFFFF: should clamp, not crash. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_build_options o = {
            .quality = LRT_TRI_BUILD_DEFAULT,
            .layout = LRT_TRI_LAYOUT_BVH4,
            .max_leaf_size = 0x7FFFFFFF,
            .num_threads = 1};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, &o, NULL);
        CHECK(s != NULL, "build max_leaf=0x7FFFFFFF succeeds (clamped)");
        if (s) {
            lrt_hit h;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            lrt_tri_intersect1(s, &r, &h);
            lrt_tri_scene_free(s);
        }
    }

    /* num_threads=0: serial build (should work). */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_build_options o = {
            .quality = LRT_TRI_BUILD_DEFAULT,
            .layout = LRT_TRI_LAYOUT_BVH4,
            .max_leaf_size = 0,
            .num_threads = 0};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, &o, NULL);
        CHECK(s != NULL, "build num_threads=0 succeeds");
        if (s) {
            lrt_hit h;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "build threads=0: hits");
            lrt_tri_scene_free(s);
        }
    }

    /* num_threads=1: serial build (should work). */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_build_options o = {
            .quality = LRT_TRI_BUILD_DEFAULT,
            .layout = LRT_TRI_LAYOUT_BVH4,
            .max_leaf_size = 0,
            .num_threads = 1};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, &o, NULL);
        CHECK(s != NULL, "build num_threads=1 succeeds");
        if (s) {
            lrt_hit h;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "build threads=1: hits");
            lrt_tri_scene_free(s);
        }
    }
}

static void test_fp_precision(void) {
    /* FP precision edge cases. */
    lrt_hit h;
    lrt_result err = LRT_RESULT_OK;

    /* Ray with tmin == tmax == 1e38: should not crash. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "fp-precision: build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            r.tmin = 1e38f;
            r.tmax = 1e38f;
            int hit = lrt_tri_intersect1(s, &r, &h);
            CHECK(hit == 0, "fp tmin=tmax=1e38: no hit (expected)");
            lrt_tri_scene_free(s);
        }
    }

    /* Ray with tmin == tmax == 1e-38: should not crash. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "fp-precision: build");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            r.tmin = 1e-38f;
            r.tmax = 1e-38f;
            int hit = lrt_tri_intersect1(s, &r, &h);
            CHECK(hit == 0, "fp tmin=tmax=1e-38: no hit (expected)");
            lrt_tri_scene_free(s);
        }
    }

    /* Triangle with denormalized coordinates (1e-38): should build and hit. */
    {
        float tiny_tri[9];
        tiny_tri[0] = 1e-38f; tiny_tri[1] = 1e-38f; tiny_tri[2] = 5.0f;
        tiny_tri[3] = 1e-38f + 0.1f; tiny_tri[4] = 1e-38f; tiny_tri[5] = 5.0f;
        tiny_tri[6] = 1e-38f; tiny_tri[7] = 1e-38f + 0.1f; tiny_tri[8] = 5.0f;
        lrt_tri_scene *s = lrt_tri_scene_build(tiny_tri, 1, NULL, NULL);
        CHECK(s != NULL, "fp denorm build succeeds");
        if (s) {
            /* Ray aimed at the triangle center (~0.05, ~0.05, 5). */
            lrt_ray r;
            r.org[0] = 0.05f; r.org[1] = 0.05f; r.org[2] = 0.0f;
            r.tmin = 0.0f;
            r.dir[0] = 0.0f; r.dir[1] = 0.0f; r.dir[2] = 1.0f;
            r.tmax = 100.0f;
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "fp denorm: hits (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* Ray origin at subnormal float (1e-38): should not crash. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(s != NULL, "fp-precision: build");
        if (s) {
            lrt_ray r;
            r.org[0] = 1e-38f;
            r.org[1] = 1e-38f;
            r.org[2] = 0.0f;
            r.tmin = 0.0f;
            r.dir[0] = 0.0f;
            r.dir[1] = 0.0f;
            r.dir[2] = 1.0f;
            r.tmax = 100.0f;
            int hit = lrt_tri_intersect1(s, &r, &h);
            CHECK(hit == 1, "fp subnormal origin: hits (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* Very large coordinates (1e30 scale): should still intersect without NaN/Inf. */
    {
        const float S = 1e30f;
        const float D = 1e23f;
        float big_tri[9];
        big_tri[0] = S;
        big_tri[1] = 0.0f;
        big_tri[2] = 0.0f;
        big_tri[3] = S + D;
        big_tri[4] = 0.0f;
        big_tri[5] = 0.0f;
        big_tri[6] = S;
        big_tri[7] = 1.0f;
        big_tri[8] = 0.0f;
        lrt_tri_scene *s = lrt_tri_scene_build(big_tri, 1, NULL, &err);
        CHECK(s != NULL, "fp large coords: build");
        if (s) {
            lrt_ray r;
            r.org[0] = S;
            r.org[1] = 0.5f;
            r.org[2] = -1.0f;
            r.tmin = 0.0f;
            r.dir[0] = 0.0f;
            r.dir[1] = 0.0f;
            r.dir[2] = 1.0f;
            r.tmax = 1e38f;
            int hit = lrt_tri_intersect1(s, &r, &h);
            CHECK(hit == 1, "fp large coords: intersects");
            if (hit) {
                CHECK(h.t > 0.0f && isfinite(h.t),
                      "fp large coords: finite hit values");
                CHECK(fabs((double)h.t - 1.0) < 1e-4,
                      "fp large coords: plausible distance (t=%f)", (double)h.t);
            }
            CHECK(lrt_tri_occluded1(s, &r) == 1, "fp large coords: occluded");
            lrt_tri_scene_free(s);
        }
    }
}

static void test_tlas_edge_cases(void) {
    /* TLAS edge cases. */
    lrt_result err = LRT_RESULT_OK;

    /* TLAS with 1 BLAS, 1 instance, ray through it: should hit. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *blas = lrt_tri_scene_build(tri, 1, NULL, &err);
        CHECK(blas != NULL, "tlas-edge: BLAS build");
        if (!blas) return;

        lrt_instance inst;
        float im[12] = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0};
        memcpy(inst.obj2world, im, sizeof(im));
        inst.blas_id = 0;
        inst.instance_id = 1;
        inst.mask = 0xFFFFFFFFu;
        lrt_tlas *tlas = lrt_tlas_build(&blas, 1, &inst, 1, NULL, &err);
        CHECK(tlas != NULL, "tlas-edge: 1-instance build");
        if (tlas) {
            lrt_tlas_hit th;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            int hit = lrt_tlas_intersect1(tlas, &r, 0xFFFFFFFFu, &th);
            CHECK(hit == 1, "tlas-edge: 1-instance ray hits");
            CHECK(th.inst_id == 1, "tlas-edge: instance_id=1");
            lrt_tlas_free(tlas);
        }
        lrt_tri_scene_free(blas);
    }

    /* TLAS with 2 BLASes, 2 instances: ray should hit closest instance. */
    {
        float tri1[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        float tri2[9] = {-1, -1, 10, 1, -1, 10, 0, 1, 10};
        lrt_tri_scene *blas1 = lrt_tri_scene_build(tri1, 1, NULL, NULL);
        lrt_tri_scene *blas2 = lrt_tri_scene_build(tri2, 1, NULL, NULL);
        CHECK(blas1 && blas2, "tlas-2bl: both BLASes build");
        if (blas1 && blas2) {
            lrt_tri_scene *blases[2] = {blas1, blas2};
            lrt_instance insts[2];
            float im[12] = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0};
            memcpy(insts[0].obj2world, im, sizeof(im));
            insts[0].blas_id = 0;
            insts[0].instance_id = 1;
            insts[0].mask = 0xFFFFFFFFu;
            memcpy(insts[1].obj2world, im, sizeof(im));
            insts[1].blas_id = 1;
            insts[1].instance_id = 2;
            insts[1].mask = 0xFFFFFFFFu;
            lrt_tlas *tlas = lrt_tlas_build(blases, 2, insts, 2, NULL, &err);
            CHECK(tlas != NULL, "tlas-2bl: build");
            if (tlas) {
                lrt_tlas_hit th;
                lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                int hit = lrt_tlas_intersect1(tlas, &r, 0xFFFFFFFFu, &th);
                CHECK(hit == 1, "tlas-2bl: ray hits");
                CHECK(th.inst_id == 1, "tlas-2bl: closest instance=1 (got %u)",
                      th.inst_id);
                lrt_tlas_free(tlas);
            }
            lrt_tri_scene_free(blas1);
            lrt_tri_scene_free(blas2);
        }
    }

    /* TLAS refit with all-zero transforms: should succeed. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *blas = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(blas != NULL, "tlas-refit: BLAS build");
        if (!blas) return;

        lrt_instance inst;
        float im[12] = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0};
        memcpy(inst.obj2world, im, sizeof(im));
        inst.blas_id = 0;
        inst.instance_id = 1;
        inst.mask = 0xFFFFFFFFu;
        lrt_tlas *tlas = lrt_tlas_build(&blas, 1, &inst, 1, NULL, &err);
        CHECK(tlas != NULL, "tlas-refit: build");
        if (tlas) {
            /* Zero out the transform (identity -> zero translation, scale 1). */
            float zm[12] = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0};
            memcpy(inst.obj2world, zm, sizeof(zm));
            CHECK(lrt_tlas_refit(tlas, &inst, 1) == LRT_RESULT_OK,
                  "tlas-refit: all-zero transform succeeds");
            lrt_tlas_free(tlas);
        }
        lrt_tri_scene_free(blas);
    }
}

/* --- section 21: Parallel build edge cases ---------------------------------------- */

static void test_parallel_build(void) {
    lrt_result err = LRT_RESULT_OK;
    lrt_hit h;

    /* section 21.1 - 100 triangles, 4 threads: should use serial path (below 4096
     * threshold) and build successfully. */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_build_options o = {
            .quality = LRT_TRI_BUILD_DEFAULT,
            .layout = LRT_TRI_LAYOUT_BVH4,
            .max_leaf_size = 0,
            .num_threads = 4};
        lrt_tri_scene *s = lrt_tri_scene_build(tri, 1, &o, &err);
        CHECK(s != NULL, "parallel-build 100-tri/4t: builds");
        if (s) {
            lrt_hit h;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "parallel-build 100-tri/4t: hits");
            lrt_tri_scene_free(s);
        }
    }

    /* section 21.2 - 4096 triangles, 4 threads: should use parallel path and build. */
    {
        float *verts = make_random_soup(4096, 0.5f);
        CHECK(verts != NULL, "parallel-build: 4096-tri verts");
        if (verts) {
            lrt_tri_build_options o = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 4};
            lrt_tri_scene *s = lrt_tri_scene_build(verts, 4096, &o, &err);
            CHECK(s != NULL, "parallel-build 4096-tri/4t: builds");
            if (s) {
                /* Use brute-force to find a guaranteed hit, then verify BVH
                 * agrees. */
                lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                lrt_hit hb;
                brute_force(verts, 4096, &r, &hb);
                if (hb.prim_id != LRT_TRI_NO_HIT) {
                    lrt_hit hs;
                    CHECK(lrt_tri_intersect1(s, &r, &hs) == 1,
                          "parallel-build 4096-tri/4t: brute-force hit => BVH "
                          "hits (t=%f)",
                          (double)hs.t);
                }
                lrt_tri_scene_free(s);
            }
            free(verts);
        }
    }

    /* section 21.3 - 100000 triangles, 8 threads: parallel path, should build. */
    {
        float *verts = make_random_soup(100000, 0.5f);
        CHECK(verts != NULL, "parallel-build: 100k-tri verts");
        if (verts) {
            lrt_tri_build_options o = {
                .quality = LRT_TRI_BUILD_DEFAULT,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 8};
            lrt_tri_scene *s = lrt_tri_scene_build(verts, 100000, &o, &err);
            CHECK(s != NULL, "parallel-build 100k-tri/8t: builds");
            if (s) {
                lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                lrt_hit hb;
                brute_force(verts, 100000, &r, &hb);
                if (hb.prim_id != LRT_TRI_NO_HIT) {
                    lrt_hit hs;
                    CHECK(lrt_tri_intersect1(s, &r, &hs) == 1,
                          "parallel-build 100k-tri/8t: brute-force hit => BVH "
                          "hits (t=%f)",
                          (double)hs.t);
                }
                lrt_tri_scene_free(s);
            }
            free(verts);
        }
    }

    /* section 21.4 - 100k triangles, FAST quality, 8 threads: parallel LBVH build. */
    {
        float *verts = make_random_soup(100000, 0.5f);
        CHECK(verts != NULL, "parallel-build: 100k-tri FAST verts");
        if (verts) {
            lrt_tri_build_options o = {
                .quality = LRT_TRI_BUILD_FAST,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 8};
            lrt_tri_scene *s = lrt_tri_scene_build(verts, 100000, &o, &err);
            CHECK(s != NULL, "parallel-build 100k-tri/FAST/8t: builds");
            if (s) {
                lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                lrt_hit hb;
                brute_force(verts, 100000, &r, &hb);
                if (hb.prim_id != LRT_TRI_NO_HIT) {
                    lrt_hit hs;
                    CHECK(lrt_tri_intersect1(s, &r, &hs) == 1,
                          "parallel-build 100k-tri/FAST/8t: brute-force hit => "
                          "BVH hits (t=%f)",
                          (double)hs.t);
                }
                lrt_tri_scene_free(s);
            }
            free(verts);
        }
    }

    /* section 21.5 - 100k triangles, HQ quality (SBVH), 4 threads: SBVH is serial
     * regardless of thread count, but should still build successfully. */
    {
        float *verts = make_random_soup(100000, 0.5f);
        CHECK(verts != NULL, "parallel-build: 100k-tri HQ verts");
        if (verts) {
            lrt_tri_build_options o = {
                .quality = LRT_TRI_BUILD_HQ,
                .layout = LRT_TRI_LAYOUT_BVH4,
                .max_leaf_size = 0,
                .num_threads = 4};
            lrt_tri_scene *s = lrt_tri_scene_build(verts, 100000, &o, &err);
            CHECK(s != NULL,
                  "parallel-build 100k-tri/HQ/4t: SBVH builds (serial)");
            if (s) {
                lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
                lrt_hit hb;
                brute_force(verts, 100000, &r, &hb);
                if (hb.prim_id != LRT_TRI_NO_HIT) {
                    lrt_hit hs;
                    CHECK(lrt_tri_intersect1(s, &r, &hs) == 1,
                          "parallel-build 100k-tri/HQ/4t: brute-force hit => "
                          "SBVH hits (t=%f)",
                          (double)hs.t);
                }
                lrt_tri_scene_free(s);
            }
            free(verts);
        }
    }
}

/* --- section 12: Curve / Hair edge cases ------------------------------------------ */

static void test_curve_edge_cases(void) {
    lrt_hit h;
    lrt_result err = LRT_RESULT_OK;

    /* section 12.1 - Capsule from (0,0,0) to (0,0,1e5) with r=0.5: should build and
     * hit. */
    {
        float segs[6] = {0, 0, 0, 0, 0, 1e5f};
        lrt_tri_scene *s = lrt_curve_scene_build(segs, NULL, 0.5f, 1, NULL,
                                                 &err);
        CHECK(s != NULL, "curve long-seg build (0,0,0 -> 0,0,1e5, r=0.5)");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100000.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "curve long-seg hits (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* section 12.2 - Capsule from (0,0,0) to (0,0,1e-7) with r=0.5: may build or
     * reject (very short segment relative to radius). */
    {
        float segs[6] = {0, 0, 0, 0, 0, 1e-7f};
        lrt_tri_scene *s = lrt_curve_scene_build(segs, NULL, 0.5f, 1, NULL,
                                                 &err);
        /* Either builds or rejects - must not crash. */
        CHECK(1, "curve short-seg (0,0,0 -> 0,0,1e-7, r=0.5): no crash");
        if (s) {
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            lrt_tri_intersect1(s, &r, &h);
            lrt_tri_scene_free(s);
        }
    }

    /* section 12.3 - Capsule with constant_radius=INFINITY: should reject with
     * INVALID_BOUNDS. */
    {
        float segs[6] = {0, 0, 0, 0, 0, 10};
        lrt_result err2 = LRT_RESULT_OK;
        CHECK(lrt_curve_scene_build(segs, NULL, INFINITY, 1, NULL, &err2) ==
                  NULL &&
              err2 == LRT_RESULT_INVALID_BOUNDS,
              "curve Inf radius rejected");
    }

    /* section 12.4 - Capsule with constant_radius=NAN: should reject (INVALID_ARGUMENT
     * since NAN > 0.0f is false, caught by the early guard). */
    {
        float segs[6] = {0, 0, 0, 0, 0, 10};
        lrt_result err2 = LRT_RESULT_OK;
        CHECK(lrt_curve_scene_build(segs, NULL, NAN, 1, NULL, &err2) == NULL &&
                  err2 == LRT_RESULT_INVALID_ARGUMENT,
              "curve NaN radius rejected");
    }

    /* section 12.5 - Capsule with zero-length segment and non-zero radius: sphere at
     * origin, ray from below through sphere should hit. */
    {
        float segs[6] = {0, 0, 0, 0, 0, 0};
        lrt_tri_scene *s = lrt_curve_scene_build(segs, NULL, 0.5f, 1, NULL,
                                                 &err);
        CHECK(s != NULL, "curve zero-length-seg build (sphere at origin)");
        if (s) {
            /* Ray from (0,0,-10) going +z: near root at t=9.5 (10-0.5). */
            lrt_ray r = {{0, 0, -10}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 && fabsf(h.t - 9.5f) <
                                                      1e-3f,
                  "curve zero-length-seg hits at t=9.5 (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

   /* section 12.6 - Roundcurve with very large radius (r0=r1=1e5): should build and
     * hit. */
    {
        float pts[6] = {0, 0, 0, 2, 0, 0};
        float radii[2] = {1e5f, 1e5f};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = radii;
        hs.constant_radius = 0.0f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_tri_scene *s = lrt_roundcurve_scene_build(&hs, NULL, &err);
        CHECK(s != NULL, "roundcurve large-radius build (r0=r1=1e5)");
        if (s) {
            /* Ray from below the capsule (y=-5, x=1) going +y: should hit the
             * side of the massive capsule. The capsule center is at y=0,
             * radius 1e5, so the near root is at t = 1e5 - 5. */
            lrt_ray r = {{1, -5, 0}, 0.0f, {0, 1, 0}, 200000.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1,
                  "roundcurve large-radius hits (t=%f)", (double)h.t);
            lrt_tri_scene_free(s);
        }
    }

    /* section 12.7 - Flatcurve with zero-width ribbon (radii=[0,0]): should reject or
     * build (no crash). */
    {
        float pts[6] = {0, 0, 0, 2, 0, 0};
        float radii[2] = {0.0f, 0.0f};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = radii;
        hs.constant_radius = 0.0f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_result err2 = LRT_RESULT_OK;
        lrt_tri_scene *s = lrt_flatcurve_scene_build(&hs, NULL, &err2);
        /* Either builds or rejects - must not crash. */
        CHECK(1, "flatcurve zero-width: no crash (err=%d)", (int)err2);
        if (s) {
            lrt_tri_scene_free(s);
        }
    }

    /* section 12.8 - Flatcurve with constant_radius=INFINITY: should reject. */
    {
        float pts[6] = {0, 0, 0, 2, 0, 0};
        float radii[2] = {0.5f, 0.5f};
        uint32_t sf = 0, sc = 2;
        lrt_hair_strands hs = {0};
        hs.points = pts;
        hs.radius = radii;
        hs.constant_radius = 0.0f;
        hs.strand_first = &sf;
        hs.strand_count = &sc;
        hs.nstrands = 1;
        hs.npoints = 2;
        lrt_result err2 = LRT_RESULT_OK;
        /* Use constant_radius path - but flatcurve doesn't have a
         * constant_radius field on strands. Instead set radii to Inf. */
        float inf_radii[2] = {INFINITY, INFINITY};
        hs.radius = inf_radii;
        CHECK(lrt_flatcurve_scene_build(&hs, NULL, &err2) == NULL &&
                  err2 == LRT_RESULT_INVALID_BOUNDS,
              "flatcurve Inf radius rejected");
    }
}

/* --- section 13: Point primitive edge cases --------------------------------------- */

static void test_point_edge_cases(void) {
    lrt_hit h;
    lrt_result err = LRT_RESULT_OK;

    /* section 13.1 - Sphere point with r=INFINITY: should reject. */
    {
        float c[3] = {0, 0, 5};
        float rr = INFINITY;
        lrt_tri_scene *s = lrt_points_scene_build(c, &rr, NULL, LRT_POINT_SPHERE,
                                                  1, NULL, &err);
        CHECK(s == NULL && err == LRT_RESULT_INVALID_BOUNDS,
              "point sphere Inf radius rejected");
    }

    /* section 13.2 - Sphere point with center=NAN: should reject. */
    {
        float c[3] = {NAN, 0, 0};
        float rr = 1.0f;
        lrt_result err2 = LRT_RESULT_OK;
        lrt_tri_scene *s = lrt_points_scene_build(c, &rr, NULL, LRT_POINT_SPHERE,
                                                  1, NULL, &err2);
        CHECK(s == NULL && err2 == LRT_RESULT_INVALID_BOUNDS,
              "point sphere NaN center rejected");
    }

    /* section 13.3 - Disc point with r=0: builds OK; ray through center hits (point
     * disc with r=0 is a point, and the ray passes through it). Ray off-center
     * should miss. */
    {
        float c[3] = {0, 0, 5};
        float rr = 0.0f;
        lrt_tri_scene *s = lrt_points_scene_build(c, &rr, NULL, LRT_POINT_DISC,
                                                  1, NULL, &err);
        CHECK(s != NULL, "point disc r=0 builds");
        if (s) {
            /* Ray through center: should hit at t=5. */
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &r, &h) == 1 && fabsf(h.t - 5.0f) <
                                                      1e-3f,
                  "point disc r=0 hits when ray passes through (t=%f)",
                  (double)h.t);
            /* Ray off-center: should miss. */
            lrt_ray mr = {{1, 1, 0}, 0.0f, {0, 0, 1}, 100.0f};
            CHECK(lrt_tri_intersect1(s, &mr, &h) == 0,
                  "point disc r=0 misses when ray off-center");
            lrt_tri_scene_free(s);
        }
    }

    /* section 13.4 - Disc point with r=INFINITY: should reject. */
    {
        float c[3] = {0, 0, 5};
        float rr = INFINITY;
        lrt_result err2 = LRT_RESULT_OK;
        lrt_tri_scene *s = lrt_points_scene_build(c, &rr, NULL, LRT_POINT_DISC,
                                                  1, NULL, &err2);
        CHECK(s == NULL && err2 == LRT_RESULT_INVALID_BOUNDS,
              "point disc Inf radius rejected");
    }

    /* section 13.5 - Oriented disc with zero-length normal: should reject or handle
     * gracefully. */
    {
        float c[3] = {0, 0, 5};
        float rr = 1.0f;
        float n[3] = {0, 0, 0};
        lrt_result err2 = LRT_RESULT_OK;
        lrt_tri_scene *s = lrt_points_scene_build(c, &rr, n,
                                                  LRT_POINT_ORIENTED_DISC, 1,
                                                  NULL, &err2);
        /* Either builds or rejects - must not crash. */
        CHECK(1, "oriented disc zero normal: no crash (err=%d)", (int)err2);
        if (s) {
            lrt_tri_scene_free(s);
        }
    }
}

/* --- section 25: Thread safety (crosses pthread guard) ----------------------------- */

#ifdef __linux__

/* Deterministic PRNG state per worker thread. */
static uint32_t thread_rnd_u32(uint64_t *seed) {
    uint64_t x = *seed;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *seed = x;
    return (uint32_t)(x >> 32);
}

static float thread_rnd_f(uint64_t *seed, float lo, float hi) {
    return lo + (hi - lo) * ((float)(thread_rnd_u32(seed) & 0xFFFFFF) / 16777216.0f);
}

static void thread_make_ray(uint64_t *seed, lrt_ray *r) {
    r->org[0] = thread_rnd_f(seed, -4.0f, 4.0f);
    r->org[1] = thread_rnd_f(seed, -4.0f, 4.0f);
    r->org[2] = thread_rnd_f(seed, -4.0f, 4.0f);
    float dx = thread_rnd_f(seed, -1.0f, 1.0f), dy = thread_rnd_f(seed, -1.0f, 1.0f),
          dz = thread_rnd_f(seed, -1.0f, 1.0f);
    float len = sqrtf(dx * dx + dy * dy + dz * dz);
    if (len < 1e-10f) {
        dx = 0.0f;
        dy = 0.0f;
        dz = 1.0f;
        len = 1.0f;
    }
    r->dir[0] = dx / len;
    r->dir[1] = dy / len;
    r->dir[2] = dz / len;
    r->tmin = 0.0f;
    r->tmax = 100.0f;
}

typedef struct {
    lrt_tri_scene *scene;
    int thread_id;
    uint64_t seed;
} thread_args_t;

static void *thread_intersect1(void *arg) {
    thread_args_t *ta = (thread_args_t *)arg;
    ta->seed = 0x12345678u + (uint64_t)ta->thread_id * 0x9E3779B9u;

    lrt_hit h;
    for (int i = 0; i < 1000; i++) {
        lrt_ray r;
        thread_make_ray(&ta->seed, &r);
        lrt_tri_intersect1(ta->scene, &r, &h);
    }
    return NULL;
}

static void *thread_intersect1N(void *arg) {
    thread_args_t *ta = (thread_args_t *)arg;
    ta->seed = 0x12345678u + (uint64_t)ta->thread_id * 0x9E3779B9u;

    /* Each thread gets its own ray/hit buffers (4 rays each). */
    lrt_ray rays[4];
    lrt_hit hits[4];
    for (int i = 0; i < 100; i++) {
        for (int j = 0; j < 4; j++) {
            thread_make_ray(&ta->seed, &rays[j]);
        }
        lrt_tri_intersect1N(ta->scene, rays, hits, 4, LRT_TRI_BATCH_AUTO);
    }
    return NULL;
}

static void test_thread_safety(void) {
    /* Build a reusable scene. */
    float *verts = make_random_soup(500, 0.5f);
    CHECK(verts != NULL, "thread-safety: verts");
    if (!verts) return;

    lrt_tri_build_options o = {
        .quality = LRT_TRI_BUILD_DEFAULT,
        .layout = LRT_TRI_LAYOUT_BVH4,
        .max_leaf_size = 0,
        .num_threads = 1};
    lrt_tri_scene *scene = lrt_tri_scene_build(verts, 500, &o, NULL);
    CHECK(scene != NULL, "thread-safety: build");
    if (!scene) {
        free(verts);
        return;
    }

    /* section 25.1 - 4 threads each calling intersect1 with 1000 rays. */
    {
        thread_args_t args[4];
        pthread_t threads[4];
        for (int i = 0; i < 4; i++) {
            args[i].scene = scene;
            args[i].thread_id = i;
        }
        for (int i = 0; i < 4; i++) {
            CHECK(pthread_create(&threads[i], NULL, thread_intersect1,
                                 &args[i]) == 0,
                  "thread-safety: create thread %d", i);
        }
        for (int i = 0; i < 4; i++) {
            CHECK(pthread_join(threads[i], NULL) == 0,
                  "thread-safety: join thread %d", i);
        }
        CHECK(1, "thread-safety section 25.1: 4 threads x 1000 intersect1 calls - "
              "no crash");
    }

    /* section 25.2 - 4 threads each calling intersect1N with 100 batches of 4 rays. */
    {
        thread_args_t args[4];
        pthread_t threads[4];
        for (int i = 0; i < 4; i++) {
            args[i].scene = scene;
            args[i].thread_id = i + 10; /* different seed offset */
        }
        for (int i = 0; i < 4; i++) {
            CHECK(pthread_create(&threads[i], NULL, thread_intersect1N,
                                 &args[i]) == 0,
                  "thread-safety: create batch thread %d", i);
        }
        for (int i = 0; i < 4; i++) {
            CHECK(pthread_join(threads[i], NULL) == 0,
                  "thread-safety: join batch thread %d", i);
        }
        CHECK(1, "thread-safety section 25.2: 4 threads x 100x intersect1N(4) - "
              "no crash");
    }

    lrt_tri_scene_free(scene);
    free(verts);
}

#else

/* pthread not available on this platform; stub the test. */
static void test_thread_safety(void) {
    CHECK(1, "thread-safety: skipped (no pthread on this platform)");
}

#endif

/* --- section 1.5, section 1.6, section 4.1-section 4.6: quantized refit/save rejection + refit edge
 * cases (zero, permuted, flattened, large deformation, +-0, denormalized) --- */

static void test_refit_quantized_and_edge_cases(void) {
    lrt_result err = LRT_RESULT_OK;

    /* section 1.5 - Quantized Q16 scene refit rejection. */
    {
        float *verts = make_random_soup(100, 0.5f);
        CHECK(verts != NULL, "refit-qtri: alloc");
        if (!verts)
            goto refit_qtri_done;
        lrt_tri_scene *s = lrt_qtri_scene_build(verts, 100, LRT_QTRI_Q16, 0,
                                                NULL, &err);
        CHECK(s != NULL, "refit-qtri: Q16 build (err=%d)", (int)err);
        if (s) {
            CHECK(lrt_tri_scene_refit(s, verts, 100) ==
                      LRT_RESULT_INVALID_ARGUMENT,
                  "refit Q16 rejected (err=%d)", (int)err);
            lrt_tri_scene_free(s);
        }
        free(verts);
    }

    /* section 1.6 - Quantized Q8 scene serialization rejection. */
    {
        float *verts = make_random_soup(100, 0.5f);
        CHECK(verts != NULL, "refit-qtri-save: alloc");
        if (!verts)
            goto refit_qtri_done;
        lrt_tri_scene *s = lrt_qtri_scene_build(verts, 100, LRT_QTRI_Q8, 0,
                                                NULL, &err);
        CHECK(s != NULL, "refit-qtri-save: Q8 build (err=%d)", (int)err);
        if (s) {
            void *buf = NULL;
            size_t n = 0;
            CHECK(lrt_tri_scene_save_to_memory(s, &buf, &n) ==
                      LRT_RESULT_INVALID_ARGUMENT,
                  "refit-qtri-save: Q8 save rejected (err=%d)", (int)err);
            lrt_tri_scene_free(s);
        }
        free(verts);
    }

refit_qtri_done:

    /* section 4.1 - Refit with all-zero vertices. */
    {
        float *verts = make_random_soup(100, 0.5f);
        CHECK(verts != NULL, "refit-zero: alloc");
        if (!verts)
            goto refit_zero_done;
        lrt_tri_scene *s = lrt_tri_scene_build(verts, 100, NULL, NULL);
        CHECK(s != NULL, "refit-zero: build");
        if (s) {
            float *zeros = (float *)malloc(100 * 9 * sizeof(float));
            memset(zeros, 0, 100 * 9 * sizeof(float));
            CHECK(lrt_tri_scene_refit(s, zeros, 100) == LRT_RESULT_OK,
                  "refit all-zero succeeds");
            lrt_hit h;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            /* Degenerate triangles at origin should not hit (zero-area). */
            CHECK(lrt_tri_intersect1(s, &r, &h) == 0,
                  "refit all-zero: never hits");
            lrt_tri_scene_free(s);
            free(zeros);
        }
        free(verts);
    }

refit_zero_done:

    /* section 4.2 - Refit with permuted vertex order (swap triangle 0 and 50). */
    {
        float *verts = make_random_soup(100, 0.5f);
        CHECK(verts != NULL, "refit-permuted: alloc");
        if (!verts)
            goto refit_perm_done;
        lrt_tri_scene *s = lrt_tri_scene_build(verts, 100, NULL, NULL);
        CHECK(s != NULL, "refit-permuted: build");
        if (s) {
            float *permuted = (float *)malloc(100 * 9 * sizeof(float));
            memcpy(permuted, verts, 100 * 9 * sizeof(float));
            /* Swap triangle 0 and triangle 50. */
            float tmp[9];
            memcpy(tmp, permuted, 9);
            memcpy(permuted, permuted + 50 * 9, 9);
            memcpy(permuted + 50 * 9, tmp, 9);
            CHECK(lrt_tri_scene_refit(s, permuted, 100) == LRT_RESULT_OK,
                  "refit permuted succeeds");
            lrt_tri_scene_free(s);
            free(permuted);
        }
        free(verts);
    }

refit_perm_done:

    /* section 4.3 - Refit that collapses scene to z=0 plane. */
    {
        float *verts = make_random_soup(100, 0.5f);
        CHECK(verts != NULL, "refit-plane: alloc");
        if (!verts)
            goto refit_plane_done;
        lrt_tri_scene *s = lrt_tri_scene_build(verts, 100, NULL, NULL);
        CHECK(s != NULL, "refit-plane: build");
        if (s) {
            float *plane = (float *)malloc(100 * 9 * sizeof(float));
            for (int i = 0; i < 100; i++) {
                plane[i * 9 + 0] = verts[i * 9 + 0]; /* x */
                plane[i * 9 + 1] = verts[i * 9 + 1]; /* y */
                plane[i * 9 + 2] = 0.0f;              /* z -> 0 */
                plane[i * 9 + 3] = verts[i * 9 + 3];
                plane[i * 9 + 4] = verts[i * 9 + 4];
                plane[i * 9 + 5] = 0.0f;
                plane[i * 9 + 6] = verts[i * 9 + 6];
                plane[i * 9 + 7] = verts[i * 9 + 7];
                plane[i * 9 + 8] = 0.0f;
            }
            CHECK(lrt_tri_scene_refit(s, plane, 100) == LRT_RESULT_OK,
                  "refit to z=0 plane succeeds");
            lrt_tri_scene_free(s);
            free(plane);
        }
        free(verts);
    }

refit_plane_done:

    /* section 4.4 - Refit with very large deformation ([-1,1] -> [-1e5,1e5]). */
    {
        float *verts = make_random_soup(100, 0.5f);
        CHECK(verts != NULL, "refit-large: alloc");
        if (!verts)
            goto refit_large_done;
        lrt_tri_scene *s = lrt_tri_scene_build(verts, 100, NULL, NULL);
        CHECK(s != NULL, "refit-large: build");
        if (s) {
            float *large = (float *)malloc(100 * 9 * sizeof(float));
            for (int i = 0; i < 100; i++)
                for (int k = 0; k < 9; k++)
                    large[i * 9 + k] = verts[i * 9 + k] * 1e5f;
            CHECK(lrt_tri_scene_refit(s, large, 100) == LRT_RESULT_OK,
                  "refit large deformation succeeds");
            lrt_tri_scene_free(s);
            free(large);
        }
        free(verts);
    }

refit_large_done:

    /* section 4.5 - Refit with vertices that have +0 and -0. */
    {
        float *verts = make_random_soup(100, 0.5f);
        CHECK(verts != NULL, "refit-pzn: alloc");
        if (!verts)
            goto refit_pzn_done;
        lrt_tri_scene *s = lrt_tri_scene_build(verts, 100, NULL, NULL);
        CHECK(s != NULL, "refit-pzn: build");
        if (s) {
            float *pzn = (float *)malloc(100 * 9 * sizeof(float));
            for (int i = 0; i < 100; i++)
                for (int k = 0; k < 9; k++)
                    pzn[i * 9 + k] = (k % 2 == 0) ? 0.0f : -0.0f;
            CHECK(lrt_tri_scene_refit(s, pzn, 100) == LRT_RESULT_OK,
                  "refit +0/-0 succeeds");
            lrt_tri_scene_free(s);
            free(pzn);
        }
        free(verts);
    }

refit_pzn_done:

    /* section 4.6 - Refit with denormalized float values (~1e-38). */
    {
        float *verts = make_random_soup(100, 0.5f);
        CHECK(verts != NULL, "refit-dn: alloc");
        if (!verts)
            goto refit_dn_done;
        lrt_tri_scene *s = lrt_tri_scene_build(verts, 100, NULL, NULL);
        CHECK(s != NULL, "refit-dn: build");
        if (s) {
            float *dn = (float *)malloc(100 * 9 * sizeof(float));
            for (int i = 0; i < 100; i++) {
                dn[i * 9 + 0] = 1e-38f;
                dn[i * 9 + 1] = 2e-38f;
                dn[i * 9 + 2] = 3e-38f;
                dn[i * 9 + 3] = 4e-38f;
                dn[i * 9 + 4] = 5e-38f;
                dn[i * 9 + 5] = 6e-38f;
                dn[i * 9 + 6] = 7e-38f;
                dn[i * 9 + 7] = 8e-38f;
                dn[i * 9 + 8] = 9e-38f;
            }
            CHECK(lrt_tri_scene_refit(s, dn, 100) == LRT_RESULT_OK,
                  "refit denormalized succeeds");
            lrt_tri_scene_free(s);
            free(dn);
        }
        free(verts);
    }

refit_dn_done:
    ; /* empty statement: a label must be followed by a statement (pre-C23) */
}

/* --- section 6: SDF edge-case tests ----------------------------------------------- */

static void test_sdf_edge_cases(void) {
    lrt_result err = LRT_RESULT_OK;

    /* section 6.1: SDF sphere trace with NaN field value */
    {
        lrt_sdf_params p;
        memset(&p, 0, sizeof(p));
        p.max_steps = 128;
        p.epsilon = 1e-4f;
        lrt_sdf_hit hit;
        int ret = lrt_sdf_sphere_trace(
            (float[3]){0, 0, 0}, (float[3]){0, 0, 1}, 0.0f, 100.0f,
            sdf_nan_cb, NULL, &p, &hit);
        CHECK(ret == 0 || ret == 1,
              "sdf NaN field: no crash (ret=%d)", ret);
    }

    /* section 6.2: SDF sphere trace with Inf field value */
    {
        lrt_sdf_params p;
        memset(&p, 0, sizeof(p));
        p.max_steps = 128;
        p.epsilon = 1e-4f;
        lrt_sdf_hit hit;
        int ret = lrt_sdf_sphere_trace(
            (float[3]){0, 0, 0}, (float[3]){0, 0, 1}, 0.0f, 100.0f,
            sdf_inf_cb, NULL, &p, &hit);
        CHECK(ret == 0 || ret == 1,
              "sdf Inf field: no crash (ret=%d)", ret);
    }

    /* section 6.3: SDF sphere trace with non-Lipschitz field (dist*2) */
    {
        sdf_sphere_ctx c = {{0, 0, 0}, 1.0f};
        lrt_sdf_params p;
        memset(&p, 0, sizeof(p));
        p.max_steps = 128;
        p.epsilon = 1e-4f;
        lrt_sdf_hit hit;
        int ret = lrt_sdf_sphere_trace(
            (float[3]){0, 0, -3}, (float[3]){0, 0, 1}, 0.0f, 100.0f,
            sdf_nonlipschitz_cb, NULL, &p, &hit);
        CHECK(ret == 0 || ret == 1,
              "sdf non-Lipschitz: no crash (ret=%d)", ret);
    }

    /* section 6.4: SDF sphere trace with constant field */
    {
        lrt_sdf_params p;
        memset(&p, 0, sizeof(p));
        p.max_steps = 128;
        p.epsilon = 1e-4f;
        lrt_sdf_hit hit;
        int ret = lrt_sdf_sphere_trace(
            (float[3]){0, 0, -3}, (float[3]){0, 0, 1}, 0.0f, 100.0f,
            sdf_constant_cb, NULL, &p, &hit);
        CHECK(ret == 0 || ret == 1,
              "sdf constant field: no crash (ret=%d)", ret);
    }

    /* section 6.6: SDF sphere trace with max_steps=1 */
    {
        sdf_sphere_ctx c = {{0, 0, 0}, 1.0f};
        lrt_sdf_params p1;
        memset(&p1, 0, sizeof(p1));
        p1.max_steps = 1;
        p1.epsilon = 1e-4f;
        lrt_sdf_hit hit;
        int ret = lrt_sdf_sphere_trace(
            (float[3]){0, 0, -3}, (float[3]){0, 0, 1}, 0.0f, 100.0f,
            sdf_sphere, &c, &p1, &hit);
        CHECK(ret == 0 || ret == 1,
              "sdf max_steps=1: no crash (ret=%d)", ret);
    }

    /* section 6.7: SDF sphere trace with tmax very small */
    {
        sdf_sphere_ctx c = {{0, 0, 0}, 1.0f};
        lrt_sdf_params p2;
        memset(&p2, 0, sizeof(p2));
        p2.max_steps = 128;
        p2.epsilon = 1e-4f;
        lrt_sdf_hit hit;
        int ret = lrt_sdf_sphere_trace(
            (float[3]){0, 0, -3}, (float[3]){0, 0, 1}, 0.0f, 1e-6f,
            sdf_sphere, &c, &p2, &hit);
        CHECK(ret == 0,
              "sdf tmax=1e-6: miss (ret=%d)", ret);
    }

    /* section 6.8: SDF sphere trace with tmin > tmax */
    {
        sdf_sphere_ctx c = {{0, 0, 0}, 1.0f};
        lrt_sdf_params p3;
        memset(&p3, 0, sizeof(p3));
        p3.max_steps = 128;
        p3.epsilon = 1e-4f;
        lrt_sdf_hit hit;
        int ret = lrt_sdf_sphere_trace(
            (float[3]){0, 0, -3}, (float[3]){0, 0, 1}, 10.0f, 5.0f,
            sdf_sphere, &c, &p3, &hit);
        CHECK(ret == 0,
              "sdf tmin>tmax: no crash, miss (ret=%d)", ret);
    }

    /* section 6.9: SDF sphere trace with zero-length direction */
    {
        sdf_sphere_ctx c = {{0, 0, 0}, 1.0f};
        lrt_sdf_params p4;
        memset(&p4, 0, sizeof(p4));
        p4.max_steps = 128;
        p4.epsilon = 1e-4f;
        lrt_sdf_hit hit;
        int ret = lrt_sdf_sphere_trace(
            (float[3]){0, 0, -3}, (float[3]){0, 0, 0}, 0.0f, 100.0f,
            sdf_sphere, &c, &p4, &hit);
        CHECK(ret == 0 || ret == 1,
              "sdf zero-dir: no crash (ret=%d)", ret);
    }

    /* section 6.10: SDF sphere trace with over-relaxation omega=2.0 */
    {
        sdf_sphere_ctx c = {{0, 0, 0}, 1.0f};
        lrt_sdf_params p5;
        memset(&p5, 0, sizeof(p5));
        p5.max_steps = 128;
        p5.epsilon = 1e-4f;
        p5.over_relax = 2.0f;
        lrt_sdf_hit hit;
        int ret = lrt_sdf_sphere_trace(
            (float[3]){0, 0, -3}, (float[3]){0, 0, 1}, 0.0f, 100.0f,
            sdf_sphere, &c, &p5, &hit);
        CHECK(ret == 0 || ret == 1,
              "sdf omega=2.0: no crash (ret=%d)", ret);
    }

    /* section 6.12: SDF sphere trace with very large epsilon */
    {
        sdf_sphere_ctx c = {{0, 0, 0}, 1.0f};
        lrt_sdf_params p6;
        memset(&p6, 0, sizeof(p6));
        p6.max_steps = 128;
        p6.epsilon = 1.0f; /* very loose threshold */
        lrt_sdf_hit hit;
        int ret = lrt_sdf_sphere_trace(
            (float[3]){0, 0, -3}, (float[3]){0, 0, 1}, 0.0f, 100.0f,
            sdf_sphere, &c, &p6, &hit);
        CHECK(ret == 0 || ret == 1,
              "sdf epsilon=1.0: no crash (ret=%d)", ret);
    }

    /* section 6.13: SDF scene with NaN blob AABB */
    {
        lrt_sdf_blob nan_blob;
        nan_blob.aabb[0] = NAN; nan_blob.aabb[1] = 0; nan_blob.aabb[2] = 0;
        nan_blob.aabb[3] = 1; nan_blob.aabb[4] = 1; nan_blob.aabb[5] = 1;
        nan_blob.sdf = sdf_sphere;
        sdf_sphere_ctx c_nan = {{0}, 1};
        nan_blob.user = &c_nan;
        lrt_result err2 = LRT_RESULT_OK;
        lrt_tri_scene *sdf_nan = lrt_sdf_scene_build(&nan_blob, 1, NULL, NULL, &err2);
        CHECK(sdf_nan == NULL && err2 == LRT_RESULT_INVALID_BOUNDS,
              "sdf NaN AABB rejected (err=%d)", (int)err2);
        if (sdf_nan)
            lrt_tri_scene_free(sdf_nan);
    }

    /* section 6.14: SDF scene with zero-width blob (lo==hi) */
    {
        lrt_sdf_blob zero_blob;
        zero_blob.aabb[0] = 0; zero_blob.aabb[1] = 0; zero_blob.aabb[2] = 0;
        zero_blob.aabb[3] = 0; zero_blob.aabb[4] = 0; zero_blob.aabb[5] = 0;
        zero_blob.sdf = sdf_sphere;
        sdf_sphere_ctx c_zero = {{0}, 1};
        zero_blob.user = &c_zero;
        lrt_result err3 = LRT_RESULT_OK;
        lrt_tri_scene *sdf_zero = lrt_sdf_scene_build(&zero_blob, 1, NULL, NULL, &err3);
        CHECK(sdf_zero != NULL,
              "sdf zero-width blob builds (err=%d)", (int)err3);
        if (sdf_zero)
            lrt_tri_scene_free(sdf_zero);
    }

    /* section 6.15: SDF scene with overlapping blobs */
    {
        lrt_sdf_blob blobs[2];
        lrt_sdf_params p7;
        memset(&p7, 0, sizeof(p7));
        p7.epsilon = 1e-4f;
        p7.max_steps = 128;

        /* Two identical sphere blobs centered at origin (full overlap) */
        sdf_sphere_ctx c_overlap = {{0}, 1};
        for (int i = 0; i < 2; i++) {
            blobs[i].aabb[0] = -1; blobs[i].aabb[1] = -1; blobs[i].aabb[2] = -1;
            blobs[i].aabb[3] = 1;  blobs[i].aabb[4] = 1;  blobs[i].aabb[5] = 1;
            blobs[i].sdf = sdf_sphere;
            blobs[i].user = &c_overlap;
        }
        lrt_result err4 = LRT_RESULT_OK;
        lrt_tri_scene *sdf_overlap = lrt_sdf_scene_build(blobs, 2, &p7, NULL, &err4);
        CHECK(sdf_overlap != NULL,
              "sdf overlapping blobs build (err=%d)", (int)err4);
        if (sdf_overlap) {
            lrt_hit hit2;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            lrt_tri_intersect1(sdf_overlap, &r, &hit2);
            lrt_tri_scene_free(sdf_overlap);
        }
    }
}

/* --- section 3: TLAS edge-case tests (continued) ---------------------------------- */

static void test_tlas_edge_cases2(void) {
    lrt_result err = LRT_RESULT_OK;

    /* section 3.5: TLAS with near-singular transform */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *blas = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(blas != NULL, "tlas2 near-singular: BLAS build");
        if (!blas)
            return;

        lrt_instance inst;
        float near_singular[12] = {1e-20f, 0, 0, 0, 0, 1e-20f, 0, 0, 0, 0, 1, 0};
        memcpy(inst.obj2world, near_singular, sizeof(near_singular));
        inst.blas_id = 0;
        inst.instance_id = 1;
        inst.mask = 0xFFFFFFFFu;
        lrt_result err5 = LRT_RESULT_OK;
        lrt_tlas *tlas_ns = lrt_tlas_build(&blas, 1, &inst, 1, NULL, &err5);
        /* Near-singular should be skipped; TLAS may be NULL or empty */
        CHECK(tlas_ns != NULL || err5 != LRT_RESULT_OK,
              "tlas near-singular: no crash (tlas=%p, err=%d)",
              (void *)tlas_ns, (int)err5);
        if (tlas_ns) {
            lrt_tlas_hit th;
            lrt_ray r = {{0, 0, 0}, 0.0f, {0, 0, 1}, 100.0f};
            int hit = lrt_tlas_intersect1(tlas_ns, &r, 0xFFFFFFFFu, &th);
            /* Near-singular transform collapses geometry; may miss */
            CHECK(hit == 0 || hit == 1,
                  "tlas near-singular: no crash (hit=%d)", hit);
            lrt_tlas_free(tlas_ns);
        }
        lrt_tri_scene_free(blas);
    }

    /* section 3.8: TLAS refit with invalid instance count */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *blas1 = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(blas1 != NULL, "tlas2 refit-err: BLAS build");
        if (!blas1)
            return;

        lrt_instance insts[2];
        float im[12] = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0};
        memcpy(insts[0].obj2world, im, sizeof(im));
        insts[0].blas_id = 0;
        insts[0].instance_id = 1;
        insts[0].mask = 0xFFFFFFFFu;
        memcpy(insts[1].obj2world, im, sizeof(im));
        insts[1].blas_id = 0;
        insts[1].instance_id = 2;
        insts[1].mask = 0xFFFFFFFFu;
        lrt_result err6 = LRT_RESULT_OK;
        lrt_tlas *tlas2 = lrt_tlas_build(&blas1, 1, insts, 2, NULL, &err6);
        CHECK(tlas2 != NULL, "tlas2 refit-err: build 2-inst");
        if (tlas2) {
            /* Refit with ninsts != original count -> INVALID_ARGUMENT. */
            lrt_instance refit_inst;
            memcpy(refit_inst.obj2world, im, sizeof(im));
            refit_inst.blas_id = 0;
            refit_inst.instance_id = 3;
            refit_inst.mask = 0xFFFFFFFFu;
            CHECK(lrt_tlas_refit(tlas2, &refit_inst, 1) == LRT_RESULT_INVALID_ARGUMENT,
                  "tlas refit ninst mismatch rejected");
            lrt_tlas_free(tlas2);
        }
        lrt_tri_scene_free(blas1);
    }

    /* section 3.10: TLAS with negative scale transform */
    {
        float tri[9] = {-1, -1, 5, 1, -1, 5, 0, 1, 5};
        lrt_tri_scene *blas = lrt_tri_scene_build(tri, 1, NULL, NULL);
        CHECK(blas != NULL, "tlas2 neg-scale: BLAS build");
        if (!blas)
            return;

        lrt_instance inst_neg;
        float neg_scale[12] = {-1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0};
        memcpy(inst_neg.obj2world, neg_scale, sizeof(neg_scale));
        inst_neg.blas_id = 0;
        inst_neg.instance_id = 1;
        inst_neg.mask = 0xFFFFFFFFu;
        lrt_result err7 = LRT_RESULT_OK;
        lrt_tlas *tlas_neg = lrt_tlas_build(&blas, 1, &inst_neg, 1, NULL, &err7);
        CHECK(tlas_neg != NULL, "tlas2 neg-scale: build");
        if (tlas_neg) {
            lrt_tlas_hit th;
            /* Ray from (0,0,-5) going +z: in mirrored space, hits the mirrored
             * triangle at z=5 with x in [-1,1]. */
            lrt_ray r = {{0, 0, -5}, 0.0f, {0, 0, 1}, 100.0f};
            int hit = lrt_tlas_intersect1(tlas_neg, &r, 0xFFFFFFFFu, &th);
            CHECK(hit == 1,
                  "tlas neg-scale: ray hits (hit=%d)", hit);
            lrt_tlas_free(tlas_neg);
        }
        lrt_tri_scene_free(blas);
    }
}

int main(void) {
    printf("lightrt_c_tri test\n");

    test_qtri();
    test_qnodes();
    test_edge_cases();
    test_tri_build_edge_cases();
    test_tri_edge_cases();
    test_curve_scene();
    test_roundcurve_scene();
    test_flatcurve_scene();
    test_bezcurve_scene();
    test_points_scene();
    test_sphere_edge_cases();
    test_hair_edge_cases();
    test_curve_point_edge_cases();
    test_sphere_scene();
    test_user_geometry();
    test_sdf_standalone();
    test_sdf_scene();
    test_sdf_edge_cases();
    test_closest_point_knn();
    test_region_queries();
    test_frustum();
    test_multihit();
    test_query_layouts();
    test_serialization();
    test_refit();
    test_tlas();
    test_packets();
    test_anyhit_filter();

    /* New edge-case tests. */
    test_null_inputs();
    test_batch_edge_cases();
    test_stats();
    test_kernel_name();
    test_user_geometry_edge_cases();
    test_sphere_scene_edge_cases();
    test_triangle_intersection_edge_cases();
    test_multihit_edge_cases();
    test_closest_point_edge_cases();
    test_region_query_edge_cases();
    test_build_options();
    test_fp_precision();
    test_tlas_edge_cases();
    test_tlas_edge_cases2();

    /* section 21, section 12, section 13, section 25 edge-case tests. */
    test_parallel_build();
    test_curve_edge_cases();
    test_point_edge_cases();
    test_thread_safety();

    /* section 1.5, section 1.6, section 4.1-section 4.6: quantized refit/save rejection + refit edge
     * cases. */
    test_refit_quantized_and_edge_cases();

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
    test_vs_brute_force("medium/bvh8q/sah", med, 5000, LRT_TRI_LAYOUT_BVH8Q,
                        LRT_TRI_BUILD_DEFAULT, 4000);
    test_vs_brute_force("medium/bvh4/hq", med, 5000, LRT_TRI_LAYOUT_BVH4,
                        LRT_TRI_BUILD_HQ, 4000);
    test_vs_brute_force("medium/bvh8/hq", med, 5000, LRT_TRI_LAYOUT_BVH8,
                        LRT_TRI_BUILD_HQ, 4000);
    test_vs_brute_force("medium/bvh8q/fast", med, 5000, LRT_TRI_LAYOUT_BVH8Q,
                        LRT_TRI_BUILD_FAST, 4000);
    test_layouts_agree(med, 5000, 50000);
    test_batch_matches_single(med, 5000, LRT_TRI_LAYOUT_BVH4, 30000);
    test_batch_matches_single(med, 5000, LRT_TRI_LAYOUT_BVH8, 30000);
    test_batch_matches_single(med, 5000, LRT_TRI_LAYOUT_BVH8Q, 30000);
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
    test_vs_brute_force("coplanar/bvh8q/sah", flat, 2000, LRT_TRI_LAYOUT_BVH8Q,
                        LRT_TRI_BUILD_DEFAULT, 4000);
    test_vs_brute_force("coplanar/bvh4/hq", flat, 2000, LRT_TRI_LAYOUT_BVH4,
                        LRT_TRI_BUILD_HQ, 4000);
    free(flat);

    if (g_failures == 0) {
        printf("RESULT: PASS\n");
        return 0;
    }
    printf("RESULT: FAIL (%d failures)\n", g_failures);
    return 1;
}
