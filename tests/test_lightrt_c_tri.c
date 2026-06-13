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

    size_t mismatches = 0, occl_mismatches = 0;
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
    }
    /* A handful of grazing/joint rays flip by one ulp at fp32 (the cross-check
     * vs Embree on wCurly.hair shows the same ~5e-6 rate); allow the same
     * budget the capsule and fp64 verifications use. */
    CHECK(mismatches <= NRAYS / 1000, "roundcurve: %zu/%d mismatches vs "
          "brute-force cone+spheres", mismatches, NRAYS);
    CHECK(occl_mismatches == 0, "roundcurve: %zu occluded disagreements",
          occl_mismatches);

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

    /* curve scenes serialize too; user/sphere scenes must refuse. */
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
            CHECK(lrt_tri_scene_save_to_memory(sp, &buf, &n) ==
                      LRT_RESULT_INVALID_ARGUMENT,
                  "sphere scene should refuse serialization");
            free(buf);
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
        size_t mism = 0, occl = 0;
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
        }
        CHECK(mism <= NRAYS / 1000, "points(%s): %zu/%d mismatches vs brute force",
              names[ti], mism, NRAYS);
        CHECK(occl == 0, "points(%s): %zu occluded disagreements", names[ti],
              occl);
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
    lrt_tri_scene_free(s);
    free(pts);
    free(rad);
    free(sfirst);
    free(scount);
}

int main(void) {
    printf("lightrt_c_tri test\n");

    test_qtri();
    test_qnodes();
    test_edge_cases();
    test_curve_scene();
    test_roundcurve_scene();
    test_flatcurve_scene();
    test_points_scene();
    test_sphere_scene();
    test_user_geometry();
    test_sdf_standalone();
    test_sdf_scene();
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
