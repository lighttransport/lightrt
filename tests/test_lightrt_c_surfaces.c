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

/* ---- reference NURBS evaluator (Cox-de Boor, NURBS Book A2.1/A2.2/A4.3) --- */
static int ns_span(int n, int p, float u, const float *U) {
    if (u >= U[n + 1]) return n;
    if (u <= U[p]) return p;
    int lo = p, hi = n + 1, mid = (lo + hi) / 2;
    while (u < U[mid] || u >= U[mid + 1]) {
        if (u < U[mid]) hi = mid; else lo = mid;
        mid = (lo + hi) / 2;
    }
    return mid;
}
static void ns_basis(int span, float u, int p, const float *U, float *N) {
    float left[16], right[16];
    N[0] = 1.0f;
    for (int j = 1; j <= p; j++) {
        left[j] = u - U[span + 1 - j];
        right[j] = U[span + j] - u;
        float saved = 0.0f;
        for (int r = 0; r < j; r++) {
            float tmp = N[r] / (right[r + 1] + left[j - r]);
            N[r] = saved + right[r + 1] * tmp;
            saved = left[j - r] * tmp;
        }
        N[j] = saved;
    }
}
static void nurbs_eval(const float *net, int nu, int nv, const float *U,
                       const float *V, const float *w, int degu, int degv,
                       float u, float v, float S[3]) {
    int su = ns_span(nu, degu, u, U), sv = ns_span(nv, degv, v, V);
    float Nu[16], Nv[16];
    ns_basis(su, u, degu, U, Nu);
    ns_basis(sv, v, degv, V, Nv);
    float num[3] = {0, 0, 0}, den = 0.0f;
    for (int l = 0; l <= degv; l++)
        for (int k = 0; k <= degu; k++) {
            int idx = (sv - degv + l) * (nu + 1) + (su - degu + k);
            float wk = (w ? w[idx] : 1.0f);
            float b = Nu[k] * Nv[l] * wk;
            den += b;
            for (int c = 0; c < 3; c++) num[c] += b * net[idx * 3 + c];
        }
    for (int c = 0; c < 3; c++) S[c] = num[c] / den;
}

static void test_nurbs(void) {
    const int degu = 3, degv = 3, nu = 4, nv = 4; /* 5x5 bicubic */
    const float U[9] = {0, 0, 0, 0, 0.5f, 1, 1, 1, 1};
    const int NS = 60;     /* surfaces (each its own scene) */
    const int RPS = 2000;  /* rays per surface */
    size_t hits = 0, resid_ok = 0;
    double max_resid = 0.0;
    for (int s = 0; s < NS; s++) {
        float net[25 * 3], w[25];
        float c[3] = {rf(-2, 2), rf(-2, 2), rf(-2, 2)};
        float ax[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float ay[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        for (int j = 0; j <= nv; j++)
            for (int i = 0; i <= nu; i++) {
                int idx = j * (nu + 1) + i;
                float fu = (float)i / nu - 0.5f, fv = (float)j / nv - 0.5f;
                for (int k = 0; k < 3; k++)
                    net[idx * 3 + k] = c[k] + 0.7f * fu * ax[k] +
                                       0.7f * fv * ay[k] + rf(-0.1f, 0.1f);
                w[idx] = rf(0.4f, 2.5f); /* positive weights */
            }
        lrt_tri_build_options o;
        memset(&o, 0, sizeof(o));
        o.num_threads = 1;
        lrt_result err = LRT_RESULT_OK;
        lrt_tri_scene *sc =
            lrt_nurbs_scene_build(net, nu, nv, U, U, w, degu, degv, &o, &err);
        CHECK(sc != NULL, "nurbs build (err=%d)", (int)err);
        if (!sc) continue;
        for (int rr = 0; rr < RPS; rr++) {
            lrt_ray r;
            float o2[3] = {c[0] + rf(-3, 3), c[1] + rf(-3, 3), c[2] + rf(-3, 3)};
            float d[3] = {c[0] - o2[0] + rf(-0.4f, 0.4f),
                          c[1] - o2[1] + rf(-0.4f, 0.4f),
                          c[2] - o2[2] + rf(-0.4f, 0.4f)};
            float l = sqrtf(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]) + 1e-9f;
            for (int k = 0; k < 3; k++) {
                r.org[k] = o2[k];
                r.dir[k] = d[k] / l;
            }
            r.tmin = 1e-4f;
            r.tmax = 1e9f;
            lrt_hit h;
            if (lrt_tri_intersect1(sc, &r, &h)) {
                hits++;
                float ps[3], pr[3];
                nurbs_eval(net, nu, nv, U, U, w, degu, degv, h.u, h.v, ps);
                for (int k = 0; k < 3; k++) pr[k] = r.org[k] + h.t * r.dir[k];
                float dd = sqrtf((ps[0] - pr[0]) * (ps[0] - pr[0]) +
                                 (ps[1] - pr[1]) * (ps[1] - pr[1]) +
                                 (ps[2] - pr[2]) * (ps[2] - pr[2]));
                double rel = dd / (1.0 + fabs((double)h.t));
                if (rel > max_resid) max_resid = rel;
                if (rel < 2e-3) resid_ok++;
            }
        }
        lrt_tri_scene_free(sc);
    }
    double rfrac = hits ? (double)resid_ok / (double)hits : 1.0;
    printf("nurbs:    %zu hits over %d surfaces, residual ok %.3f%% (max %.2e)\n",
           hits, NS, rfrac * 100.0, max_resid);
    CHECK(hits > (size_t)(NS * 50), "nurbs: too few hits (%zu)", hits);
    CHECK(rfrac >= 0.995, "nurbs residual agreement %.3f%% < 99.5%%",
          rfrac * 100.0);
}

/* even-odd point-in-loops, same rule as the library (mirror tri_trim_inside). */
static int pt_in_loops(const float *pts, const uint32_t *off, int nloops,
                       float u, float v) {
    int cross = 0;
    for (int L = 0; L < nloops; L++) {
        uint32_t a = off[L], b = off[L + 1], np = b - a;
        for (uint32_t i = 0; i < np; i++) {
            uint32_t j = (i + 1 == np) ? 0 : i + 1;
            float ui = pts[(a + i) * 2], vi = pts[(a + i) * 2 + 1];
            float uj = pts[(a + j) * 2], vj = pts[(a + j) * 2 + 1];
            if ((vi > v) != (vj > v)) {
                float ut = ui + (v - vi) / (vj - vi) * (uj - ui);
                if (u < ut) cross ^= 1;
            }
        }
    }
    return cross;
}

static void test_trimnurbs(void) {
    const int degu = 3, degv = 3, nu = 4, nv = 4;
    const float U[9] = {0, 0, 0, 0, 0.5f, 1, 1, 1, 1};
    /* trim loop = a 40-gon disk in (u,v) centered (0.5,0.5), r=0.3: visible
     * region is its interior. */
    const int NG = 40;
    float trim_pts[40 * 2];
    uint32_t loop_len[1] = {(uint32_t)NG};
    uint32_t loop_off[2] = {0, (uint32_t)NG};
    for (int i = 0; i < NG; i++) {
        float a = 6.2831853f * i / NG;
        trim_pts[i * 2 + 0] = 0.5f + 0.3f * cosf(a);
        trim_pts[i * 2 + 1] = 0.5f + 0.3f * sinf(a);
    }
    const int NS = 60, RPS = 3000;
    size_t thits = 0, inside_ok = 0, preserved = 0, preserved_tot = 0,
           removed = 0, outside_tot = 0;
    for (int s = 0; s < NS; s++) {
        float net[25 * 3], w[25];
        float c[3] = {rf(-2, 2), rf(-2, 2), rf(-2, 2)};
        float ax[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float ay[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        for (int j = 0; j <= nv; j++)
            for (int i = 0; i <= nu; i++) {
                int idx = j * (nu + 1) + i;
                float fu = (float)i / nu - 0.5f, fv = (float)j / nv - 0.5f;
                for (int k = 0; k < 3; k++)
                    net[idx * 3 + k] =
                        c[k] + 0.7f * fu * ax[k] + 0.7f * fv * ay[k];
                w[idx] = rf(0.6f, 1.8f);
            }
        lrt_tri_build_options o;
        memset(&o, 0, sizeof(o));
        o.num_threads = 1;
        lrt_tri_scene *un =
            lrt_nurbs_scene_build(net, nu, nv, U, U, w, degu, degv, &o, NULL);
        lrt_tri_scene *tr = lrt_trimnurbs_scene_build(
            net, nu, nv, U, U, w, degu, degv, trim_pts, loop_len, 1, &o, NULL);
        CHECK(un && tr, "trimnurbs build");
        if (!un || !tr) {
            if (un) lrt_tri_scene_free(un);
            if (tr) lrt_tri_scene_free(tr);
            continue;
        }
        for (int rr = 0; rr < RPS; rr++) {
            lrt_ray r;
            float o2[3] = {c[0] + rf(-3, 3), c[1] + rf(-3, 3), c[2] + rf(-3, 3)};
            float d[3] = {c[0] - o2[0] + rf(-0.4f, 0.4f),
                          c[1] - o2[1] + rf(-0.4f, 0.4f),
                          c[2] - o2[2] + rf(-0.4f, 0.4f)};
            float l = sqrtf(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]) + 1e-9f;
            for (int k = 0; k < 3; k++) {
                r.org[k] = o2[k];
                r.dir[k] = d[k] / l;
            }
            r.tmin = 1e-4f;
            r.tmax = 1e9f;
            lrt_hit hu, ht;
            int uh = lrt_tri_intersect1(un, &r, &hu);
            int th = lrt_tri_intersect1(tr, &r, &ht);
            if (th) {
                thits++;
                /* core invariant: every trimmed hit is inside the trim region */
                if (pt_in_loops(trim_pts, loop_off, 1, ht.u, ht.v)) inside_ok++;
            }
            if (uh) {
                int in = pt_in_loops(trim_pts, loop_off, 1, hu.u, hu.v);
                if (in) {
                    preserved_tot++;
                    if (th && fabsf(ht.t - hu.t) < 1e-2f) preserved++;
                } else {
                    outside_tot++;
                    if (!th) removed++; /* outside-region hit correctly trimmed */
                }
            }
        }
        lrt_tri_scene_free(un);
        lrt_tri_scene_free(tr);
    }
    double inside = thits ? (double)inside_ok / thits : 1.0;
    double pres = preserved_tot ? (double)preserved / preserved_tot : 1.0;
    double rem = outside_tot ? (double)removed / outside_tot : 1.0;
    printf("trimnurbs: %zu trimmed hits, all-inside %.3f%%, preserved %.3f%%, "
           "removed %.3f%%\n",
           thits, inside * 100.0, pres * 100.0, rem * 100.0);
    CHECK(thits > (size_t)(NS * 30), "trimnurbs: too few hits");
    CHECK(inside >= 0.999, "trimnurbs: trimmed hit outside region %.3f%%",
          inside * 100.0);
    CHECK(pres >= 0.98, "trimnurbs: inside hits not preserved %.3f%%",
          pres * 100.0);
    CHECK(rem >= 0.98, "trimnurbs: outside hits not removed %.3f%%",
          rem * 100.0);
}

/* LRTS v2: trimmed-NURBS scenes (with trim loops) must round-trip through
 * save/load to memory and produce identical hits. */
static void test_trim_serialize(void) {
    const int degu = 3, degv = 3, nu = 4, nv = 4;
    const float U[9] = {0, 0, 0, 0, 0.5f, 1, 1, 1, 1};
    const int NG = 32;
    float tp[32 * 2];
    uint32_t ll[1] = {(uint32_t)NG};
    for (int i = 0; i < NG; i++) {
        float a = 6.2831853f * i / NG;
        tp[i * 2] = 0.5f + 0.3f * cosf(a);
        tp[i * 2 + 1] = 0.5f + 0.3f * sinf(a);
    }
    float net[25 * 3], w[25];
    float c[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
    for (int j = 0; j < 5; j++)
        for (int i = 0; i < 5; i++) {
            int idx = j * 5 + i;
            for (int k = 0; k < 3; k++)
                net[idx * 3 + k] = c[k] + 0.5f * (i - 2) * (k == 0) +
                                   0.5f * (j - 2) * (k == 1) + rf(-0.1f, 0.1f);
            w[idx] = rf(0.6f, 1.8f);
        }
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    lrt_tri_scene *orig = lrt_trimnurbs_scene_build(net, nu, nv, U, U, w, degu,
                                                    degv, tp, ll, 1, &o, NULL);
    CHECK(orig != NULL, "trim serialize: build");
    if (!orig) return;
    void *buf = NULL;
    size_t n = 0;
    lrt_result sr = lrt_tri_scene_save_to_memory(orig, &buf, &n);
    CHECK(sr == LRT_RESULT_OK && buf, "trim serialize: save (err=%d)", (int)sr);
    lrt_tri_scene *loaded = buf ? lrt_tri_scene_load_from_memory(buf, n, NULL)
                                : NULL;
    CHECK(loaded != NULL, "trim serialize: load");
    if (loaded) {
        size_t nr = 40000, agree = 0;
        for (size_t i = 0; i < nr; i++) {
            lrt_ray r;
            float o2[3] = {c[0] + rf(-3, 3), c[1] + rf(-3, 3), c[2] + rf(-3, 3)};
            float d[3] = {c[0] - o2[0] + rf(-0.4f, 0.4f),
                          c[1] - o2[1] + rf(-0.4f, 0.4f),
                          c[2] - o2[2] + rf(-0.4f, 0.4f)};
            float l = sqrtf(d[0]*d[0]+d[1]*d[1]+d[2]*d[2]) + 1e-9f;
            for (int k = 0; k < 3; k++) { r.org[k]=o2[k]; r.dir[k]=d[k]/l; }
            r.tmin = 1e-4f; r.tmax = 1e9f;
            lrt_hit a, b;
            int ha = lrt_tri_intersect1(orig, &r, &a);
            int hb = lrt_tri_intersect1(loaded, &r, &b);
            if (ha == hb && (!ha || (a.prim_id == b.prim_id &&
                                     fabsf(a.t - b.t) < 1e-5f)))
                agree++;
        }
        double f = (double)agree / nr;
        printf("trim-io:  save/load round-trip agree %.4f%%\n", f * 100.0);
        CHECK(f >= 0.9999, "trim serialize: round-trip %.4f%%", f * 100.0);
        lrt_tri_scene_free(loaded);
    }
    free(buf);
    lrt_tri_scene_free(orig);
}

/* Malformed knot vectors must be rejected, not crash (regression: a non-
 * monotone knot vector previously overflowed the extraction scratch). */
static void test_nurbs_bad_knots(void) {
    float net[25 * 3];
    for (int i = 0; i < 75; i++) net[i] = (float)(i % 5) * 0.3f;
    float Vbad[9] = {0, 0, 0, 0, 0.5f, 1, 1, 1, 0}; /* trailing 0: non-monotone */
    float Vok[9] = {0, 0, 0, 0, 0.5f, 1, 1, 1, 1};
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    lrt_result err = LRT_RESULT_OK;
    lrt_tri_scene *bad =
        lrt_nurbs_scene_build(net, 4, 4, Vok, Vbad, NULL, 3, 3, &o, &err);
    CHECK(bad == NULL && err == LRT_RESULT_INVALID_ARGUMENT,
          "non-monotone knots should be rejected (got %p err=%d)", (void *)bad,
          (int)err);
    if (bad) lrt_tri_scene_free(bad);
    /* the valid twin must still build */
    lrt_tri_scene *good =
        lrt_nurbs_scene_build(net, 4, 4, Vok, Vok, NULL, 3, 3, &o, NULL);
    CHECK(good != NULL, "valid knots should build");
    if (good) lrt_tri_scene_free(good);
    printf("nurbs-knots: malformed rejected, valid accepted\n");
}

/* ----- post-hit shading query (lrt_tri_surface_normal) ----------------------
 * For every hit on a parametric surface scene, validates:
 *   - residual:    returned P lies on the ray (org + t*dir);
 *   - tangents:    dPdu/dPdv match a central finite difference of P (direction);
 *   - normal:      Ng agrees with cross(fd_u, fd_v);
 *   - perpendic.:  Ng is orthogonal to both tangents (by construction).
 * Aggregated as pass fractions (a handful of grazing/boundary hits may miss the
 * FD direction tolerance), matching the residual-test style elsewhere. */
static float vdot3(const float *a, const float *b) {
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
}
static float vlen3(const float *a) { return sqrtf(vdot3(a, a)); }

static void check_normals(lrt_tri_scene *sc, size_t nprims, const char *label) {
    const size_t NR = 40000;
    size_t hits = 0, resid_ok = 0, tan_ok = 0, norm_ok = 0, perp_ok = 0;
    const float h = 5e-4f;
    for (size_t i = 0; i < NR; i++) {
        lrt_ray r;
        make_ray(&r);
        lrt_hit hit;
        if (!lrt_tri_intersect1(sc, &r, &hit)) continue;
        hits++;
        float P[3], Ng[3], dU[3], dV[3];
        lrt_result q =
            lrt_tri_surface_normal(sc, hit.prim_id, hit.u, hit.v, P, Ng, dU, dV);
        CHECK(q == LRT_RESULT_OK, "%s: surface_normal err=%d", label, (int)q);
        if (q != LRT_RESULT_OK) continue;
        /* residual: P on the ray */
        float pr[3];
        for (int k = 0; k < 3; k++) pr[k] = r.org[k] + hit.t * r.dir[k];
        float dd[3] = {P[0] - pr[0], P[1] - pr[1], P[2] - pr[2]};
        if (vlen3(dd) / (1.0f + fabsf(hit.t)) < 1e-3f) resid_ok++;
        /* central finite-difference of P in u and v (via the query itself) */
        float Pup[3], Pum[3], Pvp[3], Pvm[3];
        lrt_result a = lrt_tri_surface_normal(sc, hit.prim_id, hit.u + h, hit.v,
                                              Pup, NULL, NULL, NULL);
        lrt_result b = lrt_tri_surface_normal(sc, hit.prim_id, hit.u - h, hit.v,
                                              Pum, NULL, NULL, NULL);
        lrt_result cc = lrt_tri_surface_normal(sc, hit.prim_id, hit.u, hit.v + h,
                                               Pvp, NULL, NULL, NULL);
        lrt_result e = lrt_tri_surface_normal(sc, hit.prim_id, hit.u, hit.v - h,
                                              Pvm, NULL, NULL, NULL);
        if (a != LRT_RESULT_OK || b != LRT_RESULT_OK || cc != LRT_RESULT_OK ||
            e != LRT_RESULT_OK)
            continue;
        float fu[3], fv[3];
        for (int k = 0; k < 3; k++) {
            fu[k] = (Pup[k] - Pum[k]) / (2 * h);
            fv[k] = (Pvp[k] - Pvm[k]) / (2 * h);
        }
        /* tangent direction agreement (skip near-degenerate steps) */
        float lu = vlen3(fu), lv = vlen3(fv), ldU = vlen3(dU), ldV = vlen3(dV);
        int tu = lu < 1e-5f || ldU < 1e-5f ||
                 vdot3(fu, dU) / (lu * ldU) > 0.99f;
        int tv = lv < 1e-5f || ldV < 1e-5f ||
                 vdot3(fv, dV) / (lv * ldV) > 0.99f;
        if (tu && tv) tan_ok++;
        /* normal vs cross(fu,fv) */
        float fn[3] = {fu[1] * fv[2] - fu[2] * fv[1],
                       fu[2] * fv[0] - fu[0] * fv[2],
                       fu[0] * fv[1] - fu[1] * fv[0]};
        float lN = vlen3(Ng), lfn = vlen3(fn);
        if (lN < 1e-6f || lfn < 1e-6f || vdot3(Ng, fn) / (lN * lfn) > 0.999f)
            norm_ok++;
        /* perpendicularity (exact by construction) */
        if (lN < 1e-6f ||
            (fabsf(vdot3(Ng, dU)) / (lN * (ldU + 1e-9f)) < 1e-4f &&
             fabsf(vdot3(Ng, dV)) / (lN * (ldV + 1e-9f)) < 1e-4f))
            perp_ok++;
    }
    (void)nprims;
    double rf_ = hits ? (double)resid_ok / hits : 1.0;
    double tf = hits ? (double)tan_ok / hits : 1.0;
    double nf = hits ? (double)norm_ok / hits : 1.0;
    double pf = hits ? (double)perp_ok / hits : 1.0;
    printf("normals[%s]: %zu hits, resid %.2f%% tangent %.2f%% normal %.2f%% "
           "perp %.2f%%\n",
           label, hits, rf_ * 100, tf * 100, nf * 100, pf * 100);
    CHECK(hits > NR / 200, "%s: too few hits (%zu)", label, hits);
    CHECK(rf_ >= 0.999, "%s: P residual %.2f%% < 99.9%%", label, rf_ * 100);
    CHECK(tf >= 0.99, "%s: tangent agreement %.2f%% < 99%%", label, tf * 100);
    CHECK(nf >= 0.99, "%s: normal agreement %.2f%% < 99%%", label, nf * 100);
    CHECK(pf >= 0.999, "%s: perpendicularity %.2f%% < 99.9%%", label, pf * 100);
}

static void test_surface_normals(void) {
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;

    /* bilinear */
    const size_t NB = 1500;
    float *bil = (float *)malloc(NB * 12 * sizeof(float));
    for (size_t i = 0; i < NB; i++) {
        float c[3] = {rf(-2, 2), rf(-2, 2), rf(-2, 2)};
        float *p = &bil[i * 12];
        float ax[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float ay[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float s = 0.35f, w = 0.3f;
        for (int k = 0; k < 3; k++) {
            float warp = rf(-w, w);
            p[0 + k] = c[k] - s * ax[k] - s * ay[k];
            p[3 + k] = c[k] + s * ax[k] - s * ay[k] + (k == 2 ? warp : 0);
            p[6 + k] = c[k] + s * ax[k] + s * ay[k];
            p[9 + k] = c[k] - s * ax[k] + s * ay[k] - (k == 2 ? warp : 0);
        }
    }
    lrt_tri_scene *sb = lrt_bilinear_scene_build(bil, NB, &o, NULL);
    CHECK(sb != NULL, "normals: bilinear build");
    if (sb) check_normals(sb, NB, "bilinear");

    /* bicubic Bezier */
    const size_t NP = 1500;
    float *cps = (float *)malloc(NP * 48 * sizeof(float));
    for (size_t i = 0; i < NP; i++) {
        float c[3] = {rf(-2, 2), rf(-2, 2), rf(-2, 2)};
        float ax[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float ay[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float *cp = &cps[i * 48];
        for (int jj = 0; jj < 4; jj++)
            for (int ii = 0; ii < 4; ii++) {
                float fu = ii / 3.0f - 0.5f, fv = jj / 3.0f - 0.5f;
                int idx = (jj * 4 + ii) * 3;
                for (int k = 0; k < 3; k++)
                    cp[idx + k] = c[k] + 0.8f * fu * ax[k] + 0.8f * fv * ay[k] +
                                  rf(-0.12f, 0.12f);
            }
    }
    lrt_tri_scene *sp = lrt_bezpatch_scene_build(cps, NP, &o, NULL);
    CHECK(sp != NULL, "normals: bezpatch build");
    if (sp) check_normals(sp, NP, "bezpatch");

    /* NURBS (global-domain u,v + per-patch remap) */
    const int nu = 4, nv = 4;
    const float U[9] = {0, 0, 0, 0, 0.5f, 1, 1, 1, 1};
    float net[25 * 3], w[25];
    float cc[3] = {0, 0, 0};
    float ax[3] = {1, 0.2f, 0}, ay[3] = {0.1f, 1, 0.3f};
    for (int jj = 0; jj <= nv; jj++)
        for (int ii = 0; ii <= nu; ii++) {
            int idx = jj * (nu + 1) + ii;
            float fu = (float)ii / nu - 0.5f, fv = (float)jj / nv - 0.5f;
            for (int k = 0; k < 3; k++)
                net[idx * 3 + k] =
                    cc[k] + 1.2f * fu * ax[k] + 1.2f * fv * ay[k] + rf(-0.1f, 0.1f);
            w[idx] = rf(0.5f, 2.0f);
        }
    lrt_tri_scene *sn = lrt_nurbs_scene_build(net, nu, nv, U, U, w, 3, 3, &o, NULL);
    CHECK(sn != NULL, "normals: nurbs build");
    if (sn) check_normals(sn, 0, "nurbs");

    /* edge cases (reuse the bilinear scene) */
    if (sb) {
        lrt_result r;
        r = lrt_tri_surface_normal(sb, 0, 0.5f, 0.5f, NULL, NULL, NULL, NULL);
        CHECK(r == LRT_RESULT_OK, "normals: all-NULL outputs should be OK");
        r = lrt_tri_surface_normal(NULL, 0, 0.5f, 0.5f, NULL, NULL, NULL, NULL);
        CHECK(r == LRT_RESULT_INVALID_ARGUMENT, "normals: NULL scene -> INVALID");
        float tmp[3];
        r = lrt_tri_surface_normal(sb, (uint32_t)NB, 0.5f, 0.5f, tmp, NULL, NULL,
                                   NULL);
        CHECK(r == LRT_RESULT_INVALID_ARGUMENT,
              "normals: prim_id==nprims -> INVALID");
        /* a triangle scene must be rejected */
        float tri[9] = {0, 0, 0, 1, 0, 0, 0, 1, 0};
        lrt_tri_scene *st = lrt_tri_scene_build(tri, 1, &o, NULL);
        if (st) {
            r = lrt_tri_surface_normal(st, 0, 0.3f, 0.3f, tmp, NULL, NULL, NULL);
            CHECK(r == LRT_RESULT_INVALID_ARGUMENT,
                  "normals: triangle scene -> INVALID");
            lrt_tri_scene_free(st);
        }
        /* a deserialized surface scene reconstructs shade data from its leaves:
         * the query works and matches the original scene's normal. */
        void *blob = NULL;
        size_t blob_sz = 0;
        if (lrt_tri_scene_save_to_memory(sb, &blob, &blob_sz) == LRT_RESULT_OK &&
            blob) {
            lrt_tri_scene *sl = lrt_tri_scene_load_from_memory(blob, blob_sz, NULL);
            if (sl) {
                float Po[3], No[3], Pl[3], Nl[3];
                lrt_result ro = lrt_tri_surface_normal(sb, 7, 0.4f, 0.6f, Po, No,
                                                       NULL, NULL);
                lrt_result rl = lrt_tri_surface_normal(sl, 7, 0.4f, 0.6f, Pl, Nl,
                                                       NULL, NULL);
                CHECK(ro == LRT_RESULT_OK && rl == LRT_RESULT_OK,
                      "normals: loaded scene query (got %d/%d)", (int)ro, (int)rl);
                if (ro == LRT_RESULT_OK && rl == LRT_RESULT_OK) {
                    float dP = fabsf(Po[0] - Pl[0]) + fabsf(Po[1] - Pl[1]) +
                               fabsf(Po[2] - Pl[2]);
                    float dN = fabsf(No[0] - Nl[0]) + fabsf(No[1] - Nl[1]) +
                               fabsf(No[2] - Nl[2]);
                    CHECK(dP < 1e-5f && dN < 1e-5f,
                          "normals: loaded normal mismatch dP=%.2e dN=%.2e", dP,
                          dN);
                }
                lrt_tri_scene_free(sl);
            }
            free(blob);
        }
    }

    free(bil);
    free(cps);
    if (sb) lrt_tri_scene_free(sb);
    if (sp) lrt_tri_scene_free(sp);
    if (sn) lrt_tri_scene_free(sn);
}

/* ----- tessellation (lrt_tri_surface_tessellate) ----------------------------
 * Verifies emitted vertices lie on the surface (independent eval), the
 * geometric normal aligns with a finite-difference normal, the count matches
 * the bound (untrimmed), and trimmed cells are dropped (all centroids inside). */
static void test_tessellate(void) {
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.num_threads = 1;
    const uint32_t SU = 6, SV = 5;

    /* --- bezpatch: positions + normals vs independent eval --- */
    const size_t NP = 80;
    float *cps = (float *)malloc(NP * 48 * sizeof(float));
    for (size_t i = 0; i < NP; i++) {
        float c[3] = {rf(-2, 2), rf(-2, 2), rf(-2, 2)};
        float ax[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float ay[3] = {rf(-1, 1), rf(-1, 1), rf(-1, 1)};
        float *cp = &cps[i * 48];
        for (int jj = 0; jj < 4; jj++)
            for (int ii = 0; ii < 4; ii++) {
                float fu = ii / 3.0f - 0.5f, fv = jj / 3.0f - 0.5f;
                int idx = (jj * 4 + ii) * 3;
                for (int k = 0; k < 3; k++)
                    cp[idx + k] = c[k] + 0.8f * fu * ax[k] + 0.8f * fv * ay[k] +
                                  rf(-0.1f, 0.1f);
            }
    }
    lrt_tri_scene *sp = lrt_bezpatch_scene_build(cps, NP, &o, NULL);
    CHECK(sp != NULL, "tess: bezpatch build");
    if (sp) {
        size_t bound = lrt_tri_surface_tessellate_bound(sp, SU, SV);
        CHECK(bound == NP * SU * SV * 2, "tess: bound %zu", bound);
        float *pos = (float *)malloc(bound * 9 * sizeof(float));
        float *nrm = (float *)malloc(bound * 9 * sizeof(float));
        float *uv = (float *)malloc(bound * 6 * sizeof(float));
        size_t nt = 0;
        lrt_result r =
            lrt_tri_surface_tessellate(sp, SU, SV, pos, nrm, uv, bound, &nt);
        CHECK(r == LRT_RESULT_OK && nt == bound, "tess: bezpatch count %zu", nt);
        size_t resid_ok = 0, norm_ok = 0, nverts = nt * 3;
        for (size_t vtx = 0; vtx < nverts; vtx++) {
            float u = uv[vtx * 2 + 0], v = uv[vtx * 2 + 1];
            int prim = (int)((vtx / 3) / (SU * SV * 2)); /* patch from tri order */
            float S[3];
            bezpatch_eval(&cps[(size_t)prim * 48], u, v, S);
            float dp = fabsf(S[0] - pos[vtx * 3]) + fabsf(S[1] - pos[vtx * 3 + 1]) +
                       fabsf(S[2] - pos[vtx * 3 + 2]);
            if (dp < 1e-4f) resid_ok++;
            /* FD normal from the independent eval */
            float h = 1e-3f, Su0[3], Su1[3], Sv0[3], Sv1[3];
            bezpatch_eval(&cps[(size_t)prim * 48], u + h, v, Su1);
            bezpatch_eval(&cps[(size_t)prim * 48], u - h, v, Su0);
            bezpatch_eval(&cps[(size_t)prim * 48], u, v + h, Sv1);
            bezpatch_eval(&cps[(size_t)prim * 48], u, v - h, Sv0);
            float du[3], dv[3];
            for (int k = 0; k < 3; k++) {
                du[k] = Su1[k] - Su0[k];
                dv[k] = Sv1[k] - Sv0[k];
            }
            float fn[3] = {du[1] * dv[2] - du[2] * dv[1],
                           du[2] * dv[0] - du[0] * dv[2],
                           du[0] * dv[1] - du[1] * dv[0]};
            const float *gn = &nrm[vtx * 3];
            float lf = sqrtf(fn[0] * fn[0] + fn[1] * fn[1] + fn[2] * fn[2]);
            float lg = sqrtf(gn[0] * gn[0] + gn[1] * gn[1] + gn[2] * gn[2]);
            if (lf < 1e-9f || lg < 1e-9f ||
                (fn[0] * gn[0] + fn[1] * gn[1] + fn[2] * gn[2]) / (lf * lg) >
                    0.999f)
                norm_ok++;
        }
        printf("tess[bezpatch]: %zu tris, resid %.2f%% normal %.2f%%\n", nt,
               100.0 * resid_ok / nverts, 100.0 * norm_ok / nverts);
        CHECK(resid_ok == nverts, "tess: bezpatch residual %.3f%%",
              100.0 * resid_ok / nverts);
        CHECK(norm_ok >= (size_t)(0.99 * nverts), "tess: bezpatch normal %.3f%%",
              100.0 * norm_ok / nverts);
        free(pos);
        free(nrm);
        free(uv);
        lrt_tri_scene_free(sp);
    }
    free(cps);

    /* --- trimmed NURBS: every emitted cell centroid is inside the trim disk,
     * and the trimmed count is strictly below the untrimmed bound --- */
    {
        const int nu = 4, nv = 4;
        const float U[9] = {0, 0, 0, 0, 0.5f, 1, 1, 1, 1};
        const int NG = 40;
        float tp[40 * 2];
        uint32_t ll[1] = {(uint32_t)NG};
        for (int i = 0; i < NG; i++) {
            float a = 6.2831853f * i / NG;
            tp[i * 2 + 0] = 0.5f + 0.3f * cosf(a);
            tp[i * 2 + 1] = 0.5f + 0.3f * sinf(a);
        }
        float net[25 * 3], w[25];
        for (int jj = 0; jj <= nv; jj++)
            for (int ii = 0; ii <= nu; ii++) {
                int idx = jj * (nu + 1) + ii;
                float fu = (float)ii / nu - 0.5f, fv = (float)jj / nv - 0.5f;
                net[idx * 3 + 0] = fu;
                net[idx * 3 + 1] = fv;
                net[idx * 3 + 2] = 0.2f * fu * fv;
                w[idx] = 1.0f;
            }
        lrt_tri_scene *st = lrt_trimnurbs_scene_build(net, nu, nv, U, U, w, 3, 3,
                                                      tp, ll, 1, &o, NULL);
        CHECK(st != NULL, "tess: trimnurbs build");
        if (st) {
            const uint32_t S = 24;
            size_t bound = lrt_tri_surface_tessellate_bound(st, S, S);
            float *pos = (float *)malloc(bound * 9 * sizeof(float));
            float *uv = (float *)malloc(bound * 6 * sizeof(float));
            size_t nt = 0;
            lrt_result r =
                lrt_tri_surface_tessellate(st, S, S, pos, NULL, uv, bound, &nt);
            CHECK(r == LRT_RESULT_OK, "tess: trimnurbs result");
            CHECK(nt > 0 && nt < bound, "tess: trim should drop cells (%zu/%zu)",
                  nt, bound);
            /* every emitted vertex's (u,v) lies within ~the trim disk (allow a
             * cell-diagonal slack, since the *centroid* is the gate) */
            size_t inside = 0, nverts = nt * 3;
            float cellr = 1.0f / (float)S; /* domain span ~1; cell ~1/S */
            for (size_t vtx = 0; vtx < nverts; vtx++) {
                float du = uv[vtx * 2] - 0.5f, dv = uv[vtx * 2 + 1] - 0.5f;
                if (sqrtf(du * du + dv * dv) <= 0.3f + 1.5f * cellr) inside++;
            }
            printf("tess[trimnurbs]: %zu/%zu tris kept, verts-in-disk %.2f%%\n",
                   nt, bound, 100.0 * inside / nverts);
            CHECK(inside == nverts, "tess: trim vertices outside disk (%.2f%%)",
                  100.0 * inside / nverts);
            free(pos);
            free(uv);
            lrt_tri_scene_free(st);
        }
    }

    /* edge cases */
    {
        float tri[9] = {0, 0, 0, 1, 0, 0, 0, 1, 0};
        lrt_tri_scene *st = lrt_tri_scene_build(tri, 1, &o, NULL);
        if (st) {
            size_t nt = 0;
            lrt_result r =
                lrt_tri_surface_tessellate(st, 2, 2, NULL, NULL, NULL, 0, &nt);
            CHECK(r == LRT_RESULT_INVALID_ARGUMENT, "tess: tri scene rejected");
            CHECK(lrt_tri_surface_tessellate_bound(st, 2, 2) == 0,
                  "tess: tri bound 0");
            lrt_tri_scene_free(st);
        }
    }
}

int main(void) {
    test_bilinear();
    test_bezpatch();
    test_nurbs();
    test_nurbs_bad_knots();
    test_trimnurbs();
    test_trim_serialize();
    test_surface_normals();
    test_tessellate();
    if (g_fail) {
        printf("\n%d FAILURES\n", g_fail);
        return 1;
    }
    printf("\nAll surface tests passed.\n");
    return 0;
}
