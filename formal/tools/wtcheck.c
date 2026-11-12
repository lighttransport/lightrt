/*
 * wtcheck: the SIMD watertight leaves (tri_woop4_block / tri_woop8_block,
 * LRT_TRI_WATERTIGHT_TRI) against the scalar tri_woop_one, bit for bit.
 *
 *  1. Leaf fuzz: random blocks and rays, including special values (+-0, inf,
 *     NaN, subnormal, huge, axis-parallel directions, rays through vertices
 *     and edges), each lane against tri_woop_one, and the block's chosen
 *     (t, u, v, prim) against the scalar lane loop with a strict t < best.
 *  2. Traversal: the dispatched lrt_tri_intersect1 / lrt_tri_occluded1 (SIMD
 *     kernels with the SIMD watertight leaf) against tri_intersect_scalar /
 *     tri_occluded_scalar (scalar kernels with tri_woop_one), bit for bit, on
 *     BVH4/BVH8 x LBVH/SAH x soup/shared-edge grid/coplanar scenes; also the
 *     batched (lrt_tri_intersect1N / occluded1N, both hints) and packet
 *     (lrt_tri_intersect4) entry points, and the scene after
 *     save_to_memory/load_from_memory and after lrt_tri_scene_refit.
 *
 * Build: cc -O1 -ffp-contract=off -msse4.1 -mavx2 -mfma -DLRT_TRI_WATERTIGHT_TRI
 *        -I. formal/tools/wtcheck.c -lm -lpthread
 */
#include "../../lightrt_c_tri.c"
#include <stdio.h>
#include <string.h>

#ifndef LRT_TRI_WATERTIGHT_TRI
#error build with -DLRT_TRI_WATERTIGHT_TRI
#endif

static uint32_t rs = 1;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }
static float frand(void) { return (float)(rnd() & 0xffffff) / 16777216.0f; }
static float fspecial(void) {
    static const float sp[] = {0.0f, -0.0f, 1.0f, -1.0f, 1e-40f, -1e-40f, 1e30f, -1e30f,
                               INFINITY, -INFINITY, NAN, 0.5f, 3.0f};
    return sp[rnd() % (sizeof sp / sizeof sp[0])];
}
static float fval(int mode) {
    if (mode == 1 && rnd() % 6 == 0) return fspecial();
    return frand() * 4 - 2;
}
static int same(float a, float b) { return memcmp(&a, &b, 4) == 0 || (a != a && b != b); }

static long leaf_lanes, leaf_bad, leaf_blocks, leaf_bad_blk, leaf_hits;

static void leaf_fuzz(int W, int iters) {
    for (int it = 0; it < iters; it++) {
        int mode = it % 3; /* 0 plain, 1 special values, 2 rays through vertices/edges */
        _Alignas(32) float wb[9 * 8];
        uint32_t ids[8];
        for (int l = 0; l < W; l++) {
            ids[l] = (rnd() % 7 == 0) ? LRT_TRI_NO_HIT : (uint32_t)l * 10 + 1;
            for (int c = 0; c < 9; c++) wb[c * W + l] = ids[l] == LRT_TRI_NO_HIT ? 0.0f : fval(mode);
            if (mode == 2 && l > 0 && rnd() % 2) /* share an edge with lane l-1 */
                for (int c = 0; c < 6; c++) wb[c * W + l] = wb[(c + 3) % 9 * W + l - 1];
        }
        lrt_ray ray;
        for (int a = 0; a < 3; a++) { ray.org[a] = fval(mode); ray.dir[a] = fval(mode); }
        if (mode == 2) {
            int l = (int)(rnd() % W), vtx = (int)(rnd() % 3), vtx2 = (int)(rnd() % 3);
            float f = (rnd() % 2) ? 0.0f : frand();
            for (int a = 0; a < 3; a++) {
                float p = wb[(3 * vtx + a) * W + l] * (1 - f) + wb[(3 * vtx2 + a) * W + l] * f;
                ray.dir[a] = p - ray.org[a];
            }
            if (rnd() % 4 == 0) ray.dir[rnd() % 3] = 0.0f;
        }
        ray.tmin = (rnd() % 5 == 0) ? -1.0f : 0.0f;
        ray.tmax = (rnd() % 4 == 0) ? 0.7f : 1e30f;
        tri_ray_ctx rc;
        tri_ray_setup(&ray, &rc);
        /* scalar reference: lane loop, strict update */
        float bt = ray.tmax, bu = 0, bv = 0;
        uint32_t bp = LRT_TRI_NO_HIT;
        int anyhit = 0;
        for (int l = 0; l < W; l++) {
            if (ids[l] == LRT_TRI_NO_HIT) continue;
            float v0[3], v1[3], v2[3];
            for (int a = 0; a < 3; a++) {
                v0[a] = wb[(0 + a) * W + l]; v1[a] = wb[(3 + a) * W + l]; v2[a] = wb[(6 + a) * W + l];
            }
            float t, u, v;
            if (tri_woop_one(rc.org, rc.dir, v0, v1, v2, rc.tmin, ray.tmax, &t, &u, &v)) anyhit = 1;
            if (tri_woop_one(rc.org, rc.dir, v0, v1, v2, rc.tmin, bt, &t, &u, &v)) {
                bt = t; bu = u; bv = v; bp = ids[l];
            }
            leaf_lanes++;
        }
        float st = ray.tmax, su = 0, sv = 0;
        uint32_t spid = LRT_TRI_NO_HIT;
        int socc;
        if (W == 4) {
#if LRT_TRI_HAS_SSE4 && !LRT_TRI_NEON_SHIM
            tri_woop4_ctx wc;
            tri_woop4_setup(&rc, &wc);
            tri_woop4_block(wb, ids, &wc, &st, &su, &sv, &spid);
            socc = tri_woop4_block_occ(wb, ids, &wc, ray.tmax);
#else
            continue;
#endif
        } else {
#if LRT_TRI_HAS_AVX2
            tri_woop8_ctx wc;
            tri_woop8_setup(&rc, &wc);
            tri_woop8_block(wb, ids, &wc, &st, &su, &sv, &spid);
            socc = tri_woop8_block_occ(wb, ids, &wc, ray.tmax);
#else
            continue;
#endif
        }
        leaf_blocks++;
        if (bp != LRT_TRI_NO_HIT) leaf_hits++;
        if (spid != bp || (bp != LRT_TRI_NO_HIT && (!same(st, bt) || !same(su, bu) || !same(sv, bv))) ||
            socc != anyhit) {
            if (leaf_bad_blk < 5)
                fprintf(stderr, "leaf W=%d it=%d: simd (%u %.9g %.9g %.9g occ %d) scalar (%u %.9g %.9g %.9g occ %d)\n",
                        W, it, spid, st, su, sv, socc, bp, bt, bu, bv, anyhit);
            leaf_bad_blk++;
        }
    }
    (void)leaf_bad;
}

static long trav_rays, trav_bad, occ_bad, trav_hits, batch_bad, persist_bad, reader_bad, hp_rays, hp_diff, gv_bad, mh_slack, mh_maxulp;

static void scene_verts(int g, int n, float *v) {
    if (g == 0) { /* soup */
        for (int i = 0; i < n; i++) {
            float c[3] = {frand() * 2 - 1, frand() * 2 - 1, frand() * 2 - 1};
            for (int k = 0; k < 9; k++) v[9 * i + k] = c[k % 3] + (frand() - 0.5f) * 0.3f;
        }
    } else if (g == 1) { /* grid with shared edges (heightfield) */
        int m = 1;
        while (2 * (m + 1) * (m + 1) <= n) m++;
        int k = 0;
        for (int i = 0; i < m && k + 2 <= n; i++)
            for (int j = 0; j < m && k + 2 <= n; j++) {
                float x0 = -1 + 2.0f * i / m, x1 = -1 + 2.0f * (i + 1) / m;
                float y0 = -1 + 2.0f * j / m, y1 = -1 + 2.0f * (j + 1) / m;
                float h00 = 0.2f * sinf(3 * x0 + 2 * y0), h10 = 0.2f * sinf(3 * x1 + 2 * y0);
                float h11 = 0.2f * sinf(3 * x1 + 2 * y1), h01 = 0.2f * sinf(3 * x0 + 2 * y1);
                float A[3] = {x0, y0, h00}, B[3] = {x1, y0, h10}, C[3] = {x1, y1, h11}, D[3] = {x0, y1, h01};
                memcpy(&v[9 * k], A, 12); memcpy(&v[9 * k + 3], B, 12); memcpy(&v[9 * k + 6], C, 12); k++;
                memcpy(&v[9 * k], A, 12); memcpy(&v[9 * k + 3], C, 12); memcpy(&v[9 * k + 6], D, 12); k++;
            }
        for (; k < n; k++) memcpy(&v[9 * k], &v[0], 36);
    } else { /* coplanar overlapping, z = 0 */
        for (int i = 0; i < n; i++)
            for (int c = 0; c < 3; c++) {
                v[9 * i + 3 * c] = frand() * 2 - 1;
                v[9 * i + 3 * c + 1] = frand() * 2 - 1;
                v[9 * i + 3 * c + 2] = 0.0f;
            }
    }
}

/* A reported hit must be exactly tri_woop_one on the caller's input vertices
 * of that prim (independent of the scene's internal vertex copy). */
static long src_bad, exn_diff, exn_maxulp, exn_miss;
static void check_src(const float *v, const lrt_ray *ray, const lrt_hit *h) {
    if (h->prim_id == LRT_TRI_NO_HIT) return;
    tri_ray_ctx rc;
    tri_ray_setup(ray, &rc);
    const float *w = &v[(size_t)h->prim_id * 9];
    float t, u, vv;
    if (!tri_woop_one(rc.org, rc.dir, w, w + 3, w + 6, rc.tmin, ray->tmax, &t, &u, &vv) ||
        !same(t, h->t) || !same(u, h->u) || !same(vv, h->v))
        src_bad++;
}

static void trav(int seed, int n, int q, int w, int g, int nrays) {
    float *v = malloc(sizeof(float) * 9 * n);
    scene_verts(g, n, v);
    lrt_tri_build_options o = {0};
    o.quality = (lrt_tri_quality)q;
    o.layout = (lrt_tri_layout)w;
    lrt_tri_scene *s = lrt_tri_scene_build(v, (size_t)n, &o, NULL);
#if LRT_TRI_HAS_SSE4 && !LRT_TRI_NEON_SHIM
    int need_simd = 1;
#else
    int need_simd = 0; /* scalar-only build: scalar watertight kernels */
#endif
    if (!s || (need_simd && !TRI_WBLK_SIMD(s)) || !s->wblk) {
        fprintf(stderr, "seed %d cfg (%d %d %d %d): no SIMD watertight leaf\n", seed, n, q, w, g);
        trav_bad++;
        lrt_tri_scene_free(s);
        free(v);
        return;
    }
    lrt_ray *R = malloc(sizeof(lrt_ray) * nrays);
    lrt_hit *H = malloc(sizeof(lrt_hit) * nrays);
    for (int r = 0; r < nrays; r++) {
        lrt_ray ray;
        int kind = r % 4;
        for (int a = 0; a < 3; a++) ray.org[a] = (frand() - 0.5f) * 6;
        float tgt[3];
        if (kind >= 2) { /* aim at a vertex or an edge point */
            int p = (int)(rnd() % n), c0 = (int)(rnd() % 3), c1 = (int)(rnd() % 3);
            float f = kind == 2 ? 0.0f : frand();
            for (int a = 0; a < 3; a++) tgt[a] = v[9 * p + 3 * c0 + a] * (1 - f) + v[9 * p + 3 * c1 + a] * f;
        } else {
            for (int a = 0; a < 3; a++) tgt[a] = (frand() - 0.5f) * 2.4f;
        }
        for (int a = 0; a < 3; a++) ray.dir[a] = tgt[a] - ray.org[a];
        if (r % 7 == 3) ray.dir[rnd() % 3] = 0.0f;
        if (g == 2 && r % 5 == 2) ray.org[2] = 0.0f, ray.dir[2] = 0.0f; /* in the plane */
        ray.tmin = 0.0f;
        ray.tmax = (r % 6 == 1) ? 2.0f : 1e30f;
        lrt_hit a, b;
        int ka = lrt_tri_intersect1(s, &ray, &a);
        check_src(v, &ray, &a);
        { /* brute force over the input triangles with the same watertight test */
            tri_ray_ctx brc;
            tri_ray_setup(&ray, &brc);
            float bt = ray.tmax;
            int bk = 0;
            for (int p = 0; p < n; p++) {
                float t, u, vv;
                const float *w = &v[9 * p];
                if (tri_woop_one(brc.org, brc.dir, w, w + 3, w + 6, brc.tmin, bt, &t, &u, &vv)) {
                    bt = t;
                    bk = 1;
                }
            }
            if (bk != ka || (bk && !same(bt, a.t))) {
                if (exn_diff < 8)
                    fprintf(stderr, "exn cfg (%d %d %d %d) ray %d: brute %d %.9g  C %d %u %.9g  dir %g %g %g\n",
                            n, q, w, g, r, bk, bt, ka, a.prim_id, a.t, ray.dir[0], ray.dir[1], ray.dir[2]);
                exn_diff++;
                if (bk && !ka) exn_miss++;
                int32_t ia, ib;
                memcpy(&ia, &bt, 4);
                memcpy(&ib, &a.t, 4);
                long d = (bk && ka) ? labs((long)ia - (long)ib) : 1000000;
                if (d > exn_maxulp) exn_maxulp = d;
            }
        }
        int kb = tri_intersect_scalar(s, &ray, &b);
        trav_rays++;
        if (kb) trav_hits++;
        if (ka != kb || a.prim_id != b.prim_id ||
            (kb && (!same(a.t, b.t) || !same(a.u, b.u) || !same(a.v, b.v)))) {
            if (trav_bad < 5)
                fprintf(stderr, "seed %d cfg (%d %d %d %d) ray %d: dispatched %d %u %.9g scalar %d %u %.9g\n",
                        seed, n, q, w, g, r, ka, a.prim_id, a.t, kb, b.prim_id, b.t);
            trav_bad++;
        }
        if (lrt_tri_occluded1(s, &ray) != tri_occluded_scalar(s, &ray)) occ_bad++;
        R[r] = ray;
        H[r] = b;
    }
    /* batched (interleaved pipeline / per-ray) and packet entry points */
    lrt_hit *B = malloc(sizeof(lrt_hit) * nrays);
    uint8_t *O = malloc(nrays);
    for (int hint = 0; hint < 2; hint++) {
        lrt_tri_intersect1N(s, R, B, (size_t)nrays,
                            hint ? LRT_TRI_BATCH_COHERENT : LRT_TRI_BATCH_INCOHERENT);
        lrt_tri_occluded1N(s, R, O, (size_t)nrays,
                           hint ? LRT_TRI_BATCH_COHERENT : LRT_TRI_BATCH_INCOHERENT);
        for (int r = 0; r < nrays; r++) {
            if (B[r].prim_id != H[r].prim_id ||
                (H[r].prim_id != LRT_TRI_NO_HIT &&
                 (!same(B[r].t, H[r].t) || !same(B[r].u, H[r].u) || !same(B[r].v, H[r].v))))
                batch_bad++;
            if (O[r] != tri_occluded_scalar(s, &R[r])) batch_bad++;
        }
    }
    for (int r = 0; r + 4 <= nrays; r += 4) {
        lrt_ray4 p4;
        for (int k = 0; k < 4; k++) {
            p4.orgx[k] = R[r + k].org[0]; p4.orgy[k] = R[r + k].org[1]; p4.orgz[k] = R[r + k].org[2];
            p4.dirx[k] = R[r + k].dir[0]; p4.diry[k] = R[r + k].dir[1]; p4.dirz[k] = R[r + k].dir[2];
            p4.tmin[k] = R[r + k].tmin; p4.tmax[k] = R[r + k].tmax;
        }
        lrt_hit4 h4;
        lrt_tri_intersect4(s, &p4, &h4);
        for (int k = 0; k < 4; k++)
            if (h4.prim_id[k] != H[r + k].prim_id ||
                (H[r + k].prim_id != LRT_TRI_NO_HIT && !same(h4.t[k], H[r + k].t)))
                batch_bad++;
    }
    /* readers of the leaf blocks other than the traversal leaves */
    for (int p = 0; p < n; p++) { /* exact vertices back (vertex-format leaves) */
        float A[3], Bv[3], C[3];
        if (lrt_tri_get_verts(s, (uint32_t)p, A, Bv, C) &&
            (memcmp(A, &v[9 * p], 12) || memcmp(Bv, &v[9 * p + 3], 12) || memcmp(C, &v[9 * p + 6], 12)))
            reader_bad++, gv_bad++;
    }
    for (int r = 0; r < nrays; r++) {
        lrt_hit mh[4];
        size_t k = lrt_tri_intersect_n(s, &R[r], mh, 4);
        if (k > 0 && H[r].prim_id != LRT_TRI_NO_HIT && !same(mh[0].t, H[r].t)) mh_slack++;
        if (k > 0 && H[r].prim_id != LRT_TRI_NO_HIT) {
            int32_t ia, ib;
            memcpy(&ia, &mh[0].t, 4);
            memcpy(&ib, &H[r].t, 4);
            long d = labs((long)ia - (long)ib);
            if (d > mh_maxulp) mh_maxulp = d;
        }
        if ((k > 0) != (H[r].prim_id != LRT_TRI_NO_HIT)) {
            /* both searches prune nodes by a rounded tnear against a running
             * bound (intersect1: the best hit; intersect_n: its max_hits-th),
             * so either may miss the true nearest by the pruning slack
             * (Flat.run_approx, <= 4 ulp measured); ties at a shared edge may
             * also pick another prim with the same t. Exact only under
             * LRT_TRI_EXACT_NEAREST. */
            if (reader_bad - gv_bad < 6)
                fprintf(stderr, "cfg (%d %d %d %d) ray %d: n=%zu first %u t=%.9g | closest %u t=%.9g tmax %g\n",
                        n, q, w, g, r, k, k ? mh[0].prim_id : 0u, k ? mh[0].t : 0.f, H[r].prim_id, H[r].t, R[r].tmax);
            reader_bad++;
        }
        lrt_ray_hp rh;
        for (int a2 = 0; a2 < 3; a2++) { rh.org[a2] = R[r].org[a2]; rh.dir[a2] = R[r].dir[a2]; }
        rh.tmin = R[r].tmin;
        rh.tmax = R[r].tmax;
        lrt_hit_hp hh;
        int kh = lrt_tri_intersect1_hp(s, &rh, &hh);
        hp_rays++;
        if (kh != (H[r].prim_id != LRT_TRI_NO_HIT)) hp_diff++;
    }
    /* serialization: the loaded scene rebuilds wblk from the stored exact
     * vertices; its SIMD answers must equal the original's scalar ones */
    void *buf = NULL;
    size_t nb = 0;
    if (lrt_tri_scene_save_to_memory(s, &buf, &nb) == LRT_RESULT_OK) {
        lrt_tri_scene *L = lrt_tri_scene_load_from_memory(buf, nb, NULL);
        if (!L || (need_simd && !TRI_WBLK_SIMD(L)) || !L->wblk) {
            persist_bad++;
        } else {
            for (int r = 0; r < nrays; r++) {
                lrt_hit a;
                lrt_tri_intersect1(L, &R[r], &a);
                check_src(v, &R[r], &a);
                if (a.prim_id != H[r].prim_id ||
                    (H[r].prim_id != LRT_TRI_NO_HIT && !same(a.t, H[r].t)))
                    persist_bad++;
            }
        }
        lrt_tri_scene_free(L);
        free(buf);
    } else {
        persist_bad++;
    }
    /* refit: wblk is re-derived from the new vertices (scalar reads wverts,
     * SIMD reads wblk, so a stale wblk shows as a disagreement) */
    for (int i = 0; i < 9 * n; i++) v[i] += (frand() - 0.5f) * 0.05f;
    if (lrt_tri_scene_refit(s, v, (size_t)n) != LRT_RESULT_OK) persist_bad++;
    for (int r = 0; r < nrays; r++) {
        lrt_hit a, b;
        int ka = lrt_tri_intersect1(s, &R[r], &a), kb = tri_intersect_scalar(s, &R[r], &b);
        check_src(v, &R[r], &a);
        if (ka != kb || a.prim_id != b.prim_id || (kb && !same(a.t, b.t))) persist_bad++;
        if (lrt_tri_occluded1(s, &R[r]) != tri_occluded_scalar(s, &R[r])) persist_bad++;
    }
    free(B); free(O); free(R); free(H);
    lrt_tri_scene_free(s);
    free(v);
}

int main(int argc, char **argv) {
    int seeds = argc > 1 ? atoi(argv[1]) : 2;
    int nrays = argc > 2 ? atoi(argv[2]) : 3000;
    for (int seed = 1; seed <= seeds; seed++) {
        rs = (uint32_t)seed * 2654435761u + 7;
#if LRT_TRI_HAS_SSE4 && !LRT_TRI_NEON_SHIM
        leaf_fuzz(4, 200000);
#endif
#if LRT_TRI_HAS_AVX2
        leaf_fuzz(8, 200000);
#endif
        const int cfg[][4] = {{400, 0, 4, 0}, {600, 1, 4, 1}, {500, 1, 4, 2},
                              {800, 1, 8, 0}, {1200, 0, 8, 1}, {500, 1, 8, 2}};
        unsigned ncfg = (LRT_TRI_HAS_AVX2 || !LRT_TRI_HAS_SSE4) ? 6u : 3u; /* SSE-only: no BVH8 SIMD leaf */
        for (unsigned c = 0; c < ncfg; c++)
            trav(seed, cfg[c][0], cfg[c][1], cfg[c][2], cfg[c][3], nrays);
    }
    printf("wtcheck leaf: %ld blocks (%ld lanes, %ld with a hit), SIMD != scalar %ld\n", leaf_blocks,
           leaf_lanes, leaf_hits, leaf_bad_blk);
    printf("wtcheck traversal: %ld rays (%ld hits), dispatched != scalar (t,u,v,prim) %ld, occluded %ld\n",
           trav_rays, trav_hits, trav_bad, occ_bad);
    printf("wtcheck batch (intersect1N/occluded1N x 2 hints, intersect4): != scalar %ld\n", batch_bad);
    printf("wtcheck save/load + refit: != scalar %ld\n", persist_bad);
    printf("wtcheck hits != tri_woop_one on the input vertices (build, load, refit): %ld\n", src_bad);
    printf("wtcheck readers: get_verts != input or intersect_n hit/miss != intersect1: %ld; "
           "fp64 path (MT on the same leaves) hit/miss != watertight %ld of %ld (report only)\n",
           reader_bad, hp_diff, hp_rays);
    printf("  (get_verts part: %ld; intersect_n[0].t != intersect1 t on %ld rays, max %ld ulp: the pruning slack\n"
           "   of both searches, Flat.run_approx; exact only under LRT_TRI_EXACT_NEAREST; report only)\n",
           gv_bad, mh_slack, mh_maxulp);
#ifdef LRT_TRI_EXACT_NEAREST
    printf("wtcheck EXACT_NEAREST (pruning key): intersect1 t != brute-force watertight t: %ld\n", exn_diff);
    int exn_bad = exn_diff != 0;
#else
    printf("wtcheck intersect1 t != brute force: %ld rays (%ld misses, must be 0), max %ld ulp (t: report only)\n",
           exn_diff, exn_miss, exn_maxulp);
    int exn_bad = exn_miss != 0; /* a miss where brute force hits = a slab false miss */
#endif
    int bad = leaf_bad_blk || trav_bad || occ_bad || batch_bad || persist_bad || src_bad || reader_bad || exn_bad;
    printf("RESULT: %s\n", bad ? "FAIL" : "PASS");
    return bad;
}
