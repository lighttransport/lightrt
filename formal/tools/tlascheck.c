/* TLAS/BLAS validator (formal/LightRT/BVH/TwoLevel.lean).
 *
 * Builds random BLAS meshes and instances with random affine transforms, then
 * for each ray checks
 *  1. `tlas_root`: lrt_tlas_intersect1 (t) == the brute-force minimum over all
 *     visible instances of the per-instance BLAS query on the same transformed
 *     ray (the "fold over (instance, primitive) pairs"). With
 *     -DLRT_TRI_EXACT_NEAREST the BLAS query is exact, so this must hold bit for
 *     bit; otherwise it is reported (best-dependent BLAS pruning, run_approx).
 *  2. any-hit: lrt_tlas_occluded1 == brute force any-hit.
 *  3. `hit_iff` + `xform_*_err`: the float result against an fp64 world-space
 *     Moller-Trumbore over the obj2world-transformed triangles (no float
 *     transform at all): hit/miss disagreements and max relative t error.
 * Usage: tlascheck SEED NRAYS ; prints one summary line, exit 1 on failure. */
#include "lightrt_c_tri.c"
#include <stdio.h>

static uint32_t rs = 1;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }
static float frand(void) { return (float)(rnd() & 0xffffff) / 16777216.0f; }

static int mt64(const double o[3], const double d[3], const double a[3], const double b[3],
                const double c[3], double tmin, double tmax, double *t) {
    double e1[3] = {b[0] - a[0], b[1] - a[1], b[2] - a[2]};
    double e2[3] = {c[0] - a[0], c[1] - a[1], c[2] - a[2]};
    double p[3] = {d[1] * e2[2] - d[2] * e2[1], d[2] * e2[0] - d[0] * e2[2],
                   d[0] * e2[1] - d[1] * e2[0]};
    double det = e1[0] * p[0] + e1[1] * p[1] + e1[2] * p[2];
    if (fabs(det) < 1e-300) return 0;
    double inv = 1.0 / det;
    double s[3] = {o[0] - a[0], o[1] - a[1], o[2] - a[2]};
    double u = (s[0] * p[0] + s[1] * p[1] + s[2] * p[2]) * inv;
    if (u < 0 || u > 1) return 0;
    double q[3] = {s[1] * e1[2] - s[2] * e1[1], s[2] * e1[0] - s[0] * e1[2],
                   s[0] * e1[1] - s[1] * e1[0]};
    double v = (d[0] * q[0] + d[1] * q[1] + d[2] * q[2]) * inv;
    if (v < 0 || u + v > 1) return 0;
    double tt = (e2[0] * q[0] + e2[1] * q[1] + e2[2] * q[2]) * inv;
    if (tt < tmin || tt >= tmax) return 0;
    *t = tt;
    return 1;
}

/* Exact (double) world image of each instance's BLAS root box must lie in the
 * TLAS slot box holding it (TwoLevel.aff_in_corner_box + this check = the
 * instance boxes contain the transformed BLAS geometry); inner boxes nest.
 * Corner coordinates m0*x + m1*y + m2*z + m3: each product is exact in double;
 * the 3 additions round at 2^-53, far below the float ulps checked. */
static long box_bad, box_checks;
static double box_worst;
static void chk_ge(double x, float lo) {
    box_checks++;
    if (!(x >= (double)lo)) {
        box_bad++;
        double e = ((double)lo - x) / (double)(nextafterf(lo, INFINITY) - lo);
        if (e > box_worst) box_worst = e;
    }
}
static void chk_le(double x, float hi) {
    box_checks++;
    if (!(x <= (double)hi)) {
        box_bad++;
        double e = (x - (double)hi) / (double)(hi - nextafterf(hi, -INFINITY));
        if (e > box_worst) box_worst = e;
    }
}
static void tlas_walk(const lrt_tlas *T, uint32_t ref, const float *lo, const float *hi) {
    if (TRI_REF_IS_LEAF(ref)) {
        uint32_t first = TRI_REF_BLOCK(ref), count = TRI_REF_NBLOCKS(ref);
        for (uint32_t k = 0; k < count; k++) {
            const lrt_instance_int *in = &T->insts[T->inst_refs[first + k]];
            if (in->degenerate) continue;
            const lrt_tri_scene *b = T->blas[in->blas_id];
            for (int c = 0; c < 8; c++) {
                double p[3] = {(c & 1) ? b->root_hi[0] : b->root_lo[0], (c & 2) ? b->root_hi[1] : b->root_lo[1],
                               (c & 4) ? b->root_hi[2] : b->root_lo[2]};
                for (int a = 0; a < 3; a++) {
                    const float *m = &in->obj2world[4 * a];
                    double w = (double)m[0] * p[0] + (double)m[1] * p[1] + (double)m[2] * p[2] + (double)m[3];
                    chk_ge(w, lo[a]); chk_le(w, hi[a]);
                }
            }
        }
        return;
    }
    const lrt_bvh4_node *n = &T->nodes[TRI_REF_NODE(ref)];
    for (int i = 0; i < (int)n->nchildren; i++) {
        float clo[3] = {n->lo_x[i], n->lo_y[i], n->lo_z[i]}, chi[3] = {n->hi_x[i], n->hi_y[i], n->hi_z[i]};
        if (lo) for (int a = 0; a < 3; a++) { chk_ge(clo[a], lo[a]); chk_le(chi[a], hi[a]); }
        tlas_walk(T, n->child[i], clo, chi);
    }
}

int main(int argc, char **argv) {
    rs = argc > 1 ? (uint32_t)atoi(argv[1]) * 2654435761u + 1 : 1;
    int nrays = argc > 2 ? atoi(argv[2]) : 2000;
    enum { NB = 3, NT = 300, NI = 60 };
    float *verts[NB];
    lrt_tri_scene *blas[NB];
    for (int b = 0; b < NB; b++) {
        verts[b] = malloc(sizeof(float) * 9 * NT);
        for (int i = 0; i < NT; i++) {
            float c[3] = {frand() * 2 - 1, frand() * 2 - 1, frand() * 2 - 1};
            for (int k = 0; k < 3; k++)
                for (int a = 0; a < 3; a++)
                    verts[b][9 * i + 3 * k + a] = c[a] + (frand() - 0.5f) * 0.4f;
        }
        lrt_tri_build_options o = {0};
        o.layout = b == 1 ? LRT_TRI_LAYOUT_BVH8 : LRT_TRI_LAYOUT_BVH4;
        o.quality = (lrt_tri_quality)(b % 2);
        lrt_result err;
        blas[b] = lrt_tri_scene_build(verts[b], NT, &o, &err);
        if (!blas[b]) { fprintf(stderr, "blas build failed\n"); return 1; }
    }
    lrt_instance inst[NI];
    for (int i = 0; i < NI; i++) {
        /* random rotation (axis-angle) * nonuniform scale, translation in [-8,8] */
        float ax[3] = {frand() - 0.5f, frand() - 0.5f, frand() - 0.5f};
        float n = sqrtf(ax[0] * ax[0] + ax[1] * ax[1] + ax[2] * ax[2]) + 1e-6f;
        for (int a = 0; a < 3; a++) ax[a] /= n;
        float th = frand() * 6.2831853f, cs = cosf(th), sn = sinf(th), C = 1 - cs;
        float Rm[9] = {cs + ax[0] * ax[0] * C, ax[0] * ax[1] * C - ax[2] * sn, ax[0] * ax[2] * C + ax[1] * sn,
                       ax[1] * ax[0] * C + ax[2] * sn, cs + ax[1] * ax[1] * C, ax[1] * ax[2] * C - ax[0] * sn,
                       ax[2] * ax[0] * C - ax[1] * sn, ax[2] * ax[1] * C + ax[0] * sn, cs + ax[2] * ax[2] * C};
        float sc[3] = {0.3f + frand() * 2, 0.3f + frand() * 2, 0.3f + frand() * 2};
        inst[i].blas_id = (uint32_t)(i % NB);
        inst[i].instance_id = 1000u + (uint32_t)i;
        inst[i].mask = (i % 7 == 3) ? 2u : 1u;
        for (int r = 0; r < 3; r++) {
            for (int c = 0; c < 3; c++) inst[i].obj2world[4 * r + c] = Rm[3 * r + c] * sc[c];
            inst[i].obj2world[4 * r + 3] = (frand() - 0.5f) * 16.0f;
        }
    }
    lrt_result err;
    lrt_tlas *T = lrt_tlas_build(blas, NB, inst, NI, NULL, &err);
    if (!T) { fprintf(stderr, "tlas build failed\n"); return 1; }

    if (!TRI_REF_IS_LEAF(T->root)) tlas_walk(T, T->root, NULL, NULL);
    printf("tlas boxes: %ld exact containment checks, %ld fail (worst %.2f ulp)\n", box_checks, box_bad,
           box_worst);
    int bad_t = 0, bad_any = 0, approx_t = 0, miss64 = 0, n64 = 0;
    long npair = 0, margin_bad = 0, sbound_bad = 0;
    double margin_worst = 0;
    double max_rel = 0;
    for (int r = 0; r < nrays; r++) {
        lrt_ray ray;
        for (int a = 0; a < 3; a++) ray.org[a] = (frand() - 0.5f) * 30.0f;
        float tgt[3] = {(frand() - 0.5f) * 14.0f, (frand() - 0.5f) * 14.0f, (frand() - 0.5f) * 14.0f};
        for (int a = 0; a < 3; a++) ray.dir[a] = tgt[a] - ray.org[a];
        if (r % 9 == 4) ray.dir[1] = 0.0f;
        ray.tmin = 0.0f;
        ray.tmax = (r % 5 == 1) ? 0.8f : 1e30f;
        uint32_t mask = (r % 3 == 0) ? 3u : 1u;
        lrt_tlas_hit th;
        int k = lrt_tlas_intersect1(T, &ray, mask, &th);
        int occ = lrt_tlas_occluded1(T, &ray, mask);
        /* brute force over instances: same transformed ray, BLAS query with full tmax */
        float bt = ray.tmax;
        int bk = 0;
        for (uint32_t i = 0; i < T->ninsts; i++) {
            const lrt_instance_int *in = &T->insts[i];
            if (in->degenerate || !(in->mask & mask)) continue;
            lrt_ray q;
            tlas_xform_point(in->world2obj, ray.org, q.org);
            tlas_xform_vec(in->world2obj, ray.dir, q.dir);
            q.tmin = ray.tmin;
            q.tmax = ray.tmax;
            lrt_hit h;
            if (!lrt_tri_intersect1(T->blas[in->blas_id], &q, &h)) continue;
            if (h.t < bt) { bt = h.t; bk = 1; }
#ifdef LRT_TRI_LEAF_BOX_EXACT
            /* TwoLevel.world_near_obj: |o + s d - A(q.org + s q.dir)| <= alpha(|o|+|s||d|) + beta */
            long double sv = h.t, on = 0, dn = 0, worst = 0;
            for (int a = 0; a < 3; a++) { on += fabsl((long double)ray.org[a]); dn += fabsl((long double)ray.dir[a]); }
            long double qp[3];
            for (int a = 0; a < 3; a++) qp[a] = (long double)q.org[a] + sv * (long double)q.dir[a];
            for (int a = 0; a < 3; a++) {
                const float *m = &in->obj2world[4 * a];
                long double aq = (long double)m[0] * qp[0] + (long double)m[1] * qp[1] +
                                 (long double)m[2] * qp[2] + (long double)m[3];
                long double w = (long double)ray.org[a] + sv * (long double)ray.dir[a];
                long double e = fabsl(w - aq);
                if (e > worst) worst = e;
            }
            long double bound = (long double)in->alpha * (on + fabsl(sv) * dn) + (long double)in->beta;
            double ratio = (double)(worst / bound);
            npair++;
            if (ratio > margin_worst) margin_worst = ratio;
            if (ratio > 1.0) margin_bad++;
            /* TwoLevel.s_bound */
            if (fabsl(sv) > 0 && (double)fabsl(sv) > 0) {
                tlas_dil dl;
                tlas_dil_setup(T, &ray, &dl);
                if ((double)fabsl(sv) > dl.sgeo) sbound_bad++;
            }
#endif
        }
        if (k != bk || (k && th.t != bt)) {
#ifdef LRT_TRI_EXACT_NEAREST
            if (bad_t < 5) fprintf(stderr, "ray %d: tlas %d %.9g brute %d %.9g\n", r, k, th.t, bk, bt);
            bad_t++;
#else
            approx_t++;
#endif
        }
        if (occ != bk) {
            if (bad_any < 5) fprintf(stderr, "ray %d: occluded %d brute %d\n", r, occ, bk);
            bad_any++;
        }
        /* fp64 world-space reference: transform the triangles, not the ray */
        double o64[3] = {ray.org[0], ray.org[1], ray.org[2]}, d64[3] = {ray.dir[0], ray.dir[1], ray.dir[2]};
        double best = ray.tmax;
        int hk = 0;
        for (int i = 0; i < NI; i++) {
            if (!(inst[i].mask & mask)) continue;
            const float *M = inst[i].obj2world, *V = verts[inst[i].blas_id];
            for (int p = 0; p < NT; p++) {
                double w[3][3];
                for (int c = 0; c < 3; c++)
                    for (int a = 0; a < 3; a++)
                        w[c][a] = (double)M[4 * a] * V[9 * p + 3 * c] + (double)M[4 * a + 1] * V[9 * p + 3 * c + 1] +
                                  (double)M[4 * a + 2] * V[9 * p + 3 * c + 2] + (double)M[4 * a + 3];
                double t;
                if (mt64(o64, d64, w[0], w[1], w[2], ray.tmin, best, &t)) { best = t; hk = 1; }
            }
        }
        if (hk != k) miss64++;
        else if (k) {
            double rel = fabs(th.t - best) / fmax(fabs(best), 1e-30);
            if (rel > max_rel) max_rel = rel;
            n64++;
        }
    }
    printf("tlascheck seed=%s rays=%d exactn=%d: tlas!=brute(t)=%d%s any-hit!=brute=%d "
           "fp64-world hit/miss=%d max-rel-t=%.3g over %d hits\n",
           argc > 1 ? argv[1] : "1", nrays,
#ifdef LRT_TRI_EXACT_NEAREST
           1,
#else
           0,
#endif
           bad_t + approx_t, approx_t ? " (approx: BLAS not exact-nearest)" : "", bad_any, miss64,
           max_rel, n64);
#ifdef LRT_TRI_LEAF_BOX_EXACT
    printf("tlas margin: %ld pair hits, |world - A(obj)| / bound worst %.3g, over bound %ld, |s| > s_bound %ld\n",
           npair, margin_worst, margin_bad, sbound_bad);
#endif
    lrt_tlas_free(T);
    for (int b = 0; b < NB; b++) { lrt_tri_scene_free(blas[b]); free(verts[b]); }
    return (bad_t || bad_any || box_bad || margin_bad || sbound_bad) ? 1 : 0;
}
