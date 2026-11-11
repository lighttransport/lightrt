/* High-precision hit-accuracy reference for curves, points and patches.
 *
 * For each primitive kind, random rays are traced with the C kernel
 * (lrt_tri_intersect1) and compared, in double precision, with
 *  - the RESIDUAL of the reported hit on the exact stored geometry:
 *      tubes/points: d(x) = min_s |x - c(s)| - r(s) at x = o + t d (round
 *        curves are the union of balls B(c(s), r(s)); c, r linear for
 *        round-linear, cubic Bezier for Bezier curves);
 *      patches: |S(u,v) - (o + t d)| at the reported (u,v) (NURBS: mapped to
 *        the extracted patch's local domain);
 *  - an INDEPENDENT nearest-hit reference: sphere tracing on the exact
 *    union-of-balls distance (tubes/points), or MT on a fine double-precision
 *    tessellation of every patch (patches; error O(h^2) of the tessellation).
 * Reported per kind: hits, hit/miss disagreements (split by whether the
 * reference ray passes within `graze` of the silhouette), max |t - t_ref|*|d|,
 * and the max / 99.9th-percentile residual. Thresholds (exit 1) are set well
 * above measured values; see formal/PLAN.md M10.
 * Usage: primhitcheck SEED NRAYS */
#include "lightrt_c_tri.c"
#include <stdio.h>

static uint32_t rs = 1;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }
static float frand(void) { return (float)(rnd() & 0xffffff) / 16777216.0f; }
static float fr(float lo, float hi) { return lo + (hi - lo) * frand(); }

/* ---------- tube distance: c(s), r(s) for linear (n=2) or cubic (n=4) ---------- */
typedef struct { double p[4][3], r[4]; int n; } tube_t;
static void tube_eval(const tube_t *T, double s, double c[3], double *r) {
    if (T->n == 2) {
        for (int a = 0; a < 3; a++) c[a] = (1 - s) * T->p[0][a] + s * T->p[1][a];
        *r = (1 - s) * T->r[0] + s * T->r[1];
        return;
    }
    double u = 1 - s, b[4] = {u * u * u, 3 * s * u * u, 3 * s * s * u, s * s * s};
    *r = 0;
    for (int a = 0; a < 3; a++) c[a] = 0;
    for (int k = 0; k < 4; k++) {
        for (int a = 0; a < 3; a++) c[a] += b[k] * T->p[k][a];
        *r += b[k] * T->r[k];
    }
}
static double tube_f(const tube_t *T, double s, const double x[3]) {
    double c[3], r;
    tube_eval(T, s, c, &r);
    double dx = x[0] - c[0], dy = x[1] - c[1], dz = x[2] - c[2];
    return sqrt(dx * dx + dy * dy + dz * dz) - r;
}
/* min over s in [0,1]: dense sampling + golden-section refinement */
static double tube_golden(const tube_t *T, const double x[3], double a, double b) {
    const double g = 0.6180339887498949;
    double c = b - g * (b - a), d = a + g * (b - a), fc = tube_f(T, c, x), fd = tube_f(T, d, x);
    for (int it = 0; it < 60; it++) {
        if (fc < fd) { b = d; d = c; fd = fc; c = b - g * (b - a); fc = tube_f(T, c, x); }
        else { a = c; c = d; fc = fd; d = a + g * (b - a); fd = tube_f(T, d, x); }
    }
    return fmin(fc, fd);
}
/* min over s in [0,1]: dense sampling, then golden-section refinement around
 * EVERY sampled local minimum (refining only the best sample can pick the
 * wrong basin and overestimate the distance, which made this reference miss
 * thin parts of strongly curved cubics) */
static double tube_dist(const tube_t *T, const double x[3]) {
    enum { NS = 256 };
    double f[NS + 1];
    for (int i = 0; i <= NS; i++) f[i] = tube_f(T, (double)i / NS, x);
    double best = f[0];
    for (int i = 0; i <= NS; i++) {
        if (f[i] < best) best = f[i];
        int lm = (i == 0 || f[i] <= f[i - 1]) && (i == NS || f[i] <= f[i + 1]);
        if (lm) {
            double a = fmax(0, (i - 1.0) / NS), b = fmin(1, (i + 1.0) / NS);
            best = fmin(best, tube_golden(T, x, a, b));
        }
    }
    return best;
}
/* double slab entry/exit against [lo,hi] */
static int slab64(const double o[3], const double d[3], const double lo[3], const double hi[3],
                  double tmin, double tmax, double *t0, double *t1) {
    for (int a = 0; a < 3; a++) {
        if (d[a] == 0) { if (o[a] < lo[a] || o[a] > hi[a]) return 0; continue; }
        double ta = (lo[a] - o[a]) / d[a], tb = (hi[a] - o[a]) / d[a];
        if (ta > tb) { double t = ta; ta = tb; tb = t; }
        if (ta > tmin) tmin = ta;
        if (tb < tmax) tmax = tb;
    }
    *t0 = tmin; *t1 = tmax;
    return tmin <= tmax;
}
/* first t in [t0, t1) where the tube distance reaches 0 (sphere tracing; the
 * union-of-balls distance is 1-Lipschitz, so steps never skip the surface) */
static int tube_trace(const tube_t *T, const double o[3], const double d[3], double t0, double t1,
                      double *th) {
    double dn = sqrt(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]), t = t0, tp = t0;
    for (int it = 0; it < 4000 && t < t1; it++) {
        double x[3] = {o[0] + t * d[0], o[1] + t * d[1], o[2] + t * d[2]};
        double f = tube_dist(T, x);
        if (f < 0 && t > tp) {
            /* overshot (the sampled distance can overestimate): bisect back to
             * the sign change between the last outside point and here */
            double a = tp, b = t;
            for (int k = 0; k < 80; k++) {
                double m = 0.5 * (a + b), y[3] = {o[0] + m * d[0], o[1] + m * d[1], o[2] + m * d[2]};
                if (tube_dist(T, y) < 0) b = m; else a = m;
            }
            *th = b;
            return 1;
        }
        if (f < 1e-10) { *th = t; return 1; }
        tp = t;
        t += 0.9 * f / dn;
    }
    return 0;
}
static void tube_box(const tube_t *T, double lo[3], double hi[3]) {
    for (int a = 0; a < 3; a++) { lo[a] = 1e300; hi[a] = -1e300; }
    for (int k = 0; k < T->n; k++)
        for (int a = 0; a < 3; a++) {
            lo[a] = fmin(lo[a], T->p[k][a] - T->r[k]);
            hi[a] = fmax(hi[a], T->p[k][a] + T->r[k]);
        }
}

/* ---------- patches: exact double eval + tessellated reference ---------- */
typedef struct { double cp[16][4]; int rational; double dom[4]; } patch_t; /* cp[k] k=4j+i */
static void patch_eval(const patch_t *P, double u, double v, double S[3]) {
    double bu[4], bv[4], uu = 1 - u, vv = 1 - v;
    bu[0] = uu * uu * uu; bu[1] = 3 * u * uu * uu; bu[2] = 3 * u * u * uu; bu[3] = u * u * u;
    bv[0] = vv * vv * vv; bv[1] = 3 * v * vv * vv; bv[2] = 3 * v * v * vv; bv[3] = v * v * v;
    double N[4] = {0, 0, 0, 0};
    for (int j = 0; j < 4; j++)
        for (int i = 0; i < 4; i++)
            for (int c = 0; c < 4; c++) N[c] += bu[i] * bv[j] * P->cp[4 * j + i][c];
    for (int a = 0; a < 3; a++) S[a] = P->rational ? N[a] / N[3] : N[a];
}
static void bilin_eval(const double q[4][3], double u, double v, double S[3]) {
    for (int a = 0; a < 3; a++)
        S[a] = (1 - u) * (1 - v) * q[0][a] + u * (1 - v) * q[1][a] + u * v * q[2][a] + (1 - u) * v * q[3][a];
}
static int mt64(const double o[3], const double d[3], const double a[3], const double b[3],
                const double c[3], double tmin, double tmax, double *t) {
    double e1[3] = {b[0] - a[0], b[1] - a[1], b[2] - a[2]}, e2[3] = {c[0] - a[0], c[1] - a[1], c[2] - a[2]};
    double p[3] = {d[1] * e2[2] - d[2] * e2[1], d[2] * e2[0] - d[0] * e2[2], d[0] * e2[1] - d[1] * e2[0]};
    double det = e1[0] * p[0] + e1[1] * p[1] + e1[2] * p[2];
    if (fabs(det) < 1e-300) return 0;
    double inv = 1 / det, s[3] = {o[0] - a[0], o[1] - a[1], o[2] - a[2]};
    double u = (s[0] * p[0] + s[1] * p[1] + s[2] * p[2]) * inv;
    if (u < 0 || u > 1) return 0;
    double q[3] = {s[1] * e1[2] - s[2] * e1[1], s[2] * e1[0] - s[0] * e1[2], s[0] * e1[1] - s[1] * e1[0]};
    double v = (d[0] * q[0] + d[1] * q[1] + d[2] * q[2]) * inv;
    if (v < 0 || u + v > 1) return 0;
    double tt = (e2[0] * q[0] + e2[1] * q[1] + e2[2] * q[2]) * inv;
    if (tt < tmin || tt >= tmax) return 0;
    *t = tt;
    return 1;
}
/* Exact (double) nearest root of the ray on one patch: multi-start Newton on
 * S(u,v) = o + t d with a central-difference Jacobian; used only to adjudicate
 * a "C farther than the tessellation" case (near silhouettes and at grazing
 * angles the 128x128 tessellation is off by more than the tolerance). */
static void any_eval(const patch_t *P, const double (*q)[3], double u, double v, double S[3]) {
    if (q) bilin_eval(q, u, v, S); else patch_eval(P, u, v, S);
}
static int exact_patch_hit(const patch_t *P, const double (*q)[3], const double o[3], const double d[3],
                           double *t_out) {
    double best = 1e300;
    int hit = 0;
    for (int a = 0; a <= 12; a++)
        for (int b = 0; b <= 12; b++) {
            double u = a / 12.0, v = b / 12.0, S[3];
            any_eval(P, q, u, v, S);
            double t = ((S[0] - o[0]) * d[0] + (S[1] - o[1]) * d[1] + (S[2] - o[2]) * d[2]) /
                       (d[0] * d[0] + d[1] * d[1] + d[2] * d[2]);
            for (int it = 0; it < 60; it++) {
                any_eval(P, q, u, v, S);
                double F[3] = {S[0] - o[0] - t * d[0], S[1] - o[1] - t * d[1], S[2] - o[2] - t * d[2]};
                if (sqrt(F[0] * F[0] + F[1] * F[1] + F[2] * F[2]) < 1e-12) {
                    if (u >= 0 && u <= 1 && v >= 0 && v <= 1 && t >= 0 && t < best) { best = t; hit = 1; }
                    break;
                }
                double h = 1e-7, Sa[3], Sb[3], du[3], dv[3];
                any_eval(P, q, u + h, v, Sa); any_eval(P, q, u - h, v, Sb);
                for (int c = 0; c < 3; c++) du[c] = (Sa[c] - Sb[c]) / (2 * h);
                any_eval(P, q, u, v + h, Sa); any_eval(P, q, u, v - h, Sb);
                for (int c = 0; c < 3; c++) dv[c] = (Sa[c] - Sb[c]) / (2 * h);
                double M[3][3] = {{du[0], dv[0], -d[0]}, {du[1], dv[1], -d[1]}, {du[2], dv[2], -d[2]}};
                double det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
                             M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
                             M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);
                if (fabs(det) < 1e-30) break;
                double X[3];
                for (int c = 0; c < 3; c++) {
                    double N[3][3];
                    for (int r = 0; r < 3; r++)
                        for (int k = 0; k < 3; k++) N[r][k] = (k == c) ? F[r] : M[r][k];
                    X[c] = (N[0][0] * (N[1][1] * N[2][2] - N[1][2] * N[2][1]) -
                            N[0][1] * (N[1][0] * N[2][2] - N[1][2] * N[2][0]) +
                            N[0][2] * (N[1][0] * N[2][1] - N[1][1] * N[2][0])) / det;
                }
                u -= X[0]; v -= X[1]; t -= X[2];
                if (fabs(u) > 3 || fabs(v) > 3) break;
            }
        }
    *t_out = best;
    return hit;
}

#define TESS 128
/* nearest hit on a tessellated surface; grid[(TESS+1)^2][3] */
static int tess_trace(const double (*g)[3], const double o[3], const double d[3], double tmin,
                      double tmax, double *th) {
    int hit = 0;
    for (int j = 0; j < TESS; j++)
        for (int i = 0; i < TESS; i++) {
            const double *a = g[j * (TESS + 1) + i], *b = g[j * (TESS + 1) + i + 1],
                         *c = g[(j + 1) * (TESS + 1) + i + 1], *e = g[(j + 1) * (TESS + 1) + i];
            double t;
            if (mt64(o, d, a, b, c, tmin, tmax, &t)) { tmax = t; hit = 1; }
            if (mt64(o, d, a, c, e, tmin, tmax, &t)) { tmax = t; hit = 1; }
        }
    *th = tmax;
    return hit;
}

/* ---------- per-kind driver ---------- */
typedef struct {
    const char *name;
    int hits, rays, mism, mism_graze, tdiff_bad, c_farther, ref_artifact;
    double max_dt, max_res, res[1 << 16];
    int nres;
} stat_t;

static int cmpd(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return x < y ? -1 : x > y;
}
/* strict: no t disagreement beyond tolerance at all; loose (adaptive Bezier
 * sweep): a bounded rate of "C returned a farther hit" (missed the nearest) */
static int finish(stat_t *st, double res_tol, int loose) {
    qsort(st->res, (size_t)st->nres, sizeof(double), cmpd);
    double p999 = st->nres ? st->res[(int)(0.999 * (st->nres - 1))] : 0;
    int nongraze = st->mism - st->mism_graze;
    int nbig = 0;
    for (int i = 0; i < st->nres; i++) nbig += st->res[i] > res_tol;
    /* loose: the documented cone fallback (ill-conditioned Newton) is approximate */
    int fail = loose ? nbig > 0.002 * st->hits : st->max_res > res_tol;
    if (loose) fail |= st->c_farther > 0.005 * st->hits || nongraze > 0.005 * st->rays;
    /* strict: C never returns a FARTHER hit than the reference. A NEARER one
     * with a tiny residual is a reference limitation (the 128x128 patch
     * tessellation can miss a silhouette sliver), not a C error. */
    else fail |= st->c_farther > 0 || nongraze > 0.002 * st->rays;
    printf("%-9s rays=%d hits=%d hit/miss-vs-ref=%d (grazing %d) t>tol=%d (C farther %d) max|dt|=%.2e "
           "residual max=%.2e p99.9=%.2e (>%.0e: %d) tess-artifacts=%d%s\n",
           st->name, st->rays, st->hits, st->mism, st->mism_graze, st->tdiff_bad, st->c_farther, st->max_dt,
           st->max_res, p999, res_tol, nbig, st->ref_artifact, fail ? "  FAIL" : "");
    return fail;
}

static void random_ray(lrt_ray *ray, const double tgt[3]) {
    for (int a = 0; a < 3; a++) ray->org[a] = (float)(tgt[a] + fr(-6, 6));
    for (int a = 0; a < 3; a++) ray->dir[a] = (float)(tgt[a] + fr(-0.3f, 0.3f) - ray->org[a]);
    ray->tmin = 0; ray->tmax = 1e30f;
}

/* tubes: tub[n], scene s, prim id -> tube */
static int run_tubes(const char *name, lrt_tri_scene *s, tube_t *tub, int n, int nrays, int loose,
                     double res_tol) {
    static stat_t st;
    memset(&st, 0, sizeof st);
    st.name = name;
    for (int r = 0; r < nrays; r++) {
        const tube_t *T0 = &tub[rnd() % n];
        double tgt[3];
        double rr;
        tube_eval(T0, frand(), tgt, &rr);
        lrt_ray ray;
        /* surfaces, not solids: keep origins outside every tube */
        for (int tries = 0; tries < 100; tries++) {
            random_ray(&ray, tgt);
            double x[3] = {ray.org[0], ray.org[1], ray.org[2]}, m = 1e300;
            for (int p = 0; p < n; p++) m = fmin(m, tube_dist(&tub[p], x));
            if (m > 1e-3) break;
        }
        lrt_hit h;
        int k = lrt_tri_intersect1(s, &ray, &h);
        double o[3] = {ray.org[0], ray.org[1], ray.org[2]}, d[3] = {ray.dir[0], ray.dir[1], ray.dir[2]};
        double dn = sqrt(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]);
        double best = 1e300, graze = 1e300;
        int hk = 0;
        for (int p = 0; p < n; p++) {
            double lo[3], hi[3], t0, t1, th;
            tube_box(&tub[p], lo, hi);
            if (!slab64(o, d, lo, hi, 0, best, &t0, &t1)) continue;
            if (tube_trace(&tub[p], o, d, t0, fmin(t1, best), &th)) { best = th; hk = 1; }
        }
        /* grazing: closest approach of the ray to the surface near the C/ref answer */
        st.rays++;
        if (k) {
            st.hits++;
            double x[3] = {o[0] + h.t * d[0], o[1] + h.t * d[1], o[2] + h.t * d[2]};
            double res = fabs(tube_dist(&tub[h.prim_id < (uint32_t)n ? h.prim_id : 0], x));
            if (res > st.max_res) st.max_res = res;
            if (st.nres < (1 << 16)) st.res[st.nres++] = res;
            if (res > 1e-4 && getenv("PHC_VERBOSE")) {
                const tube_t *T = &tub[h.prim_id];
                double rmin = fmin(fmin(T->r[0], T->r[1]), T->n == 4 ? fmin(T->r[2], T->r[3]) : 1e9);
                fprintf(stderr, "%s ray %d prim %u: residual %.3g (r_min %.3g) t=%.6g ref=%s %.6g u=%.4f\n", name, r,
                        h.prim_id, res, rmin, h.t, hk ? "hit" : "miss", best, h.u);
            }
        }
        if (k != hk) {
            st.mism++;
            /* a disagreement is "grazing" if the other answer's ray passes within 1e-4 of a tube */
            double tt = k ? h.t : best, x[3] = {o[0] + tt * d[0], o[1] + tt * d[1], o[2] + tt * d[2]};
            graze = 1e300;
            for (int p = 0; p < n; p++) graze = fmin(graze, fabs(tube_dist(&tub[p], x)));
            if (graze < 1e-4 || !k) {
                /* C missed: check the reference hit is near-tangent: min distance along a
                 * short window around best is ~0 only at a touch */
                double m = 1e300;
                for (int q = -20; q <= 20; q++) {
                    double t = best + q * 1e-3 / dn, y[3] = {o[0] + t * d[0], o[1] + t * d[1], o[2] + t * d[2]};
                    for (int p = 0; p < n; p++) m = fmin(m, tube_dist(&tub[p], y));
                }
                if (k || m > -1e-4) st.mism_graze++;
            }
        } else if (k) {
            double dt = fabs(h.t - best) * dn;
            if (dt > st.max_dt) st.max_dt = dt;
            if (dt > 1e-3) {
                st.tdiff_bad++;
                if (h.t > best) st.c_farther++;
                if (getenv("PHC_VERBOSE"))
                    fprintf(stderr, "%s ray %d: C t=%.7g prim %u, ref t=%.7g (C %s)\n", name, r, h.t, h.prim_id,
                            best, h.t > best ? "farther: missed the nearest" : "nearer: ref missed");
            }
        }
    }
    return finish(&st, res_tol, loose);
}

static int run_patches(const char *name, lrt_tri_scene *s, patch_t *pt, double (*bq)[4][3], int n,
                       int nrays) {
    static stat_t st;
    memset(&st, 0, sizeof st);
    st.name = name;
    double (*grid)[(TESS + 1) * (TESS + 1)][3] = malloc(sizeof(*grid) * (size_t)n);
    double (*plo)[3] = malloc(sizeof(double) * 3 * n), (*phi)[3] = malloc(sizeof(double) * 3 * n);
    for (int p = 0; p < n; p++) {
        for (int a = 0; a < 3; a++) { plo[p][a] = 1e300; phi[p][a] = -1e300; }
        for (int j = 0; j <= TESS; j++)
            for (int i = 0; i <= TESS; i++) {
                double S[3];
                if (bq) bilin_eval(bq[p], (double)i / TESS, (double)j / TESS, S);
                else patch_eval(&pt[p], (double)i / TESS, (double)j / TESS, S);
                for (int a = 0; a < 3; a++) {
                    grid[p][j * (TESS + 1) + i][a] = S[a];
                    plo[p][a] = fmin(plo[p][a], S[a]); phi[p][a] = fmax(phi[p][a], S[a]);
                }
            }
    }
    for (int r = 0; r < nrays; r++) {
        int p0 = (int)(rnd() % (uint32_t)n);
        double tgt[3];
        if (bq) bilin_eval(bq[p0], frand(), frand(), tgt);
        else patch_eval(&pt[p0], frand(), frand(), tgt);
        lrt_ray ray;
        random_ray(&ray, tgt);
        lrt_hit h;
        int k = lrt_tri_intersect1(s, &ray, &h);
        double o[3] = {ray.org[0], ray.org[1], ray.org[2]}, d[3] = {ray.dir[0], ray.dir[1], ray.dir[2]};
        double dn = sqrt(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]);
        double best = 1e300;
        int hk = 0;
        for (int p = 0; p < n; p++) {
            double t0, t1, th;
            double lo[3] = {plo[p][0] - 1e-3, plo[p][1] - 1e-3, plo[p][2] - 1e-3},
                   hi[3] = {phi[p][0] + 1e-3, phi[p][1] + 1e-3, phi[p][2] + 1e-3};
            if (!slab64(o, d, lo, hi, 0, best, &t0, &t1)) continue;
            if (tess_trace((const double (*)[3])grid[p], o, d, 0, best, &th)) { best = th; hk = 1; }
        }
        st.rays++;
        if (k) {
            st.hits++;
            uint32_t pid = h.prim_id < (uint32_t)n ? h.prim_id : 0;
            double u = h.u, v = h.v, S[3];
            if (!bq && pt[pid].rational) {
                const double *dm = pt[pid].dom;
                u = (u - dm[0]) / (dm[1] - dm[0]);
                v = (v - dm[2]) / (dm[3] - dm[2]);
            }
            if (bq) bilin_eval(bq[pid], u, v, S);
            else patch_eval(&pt[pid], u, v, S);
            double e = 0;
            for (int a = 0; a < 3; a++) e = fmax(e, fabs(S[a] - (o[a] + h.t * d[a])));
            if (e > st.max_res) st.max_res = e;
            if (st.nres < (1 << 16)) st.res[st.nres++] = e;
            if (e > 1e-4 && getenv("PHC_VERBOSE"))
                fprintf(stderr, "%s ray %d prim %u: residual %.3g t=%.7g u=%.6f v=%.6f ref %s t=%.7g\n"
                        "  org %a %a %a dir %a %a %a\n", name, r, h.prim_id, e, h.t, h.u, h.v,
                        hk ? "hit" : "miss", best, ray.org[0], ray.org[1], ray.org[2], ray.dir[0], ray.dir[1],
                        ray.dir[2]);
            if (e > 1e-4 && getenv("PHC_VERBOSE")) {
                double x[3] = {o[0] + h.t * d[0], o[1] + h.t * d[1], o[2] + h.t * d[2]}, bd = 1e300;
                int bp = -1;
                for (int p = 0; p < n; p++)
                    for (int q = 0; q < (TESS + 1) * (TESS + 1); q++) {
                        double dd = 0;
                        for (int a = 0; a < 3; a++) dd = fmax(dd, fabs(grid[p][q][a] - x[a]));
                        if (dd < bd) { bd = dd; bp = p; }
                    }
                fprintf(stderr, "  nearest surface to the C hit point: patch %d at %.3g (grid)\n", bp, bd);
            }
        }
        if (k != hk) {
            st.mism++;
            /* tessellation vs exact surface near a silhouette: count as grazing when
             * the hit that exists is within the tessellation error band of an edge */
            /* C missed but the tessellation hit (or the reverse): decide with
             * the exact roots. A confirmed exact hit that C missed is a real
             * C miss (fails); otherwise it is a tessellation artifact. A C hit
             * with no tessellation hit is already checked by its residual. */
            if (!k && hk) {
                double et = 1e300;
                for (int p = 0; p < n; p++) {
                    double t0, t1, th;
                    double lo[3] = {plo[p][0] - 1e-3, plo[p][1] - 1e-3, plo[p][2] - 1e-3},
                           hi[3] = {phi[p][0] + 1e-3, phi[p][1] + 1e-3, phi[p][2] + 1e-3};
                    if (!slab64(o, d, lo, hi, 0, et, &t0, &t1)) continue;
                    if (exact_patch_hit(bq ? NULL : &pt[p], bq ? (const double (*)[3])bq[p] : NULL, o, d, &th) &&
                        th < et)
                        et = th;
                }
                if (et < 1e300) st.c_farther++; /* exact hit exists: C missed it */
                else { st.ref_artifact++; st.mism_graze++; }
            } else {
                st.ref_artifact++;
                st.mism_graze++;
            }
        } else if (k) {
            double dt = fabs(h.t - best) * dn;
            if (dt > st.max_dt) st.max_dt = dt;
            if (dt > 2e-3) {
                st.tdiff_bad++;
                if (h.t > best) {
                    /* adjudicate with the exact root over every patch the ray's
                     * box test admits: only a confirmed nearer exact hit counts */
                    double et = 1e300;
                    for (int p = 0; p < n; p++) {
                        double t0, t1, th;
                        double lo[3] = {plo[p][0] - 1e-3, plo[p][1] - 1e-3, plo[p][2] - 1e-3},
                               hi[3] = {phi[p][0] + 1e-3, phi[p][1] + 1e-3, phi[p][2] + 1e-3};
                        if (!slab64(o, d, lo, hi, 0, et, &t0, &t1)) continue;
                        if (exact_patch_hit(bq ? NULL : &pt[p], bq ? (const double (*)[3])bq[p] : NULL, o, d, &th) &&
                            th < et)
                            et = th;
                    }
                    if (et < h.t - 2e-3 / dn) st.c_farther++;
                    else st.ref_artifact++;
                }
            }
        }
    }
    free(grid); free(plo); free(phi);
    return finish(&st, 1e-4, 0);
}

int main(int argc, char **argv) {
    rs = argc > 1 ? (uint32_t)atoi(argv[1]) * 2654435761u + 3 : 3;
    int nrays = argc > 2 ? atoi(argv[2]) : 300;
    int bad = 0;
    lrt_result err;
    /* round-linear hair */
    enum { NS = 60, NP = 5 };
    float pts[NS * NP * 3], rad[NS * NP];
    uint32_t first[NS], cnt[NS];
    for (int s = 0; s < NS; s++) {
        float b[3] = {fr(-3, 3), fr(-3, 3), fr(-3, 3)};
        first[s] = (uint32_t)(s * NP); cnt[s] = NP;
        for (int k = 0; k < NP; k++) {
            for (int a = 0; a < 3; a++) pts[(s * NP + k) * 3 + a] = b[a] + fr(-0.25f, 0.25f) * (float)k;
            rad[s * NP + k] = fr(0.01f, 0.08f);
        }
    }
    lrt_hair_strands hs = {pts, rad, 0.0f, first, cnt, NS, NS * NP};
    tube_t *tub = malloc(sizeof(tube_t) * NS * NP);
    int nt = 0;
    for (int s = 0; s < NS; s++)
        for (int k = 0; k + 1 < NP; k++, nt++) {
            tub[nt].n = 2;
            for (int e = 0; e < 2; e++) {
                for (int a = 0; a < 3; a++) tub[nt].p[e][a] = pts[(s * NP + k + e) * 3 + a];
                tub[nt].r[e] = rad[s * NP + k + e];
            }
        }
    lrt_tri_scene *sc = lrt_roundcurve_scene_build(&hs, NULL, &err);
    bad |= run_tubes("roundlin", sc, tub, nt, nrays, 0, 1e-4);
    lrt_tri_scene_free(sc);
    /* cubic Bezier curves */
    enum { NB = 150 };
    float *bz = malloc(sizeof(float) * 16 * NB);
    for (int i = 0; i < NB; i++) {
        float b[3] = {fr(-3, 3), fr(-3, 3), fr(-3, 3)};
        tub[i].n = 4;
        for (int k = 0; k < 4; k++) {
            for (int a = 0; a < 3; a++) tub[i].p[k][a] = bz[16 * i + 4 * k + a] = b[a] + fr(-0.6f, 0.6f);
            tub[i].r[k] = bz[16 * i + 4 * k + 3] = fr(0.01f, 0.06f);
        }
    }
    sc = lrt_bezcurve_scene_build(bz, NB, NULL, &err);
    bad |= run_tubes("bezcurve", sc, tub, NB, nrays, 0, 2e-4) /* strict since the canal-surface leaf solve */;
    lrt_tri_scene_free(sc);
    /* sphere points (degenerate tubes) */
    enum { NPT = 300 };
    float cen[3 * NPT], pr[NPT];
    for (int i = 0; i < NPT; i++) {
        tub[i].n = 2;
        for (int a = 0; a < 3; a++) tub[i].p[0][a] = tub[i].p[1][a] = cen[3 * i + a] = fr(-3, 3);
        tub[i].r[0] = tub[i].r[1] = pr[i] = fr(0.02f, 0.2f);
    }
    sc = lrt_points_scene_build(cen, pr, NULL, LRT_POINT_SPHERE, NPT, NULL, &err);
    bad |= run_tubes("sphere-pt", sc, tub, NPT, nrays, 0, 1e-4);
    lrt_tri_scene_free(sc);
    /* bilinear + bicubic patches (gently curved so the tessellation is accurate) */
    enum { NQ = 60 };
    float *bl = malloc(sizeof(float) * 12 * NQ), *bp = malloc(sizeof(float) * 48 * NQ);
    double (*bq)[4][3] = malloc(sizeof(double) * 12 * NQ);
    patch_t *pt = malloc(sizeof(patch_t) * NQ);
    for (int i = 0; i < NQ; i++) {
        float b[3] = {fr(-3, 3), fr(-3, 3), fr(-3, 3)};
        float q[4][2] = {{0, 0}, {1, 0}, {1, 1}, {0, 1}};
        for (int c = 0; c < 4; c++) {
            float x[3] = {b[0] + q[c][0], b[1] + q[c][1], b[2] + fr(-0.3f, 0.3f)};
            for (int a = 0; a < 3; a++) bq[i][c][a] = bl[12 * i + 3 * c + a] = x[a];
        }
        pt[i].rational = 0;
        for (int j = 0; j < 4; j++)
            for (int k = 0; k < 4; k++) {
                float x[3] = {b[0] + k / 3.0f + fr(-0.05f, 0.05f), b[1] + j / 3.0f + fr(-0.05f, 0.05f),
                              b[2] + fr(-0.3f, 0.3f)};
                for (int a = 0; a < 3; a++) pt[i].cp[4 * j + k][a] = bp[48 * i + 3 * (4 * j + k) + a] = x[a];
                pt[i].cp[4 * j + k][3] = 1;
            }
    }
    sc = lrt_bilinear_scene_build(bl, NQ, NULL, &err);
    bad |= run_patches("bilinear", sc, NULL, bq, NQ, nrays);
    lrt_tri_scene_free(sc);
    sc = lrt_bezpatch_scene_build(bp, NQ, NULL, &err);
    bad |= run_patches("bezpatch", sc, pt, NULL, NQ, nrays);
    lrt_tri_scene_free(sc);
    /* NURBS: 7x7 bicubic, positive weights; reference = the extracted rational
     * patches read back from the leaves (the geometry the intersector uses) */
    enum { NU = 7, NV = 7 };
    float net[3 * NU * NV], w[NU * NV], ku[NU + 4], kv[NV + 4];
    for (int j = 0; j < NV; j++)
        for (int i = 0; i < NU; i++) {
            net[3 * (j * NU + i) + 0] = (float)i * 0.6f;
            net[3 * (j * NU + i) + 1] = (float)j * 0.6f;
            net[3 * (j * NU + i) + 2] = fr(-0.4f, 0.4f);
            w[j * NU + i] = fr(0.5f, 2.0f);
        }
    for (int k = 0; k < NU + 4; k++) ku[k] = k < 4 ? 0.0f : k >= NU ? 1.0f : (float)(k - 3) / (NU - 3);
    for (int k = 0; k < NV + 4; k++) kv[k] = k < 4 ? 0.0f : k >= NV ? 1.0f : (float)(k - 3) / (NV - 3);
    sc = lrt_nurbs_scene_build(net, NU - 1, NV - 1, ku, kv, w, 3, 3, NULL, &err);
    int np = 0;
    for (uint32_t b = 0; b < sc->block_count; b++) {
        const lrt_rbezpatch4 *rb = (const lrt_rbezpatch4 *)tri_block_ptr(sc->blocks, b, sc->block_stride);
        for (int l = 0; l < 4; l++) {
            uint32_t id = rb->prim[l];
            if (id == LRT_TRI_NO_HIT || id >= NQ) continue;
            pt[id].rational = 1;
            for (int k = 0; k < 16; k++)
                for (int c = 0; c < 4; c++) pt[id].cp[k][c] = rb->cp[k * 4 + c][l];
            for (int c = 0; c < 4; c++) pt[id].dom[c] = rb->dom[c][l];
            if ((int)id + 1 > np) np = (int)id + 1;
        }
    }
    bad |= run_patches("nurbs", sc, pt, NULL, np, nrays);
    lrt_tri_scene_free(sc);
    free(tub); free(bz); free(bl); free(bp); free(bq); free(pt);
    return bad;
}
