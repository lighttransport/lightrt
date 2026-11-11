/* Exact BVH box check for the non-triangle primitives
 * (formal/LightRT/Geom/Hull.lean).
 *
 * The Lean side proves, over R, that every curve / patch lies in the
 * (radius-dilated) min/max box of its control points:
 *   round-linear and flat curves  -> union of the end-ball boxes
 *   round cubic Bezier curve      -> CP box dilated by the CP radii
 *   bilinear / bicubic patch      -> CP box
 *   rational (NURBS) patch, w > 0 -> box of the projected CPs x/w
 *   point (sphere / disc)         -> center +- r
 * This tool checks, EXACTLY, the remaining step for real C-built scenes: every
 * BVH4 child box contains that control-point hull of the STORED leaf geometry
 * (the data the intersector reads), and every inner child box contains its
 * children's boxes. All tests are exact in double: float+-float and
 * float*float are exact there, and x/w >= lo is tested as x >= lo*w.
 * Together: every C box contains the exact stored primitive (condition C1's
 * containment hypothesis, `WF`).
 * Usage: primboxcheck SEED ; exit 1 if any containment fails. */
#include "lightrt_c_tri.c"
#include <stdio.h>

static uint32_t rs = 1;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }
static float frand(void) { return (float)(rnd() & 0xffffff) / 16777216.0f; }
/* odd decimal-ish values so that +-r and /w round */
static float fr(float lo, float hi) { return lo + (hi - lo) * frand(); }

typedef struct { long checks, bad; double worst; } stat_t;

/* x must be >= lo (resp. <= hi); `worst` is in ulps of the box bound */
static void need_ge(stat_t *st, double x, float lo) {
    st->checks++;
    if (!(x >= (double)lo)) {
        st->bad++;
        double u = (double)(nextafterf(lo, INFINITY) - lo);
        double e = ((double)lo - x) / u;
        if (e > st->worst) st->worst = e;
    }
}
static void need_le(stat_t *st, double x, float hi) {
    st->checks++;
    if (!(x <= (double)hi)) {
        st->bad++;
        double u = (double)(hi - nextafterf(hi, -INFINITY));
        double e = (x - (double)hi) / u;
        if (e > st->worst) st->worst = e;
    }
}

/* Check the hull of one stored primitive against child box [lo,hi]. */
static void check_prim(const lrt_tri_scene *s, const void *blk, int lane, const float lo[3],
                       const float hi[3], stat_t *st) {
    switch (s->prim_kind) {
    case TRI_PRIM_RLCURVE: case TRI_PRIM_FLATCURVE: {
        const float *p0x, *p0y, *p0z, *r0, *p1x, *p1y, *p1z, *r1;
        if (s->prim_kind == TRI_PRIM_RLCURVE) {
            const lrt_rlc4 *c = blk;
            p0x = c->p0x; p0y = c->p0y; p0z = c->p0z; r0 = c->r0;
            p1x = c->p1x; p1y = c->p1y; p1z = c->p1z; r1 = c->r1;
        } else {
            const lrt_flat4 *c = blk;
            p0x = c->p0x; p0y = c->p0y; p0z = c->p0z; r0 = c->r0;
            p1x = c->p1x; p1y = c->p1y; p1z = c->p1z; r1 = c->r1;
        }
        double P[2][3] = {{p0x[lane], p0y[lane], p0z[lane]}, {p1x[lane], p1y[lane], p1z[lane]}};
        double R[2] = {fmax(r0[lane], 0), fmax(r1[lane], 0)};
        for (int k = 0; k < 2; k++)
            for (int a = 0; a < 3; a++) {
                need_ge(st, P[k][a] - R[k], lo[a]);
                need_le(st, P[k][a] + R[k], hi[a]);
            }
        break;
    }
    case TRI_PRIM_BEZCURVE: {
        const lrt_bez4 *c = blk;
        const float *X[4] = {c->b0x, c->b1x, c->b2x, c->b3x}, *Y[4] = {c->b0y, c->b1y, c->b2y, c->b3y},
                    *Z[4] = {c->b0z, c->b1z, c->b2z, c->b3z}, *Rr[4] = {c->b0r, c->b1r, c->b2r, c->b3r};
        for (int k = 0; k < 4; k++) {
            double p[3] = {X[k][lane], Y[k][lane], Z[k][lane]}, r = fmax(Rr[k][lane], 0);
            for (int a = 0; a < 3; a++) { need_ge(st, p[a] - r, lo[a]); need_le(st, p[a] + r, hi[a]); }
        }
        break;
    }
    case TRI_PRIM_BILINEAR: {
        const lrt_quad4 *q = blk;
        const float *X[4] = {q->x0, q->x1, q->x2, q->x3}, *Y[4] = {q->y0, q->y1, q->y2, q->y3},
                    *Z[4] = {q->z0, q->z1, q->z2, q->z3};
        for (int k = 0; k < 4; k++) {
            double p[3] = {X[k][lane], Y[k][lane], Z[k][lane]};
            for (int a = 0; a < 3; a++) { need_ge(st, p[a], lo[a]); need_le(st, p[a], hi[a]); }
        }
        break;
    }
    case TRI_PRIM_BEZPATCH: {
        const lrt_bezpatch4 *b = blk;
        for (int k = 0; k < 16; k++)
            for (int a = 0; a < 3; a++) {
                need_ge(st, b->cp[k * 3 + a][lane], lo[a]);
                need_le(st, b->cp[k * 3 + a][lane], hi[a]);
            }
        break;
    }
    case TRI_PRIM_RBEZPATCH: case TRI_PRIM_TRIMNURBS: {
        const lrt_rbezpatch4 *b = blk;
        for (int k = 0; k < 16; k++) {
            double w = b->cp[k * 4 + 3][lane];
            st->checks++;
            if (!(w > 0)) { st->bad++; continue; }
            /* x/w >= lo  <=>  x >= lo*w (exact in double) */
            for (int a = 0; a < 3; a++) {
                double x = b->cp[k * 4 + a][lane];
                st->checks++;
                if (!(x >= (double)lo[a] * w) || !(x <= (double)hi[a] * w)) {
                    st->bad++;
                    double p = x / w, u = (double)(nextafterf(lo[a], INFINITY) - lo[a]);
                    double e = fmax((double)lo[a] - p, p - (double)hi[a]) / u;
                    if (e > st->worst) st->worst = e;
                }
            }
        }
        break;
    }
    case TRI_PRIM_POINT: {
        const lrt_point4 *p = blk;
        double c[3] = {p->cx[lane], p->cy[lane], p->cz[lane]}, r = fmax(p->r[lane], 0);
        for (int a = 0; a < 3; a++) { need_ge(st, c[a] - r, lo[a]); need_le(st, c[a] + r, hi[a]); }
        break;
    }
    default:
        break;
    }
}

static uint32_t prim_of(const lrt_tri_scene *s, const void *blk, int lane) {
    switch (s->prim_kind) {
    case TRI_PRIM_RLCURVE: return ((const lrt_rlc4 *)blk)->prim[lane];
    case TRI_PRIM_FLATCURVE: return ((const lrt_flat4 *)blk)->prim[lane];
    case TRI_PRIM_BEZCURVE: return ((const lrt_bez4 *)blk)->prim[lane];
    case TRI_PRIM_BILINEAR: return ((const lrt_quad4 *)blk)->prim[lane];
    case TRI_PRIM_BEZPATCH: return ((const lrt_bezpatch4 *)blk)->prim[lane];
    case TRI_PRIM_RBEZPATCH: case TRI_PRIM_TRIMNURBS: return ((const lrt_rbezpatch4 *)blk)->prim[lane];
    case TRI_PRIM_POINT: return ((const lrt_point4 *)blk)->prim[lane];
    default: return LRT_TRI_NO_HIT;
    }
}

static void walk(const lrt_tri_scene *s, uint32_t ref, const float lo[3], const float hi[3],
                 stat_t *leaf, stat_t *inner, long *nprim) {
    if (TRI_REF_IS_LEAF(ref)) {
        uint32_t b0 = TRI_REF_BLOCK(ref), nb = TRI_REF_NBLOCKS(ref);
        for (uint32_t b = 0; b < nb; b++) {
            const void *blk = tri_block_ptr(s->blocks, b0 + b, s->block_stride);
            for (int l = 0; l < 4; l++)
                if (prim_of(s, blk, l) != LRT_TRI_NO_HIT) { check_prim(s, blk, l, lo, hi, leaf); (*nprim)++; }
        }
        return;
    }
    const lrt_bvh4_node *n = &s->nodes4[TRI_REF_NODE(ref)];
    for (int i = 0; i < (int)n->nchildren; i++) {
        float clo[3] = {n->lo_x[i], n->lo_y[i], n->lo_z[i]}, chi[3] = {n->hi_x[i], n->hi_y[i], n->hi_z[i]};
        if (lo) /* child box inside this node's box (slot box of the parent) */
            for (int a = 0; a < 3; a++) { need_ge(inner, clo[a], lo[a]); need_le(inner, chi[a], hi[a]); }
        walk(s, n->child[i], clo, chi, leaf, inner, nprim);
    }
}

static int report(const char *name, lrt_tri_scene *s) {
    if (!s) { printf("%-10s build failed\n", name); return 1; }
    stat_t leaf = {0}, inner = {0};
    long np = 0;
    if (TRI_REF_IS_LEAF(s->root)) { printf("%-10s root is a leaf (skipped)\n", name); return 0; }
    walk(s, s->root, NULL, NULL, &leaf, &inner, &np);
    printf("%-10s prims=%ld hull-checks=%ld fail=%ld (worst %.2f ulp)  node-checks=%ld fail=%ld\n", name,
           np, leaf.checks, leaf.bad, leaf.worst, inner.checks, inner.bad);
    lrt_tri_scene_free(s);
    return leaf.bad || inner.bad;
}

int main(int argc, char **argv) {
    rs = argc > 1 ? (uint32_t)atoi(argv[1]) * 2654435761u + 7 : 7;
    int bad = 0;
    lrt_result err;
    /* hair: 200 strands x 6 points, varying radii */
    enum { NS = 200, NP = 6 };
    float pts[NS * NP * 3], rad[NS * NP];
    uint32_t first[NS], cnt[NS];
    for (int s = 0; s < NS; s++) {
        float b[3] = {fr(-3, 3), fr(-3, 3), fr(-3, 3)};
        first[s] = (uint32_t)(s * NP); cnt[s] = NP;
        for (int k = 0; k < NP; k++) {
            for (int a = 0; a < 3; a++) pts[(s * NP + k) * 3 + a] = b[a] + fr(-0.3f, 0.3f) * (float)k;
            rad[s * NP + k] = fr(0.001f, 0.07f);
        }
    }
    lrt_hair_strands hs = {pts, rad, 0.0f, first, cnt, NS, NS * NP};
    bad |= report("roundlin", lrt_roundcurve_scene_build(&hs, NULL, &err));
    bad |= report("flat", lrt_flatcurve_scene_build(&hs, NULL, &err));
    /* cubic Bezier curves */
    enum { NB = 300 };
    float *bz = malloc(sizeof(float) * 16 * NB);
    for (int i = 0; i < NB; i++) {
        float b[3] = {fr(-3, 3), fr(-3, 3), fr(-3, 3)};
        for (int k = 0; k < 4; k++) {
            for (int a = 0; a < 3; a++) bz[16 * i + 4 * k + a] = b[a] + fr(-0.7f, 0.7f);
            bz[16 * i + 4 * k + 3] = fr(0.002f, 0.09f);
        }
    }
    bad |= report("bezcurve", lrt_bezcurve_scene_build(bz, NB, NULL, &err));
    /* points */
    float cen[3 * 500], pr[500];
    for (int i = 0; i < 500; i++) { for (int a = 0; a < 3; a++) cen[3 * i + a] = fr(-3, 3); pr[i] = fr(0.01f, 0.2f); }
    bad |= report("sphere-pt", lrt_points_scene_build(cen, pr, NULL, LRT_POINT_SPHERE, 500, NULL, &err));
    bad |= report("disc-pt", lrt_points_scene_build(cen, pr, NULL, LRT_POINT_DISC, 500, NULL, &err));
    /* bilinear + bicubic patches */
    enum { NQ = 300 };
    float *bl = malloc(sizeof(float) * 12 * NQ), *bp = malloc(sizeof(float) * 48 * NQ);
    for (int i = 0; i < NQ; i++) {
        float b[3] = {fr(-3, 3), fr(-3, 3), fr(-3, 3)};
        for (int k = 0; k < 12; k++) bl[12 * i + k] = b[k % 3] + fr(-0.5f, 0.5f);
        for (int k = 0; k < 48; k++) bp[48 * i + k] = b[k % 3] + fr(-0.5f, 0.5f);
    }
    bad |= report("bilinear", lrt_bilinear_scene_build(bl, NQ, NULL, &err));
    bad |= report("bezpatch", lrt_bezpatch_scene_build(bp, NQ, NULL, &err));
    /* NURBS: 8x8 net, bicubic, clamped knots, random positive weights */
    enum { NU = 8, NV = 8 };
    float net[3 * NU * NV], w[NU * NV], ku[NU + 4], kv[NV + 4];
    for (int j = 0; j < NV; j++)
        for (int i = 0; i < NU; i++) {
            net[3 * (j * NU + i) + 0] = (float)i * 0.37f + fr(-0.1f, 0.1f);
            net[3 * (j * NU + i) + 1] = (float)j * 0.41f + fr(-0.1f, 0.1f);
            net[3 * (j * NU + i) + 2] = fr(-0.6f, 0.6f);
            w[j * NU + i] = fr(0.3f, 3.0f);
        }
    for (int k = 0; k < NU + 4; k++) ku[k] = k < 4 ? 0.0f : k >= NU ? 1.0f : (float)(k - 3) / (NU - 3);
    for (int k = 0; k < NV + 4; k++) kv[k] = k < 4 ? 0.0f : k >= NV ? 1.0f : (float)(k - 3) / (NV - 3);
    bad |= report("nurbs", lrt_nurbs_scene_build(net, NU - 1, NV - 1, ku, kv, w, 3, 3, NULL, &err));
    free(bz); free(bl); free(bp);
    return bad;
}
