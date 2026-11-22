/*
 * BITEXACT SIMD == scalar check for the Möller–Trumbore packet path.
 *
 * `wtcheck` builds with -DLRT_TRI_WATERTIGHT_TRI, so `lrt_tri_intersect4`
 * falls back to per-ray per-lane scalar Woop and the MT packet is never
 * exercised. This check builds *without* WATERTIGHT_TRI (the MT path, packet
 * SIMD kernels live) and fuzzes `tri_packet4_tri` against the scalar per-lane
 * kernel `tri_isect_lane` on the same sheared ray and the same triangle.
 *
 * Under LRT_TRI_BITEXACT (default) the det test uses the scalar order and
 * scalar predicate; the SIMD u/v/t arithmetic is in the scalar association
 * order with no FMA (cc -ffp-contract=off), so the two paths must agree
 * hit/miss and t/u/v bit for bit (NaN det: packet keeps the ray alive to the
 * compares, where NaN fails every test - same outcome as scalar's early
 * reject).
 *
 * Build: cc -O1 -ffp-contract=off -msse4.1 -mavx2 -mfma -w -I. \
 *        formal/tools/mtcheck.c -lm -lpthread   (no WATERTIGHT_TRI)
 */
#include "../../lightrt_c_tri.c"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

static uint32_t rs = 1;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }
static float frand(void) { return (float)(rnd() & 0xffffff) / 16777216.0f; }
static float fspecial(void) {
    static const float sp[] = {0.0f, -0.0f, 1.0f, -1.0f, 1e-40f, -1e-40f, 1e30f, -1e30f,
                               INFINITY, -INFINITY, NAN, 0.5f, 3.0f, 1e-20f};
    return sp[rnd() % (sizeof sp / sizeof sp[0])];
}
static float fval(int mode) {
    if (mode == 1 && rnd() % 6 == 0) return fspecial();
    if (mode == 2) { /* triangle in the ray's path: mostly normal small values */
        return frand() * 2 - 1;
    }
    return frand() * 4 - 2;
}

static int same(float a, float b) { return memcmp(&a, &b, 4) == 0 || (a != a && b != b); }

int main(int argc, char **argv) {
    int iters = argc > 1 ? atoi(argv[1]) : 200000;
    long blocks = 0, lanes = 0, hits = 0, bad = 0;
    for (int it = 0; it < iters; it++) {
        int mode = it % 3;
        /* one triangle, broadcast */
        float v0[3], e1[3], e2[3];
        float A[3], B[3], C[3];
        for (int a = 0; a < 3; a++) A[a] = fval(mode);
        for (int a = 0; a < 3; a++) B[a] = A[a] + fval(0);
        for (int a = 0; a < 3; a++) C[a] = A[a] + fval(0);
        for (int a = 0; a < 3; a++) {
            v0[a] = A[a];
            e1[a] = B[a] - A[a];
            e2[a] = C[a] - A[a];
        }
        if (mode == 2 && rnd() % 8 == 0) {
            /* degenerate (shared-edge-ish) triangle */
            for (int a = 0; a < 3; a++) e1[a] = e2[a] * (float)(rnd() % 2 ? 1 : -1);
        }
        float org[4][3], dir[4][3], tmin[4], tmax[4];
        for (int k = 0; k < 4; k++) {
            for (int a = 0; a < 3; a++) org[k][a] = fval(mode);
            if (mode == 2) {
                /* aim at a point of the triangle (t* between tmin and tmax) */
                float f = frand();
                for (int a = 0; a < 3; a++)
                    dir[k][a] = ((1.0f - 2.0f * f) * A[a] + 2.0f * f * B[a]) - org[k][a];
            } else {
                for (int a = 0; a < 3; a++) dir[k][a] = fval(mode);
            }
            tmin[k] = (rnd() % 5 == 0) ? -1.0f : 0.0f;
            tmax[k] = (rnd() % 4 == 0) ? 0.7f : 1e30f;
        }
        /* SIMD packet path */
        tri_packet4 p;
        {
            float ox[4], oy[4], oz[4], dx[4], dy[4], dz[4], tn[4];
            for (int k = 0; k < 4; k++) {
                ox[k] = org[k][0]; oy[k] = org[k][1]; oz[k] = org[k][2];
                dx[k] = dir[k][0]; dy[k] = dir[k][1]; dz[k] = dir[k][2];
                tn[k] = tmin[k];
            }
            tri_packet4_setup(ox, oy, oz, dx, dy, dz, tn, &p);
        }
        _Alignas(16) float tmax4v[4] = {tmax[0], tmax[1], tmax[2], tmax[3]};
        __m128 tmax4 = _mm_load_ps(tmax4v);
        __m128 t, u, v;
        __m128 m = tri_packet4_tri(&p, v0, e1, e2, tmax4, &t, &u, &v);
        int mask = _mm_movemask_ps(m);
        /* scalar per-lane path on a fabricated block (bw = 4, same tri) */
        for (int lane = 0; lane < 4; lane++) {
            float f[9 * 4 + 4];
            for (int a = 0; a < 3; a++) {
                f[(0 + a) * 4 + lane] = v0[a];
                f[(3 + a) * 4 + lane] = e1[a];
                f[(6 + a) * 4 + lane] = e2[a];
            }
            lrt_ray rr = {{org[lane][0], org[lane][1], org[lane][2]},
                          tmin[lane],
                          {dir[lane][0], dir[lane][1], dir[lane][2]},
                          0.0f};
            tri_ray_ctx rc;
            tri_ray_setup(&rr, &rc);
            float st, su, sv;
            int s_hit = tri_isect_lane(f, 4, lane, &rc, tmax[lane], &st, &su, &sv);
            int p_hit = (mask >> lane) & 1;
            lanes++;
            if (s_hit) hits++;
            if (s_hit != p_hit) {
                if (bad < 8)
                    fprintf(stderr, "lane %d: scalar %d packet %d (det-ish mode %d)\n",
                            lane, s_hit, p_hit, mode);
                bad++;
                continue;
            }
            if (s_hit) {
                _Alignas(16) float tv[4], uv[4], uvw[4];
                _mm_store_ps(tv, t); _mm_store_ps(uv, u); _mm_store_ps(uvw, v);
                if (!same(st, tv[lane]) || !same(su, uv[lane]) || !same(sv, uvw[lane])) {
                    if (bad < 8)
                        fprintf(stderr, "lane %d: scalar t=%.9g packet t=%.9g\n", lane, st, tv[lane]);
                    bad++;
                }
            }
        }
        blocks++;
    }
    printf("mtcheck: %ld blocks (%ld lanes, %ld scalar hits), SIMD != scalar %ld\n",
           blocks, lanes, hits, bad);
    return bad != 0;
}
