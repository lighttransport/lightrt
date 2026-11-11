/* Dump a C-built BVH4/BVH8 scene for the Lean BVH validator (CheckBVH.lean).
 *
 * Includes lightrt_c_tri.c to reach the internal node/leaf arrays and the
 * scalar traversal `tri_intersect_scalar`. All floats are hex bit patterns.
 *   usage: bvhdump <seed> <ntris> <nrays> <quality 0|1|2> <layout 4|8> <scene 0=soup|1=grid>
 * Output:
 *   W <width> ROOT <ref> NODES <n> BLOCKS <b>
 *   N <nchildren> {lo0 lo1 lo2 hi0 hi1 hi2 ref}*           (per node)
 *   B {v0x v0y v0z e1x e1y e1z e2x e2y e2z id}*width       (per block)
 *   R o0 o1 o2 tmin d0 d1 d2 tmax  hit t prim  hitS tS primS
 *   T {t|-}*(b*width)        per ray: tri_isect_lane(t_best=+inf) per slot
 * `hitS..` is the dispatched (SIMD) lrt_tri_intersect1 for comparison. */
#include "../../lightrt_c_tri.c"
#include <stdio.h>

static uint64_t rs;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)rs; }
static float frand(void) { return (rnd() >> 8) * (1.0f / 16777216.0f); }
static uint32_t fb(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage\n"); return 2; }
    rs = 0x9E3779B97F4A7C15ull ^ (uint64_t)atoll(argv[1]) * 0x2545F4914F6CDD1Dull;
    size_t n = (size_t)atoi(argv[2]);
    int nrays = atoi(argv[3]), quality = atoi(argv[4]), layout = atoi(argv[5]);
    int grid = atoi(argv[6]);
    float *v;
    if (grid) { /* g x g heightfield: triangles sharing edges, jittered */
        int g = 1; while (2 * g * g < (int)n) g++;
        n = (size_t)(2 * g * g);
        float *h = malloc(sizeof(float) * (g + 1) * (g + 1));
        for (int i = 0; i < (g + 1) * (g + 1); i++) h[i] = 0.3f * frand();
        v = malloc(sizeof(float) * 9 * n);
        size_t k = 0;
        for (int y = 0; y < g; y++) for (int x = 0; x < g; x++) {
            float P[4][3];
            for (int c = 0; c < 4; c++) {
                int xx = x + (c & 1), yy = y + (c >> 1);
                P[c][0] = (float)xx / g; P[c][1] = h[yy * (g + 1) + xx]; P[c][2] = (float)yy / g;
            }
            int T[2][3] = {{0, 1, 3}, {0, 3, 2}};
            for (int t = 0; t < 2; t++) for (int c = 0; c < 3; c++) for (int a = 0; a < 3; a++)
                v[k++] = P[T[t][c]][a];
        }
        free(h);
    } else {
        v = malloc(sizeof(float) * 9 * n);
        for (size_t i = 0; i < n; i++) {
            float c[3] = {frand(), frand(), frand()};
            for (int j = 0; j < 3; j++) for (int a = 0; a < 3; a++)
                v[9 * i + 3 * j + a] = c[a] + 0.1f * (frand() - 0.5f);
        }
    }
    lrt_tri_build_options o = {(lrt_tri_quality)quality, (lrt_tri_layout)layout, 0, 0};
    lrt_result err;
    lrt_tri_scene *s = lrt_tri_scene_build(v, n, &o, &err);
    if (!s) { fprintf(stderr, "build failed %d\n", (int)err); return 1; }
    int W = s->layout;
    if (W != 4 && W != 8) { fprintf(stderr, "layout %d unsupported\n", W); return 1; }
    if (W == 8 && s->quantized) { fprintf(stderr, "quantized\n"); return 1; }
    #ifdef LRT_TRI_SLAB_ROBUST
    int robust = 1;
#else
    int robust = 0;
#endif
#ifdef LRT_TRI_EXACT_NEAREST
    int exactn = 1;
#else
    int exactn = 0;
#endif
    printf("W %d ROOT %08x NODES %u BLOCKS %u ROBUST %d EXACTN %d\n", W, s->root, s->node_count, s->block_count, robust, exactn);
    for (uint32_t i = 0; i < s->node_count; i++) {
        const float *lo[3], *hi[3]; const uint32_t *ch; uint32_t nc;
        if (W == 4) { const lrt_bvh4_node *nd = &s->nodes4[i];
            lo[0] = nd->lo_x; lo[1] = nd->lo_y; lo[2] = nd->lo_z;
            hi[0] = nd->hi_x; hi[1] = nd->hi_y; hi[2] = nd->hi_z; ch = nd->child; nc = nd->nchildren;
        } else { const lrt_bvh8_node *nd = &s->nodes8[i];
            lo[0] = nd->lo_x; lo[1] = nd->lo_y; lo[2] = nd->lo_z;
            hi[0] = nd->hi_x; hi[1] = nd->hi_y; hi[2] = nd->hi_z; ch = nd->child; nc = nd->nchildren; }
        printf("N %u", nc);
        for (uint32_t c = 0; c < nc; c++) {
            for (int a = 0; a < 3; a++) printf(" %08x", fb(lo[a][c]));
            for (int a = 0; a < 3; a++) printf(" %08x", fb(hi[a][c]));
            printf(" %08x", ch[c]);
        }
        printf("\n");
    }
    for (uint32_t b = 0; b < s->block_count; b++) {
        const float *f = tri_block_floats(s->blocks, b, W);
        const uint32_t *ids = (const uint32_t *)(f + 9 * W);
        printf("B");
        for (int l = 0; l < W; l++) {
            for (int q = 0; q < 9; q++) printf(" %08x", fb(f[q * W + l]));
            printf(" %08x", ids[l]);
        }
        printf("\n");
    }
    for (int r = 0; r < nrays; r++) {
        lrt_ray ray;
        float tgt[3] = {frand(), grid ? 0.15f : frand(), frand()};
        if (grid && (r & 1)) { /* aim exactly at a grid vertex/edge */
            int g = 1; while (2 * g * g < (int)n) g++;
            tgt[0] = (float)(rnd() % (g + 1)) / g; tgt[2] = (float)(rnd() % (g + 1)) / g;
        }
        for (int a = 0; a < 3; a++) ray.org[a] = tgt[a] + 2.0f * (frand() - 0.5f) * 2.0f;
        if (grid) ray.org[1] = 2.0f + frand();
        for (int a = 0; a < 3; a++) ray.dir[a] = tgt[a] - ray.org[a];
        if (r % 7 == 3) { ray.dir[0] = 0.0f; ray.org[0] = tgt[0]; }
        if (r % 11 == 5) { ray.dir[0] = 0.0f; ray.dir[2] = 0.0f; ray.org[0] = tgt[0]; ray.org[2] = tgt[2]; }
        ray.tmin = 0.0f; ray.tmax = (r % 5 == 1) ? 1.0f : 1e30f;
        lrt_hit h1, h2;
        int k1 = tri_intersect_scalar(s, &ray, &h1);
        int k2 = lrt_tri_intersect1(s, &ray, &h2);
        int o1 = tri_occluded_scalar(s, &ray), o2 = lrt_tri_occluded1(s, &ray);
        printf("R %08x %08x %08x %08x %08x %08x %08x %08x %d %08x %08x %d %08x %08x %d %d\n",
               fb(ray.org[0]), fb(ray.org[1]), fb(ray.org[2]), fb(ray.tmin),
               fb(ray.dir[0]), fb(ray.dir[1]), fb(ray.dir[2]), fb(ray.tmax),
               k1, fb(h1.t), h1.prim_id, k2, fb(h2.t), h2.prim_id, o1, o2);
        tri_ray_ctx rc; tri_ray_setup(&ray, &rc);
        printf("T");
        for (uint32_t b = 0; b < s->block_count; b++) {
            const float *f = tri_block_floats(s->blocks, b, W);
            const uint32_t *ids = (const uint32_t *)(f + 9 * W);
            for (int l = 0; l < W; l++) {
                float t, u, vv;
                if (ids[l] != LRT_TRI_NO_HIT && tri_isect_lane(f, W, l, &rc, INFINITY, &t, &u, &vv))
                    printf(" %08x", fb(t));
                else printf(" -");
            }
        }
        printf("\n");
    }
    lrt_tri_scene_free(s); free(v);
    return 0;
}
