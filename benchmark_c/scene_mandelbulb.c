/*
 * scene_mandelbulb.c — marching-cubes mandelbulb, C11 port of the generator in
 * viewer_x11/viewer_x11.cc (mandelbulbDE / marchingCubes / generateMandelbulb).
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "scene_mandelbulb.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

#include "mc_tables.inc"

typedef struct {
    int power;
    int iterations;
    float bailout;
} mb_params;

/* Mandelbulb distance estimator (identical to viewer_x11.cc mandelbulbDE). */
static float mandelbulb_de(float x, float y, float z, const mb_params *p) {
    float wx = x, wy = y, wz = z;
    float dr = 1.0f;
    float r = 0.0f;
    for (int i = 0; i < p->iterations; i++) {
        r = sqrtf(wx * wx + wy * wy + wz * wz);
        if (r > p->bailout) break;
        float theta = acosf(wz / r);
        float phi = atan2f(wy, wx);
        float pow_r = powf(r, (float)p->power);
        dr = powf(r, (float)(p->power - 1)) * (float)p->power * dr + 1.0f;
        theta *= (float)p->power;
        phi *= (float)p->power;
        float st = sinf(theta);
        wx = st * cosf(phi) * pow_r + x;
        wy = st * sinf(phi) * pow_r + y;
        wz = cosf(theta) * pow_r + z;
    }
    return 0.5f * logf(r) * r / dr;
}

static float lerpf(float a, float b, float t) { return a + (b - a) * t; }

/* Growable float array for the emitted triangle soup. */
typedef struct {
    float *data;
    size_t count;
    size_t cap;
} fvec;

static int fvec_push3(fvec *v, float x, float y, float z) {
    if (v->count + 3 > v->cap) {
        size_t cap = v->cap ? v->cap * 2 : 4096;
        float *p = (float *)realloc(v->data, cap * sizeof(float));
        if (!p) return 0;
        v->data = p;
        v->cap = cap;
    }
    v->data[v->count++] = x;
    v->data[v->count++] = y;
    v->data[v->count++] = z;
    return 1;
}

size_t scene_mandelbulb_generate(int fineness, int power, float **out_verts) {
    if (out_verts) *out_verts = NULL;
    if (!out_verts || fineness < 2 || power < 2) return 0;

    mb_params params;
    params.power = power;
    params.iterations = 10;
    params.bailout = 2.0f;

    const float org_x = -MANDELBULB_BOUND;
    const float org_y = -MANDELBULB_BOUND;
    const float org_z = -MANDELBULB_BOUND;
    const int n = fineness;
    const float step = (2.0f * MANDELBULB_BOUND) / (float)n;
    const int grid_n = n + 1;
    const size_t grid_slice = (size_t)grid_n * (size_t)grid_n;

    float *grid = (float *)malloc(grid_slice * (size_t)grid_n * sizeof(float));
    if (!grid) return 0;

    for (int k = 0; k <= n; k++) {
        for (int j = 0; j <= n; j++) {
            for (int i = 0; i <= n; i++) {
                float px = org_x + (float)i * step;
                float py = org_y + (float)j * step;
                float pz = org_z + (float)k * step;
                grid[(size_t)k * grid_slice + (size_t)j * grid_n + (size_t)i] =
                    mandelbulb_de(px, py, pz, &params);
            }
        }
    }

    fvec verts = {NULL, 0, 0};
    size_t tri_count = 0;

    for (int k = 0; k < n; k++) {
        for (int j = 0; j < n; j++) {
            for (int i = 0; i < n; i++) {
                size_t idx[8];
                for (int c = 0; c < 8; c++) {
                    idx[c] = (size_t)(k + kMcCorner[c][2]) * grid_slice +
                             (size_t)(j + kMcCorner[c][1]) * grid_n +
                             (size_t)(i + kMcCorner[c][0]);
                }

                int cube_idx = 0;
                for (int c = 0; c < 8; c++) {
                    if (grid[idx[c]] < 0.0f) cube_idx |= (1 << c);
                }
                if (cube_idx == 0 || cube_idx == 255) continue;

                int edge_mask = kMcEdgeTable[cube_idx];
                float vert_list[12][3];
                for (int e = 0; e < 12; e++) {
                    if (edge_mask & (1 << e)) {
                        int c0 = kMcEdge[e][0], c1 = kMcEdge[e][1];
                        float v0 = grid[idx[c0]], v1 = grid[idx[c1]];
                        float t = v0 / (v0 - v1);
                        float x0 = org_x + (float)(i + kMcCorner[c0][0]) * step;
                        float y0 = org_y + (float)(j + kMcCorner[c0][1]) * step;
                        float z0 = org_z + (float)(k + kMcCorner[c0][2]) * step;
                        float x1 = org_x + (float)(i + kMcCorner[c1][0]) * step;
                        float y1 = org_y + (float)(j + kMcCorner[c1][1]) * step;
                        float z1 = org_z + (float)(k + kMcCorner[c1][2]) * step;
                        vert_list[e][0] = lerpf(x0, x1, t);
                        vert_list[e][1] = lerpf(y0, y1, t);
                        vert_list[e][2] = lerpf(z0, z1, t);
                    }
                }

                for (int t = 0; t + 2 < 16; t += 3) {
                    int i0 = kMcTriTable[cube_idx][t];
                    if (i0 == -1) break;
                    int i1 = kMcTriTable[cube_idx][t + 1];
                    int i2 = kMcTriTable[cube_idx][t + 2];
                    if (i1 == -1 || i2 == -1) break;
                    /* The DE is NaN where r == 0 (acosf(0/0)); cells touching
                     * that grid point emit non-finite vertices. Drop them —
                     * BVH builders reject NaN bounds. */
                    int finite = 1;
                    const int ids[3] = {i0, i1, i2};
                    for (int c = 0; c < 3 && finite; c++) {
                        for (int k = 0; k < 3; k++) {
                            if (!isfinite(vert_list[ids[c]][k])) {
                                finite = 0;
                                break;
                            }
                        }
                    }
                    if (!finite) continue;
                    if (!fvec_push3(&verts, vert_list[i0][0], vert_list[i0][1], vert_list[i0][2]) ||
                        !fvec_push3(&verts, vert_list[i1][0], vert_list[i1][1], vert_list[i1][2]) ||
                        !fvec_push3(&verts, vert_list[i2][0], vert_list[i2][1], vert_list[i2][2])) {
                        free(verts.data);
                        free(grid);
                        return 0;
                    }
                    tri_count++;
                }
            }
        }
    }

    free(grid);
    *out_verts = verts.data;
    return tri_count;
}
