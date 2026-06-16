/*
 * scene_thinspan.c — long thin diagonal triangles (see scene_thinspan.h).
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "scene_thinspan.h"

#include <math.h>
#include <stdlib.h>

static uint32_t ts_pcg(uint32_t input) {
    uint32_t state = input * 747796405u + 2891336453u;
    uint32_t word = ((state >> ((state >> 28u) + 4u)) ^ state) * 277803737u;
    return (word >> 22u) ^ word;
}

static float ts_unit(uint32_t *s) { /* [0,1) */
    *s = ts_pcg(*s);
    return (float)(*s & 0xFFFFFFu) / 16777216.0f;
}

size_t scene_thinspan_generate(size_t ntris, float thickness, float span,
                               uint32_t seed, float **out_verts) {
    if (out_verts) *out_verts = NULL;
    if (!out_verts || ntris == 0) return 0;
    if (thickness <= 0.0f) thickness = 0.002f;
    if (span <= 0.0f) span = 0.25f;

    float *v = (float *)malloc(ntris * 9 * sizeof(float));
    if (!v) return 0;

    const float B = THINSPAN_BOUND;
    const float half_len = span * B * 1.732f; /* span * half cube diagonal */
    for (size_t i = 0; i < ntris; i++) {
        uint32_t s = (uint32_t)(i * 2654435761u) ^ seed;

        /* Random center, random diagonal-ish direction, length = span. */
        float cx = (ts_unit(&s) * 2.0f - 1.0f) * B;
        float cy = (ts_unit(&s) * 2.0f - 1.0f) * B;
        float cz = (ts_unit(&s) * 2.0f - 1.0f) * B;
        float ux = ts_unit(&s) * 2.0f - 1.0f;
        float uy = ts_unit(&s) * 2.0f - 1.0f;
        float uz = ts_unit(&s) * 2.0f - 1.0f;
        float ul = sqrtf(ux * ux + uy * uy + uz * uz);
        if (ul < 1e-6f) {
            ux = 0.577f;
            uy = 0.577f;
            uz = 0.577f;
            ul = 1.0f;
        }
        ux /= ul;
        uy /= ul;
        uz /= ul;
        float ax = cx - ux * half_len, ay = cy - uy * half_len,
              az = cz - uz * half_len;
        float bx = cx + ux * half_len, by = cy + uy * half_len,
              bz = cz + uz * half_len;

        /* Width direction: any unit vector orthogonal to the segment. */
        float dx = bx - ax, dy = by - ay, dz = bz - az;
        float wx = dy * 1.0f - dz * 0.3f;
        float wy = dz * 0.7f - dx * 1.0f;
        float wz = dx * 0.3f - dy * 0.7f;
        float wl = sqrtf(wx * wx + wy * wy + wz * wz);
        if (wl < 1e-12f) {
            wx = 1.0f;
            wy = wz = 0.0f;
            wl = 1.0f;
        }
        float t = thickness / wl;
        wx *= t;
        wy *= t;
        wz *= t;

        v[i * 9 + 0] = ax;
        v[i * 9 + 1] = ay;
        v[i * 9 + 2] = az;
        v[i * 9 + 3] = bx + wx;
        v[i * 9 + 4] = by + wy;
        v[i * 9 + 5] = bz + wz;
        v[i * 9 + 6] = bx - wx;
        v[i * 9 + 7] = by - wy;
        v[i * 9 + 8] = bz - wz;
    }

    *out_verts = v;
    return ntris;
}
