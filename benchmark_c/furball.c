/*
 * furball.c — procedural fur generator. See furball.h.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "furball.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

static inline uint32_t fb_hash(uint32_t x) {
    uint32_t s = x * 747796405u + 2891336453u;
    uint32_t w = ((s >> ((s >> 28u) + 4u)) ^ s) * 277803737u;
    return (w >> 22u) ^ w;
}
static inline float fb_unit(uint32_t *s) { /* [0,1) */
    *s = fb_hash(*s);
    return (float)(*s) * (1.0f / 4294967296.0f);
}
static inline float fb_range(uint32_t *s, float lo, float hi) {
    return lo + (hi - lo) * fb_unit(s);
}

int furball_generate(size_t nstrands, int segs, float root_radius,
                     float radius_scale, uint32_t seed, cyhair_t *out) {
    if (!out || nstrands == 0 || segs < 1) return -1;
    if (!(root_radius > 0.0f)) root_radius = 0.006f;
    if (!(radius_scale > 0.0f)) radius_scale = 1.0f;
    memset(out, 0, sizeof(*out));

    const float R = 1.0f;             /* base sphere radius */
    const float L = 0.55f;            /* hair length */
    const uint32_t pts_per = (uint32_t)segs + 1u;
    const size_t npoints = nstrands * pts_per;

    float *points = (float *)malloc(npoints * 3 * sizeof(float));
    float *radius = (float *)malloc(npoints * sizeof(float));
    uint32_t *sfirst = (uint32_t *)malloc(nstrands * sizeof(uint32_t));
    uint32_t *scount = (uint32_t *)malloc(nstrands * sizeof(uint32_t));
    if (!points || !radius || !sfirst || !scount) {
        free(points);
        free(radius);
        free(sfirst);
        free(scount);
        return -10;
    }

    float lo[3] = {1e30f, 1e30f, 1e30f}, hi[3] = {-1e30f, -1e30f, -1e30f};
    const float TWO_PI = 6.2831853071795864f;

    for (size_t i = 0; i < nstrands; i++) {
        uint32_t s = seed + (uint32_t)i * 2654435761u + 1u;
        sfirst[i] = (uint32_t)(i * pts_per);
        scount[i] = pts_per;

        /* random root direction on the unit sphere */
        float z = 2.0f * fb_unit(&s) - 1.0f;
        float phi = TWO_PI * fb_unit(&s);
        float rr = sqrtf(1.0f - z * z);
        float d[3] = {rr * cosf(phi), z, rr * sinf(phi)};
        float root[3] = {R * d[0], R * d[1], R * d[2]};

        /* tangent-plane basis (u, v) perpendicular to d */
        float a[3] = {1.0f, 0.0f, 0.0f};
        if (fabsf(d[0]) > 0.9f) { a[0] = 0.0f; a[1] = 1.0f; }
        float u[3] = {d[1] * a[2] - d[2] * a[1], d[2] * a[0] - d[0] * a[2],
                      d[0] * a[1] - d[1] * a[0]};
        float ul = sqrtf(u[0] * u[0] + u[1] * u[1] + u[2] * u[2]);
        if (ul < 1e-6f) ul = 1.0f;
        for (int k = 0; k < 3; k++) u[k] /= ul;
        float v[3] = {d[1] * u[2] - d[2] * u[1], d[2] * u[0] - d[0] * u[2],
                      d[0] * u[1] - d[1] * u[0]};

        /* per-strand curl + gravity droop */
        float twist = fb_range(&s, 1.5f, 4.0f) * (fb_unit(&s) < 0.5f ? -1.0f : 1.0f);
        float phase = TWO_PI * fb_unit(&s);
        float curl = fb_range(&s, 0.08f, 0.30f) * L;
        float droop = fb_range(&s, 0.0f, 0.35f) * L;
        float rootr = root_radius * radius_scale * fb_range(&s, 0.7f, 1.3f);

        for (uint32_t k = 0; k < pts_per; k++) {
            float t = (float)k / (float)segs; /* 0..1 along the strand */
            float ang = phase + t * twist * TWO_PI;
            float cw = curl * t;       /* curl widens toward the tip */
            float ca = cosf(ang), sa = sinf(ang);
            float dg = droop * t * t;  /* gravity, accelerating */
            size_t idx = (size_t)i * pts_per + k;
            float p[3];
            for (int c = 0; c < 3; c++)
                p[c] = root[c] + d[c] * (L * t) + (u[c] * ca + v[c] * sa) * cw;
            p[1] -= dg;
            points[idx * 3 + 0] = p[0];
            points[idx * 3 + 1] = p[1];
            points[idx * 3 + 2] = p[2];
            float rad = rootr * (1.0f - 0.85f * t);
            radius[idx] = rad > 1e-5f ? rad : 1e-5f;
            for (int c = 0; c < 3; c++) {
                if (p[c] < lo[c]) lo[c] = p[c];
                if (p[c] > hi[c]) hi[c] = p[c];
            }
        }
    }

    out->points = points;
    out->radius = radius;
    out->strand_first = sfirst;
    out->strand_count = scount;
    out->nstrands = nstrands;
    out->npoints = npoints;
    out->nsegments = nstrands * (size_t)segs;
    for (int c = 0; c < 3; c++) {
        out->bbox_min[c] = lo[c];
        out->bbox_max[c] = hi[c];
    }
    return 0;
}
