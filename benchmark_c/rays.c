/*
 * rays.c — deterministic ray-workload generators.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "rays.h"

#include <math.h>

#define RAYS_PI 3.14159265358979323846f

static uint32_t pcg_hash(uint32_t input) {
    uint32_t state = input * 747796405u + 2891336453u;
    uint32_t word = ((state >> ((state >> 28u) + 4u)) ^ state) * 277803737u;
    return (word >> 22u) ^ word;
}

static void normalize3(float v[3]) {
    float len = sqrtf(v[0] * v[0] + v[1] * v[1] + v[2] * v[2]);
    if (len > 1e-12f) {
        v[0] /= len;
        v[1] /= len;
        v[2] /= len;
    }
}

static void cross3(const float a[3], const float b[3], float out[3]) {
    out[0] = a[1] * b[2] - a[2] * b[1];
    out[1] = a[2] * b[0] - a[0] * b[2];
    out[2] = a[0] * b[1] - a[1] * b[0];
}

void rays_gen_primary(lrt_ray *rays, size_t n, uint32_t seed) {
    (void)seed; /* primary rays are fully deterministic from the camera */
    const float eye[3] = {2.5f, 2.5f, 2.5f};
    float fwd[3] = {-eye[0], -eye[1], -eye[2]};
    normalize3(fwd);
    const float world_up[3] = {0.0f, 1.0f, 0.0f};
    float right[3], up[3];
    cross3(fwd, world_up, right);
    normalize3(right);
    cross3(right, fwd, up);

    uint32_t side = 1;
    while ((size_t)side * side < n) side++;
    const float fov_y = 60.0f * RAYS_PI / 180.0f;
    const float tan_half = tanf(0.5f * fov_y);

    size_t emitted = 0;
    /* Walk Morton codes; skip codes whose pixel falls outside side x side. */
    for (uint32_t code = 0; emitted < n; code++) {
        uint32_t px = 0, py = 0;
        /* de-interleave */
        {
            uint32_t x = code & 0x55555555u;
            x = (x | (x >> 1)) & 0x33333333u;
            x = (x | (x >> 2)) & 0x0F0F0F0Fu;
            x = (x | (x >> 4)) & 0x00FF00FFu;
            x = (x | (x >> 8)) & 0x0000FFFFu;
            px = x;
            uint32_t y = (code >> 1) & 0x55555555u;
            y = (y | (y >> 1)) & 0x33333333u;
            y = (y | (y >> 2)) & 0x0F0F0F0Fu;
            y = (y | (y >> 4)) & 0x00FF00FFu;
            y = (y | (y >> 8)) & 0x0000FFFFu;
            py = y;
        }
        if (px >= side || py >= side) continue;

        float sx = ((float)px + 0.5f) / (float)side * 2.0f - 1.0f;
        float sy = 1.0f - ((float)py + 0.5f) / (float)side * 2.0f;
        float dx = sx * tan_half, dy = sy * tan_half;

        lrt_ray *r = &rays[emitted++];
        r->org[0] = eye[0];
        r->org[1] = eye[1];
        r->org[2] = eye[2];
        r->dir[0] = fwd[0] + dx * right[0] + dy * up[0];
        r->dir[1] = fwd[1] + dx * right[1] + dy * up[1];
        r->dir[2] = fwd[2] + dx * right[2] + dy * up[2];
        normalize3(r->dir);
        r->tmin = 1e-6f;
        r->tmax = 1e10f;
    }
}

void rays_gen_incoherent(lrt_ray *rays, size_t n, uint32_t seed) {
    for (size_t i = 0; i < n; i++) {
        uint32_t s = (uint32_t)((i + seed) * 2654435761u);
        float theta = 2.0f * RAYS_PI * (float)(s & 0xFFFFFF) / 16777216.0f;
        s = pcg_hash(s);
        float phi = acosf(2.0f * (float)(s & 0xFFFFFF) / 16777216.0f - 1.0f);
        s = pcg_hash(s);
        float sx = sinf(phi) * cosf(theta);
        float sy = sinf(phi) * sinf(theta);
        float sz = cosf(phi);

        lrt_ray *r = &rays[i];
        r->org[0] = sx * 5.0f;
        r->org[1] = sy * 5.0f;
        r->org[2] = sz * 5.0f;

        s = pcg_hash(s);
        float spread = (float)(s & 0xFFFF) / 65536.0f * 0.5f;
        float tx = ((float)((s >> 16) & 0xFF) / 256.0f * 2.0f - 1.0f) * spread;
        float ty = ((float)((s >> 8) & 0xFF) / 256.0f * 2.0f - 1.0f) * spread;
        float tz = ((float)(s & 0xFF) / 256.0f * 2.0f - 1.0f) * spread;
        r->dir[0] = -r->org[0] + tx;
        r->dir[1] = -r->org[1] + ty;
        r->dir[2] = -r->org[2] + tz;
        normalize3(r->dir);
        r->tmin = 1e-6f;
        r->tmax = 1e10f;
    }
}

size_t rays_gen_shadow(lrt_ray *rays, size_t n, const lrt_ray *primary,
                       const lrt_hit *hits, const float *vertices,
                       size_t ntris, uint32_t seed) {
    const float light[3] = {4.0f, 6.0f, 4.0f};
    const float eps = 1e-4f;

    for (size_t i = 0; i < n; i++) {
        lrt_ray *r = &rays[i];
        const lrt_hit *h = &hits[i];
        if (h->prim_id != LRT_TRI_NO_HIT && (size_t)h->prim_id < ntris) {
            const lrt_ray *p = &primary[i];
            float hp[3] = {
                p->org[0] + p->dir[0] * h->t,
                p->org[1] + p->dir[1] * h->t,
                p->org[2] + p->dir[2] * h->t,
            };
            /* Geometric normal of the hit triangle, flipped toward the light. */
            const float *v = &vertices[(size_t)h->prim_id * 9];
            float e1[3] = {v[3] - v[0], v[4] - v[1], v[5] - v[2]};
            float e2[3] = {v[6] - v[0], v[7] - v[1], v[8] - v[2]};
            float nrm[3];
            cross3(e1, e2, nrm);
            normalize3(nrm);
            float to_light[3] = {light[0] - hp[0], light[1] - hp[1], light[2] - hp[2]};
            float dist = sqrtf(to_light[0] * to_light[0] + to_light[1] * to_light[1] +
                               to_light[2] * to_light[2]);
            if (nrm[0] * to_light[0] + nrm[1] * to_light[1] + nrm[2] * to_light[2] < 0.0f) {
                nrm[0] = -nrm[0];
                nrm[1] = -nrm[1];
                nrm[2] = -nrm[2];
            }
            r->org[0] = hp[0] + nrm[0] * eps;
            r->org[1] = hp[1] + nrm[1] * eps;
            r->org[2] = hp[2] + nrm[2] * eps;
            r->dir[0] = to_light[0];
            r->dir[1] = to_light[1];
            r->dir[2] = to_light[2];
            normalize3(r->dir);
            r->tmin = eps;
            r->tmax = dist > 2.0f * eps ? dist - eps : eps;
        } else {
            /* Primary miss: aim a ray from the light toward a jittered point
             * near the origin so the slot still traverses the scene. */
            uint32_t s = pcg_hash((uint32_t)i ^ seed);
            float jx = ((float)(s & 0x3FF) / 1024.0f - 0.5f);
            s = pcg_hash(s);
            float jy = ((float)(s & 0x3FF) / 1024.0f - 0.5f);
            s = pcg_hash(s);
            float jz = ((float)(s & 0x3FF) / 1024.0f - 0.5f);
            r->org[0] = light[0];
            r->org[1] = light[1];
            r->org[2] = light[2];
            r->dir[0] = jx - light[0];
            r->dir[1] = jy - light[1];
            r->dir[2] = jz - light[2];
            normalize3(r->dir);
            r->tmin = 1e-6f;
            r->tmax = 1e10f;
        }
    }
    return n;
}
