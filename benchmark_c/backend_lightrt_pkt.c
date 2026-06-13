/*
 * backend_lightrt_pkt.c — packet-traversal variants of the fp32 triangle
 * backends. They assemble the contiguous (coherent) ray range into Ray4/Ray8
 * SoA packets and call the lrt_tri_intersect4/8 + lrt_tri_occluded4/8 kernels,
 * to A/B the coherent ray-packet path against the per-ray path. Same geometry
 * as c11-bvh4/c11-bvh8, so they are explicit-only (not part of --backend all).
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stdlib.h>

#include "backend.h"
#include "timing.h"

static void *pkt_build_bvh4(const float *v, size_t n, int t, double *ms) {
    lrt_tri_build_options opts = {
        .quality = LRT_TRI_BUILD_DEFAULT,
        .layout = LRT_TRI_LAYOUT_BVH4,
        .max_leaf_size = 0,
        .num_threads = (unsigned)(t > 0 ? t : 1),
    };
    uint64_t t0 = bench_time_ns();
    lrt_tri_scene *s = lrt_tri_scene_build(v, n, &opts, NULL);
    uint64_t t1 = bench_time_ns();
    if (ms) *ms = bench_ns_to_ms(t1 - t0);
    return s;
}
static void *pkt_build_bvh8(const float *v, size_t n, int t, double *ms) {
    lrt_tri_build_options opts = {
        .quality = LRT_TRI_BUILD_DEFAULT,
        .layout = LRT_TRI_LAYOUT_BVH8,
        .max_leaf_size = 0,
        .num_threads = (unsigned)(t > 0 ? t : 1),
    };
    uint64_t t0 = bench_time_ns();
    lrt_tri_scene *s = lrt_tri_scene_build(v, n, &opts, NULL);
    uint64_t t1 = bench_time_ns();
    if (ms) *ms = bench_ns_to_ms(t1 - t0);
    return s;
}

static inline void pack4(const lrt_ray *r, lrt_ray4 *p) {
    for (int k = 0; k < 4; k++) {
        p->orgx[k] = r[k].org[0];
        p->orgy[k] = r[k].org[1];
        p->orgz[k] = r[k].org[2];
        p->dirx[k] = r[k].dir[0];
        p->diry[k] = r[k].dir[1];
        p->dirz[k] = r[k].dir[2];
        p->tmin[k] = r[k].tmin;
        p->tmax[k] = r[k].tmax;
    }
}
static inline void pack8(const lrt_ray *r, lrt_ray8 *p) {
    for (int k = 0; k < 8; k++) {
        p->orgx[k] = r[k].org[0];
        p->orgy[k] = r[k].org[1];
        p->orgz[k] = r[k].org[2];
        p->dirx[k] = r[k].dir[0];
        p->diry[k] = r[k].dir[1];
        p->dirz[k] = r[k].dir[2];
        p->tmin[k] = r[k].tmin;
        p->tmax[k] = r[k].tmax;
    }
}

static void pkt4_intersect1N(void *scene, int ti, const lrt_ray *rays,
                             lrt_hit *hits, size_t n, int coherent) {
    (void)ti;
    (void)coherent;
    const lrt_tri_scene *s = (const lrt_tri_scene *)scene;
    size_t i = 0;
    for (; i + 4 <= n; i += 4) {
        lrt_ray4 p;
        pack4(&rays[i], &p);
        lrt_hit4 h;
        lrt_tri_intersect4(s, &p, &h);
        for (int k = 0; k < 4; k++) {
            hits[i + k].t = h.t[k];
            hits[i + k].u = h.u[k];
            hits[i + k].v = h.v[k];
            hits[i + k].prim_id = h.prim_id[k];
        }
    }
    for (; i < n; i++) lrt_tri_intersect1(s, &rays[i], &hits[i]);
}
static void pkt4_occluded1N(void *scene, int ti, const lrt_ray *rays,
                            uint8_t *occ, size_t n, int coherent) {
    (void)ti;
    (void)coherent;
    const lrt_tri_scene *s = (const lrt_tri_scene *)scene;
    size_t i = 0;
    for (; i + 4 <= n; i += 4) {
        lrt_ray4 p;
        pack4(&rays[i], &p);
        uint8_t o[4];
        lrt_tri_occluded4(s, &p, o);
        for (int k = 0; k < 4; k++) occ[i + k] = o[k];
    }
    for (; i < n; i++) occ[i] = (uint8_t)lrt_tri_occluded1(s, &rays[i]);
}

static void pkt8_intersect1N(void *scene, int ti, const lrt_ray *rays,
                             lrt_hit *hits, size_t n, int coherent) {
    (void)ti;
    (void)coherent;
    const lrt_tri_scene *s = (const lrt_tri_scene *)scene;
    size_t i = 0;
    for (; i + 8 <= n; i += 8) {
        lrt_ray8 p;
        pack8(&rays[i], &p);
        lrt_hit8 h;
        lrt_tri_intersect8(s, &p, &h);
        for (int k = 0; k < 8; k++) {
            hits[i + k].t = h.t[k];
            hits[i + k].u = h.u[k];
            hits[i + k].v = h.v[k];
            hits[i + k].prim_id = h.prim_id[k];
        }
    }
    for (; i < n; i++) lrt_tri_intersect1(s, &rays[i], &hits[i]);
}
static void pkt8_occluded1N(void *scene, int ti, const lrt_ray *rays,
                            uint8_t *occ, size_t n, int coherent) {
    (void)ti;
    (void)coherent;
    const lrt_tri_scene *s = (const lrt_tri_scene *)scene;
    size_t i = 0;
    for (; i + 8 <= n; i += 8) {
        lrt_ray8 p;
        pack8(&rays[i], &p);
        uint8_t o[8];
        lrt_tri_occluded8(s, &p, o);
        for (int k = 0; k < 8; k++) occ[i + k] = o[k];
    }
    for (; i < n; i++) occ[i] = (uint8_t)lrt_tri_occluded1(s, &rays[i]);
}

static size_t pkt_memory(void *scene) {
    lrt_tri_stats st;
    lrt_tri_scene_stats((const lrt_tri_scene *)scene, &st);
    return st.memory_bytes;
}
static void pkt_destroy(void *scene) {
    lrt_tri_scene_free((lrt_tri_scene *)scene);
}

static const bench_backend g_bvh4_pkt = {
    "c11-bvh4-pkt", pkt_build_bvh4, pkt4_intersect1N, pkt4_occluded1N,
    pkt_memory, pkt_destroy,
};
static const bench_backend g_bvh8_pkt = {
    "c11-bvh8-pkt", pkt_build_bvh8, pkt8_intersect1N, pkt8_occluded1N,
    pkt_memory, pkt_destroy,
};

const bench_backend *backend_lightrt_bvh4_pkt(void) { return &g_bvh4_pkt; }
const bench_backend *backend_lightrt_bvh8_pkt(void) { return &g_bvh8_pkt; }

/* c11-bvh4-1ray: pure per-ray loop (no interleaved pipeline, no packet) — to
 * test whether the latency-hiding pipeline helps or hurts on cache-resident
 * incoherent rays. */
static void r1_intersect1N(void *scene, int ti, const lrt_ray *rays,
                           lrt_hit *hits, size_t n, int coherent) {
    (void)ti;
    (void)coherent;
    const lrt_tri_scene *s = (const lrt_tri_scene *)scene;
    for (size_t i = 0; i < n; i++) lrt_tri_intersect1(s, &rays[i], &hits[i]);
}
static void r1_occluded1N(void *scene, int ti, const lrt_ray *rays, uint8_t *occ,
                          size_t n, int coherent) {
    (void)ti;
    (void)coherent;
    const lrt_tri_scene *s = (const lrt_tri_scene *)scene;
    for (size_t i = 0; i < n; i++) occ[i] = (uint8_t)lrt_tri_occluded1(s, &rays[i]);
}
static const bench_backend g_bvh4_1ray = {
    "c11-bvh4-1ray", pkt_build_bvh4, r1_intersect1N, r1_occluded1N, pkt_memory,
    pkt_destroy,
};
const bench_backend *backend_lightrt_bvh4_1ray(void) { return &g_bvh4_1ray; }
