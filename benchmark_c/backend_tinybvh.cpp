/*
 * backend_tinybvh.cpp — jbikker/tinybvh backend (BVH8_CPU layout: 8-wide
 * SIMD nodes, AVX2). Compiled in when the build finds
 * third_party/tinybvh/tiny_bvh.h and defines LRTBENCH_HAVE_TINYBVH;
 * otherwise backend_tinybvh() returns NULL.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "backend.h"

#ifdef LRTBENCH_HAVE_TINYBVH

#define TINYBVH_IMPLEMENTATION
#include <tiny_bvh.h>

#include <new>
#include <vector>

#include "timing.h"

namespace {

struct tb_scene {
    tinybvh::BVH8_CPU bvh;
    std::vector<tinybvh::bvhvec4> verts; /* 3 vec4 per triangle */
};

void *tb_build(const float *vertices, size_t ntris, int num_threads,
               double *build_ms) {
    (void)num_threads; /* tinybvh builds single-threaded */
    if (build_ms) *build_ms = 0.0;
    tb_scene *ts = new (std::nothrow) tb_scene();
    if (!ts) return nullptr;

    uint64_t t0 = bench_time_ns();
    ts->verts.resize(ntris * 3);
    for (size_t i = 0; i < ntris * 3; i++) {
        ts->verts[i] = tinybvh::bvhvec4(vertices[i * 3 + 0], vertices[i * 3 + 1],
                                        vertices[i * 3 + 2], 0.0f);
    }
    ts->bvh.Build(ts->verts.data(), (uint32_t)ntris);
    uint64_t t1 = bench_time_ns();
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    return ts;
}

void tb_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                    lrt_hit *hits, size_t n, int coherent) {
    (void)coherent;
    (void)thread_idx;
    const tb_scene *ts = (const tb_scene *)scene;
    for (size_t i = 0; i < n; i++) {
        const lrt_ray *r = &rays[i];
        /* tinybvh rays have no tmin; start at org + tmin*dir instead */
        tinybvh::bvhvec3 o(r->org[0] + r->tmin * r->dir[0],
                           r->org[1] + r->tmin * r->dir[1],
                           r->org[2] + r->tmin * r->dir[2]);
        tinybvh::bvhvec3 d(r->dir[0], r->dir[1], r->dir[2]);
        float range = r->tmax - r->tmin;
        tinybvh::Ray ray(o, d, range);
        ts->bvh.Intersect(ray);
        if (ray.hit.t < range) {
            hits[i].t = ray.hit.t + r->tmin;
            hits[i].u = ray.hit.u;
            hits[i].v = ray.hit.v;
            hits[i].prim_id = ray.hit.prim;
        } else {
            hits[i].t = 0.0f;
            hits[i].u = 0.0f;
            hits[i].v = 0.0f;
            hits[i].prim_id = LRT_TRI_NO_HIT;
        }
    }
}

void tb_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                   uint8_t *occluded, size_t n, int coherent) {
    (void)coherent;
    (void)thread_idx;
    const tb_scene *ts = (const tb_scene *)scene;
    for (size_t i = 0; i < n; i++) {
        const lrt_ray *r = &rays[i];
        tinybvh::bvhvec3 o(r->org[0] + r->tmin * r->dir[0],
                           r->org[1] + r->tmin * r->dir[1],
                           r->org[2] + r->tmin * r->dir[2]);
        tinybvh::bvhvec3 d(r->dir[0], r->dir[1], r->dir[2]);
        tinybvh::Ray ray(o, d, r->tmax - r->tmin);
        occluded[i] = ts->bvh.IsOccluded(ray) ? 1 : 0;
    }
}

size_t tb_memory_bytes(void *scene) {
    const tb_scene *ts = (const tb_scene *)scene;
    /* interleaved node + triangle data, in 16-byte blocks */
    return (size_t)ts->bvh.usedBlocks * 16u;
}

void tb_destroy(void *scene) { delete (tb_scene *)scene; }

const bench_backend g_tinybvh_backend = {
    "tinybvh", tb_build, tb_intersect1N, tb_occluded1N, tb_memory_bytes,
    tb_destroy,
};

} // namespace

extern "C" const bench_backend *backend_tinybvh(void) {
    return &g_tinybvh_backend;
}

#else /* !LRTBENCH_HAVE_TINYBVH */

extern "C" const bench_backend *backend_tinybvh(void) { return nullptr; }

#endif
