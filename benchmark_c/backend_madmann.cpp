/*
 * backend_madmann.cpp — madmann91/bvh (libbvh v2) backend. Uses the
 * out-of-the-box DefaultBuilder at Quality::High (mini-tree parallel build +
 * reinsertion optimization) and single-ray traversal over PrecomputedTri,
 * following the library's own test/benchmark.cpp. Compiled in when the build
 * finds third_party/bvh/src and defines LRTBENCH_HAVE_MADMANN_BVH; otherwise
 * backend_madmann() returns NULL.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "backend.h"

#ifdef LRTBENCH_HAVE_MADMANN_BVH

#include <bvh/v2/bvh.h>
#include <bvh/v2/default_builder.h>
#include <bvh/v2/executor.h>
#include <bvh/v2/node.h>
#include <bvh/v2/ray.h>
#include <bvh/v2/stack.h>
#include <bvh/v2/thread_pool.h>
#include <bvh/v2/tri.h>
#include <bvh/v2/vec.h>

#include <new>
#include <vector>

#include "timing.h"

namespace {

using Scalar = float;
using Vec3 = bvh::v2::Vec<Scalar, 3>;
using BBox = bvh::v2::BBox<Scalar, 3>;
using Tri = bvh::v2::Tri<Scalar, 3>;
using Node = bvh::v2::Node<Scalar, 3>;
using Bvh = bvh::v2::Bvh<Node>;
using Ray = bvh::v2::Ray<Scalar, 3>;
using PrecomputedTri = bvh::v2::PrecomputedTri<Scalar>;

constexpr size_t kStackSize = 64;
constexpr size_t kInvalidId = SIZE_MAX;

struct mm_scene {
    Bvh bvh;
    std::vector<PrecomputedTri> tris; /* in input order; prim_ids indirect */
};

void *mm_build(const float *vertices, size_t ntris, int num_threads,
               double *build_ms) {
    if (build_ms) *build_ms = 0.0;
    mm_scene *ms = new (std::nothrow) mm_scene();
    if (!ms) return nullptr;

    bvh::v2::ThreadPool thread_pool(num_threads > 0 ? (size_t)num_threads : 1);
    bvh::v2::ParallelExecutor executor(thread_pool);

    uint64_t t0 = bench_time_ns();
    std::vector<BBox> bboxes(ntris);
    std::vector<Vec3> centers(ntris);
    executor.for_each(0, ntris, [&](size_t begin, size_t end) {
        for (size_t i = begin; i < end; ++i) {
            Tri tri(Vec3(vertices[i * 9 + 0], vertices[i * 9 + 1], vertices[i * 9 + 2]),
                    Vec3(vertices[i * 9 + 3], vertices[i * 9 + 4], vertices[i * 9 + 5]),
                    Vec3(vertices[i * 9 + 6], vertices[i * 9 + 7], vertices[i * 9 + 8]));
            bboxes[i] = tri.get_bbox();
            centers[i] = tri.get_center();
        }
    });

    typename bvh::v2::DefaultBuilder<Node>::Config config;
    config.quality = bvh::v2::DefaultBuilder<Node>::Quality::High;
    ms->bvh = bvh::v2::DefaultBuilder<Node>::build(thread_pool, bboxes, centers,
                                                   config);

    ms->tris.resize(ntris);
    executor.for_each(0, ntris, [&](size_t begin, size_t end) {
        for (size_t i = begin; i < end; ++i) {
            ms->tris[i] = Tri(
                Vec3(vertices[i * 9 + 0], vertices[i * 9 + 1], vertices[i * 9 + 2]),
                Vec3(vertices[i * 9 + 3], vertices[i * 9 + 4], vertices[i * 9 + 5]),
                Vec3(vertices[i * 9 + 6], vertices[i * 9 + 7], vertices[i * 9 + 8]));
        }
    });
    uint64_t t1 = bench_time_ns();
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    return ms;
}

void mm_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                    lrt_hit *hits, size_t n, int coherent) {
    (void)coherent;
    (void)thread_idx;
    const mm_scene *ms = (const mm_scene *)scene;
    for (size_t i = 0; i < n; i++) {
        const lrt_ray *r = &rays[i];
        Ray ray(Vec3(r->org[0], r->org[1], r->org[2]),
                Vec3(r->dir[0], r->dir[1], r->dir[2]), r->tmin, r->tmax);
        size_t prim_id = kInvalidId;
        Scalar u = 0, v = 0;
        bvh::v2::SmallStack<Bvh::Index, kStackSize> stack;
        ms->bvh.intersect<false, /*IsRobust=*/false>(
            ray, ms->bvh.get_root().index, stack,
            [&](size_t begin, size_t end) {
                for (size_t j = begin; j < end; ++j) {
                    size_t k = ms->bvh.prim_ids[j];
                    if (auto hit = ms->tris[k].intersect(ray)) {
                        ray.tmax = std::get<0>(*hit);
                        u = std::get<1>(*hit);
                        v = std::get<2>(*hit);
                        prim_id = k;
                    }
                }
                return prim_id != kInvalidId;
            });
        if (prim_id != kInvalidId) {
            hits[i].t = ray.tmax;
            hits[i].u = u;
            hits[i].v = v;
            hits[i].prim_id = (uint32_t)prim_id;
        } else {
            hits[i].t = 0.0f;
            hits[i].u = 0.0f;
            hits[i].v = 0.0f;
            hits[i].prim_id = LRT_TRI_NO_HIT;
        }
    }
}

void mm_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                   uint8_t *occluded, size_t n, int coherent) {
    (void)coherent;
    (void)thread_idx;
    const mm_scene *ms = (const mm_scene *)scene;
    for (size_t i = 0; i < n; i++) {
        const lrt_ray *r = &rays[i];
        Ray ray(Vec3(r->org[0], r->org[1], r->org[2]),
                Vec3(r->dir[0], r->dir[1], r->dir[2]), r->tmin, r->tmax);
        bool found = false;
        bvh::v2::SmallStack<Bvh::Index, kStackSize> stack;
        ms->bvh.intersect</*IsAnyHit=*/true, /*IsRobust=*/false>(
            ray, ms->bvh.get_root().index, stack,
            [&](size_t begin, size_t end) {
                for (size_t j = begin; j < end; ++j) {
                    size_t k = ms->bvh.prim_ids[j];
                    if (ms->tris[k].intersect(ray)) {
                        found = true;
                        return true; /* any-hit: stop traversal */
                    }
                }
                return false;
            });
        occluded[i] = found ? 1 : 0;
    }
}

size_t mm_memory_bytes(void *scene) {
    const mm_scene *ms = (const mm_scene *)scene;
    return ms->bvh.nodes.size() * sizeof(Node) +
           ms->bvh.prim_ids.size() * sizeof(size_t) +
           ms->tris.size() * sizeof(PrecomputedTri);
}

void mm_destroy(void *scene) { delete (mm_scene *)scene; }

const bench_backend g_madmann_backend = {
    "mm-bvh", mm_build, mm_intersect1N, mm_occluded1N, mm_memory_bytes,
    mm_destroy,
};

} // namespace

extern "C" const bench_backend *backend_madmann(void) {
    return &g_madmann_backend;
}

#else /* !LRTBENCH_HAVE_MADMANN_BVH */

extern "C" const bench_backend *backend_madmann(void) { return nullptr; }

#endif
