/*
 * backend_lightrt_tri.c — backends for the fp32 triangle-native lightrt API
 * (lightrt_c_tri.h), one forcing BVH4 and one forcing BVH8. The scene is
 * thread-safe, so all workers share one scene.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stdlib.h>

#include "backend.h"
#include "timing.h"

static void *tri_build_layout(const float *vertices, size_t ntris,
                              int num_threads, double *build_ms,
                              lrt_tri_layout layout, lrt_tri_quality quality) {
    lrt_tri_build_options opts = {
        .quality = quality,
        .layout = layout,
        .max_leaf_size = 0,
        .num_threads = (unsigned)(num_threads > 0 ? num_threads : 1),
    };
    uint64_t t0 = bench_time_ns();
    lrt_tri_scene *s = lrt_tri_scene_build(vertices, ntris, &opts, NULL);
    uint64_t t1 = bench_time_ns();
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    return s;
}

static void *tri_build_bvh4(const float *v, size_t n, int t, double *ms) {
    return tri_build_layout(v, n, t, ms, LRT_TRI_LAYOUT_BVH4,
                            LRT_TRI_BUILD_DEFAULT);
}
static void *tri_build_bvh8(const float *v, size_t n, int t, double *ms) {
    return tri_build_layout(v, n, t, ms, LRT_TRI_LAYOUT_BVH8,
                            LRT_TRI_BUILD_DEFAULT);
}
static void *tri_build_lbvh4(const float *v, size_t n, int t, double *ms) {
    return tri_build_layout(v, n, t, ms, LRT_TRI_LAYOUT_BVH4,
                            LRT_TRI_BUILD_FAST);
}
static void *tri_build_lbvh8(const float *v, size_t n, int t, double *ms) {
    return tri_build_layout(v, n, t, ms, LRT_TRI_LAYOUT_BVH8,
                            LRT_TRI_BUILD_FAST);
}

static void tri_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                            lrt_hit *hits, size_t n) {
    (void)thread_idx;
    lrt_tri_intersect1N((const lrt_tri_scene *)scene, rays, hits, n);
}

static void tri_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                           uint8_t *occluded, size_t n) {
    (void)thread_idx;
    lrt_tri_occluded1N((const lrt_tri_scene *)scene, rays, occluded, n);
}

static size_t tri_memory_bytes(void *scene) {
    lrt_tri_stats st;
    lrt_tri_scene_stats((const lrt_tri_scene *)scene, &st);
    return st.memory_bytes;
}

static void tri_destroy(void *scene) {
    lrt_tri_scene_free((lrt_tri_scene *)scene);
}

static const bench_backend g_bvh4_backend = {
    "c11-bvh4", tri_build_bvh4, tri_intersect1N, tri_occluded1N,
    tri_memory_bytes, tri_destroy,
};
static const bench_backend g_bvh8_backend = {
    "c11-bvh8", tri_build_bvh8, tri_intersect1N, tri_occluded1N,
    tri_memory_bytes, tri_destroy,
};
static const bench_backend g_lbvh4_backend = {
    "c11-lbvh4", tri_build_lbvh4, tri_intersect1N, tri_occluded1N,
    tri_memory_bytes, tri_destroy,
};
static const bench_backend g_lbvh8_backend = {
    "c11-lbvh8", tri_build_lbvh8, tri_intersect1N, tri_occluded1N,
    tri_memory_bytes, tri_destroy,
};

const bench_backend *backend_lightrt_bvh4(void) { return &g_bvh4_backend; }
const bench_backend *backend_lightrt_bvh8(void) { return &g_bvh8_backend; }
const bench_backend *backend_lightrt_lbvh4(void) { return &g_lbvh4_backend; }
const bench_backend *backend_lightrt_lbvh8(void) { return &g_lbvh8_backend; }
