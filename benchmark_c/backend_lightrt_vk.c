/*
 * backend_lightrt_vk.c — Vulkan GPU trace backend (Path A: CPU build -> GPU
 * trace). Gated on LRTBENCH_HAVE_VK; compiles to a NULL stub otherwise, exactly
 * like the other optional backends.
 *
 * "vk-trace" measures end-to-end GPU closest-hit throughput per ray batch,
 * INCLUDING the per-call scene upload + ray upload + dispatch + hit download
 * (lrt_vk_trace_scene is one-shot). A resident path that uploads the BVH once is
 * a planned follow-up. occluded1N falls back to the CPU kernel (there is no GPU
 * any-hit path yet), so shadow workloads do not measure the GPU.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "backend.h"
#include "timing.h"

#ifdef LRTBENCH_HAVE_VK

#include <pthread.h>
#include <stdlib.h>

#include "../lightrt_c_vk.h"

/* One process-wide engine (engine creation is expensive; a single GPU queue is
 * the bottleneck anyway). The mutex serializes concurrent worker threads onto
 * that queue. */
static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;
static lrt_vk_engine *g_engine = NULL;
static int g_engine_tried = 0;

static lrt_vk_engine *vk_engine(void) {
    if (!g_engine_tried) {
        lrt_vk_engine_options o = {0};
        o.device_index = -1;
        o.prefer_discrete = 1;
        o.want_ray_tracing = 0;
        g_engine = lrt_vk_engine_create(&o, NULL);
        g_engine_tried = 1;
    }
    return g_engine;
}

static void *vk_build(const float *vertices, size_t ntris, int num_threads,
                      double *build_ms) {
    (void)num_threads;
    pthread_mutex_lock(&g_lock);
    lrt_vk_engine *e = vk_engine();
    pthread_mutex_unlock(&g_lock);
    if (!e) {
        if (build_ms) *build_ms = 0.0;
        return NULL; /* no GPU: harness reports build failure and continues */
    }
    lrt_tri_build_options opts = {
        .quality = LRT_TRI_BUILD_DEFAULT,
        .layout = LRT_TRI_LAYOUT_BVH8,
        .max_leaf_size = 0,
        .num_threads = (unsigned)(num_threads > 0 ? num_threads : 1),
    };
    uint64_t t0 = bench_time_ns();
    lrt_tri_scene *s = lrt_tri_scene_build(vertices, ntris, &opts, NULL);
    uint64_t t1 = bench_time_ns();
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    return s;
}

static void vk_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                           lrt_hit *hits, size_t n, int coherent) {
    (void)thread_idx;
    (void)coherent;
    if (!scene || n == 0) return;
    pthread_mutex_lock(&g_lock);
    lrt_vk_engine *e = g_engine;
    if (e)
        lrt_vk_trace_scene(e, (const lrt_tri_scene *)scene, rays, (uint32_t)n,
                           hits, NULL);
    pthread_mutex_unlock(&g_lock);
}

static void vk_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                          uint8_t *occluded, size_t n, int coherent) {
    /* No GPU any-hit path yet: fall back to the CPU kernel for correctness. */
    (void)thread_idx;
    (void)coherent;
    lrt_tri_occluded1N((const lrt_tri_scene *)scene, rays, occluded, n,
                       LRT_TRI_BATCH_INCOHERENT);
}

static size_t vk_memory_bytes(void *scene) {
    lrt_tri_stats st;
    lrt_tri_scene_stats((const lrt_tri_scene *)scene, &st);
    return st.memory_bytes;
}

static void vk_destroy(void *scene) {
    lrt_tri_scene_free((lrt_tri_scene *)scene);
}

static const bench_backend g_vk_backend = {
    "vk-trace", vk_build, vk_intersect1N, vk_occluded1N, vk_memory_bytes,
    vk_destroy,
};

const bench_backend *backend_lightrt_vk(void) { return &g_vk_backend; }

#else /* !LRTBENCH_HAVE_VK */

const bench_backend *backend_lightrt_vk(void) { return 0; }

#endif
