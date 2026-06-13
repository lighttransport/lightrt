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
        o.want_ray_tracing = 1; /* enables the vk-rtx backend; harmless for vk-trace */
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

/* --- vk-rtx: hardware ray tracing (VK_KHR_ray_query) ----------------------
 * Resident mode: the acceleration structure is built ONCE in build() and the
 * per-batch trace runs against it with device-local ray/hit buffers, so the
 * timed intersect1N measures GPU traversal (build cost shows up in build_ms). */
static void *rtx_build(const float *vertices, size_t ntris, int num_threads,
                       double *build_ms) {
    (void)num_threads;
    if (build_ms) *build_ms = 0.0;
    pthread_mutex_lock(&g_lock);
    lrt_vk_engine *e = vk_engine();
    lrt_vk_rtx_scene *s = NULL;
    if (e && (lrt_vk_engine_caps(e) & LRT_VK_CAP_RAY_QUERY)) {
        uint64_t t0 = bench_time_ns();
        s = lrt_vk_rtx_scene_build(e, vertices, (uint32_t)ntris, NULL);
        uint64_t t1 = bench_time_ns();
        if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    }
    pthread_mutex_unlock(&g_lock);
    return s; /* NULL if no RT device: harness reports unavailable */
}

static void rtx_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                            lrt_hit *hits, size_t n, int coherent) {
    (void)thread_idx;
    (void)coherent;
    if (!scene || n == 0) return;
    pthread_mutex_lock(&g_lock);
    if (g_engine)
        lrt_vk_rtx_scene_trace(g_engine, (lrt_vk_rtx_scene *)scene, rays,
                               (uint32_t)n, hits, NULL);
    pthread_mutex_unlock(&g_lock);
}

static void rtx_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                           uint8_t *occluded, size_t n, int coherent) {
    (void)thread_idx;
    (void)coherent;
    if (!scene || n == 0) return;
    lrt_hit *tmp = (lrt_hit *)malloc(n * sizeof(lrt_hit));
    if (!tmp) return;
    pthread_mutex_lock(&g_lock);
    int ok = g_engine && lrt_vk_rtx_scene_trace(g_engine,
                                                (lrt_vk_rtx_scene *)scene, rays,
                                                (uint32_t)n, tmp, NULL) >= 0;
    pthread_mutex_unlock(&g_lock);
    for (size_t i = 0; i < n; i++)
        occluded[i] = (ok && tmp[i].prim_id != LRT_TRI_NO_HIT) ? 1u : 0u;
    free(tmp);
}

static size_t rtx_memory_bytes(void *scene) {
    (void)scene; /* opaque vendor AS; size not queried */
    return 0;
}

static void rtx_destroy(void *scene) {
    if (scene) lrt_vk_rtx_scene_free(g_engine, (lrt_vk_rtx_scene *)scene);
}

static const bench_backend g_rtx_backend = {
    "vk-rtx", rtx_build, rtx_intersect1N, rtx_occluded1N, rtx_memory_bytes,
    rtx_destroy,
};

const bench_backend *backend_lightrt_vk_rtx(void) { return &g_rtx_backend; }

#else /* !LRTBENCH_HAVE_VK */

const bench_backend *backend_lightrt_vk(void) { return 0; }
const bench_backend *backend_lightrt_vk_rtx(void) { return 0; }

#endif
