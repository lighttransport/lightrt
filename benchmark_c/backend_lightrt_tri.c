/*
 * backend_lightrt_tri.c — backends for the fp32 triangle-native lightrt API
 * (lightrt_c_tri.h), one forcing BVH4 and one forcing BVH8. The scene is
 * thread-safe, so all workers share one scene.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
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
static void *tri_build_bvh8q(const float *v, size_t n, int t, double *ms) {
    return tri_build_layout(v, n, t, ms, LRT_TRI_LAYOUT_BVH8Q,
                            LRT_TRI_BUILD_DEFAULT);
}
static void *tri_build_sbvh4(const float *v, size_t n, int t, double *ms) {
    return tri_build_layout(v, n, t, ms, LRT_TRI_LAYOUT_BVH4,
                            LRT_TRI_BUILD_HQ);
}

/* Hair backend: reinterpret each thin sliver triangle as a capsule. The
 * thinspan generator emits v0 = one end, v1/v2 = other end +/- width, so
 * p0 = v0, p1 = midpoint(v1,v2), r = |v1-v2|/2. Intended for the thinspan
 * scene; on generic meshes the capsules only approximate the triangles
 * (hit fractions will differ). */
static void *hair_build(const float *vertices, size_t ntris, int num_threads,
                        double *build_ms) {
    if (build_ms) *build_ms = 0.0;
    float *segs = (float *)malloc(ntris * 6 * sizeof(float));
    float *radii = (float *)malloc(ntris * sizeof(float));
    if (!segs || !radii) {
        free(segs);
        free(radii);
        return NULL;
    }
    uint64_t t0 = bench_time_ns();
    for (size_t i = 0; i < ntris; i++) {
        const float *v = &vertices[i * 9];
        float wx = v[3] - v[6], wy = v[4] - v[7], wz = v[5] - v[8];
        segs[i * 6 + 0] = v[0];
        segs[i * 6 + 1] = v[1];
        segs[i * 6 + 2] = v[2];
        segs[i * 6 + 3] = 0.5f * (v[3] + v[6]);
        segs[i * 6 + 4] = 0.5f * (v[4] + v[7]);
        segs[i * 6 + 5] = 0.5f * (v[5] + v[8]);
        float r = 0.5f * sqrtf(wx * wx + wy * wy + wz * wz);
        radii[i] = r > 1e-7f ? r : 1e-7f;
    }
    lrt_tri_build_options opts = {
        .quality = LRT_TRI_BUILD_DEFAULT,
        .layout = LRT_TRI_LAYOUT_BVH4,
        .max_leaf_size = 0,
        .num_threads = (unsigned)(num_threads > 0 ? num_threads : 1),
    };
    lrt_tri_scene *s =
        lrt_curve_scene_build(segs, radii, 0.0f, ntris, &opts, NULL);
    uint64_t t1 = bench_time_ns();
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    free(segs);
    free(radii);
    return s;
}


static void tri_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                            lrt_hit *hits, size_t n, int coherent) {
    (void)thread_idx;
    lrt_tri_intersect1N((const lrt_tri_scene *)scene, rays, hits, n,
                        coherent ? LRT_TRI_BATCH_COHERENT
                                 : LRT_TRI_BATCH_INCOHERENT);
}

static void tri_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                           uint8_t *occluded, size_t n, int coherent) {
    (void)thread_idx;
    lrt_tri_occluded1N((const lrt_tri_scene *)scene, rays, occluded, n,
                       coherent ? LRT_TRI_BATCH_COHERENT
                                : LRT_TRI_BATCH_INCOHERENT);
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
static const bench_backend g_bvh8q_backend = {
    "c11-bvh8q", tri_build_bvh8q, tri_intersect1N, tri_occluded1N,
    tri_memory_bytes, tri_destroy,
};
static const bench_backend g_sbvh4_backend = {
    "c11-sbvh4", tri_build_sbvh4, tri_intersect1N, tri_occluded1N,
    tri_memory_bytes, tri_destroy,
};

const bench_backend *backend_lightrt_bvh4(void) { return &g_bvh4_backend; }
const bench_backend *backend_lightrt_bvh8(void) { return &g_bvh8_backend; }
const bench_backend *backend_lightrt_lbvh4(void) { return &g_lbvh4_backend; }
const bench_backend *backend_lightrt_lbvh8(void) { return &g_lbvh8_backend; }
const bench_backend *backend_lightrt_bvh8q(void) { return &g_bvh8q_backend; }
const bench_backend *backend_lightrt_sbvh4(void) { return &g_sbvh4_backend; }

static const bench_backend g_hair_backend = {
    "c11-hair", hair_build, tri_intersect1N, tri_occluded1N, tri_memory_bytes,
    tri_destroy,
};
const bench_backend *backend_lightrt_hair(void) { return &g_hair_backend; }
