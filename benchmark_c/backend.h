/*
 * backend.h — uniform interface over the ray tracing backends measured by the
 * harness (lightrt C11 callback API, lightrt fp32 triangle API, Embree).
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LRTBENCH_BACKEND_H
#define LRTBENCH_BACKEND_H

#include <stddef.h>
#include <stdint.h>

#include "../lightrt_c_tri.h" /* lrt_ray / lrt_hit */

#ifdef __cplusplus
extern "C" {
#endif

typedef struct bench_backend {
    const char *name;

    /* Build a scene over a triangle soup (9*ntris floats). num_threads is the
     * maximum number of threads that will query the scene concurrently AND the
     * thread budget for the build itself (backends that build serially ignore
     * it; backends with non-thread-safe scenes replicate per thread). Returns
     * an opaque scene or NULL. Pure build time (excluding any input copy the
     * harness could have avoided) is written to *build_ms. */
    void *(*build)(const float *vertices, size_t ntris, int num_threads,
                   double *build_ms);

    /* Closest-hit a contiguous ray range. thread_idx in [0, num_threads) of
     * the calling worker; thread-safe backends ignore it. coherent is a
     * workload hint (1 = nearby rays, e.g. primary); backends without a
     * coherence-specialized path ignore it. */
    void (*intersect1N)(void *scene, int thread_idx, const lrt_ray *rays,
                        lrt_hit *hits, size_t n, int coherent);

    /* Any-hit a contiguous ray range; occluded[i] = 0 or 1. */
    void (*occluded1N)(void *scene, int thread_idx, const lrt_ray *rays,
                       uint8_t *occluded, size_t n, int coherent);

    /* Acceleration-structure memory (bytes), excluding the input soup. */
    size_t (*memory_bytes)(void *scene);

    void (*destroy)(void *scene);
} bench_backend;

/* Registered backends (NULL when compiled out). */
const bench_backend *backend_lightrt_cb(void);    /* lightrt_c.h callback API */
const bench_backend *backend_lightrt_bvh4(void);  /* lightrt_c_tri.h, BVH4/SAH */
const bench_backend *backend_lightrt_bvh8(void);  /* lightrt_c_tri.h, BVH8/SAH */
const bench_backend *backend_lightrt_lbvh4(void); /* BVH4, Morton fast build */
const bench_backend *backend_lightrt_lbvh8(void); /* BVH8, Morton fast build */
const bench_backend *backend_lightrt_bvh8q(void); /* BVH8, quantized nodes */
const bench_backend *backend_lightrt_sbvh4(void); /* BVH4, spatial splits (HQ) */
const bench_backend *backend_lightrt_hair(void);  /* capsules (thin tris) */
const bench_backend *backend_lightrt_user(void);  /* custom geom (tri callback) */
const bench_backend *backend_lightrt_tlas(void);  /* TLAS, identity instance */
const bench_backend *backend_lightrt_sphere(void);/* analytic sphere per tri */
const bench_backend *backend_lightrt_sdf(void);   /* SDF blob per tri */
const bench_backend *backend_embree(void);        /* Embree 4 (optional) */
const bench_backend *backend_tinybvh(void);       /* jbikker/tinybvh BVH8_CPU */
const bench_backend *backend_madmann(void);       /* madmann91/bvh v2 */

#ifdef __cplusplus
}
#endif

#endif /* LRTBENCH_BACKEND_H */
