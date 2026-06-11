/*
 * lightrt_c_tri.h — C11 triangle-native fp32 BVH for LightRT.
 *
 * Optimized companion to the generic callback API in lightrt_c.h. Where that
 * API serves opaque fp64 primitives through per-primitive callbacks, this one
 * owns the triangles: vertex data is copied and pre-swizzled into SIMD-friendly
 * SoA leaf blocks at build time, the BVH is a wide (4- or 8-ary) tree with
 * cache-line-sized SoA nodes, and traversal kernels are compiled scalar,
 * SSE4 (BVH4) and AVX2 (BVH8) with compile-time dispatch.
 *
 * Queries are stateless and thread-safe: any number of threads may intersect
 * a single lrt_tri_scene concurrently. There are no cancel/progress hooks in
 * the query hot path.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LIGHTRT_C_TRI_H
#define LIGHTRT_C_TRI_H

#include <stddef.h>
#include <stdint.h>

#include "lightrt_c.h" /* lrt_result */

#ifdef __cplusplus
extern "C" {
#endif

/* Stored in lrt_hit.prim_id when nothing was hit. */
#define LRT_TRI_NO_HIT 0xFFFFFFFFu

typedef struct lrt_tri_scene lrt_tri_scene;

/* Single-precision ray. dir need not be normalized; the reported t is in units
 * of |dir|. tmin/tmax bound the accepted hit interval. 32 bytes. */
typedef struct lrt_ray {
    float org[3];
    float tmin;
    float dir[3];
    float tmax;
} lrt_ray;

/* Closest-hit result. prim_id is the caller's triangle index (i.e. the index
 * into the vertices array passed to lrt_tri_scene_build), or LRT_TRI_NO_HIT.
 * u/v are Moller-Trumbore barycentrics of the hit. 16 bytes. */
typedef struct lrt_hit {
    float t, u, v;
    uint32_t prim_id;
} lrt_hit;

typedef enum lrt_tri_quality {
    LRT_TRI_BUILD_FAST = 0,   /* LBVH (Morton sort + bit splits): fastest build */
    LRT_TRI_BUILD_DEFAULT = 1 /* binned SAH (16 bins): best traversal */
} lrt_tri_quality;

typedef enum lrt_tri_layout {
    LRT_TRI_LAYOUT_AUTO = 0, /* widest kernel compiled in */
    LRT_TRI_LAYOUT_BVH4 = 4,
    LRT_TRI_LAYOUT_BVH8 = 8,
    /* 8-wide with 8-bit quantized child bounds (128-byte nodes vs 256):
     * halves node bandwidth at the cost of extra decode ALU; intended for
     * memory-latency-bound incoherent rays on large scenes. */
    LRT_TRI_LAYOUT_BVH8Q = 9
} lrt_tri_layout;

typedef struct lrt_tri_build_options {
    lrt_tri_quality quality;
    lrt_tri_layout layout;
    unsigned max_leaf_size; /* triangles per leaf; 0 = default (8) */
    unsigned num_threads;   /* build threads; 0 or 1 = serial */
} lrt_tri_build_options;

/* Build a scene over ntris triangles. vertices = 9*ntris floats laid out as
 * v0.xyz v1.xyz v2.xyz per triangle. The data is copied and re-swizzled; the
 * caller's buffer is not retained. opts may be NULL for defaults. Returns NULL
 * on failure and, when err is non-NULL, stores the reason there. */
lrt_tri_scene *lrt_tri_scene_build(const float *vertices, size_t ntris,
                                   const lrt_tri_build_options *opts,
                                   lrt_result *err);

void lrt_tri_scene_free(lrt_tri_scene *s);

/* Closest hit. Returns 1 and fills *hit on a hit; returns 0 on miss (hit, if
 * non-NULL, gets prim_id = LRT_TRI_NO_HIT). Thread-safe. */
int lrt_tri_intersect1(const lrt_tri_scene *s, const lrt_ray *ray, lrt_hit *hit);

/* Any hit (shadow/occlusion). Returns 1 if anything lies in [tmin, tmax]. */
int lrt_tri_occluded1(const lrt_tri_scene *s, const lrt_ray *ray);

/* How a batch of rays relates spatially; picks the traversal strategy. */
typedef enum lrt_tri_batch_hint {
    /* Library default (currently the incoherent strategy: the coherent case
     * is fast either way, the incoherent case is the painful one). */
    LRT_TRI_BATCH_AUTO = 0,
    /* Nearby rays visiting the same nodes (e.g. primary camera rays):
     * straight per-ray traversal, which keeps the cache hot. */
    LRT_TRI_BATCH_COHERENT = 1,
    /* Unrelated rays (e.g. path-tracing bounces): several rays are kept in
     * flight per thread, one node visit each in turn, so one ray's memory
     * stall overlaps the others' compute. */
    LRT_TRI_BATCH_INCOHERENT = 2
} lrt_tri_batch_hint;

/* Batched variants: amortize per-ray setup over n rays and, for incoherent
 * batches, hide memory latency by interleaving rays. Results are identical
 * to looping the single-ray calls regardless of hint. */
void lrt_tri_intersect1N(const lrt_tri_scene *s, const lrt_ray *rays,
                         lrt_hit *hits, size_t n, lrt_tri_batch_hint hint);
void lrt_tri_occluded1N(const lrt_tri_scene *s, const lrt_ray *rays,
                        uint8_t *occluded, size_t n, lrt_tri_batch_hint hint);

typedef struct lrt_tri_stats {
    uint32_t node_count; /* wide nodes */
    uint32_t leaf_count; /* leaf references */
    uint32_t max_depth;  /* wide-tree depth */
    size_t memory_bytes; /* nodes + triangle blocks */
    float sah_cost;      /* SAH cost of the wide tree */
} lrt_tri_stats;

void lrt_tri_scene_stats(const lrt_tri_scene *s, lrt_tri_stats *out);

/* Kernel actually selected for this scene, e.g. "bvh8/avx2", "bvh4/sse4",
 * "bvh4/scalar". Useful to detect a scalar fallback caused by missing
 * compiler SIMD flags. */
const char *lrt_tri_kernel_name(const lrt_tri_scene *s);

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_C_TRI_H */
