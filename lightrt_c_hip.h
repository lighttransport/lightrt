/*
 * lightrt_c_hip.h — HIP (ROCm/AMD) GPU interop for the LightRT C11 triangle
 * kernel. Targets RDNA4 (gfx1201, wave32) but works on any HIP device.
 *
 * Mirrors the Vulkan backend (lightrt_c_vk.h) but over HIP, with two upgrades:
 *
 *   - A DEVICE-RESIDENT scene handle: upload a CPU-built BVH once
 *     (lrt_hip_scene_upload) and trace many ray batches against it
 *     (lrt_hip_scene_trace), so throughput reflects GPU traversal rather than
 *     per-call PCIe upload (the Vulkan vk-trace re-uploads every call).
 *
 *   - Low-precision / quantized trace modes for the dynamic / motion-blur path
 *     (lrt_hip_scene_trace_ex): bf16 (default), fp8 (opt-in), and int8/int4
 *     quantized leaves accelerated with RDNA4 WMMA (matrix cores). Phase 2.
 *
 * The fp32 path (the default) traverses the SAME node/leaf memory image the C
 * builder produces, bridged through the position-independent LRTS serialization
 * (lrt_tri_scene_save_to_memory), so a closest-hit matches lrt_tri_intersect1
 * within fp tolerance.
 *
 * Everything degrades gracefully: if no HIP device is available,
 * lrt_hip_engine_create() returns NULL and the caller falls back to the CPU
 * kernel. An engine is created once and may be reused; a single engine is NOT
 * safe to use from multiple threads concurrently (one stream).
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LIGHTRT_C_HIP_H
#define LIGHTRT_C_HIP_H

#include <stddef.h>
#include <stdint.h>

#include "lightrt_c.h"     /* lrt_result */
#include "lightrt_c_tri.h" /* lrt_tri_scene, lrt_ray, lrt_hit, lrt_tri_layout */

#ifdef __cplusplus
extern "C" {
#endif

typedef struct lrt_hip_engine lrt_hip_engine;
typedef struct lrt_hip_scene lrt_hip_scene;

/* Capability flags reported by lrt_hip_engine_caps(). */
typedef enum lrt_hip_caps {
    LRT_HIP_CAP_COMPUTE = 1u << 0, /* always set when an engine exists       */
    LRT_HIP_CAP_WMMA = 1u << 1,    /* gfx11/gfx12 WMMA (matrix cores) usable  */
    LRT_HIP_CAP_FP8 = 1u << 2,     /* fp8 WMMA inputs (gfx12+)                */
    LRT_HIP_CAP_INT8 = 1u << 3,    /* iu8 WMMA inputs                        */
    LRT_HIP_CAP_INT4 = 1u << 4     /* iu4 WMMA inputs                        */
} lrt_hip_caps;

typedef struct lrt_hip_engine_options {
    int device_index; /* explicit HIP device ordinal, or -1 = auto-pick      */
    uint32_t flags;   /* reserved; pass 0                                    */
} lrt_hip_engine_options;

/* Trace precision / acceleration mode (lrt_hip_scene_trace_ex). LRT_HIP_TRACE_FP32
 * is the default and matches the CPU oracle; the others trade precision for
 * throughput on the dynamic / motion-blur path and are introduced in Phase 2. */
typedef enum lrt_hip_trace_mode {
    LRT_HIP_TRACE_FP32 = 0,     /* fp32 traversal, matches lrt_tri_intersect1 */
    LRT_HIP_TRACE_WMMA_BF16,    /* bf16 WMMA leaf, no fp32 follow-up (dynamic)*/
    LRT_HIP_TRACE_WMMA_FP8,     /* fp8  WMMA leaf, experimental opt-in         */
    LRT_HIP_TRACE_WMMA_F32SEED, /* bf16 WMMA cull + fp32 follow-up (static)    */
    LRT_HIP_TRACE_INT8,         /* int8 quantized leaf + iu8 WMMA              */
    LRT_HIP_TRACE_INT4          /* int4 quantized leaf + iu4 WMMA, experimental*/
} lrt_hip_trace_mode;

/* Create an engine (hipInit + device pick). Returns NULL and, when err is
 * non-NULL, stores the reason, on any failure: no HIP runtime, no device. opts
 * may be NULL for defaults (auto device). */
lrt_hip_engine *lrt_hip_engine_create(const lrt_hip_engine_options *opts,
                                      lrt_result *err);
void lrt_hip_engine_destroy(lrt_hip_engine *e);

/* Bitmask of lrt_hip_caps for the created device. */
uint32_t lrt_hip_engine_caps(const lrt_hip_engine *e);

/* Selected device name (e.g. "AMD Radeon RX 9070 XT"). */
const char *lrt_hip_engine_device_name(const lrt_hip_engine *e);

/* Human-readable message for the last failed call on this engine. */
const char *lrt_hip_engine_last_error(const lrt_hip_engine *e);

/* --- Resident scene: upload once, trace many ------------------------------
 *
 * Upload a CPU-built scene (via its LRTS serialization) to device memory. The
 * node/block buffers stay resident until lrt_hip_scene_free(). Only plain
 * triangle scenes with BVH4/BVH8 layout are supported (quantized/curve/user
 * scenes are rejected, as by lrt_tri_scene_save_to_memory). The engine must
 * outlive the scene. Returns NULL on error (err set). */
lrt_hip_scene *lrt_hip_scene_upload(lrt_hip_engine *e, const lrt_tri_scene *s,
                                    lrt_result *err);
void lrt_hip_scene_free(lrt_hip_engine *e, lrt_hip_scene *s);

/* Closest-hit n rays against the resident scene (fp32). Writes n hits to out;
 * ray/hit device scratch is reused/grown across calls. Returns the number of
 * rays that hit, or -1 on error (err set). Results match lrt_tri_intersect1. */
int lrt_hip_scene_trace(lrt_hip_engine *e, lrt_hip_scene *s, const lrt_ray *rays,
                        uint32_t n, lrt_hit *out, lrt_result *err);

/* Any-hit (occlusion) n rays. occluded[i] = 0 or 1. Returns #occluded, or -1. */
int lrt_hip_scene_occluded(lrt_hip_engine *e, lrt_hip_scene *s,
                           const lrt_ray *rays, uint32_t n, uint8_t *occluded,
                           lrt_result *err);

/* As lrt_hip_scene_trace but selects a precision / acceleration mode. With
 * LRT_HIP_TRACE_FP32 it is identical to lrt_hip_scene_trace. Phase 2 modes fall
 * back to fp32 with LRT_RESULT_NOT_BUILT until implemented. */
int lrt_hip_scene_trace_ex(lrt_hip_engine *e, lrt_hip_scene *s,
                           lrt_hip_trace_mode mode, const lrt_ray *rays,
                           uint32_t n, lrt_hit *out, lrt_result *err);

/* --- One-shot convenience (upload + trace + free) ------------------------- */
int lrt_hip_trace_scene(lrt_hip_engine *e, const lrt_tri_scene *s,
                        const lrt_ray *rays, uint32_t n, lrt_hit *out,
                        lrt_result *err);

/* --- Phase 2: WMMA / integer-quantized leaf intersection ------------------
 *
 * The honest open question on RDNA4 is whether the matrix cores (WMMA) beat
 * scalar FMA for the leaf-intersection inner kernel. lrt_hip_leaf_bench isolates
 * exactly that: nblocks independent "leaves", each a tile of 16 coherent rays
 * vs tris_per_leaf (<=16) triangles, intersected with the chosen method, so the
 * benchmark can compare throughput AND accuracy (vs the scalar fp32 method) on
 * the same data. This is the convergent inner kernel a coherent-packet traversal
 * would call; it is measured standalone to report S-vs-W without conflating it
 * with divergent traversal.
 *
 * The ray-triangle test is the Plücker edge-side formulation: ray Plücker
 * (dir, cross(org,dir)) dotted against per-edge Plücker (moment, direction) as a
 * 16x16x16 GEMM (3 edges -> 3 mma ops/leaf), fp32-accumulated; the sign of the
 * three edge functions classifies in/out and t is recovered in fp32 for the few
 * candidates. WMMA_BF16 runs the GEMM in bf16 (dynamic / motion-blur path, no
 * fp32 re-test); WMMA_INT8 quantizes to int8 in leaf-local coords (iu8 GEMM);
 * SCALAR is the fp32 Moller-Trumbore baseline. */
typedef enum lrt_hip_isect_method {
    LRT_HIP_ISECT_SCALAR = 0,   /* fp32 Moller-Trumbore (baseline / oracle)   */
    LRT_HIP_ISECT_WMMA_BF16,    /* bf16 Plücker GEMM, fp32 t                   */
    LRT_HIP_ISECT_WMMA_FP16,    /* fp16 Plücker GEMM, fp32 t                   */
    LRT_HIP_ISECT_WMMA_FP8,     /* fp8 (e4m3) leaf-local Plücker GEMM, fp32 t  */
    LRT_HIP_ISECT_WMMA_INT8     /* int8 leaf-local Plücker GEMM, fp32 t        */
} lrt_hip_isect_method;

/* leaf_tris: nblocks*tris_per_leaf*9 floats (v0 v1 v2). rays/out: 16*nblocks
 * (rays packed per leaf). out[k].prim_id = local triangle index [0,tris_per_leaf)
 * of the closest hit in that leaf, or LRT_TRI_NO_HIT. *kernel_ms gets the device
 * kernel time (excludes H2D/D2H). Returns 0 on success, -1 on error. Returns -1
 * with LRT_RESULT_NOT_BUILT if the method needs WMMA and it is unavailable. */
int lrt_hip_leaf_bench(lrt_hip_engine *e, lrt_hip_isect_method method,
                       const float *leaf_tris, uint32_t nblocks,
                       uint32_t tris_per_leaf, const lrt_ray *rays, lrt_hit *out,
                       double *kernel_ms, lrt_result *err);

/* Batched ray transform (instancing + motion blur) — the cleanest WMMA fit.
 * out[i] transforms rays[i] by a 3x4 affine; if m1 != NULL the per-ray transform
 * is the time-lerp (1-t)*m0 + t*m1 with t = times[i] (times != NULL). method
 * selects scalar vs WMMA (bf16/fp16). m0/m1 are 12 floats row-major (3 rows of
 * [r0 r1 r2 tx]). *kernel_ms gets device kernel time. Returns 0 / -1. */
int lrt_hip_transform_bench(lrt_hip_engine *e, lrt_hip_isect_method method,
                            const lrt_ray *rays, lrt_ray *out, uint32_t n,
                            const float *m0, const float *m1, const float *times,
                            double *kernel_ms, lrt_result *err);

/* Whether WMMA leaf/transform kernels were compiled in (rocWMMA present). */
int lrt_hip_have_wmma(void);

/* --- Path B: GPU build front end -> CPU scene -----------------------------
 *
 * vertices = 9*ntris floats (v0 v1 v2 per triangle). Computes centroids and
 * 30-bit Morton codes on the GPU, finishes the LBVH on the CPU, returns a heap
 * scene traversable with the normal lrt_tri_* queries (matches a FAST CPU
 * build). layout must be BVH4 or BVH8. Free the result with
 * lrt_tri_scene_free(). Returns 0 on success, -1 on error (err set). */
int lrt_hip_build_scene(lrt_hip_engine *e, const float *vertices, uint32_t ntris,
                        lrt_tri_layout layout, lrt_tri_scene **out,
                        lrt_result *err);

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_C_HIP_H */
