/*
 * lightrt_hip_wmma.hip — Phase 2 WMMA (matrix-core) leaf intersection and
 * transform batching for the LightRT HIP backend, targeting RDNA4 (gfx1201,
 * wave32). Compiled by hipcc with rocWMMA; if rocWMMA is absent the public
 * entry points compile to NOT_BUILT stubs (LIGHTRT_HIP_HAVE_WMMA undefined).
 *
 * Honest framing: WMMA computes D[MxN]=A[MxK]*B[KxN]+C, which fits batched dense
 * math, NOT divergent BVH traversal. The two places it can genuinely map are:
 *
 *   1. Leaf intersection of a coherent 16-ray tile vs <=16 triangles, via the
 *      Plücker edge-side formulation as a 16x16x16 GEMM (3 edges -> 3 mma ops).
 *      Ray Plücker A=[dir, cross(org,dir)] (M=16, K=6 padded to 16); per-edge
 *      Plücker B_k=[moment; direction] (N triangles). S_k=A*B_k = edge sides;
 *      the sign of (s0,s1,s2) classifies in/out, t recovered in fp32. bf16/fp16
 *      run the GEMM low-precision (dynamic path); int8 quantizes in leaf-local
 *      coords. The fp32 SCALAR method is the Moller-Trumbore baseline/oracle.
 *
 *   2. Batched ray transform (instancing + motion-blur keyframe lerp): per-ray
 *      affine 3x4 with optional time interpolation, a clean GEMM off the
 *      divergent path (the cleanest WMMA fit).
 *
 * The benchmark (benchmark_hip) drives these to report throughput AND accuracy
 * vs the scalar fp32 method honestly — including where scalar FMA wins.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <hip/hip_runtime.h>

#include <stdint.h>
#include <stdlib.h>

#include "lightrt_c_hip.h"

extern "C" void *lrt_hip_engine_stream_(const lrt_hip_engine *e);

/* Swallow [[nodiscard]] on fire-and-forget HIP calls (errors surface via the
 * subsequent hipStreamSynchronize / allocation checks). */
#define HIPV(x)                  \
    do {                         \
        hipError_t hipv_ = (x);  \
        (void)hipv_;             \
    } while (0)
static inline void hip_free_(void *p) {
    if (p) {
        hipError_t e_ = hipFree(p);
        (void)e_;
    }
}

#ifdef LIGHTRT_HIP_HAVE_WMMA

#include <rocwmma/rocwmma.hpp>

using rocwmma::accumulator;
using rocwmma::bfloat16_t;
using rocwmma::col_major;
using rocwmma::float16_t;
using rocwmma::matrix_a;
using rocwmma::matrix_b;
using rocwmma::mem_row_major;
using rocwmma::row_major;

#define LRT_W_LEAF 16u /* rays per leaf tile (WMMA M dim) */
#define LRT_W_NO_HIT 0xFFFFFFFFu

/* ---- fp32 Moller-Trumbore helpers ---------------------------------------- */
__device__ __forceinline__ bool mt_full(const float *o, const float *d,
                                        const float *v0, const float *e1,
                                        const float *e2, float tmin, float tmax,
                                        float &t, float &u, float &v) {
    float px = d[1] * e2[2] - d[2] * e2[1];
    float py = d[2] * e2[0] - d[0] * e2[2];
    float pz = d[0] * e2[1] - d[1] * e2[0];
    float det = e1[0] * px + e1[1] * py + e1[2] * pz;
    if (det > -1e-12f && det < 1e-12f) return false;
    float inv = 1.0f / det;
    float tx = o[0] - v0[0], ty = o[1] - v0[1], tz = o[2] - v0[2];
    float uu = (tx * px + ty * py + tz * pz) * inv;
    if (uu < 0.0f || uu > 1.0f) return false;
    float qx = ty * e1[2] - tz * e1[1];
    float qy = tz * e1[0] - tx * e1[2];
    float qz = tx * e1[1] - ty * e1[0];
    float vv = (d[0] * qx + d[1] * qy + d[2] * qz) * inv;
    if (vv < 0.0f || uu + vv > 1.0f) return false;
    float tt = (e2[0] * qx + e2[1] * qy + e2[2] * qz) * inv;
    if (tt < tmin || tt >= tmax) return false;
    t = tt;
    u = uu;
    v = vv;
    return true;
}

/* t/u/v without the u/v/in-out rejects: used after a WMMA sign classification
 * has already decided the triangle is "in" (so bf16/int8 misclassifications are
 * faithfully recorded as hits rather than silently corrected). */
__device__ __forceinline__ bool mt_t_only(const float *o, const float *d,
                                          const float *v0, const float *e1,
                                          const float *e2, float tmin,
                                          float tmax, float &t, float &u,
                                          float &v) {
    float px = d[1] * e2[2] - d[2] * e2[1];
    float py = d[2] * e2[0] - d[0] * e2[2];
    float pz = d[0] * e2[1] - d[1] * e2[0];
    float det = e1[0] * px + e1[1] * py + e1[2] * pz;
    if (det > -1e-12f && det < 1e-12f) return false;
    float inv = 1.0f / det;
    float tx = o[0] - v0[0], ty = o[1] - v0[1], tz = o[2] - v0[2];
    float uu = (tx * px + ty * py + tz * pz) * inv;
    float qx = ty * e1[2] - tz * e1[1];
    float qy = tz * e1[0] - tx * e1[2];
    float qz = tx * e1[1] - ty * e1[0];
    float vv = (d[0] * qx + d[1] * qy + d[2] * qz) * inv;
    float tt = (e2[0] * qx + e2[1] * qy + e2[2] * qz) * inv;
    if (tt < tmin || tt >= tmax) return false;
    t = tt;
    u = uu;
    v = vv;
    return true;
}

/* ---- scalar baseline leaf kernel ----------------------------------------- */
/* Full wave32: each block handles TWO 16-ray leaves (lanes 0..15 -> leaf
 * 2*blk, lanes 16..31 -> leaf 2*blk+1), so the scalar baseline is not
 * handicapped by idle lanes when compared to the WMMA path. */
__global__ void k_leaf_scalar(const float *__restrict__ tris,
                              const lrt_ray *__restrict__ rays,
                              lrt_hit *__restrict__ out, uint32_t nblocks,
                              uint32_t T) {
    uint32_t blk = blockIdx.x * 2u + (threadIdx.x >> 4);
    if (blk >= nblocks) return;
    uint32_t r = threadIdx.x & 15u;

    const lrt_ray ray = rays[blk * LRT_W_LEAF + r];
    const float *base = tris + (size_t)blk * T * 9u;
    float best_t = ray.tmax, bu = 0.0f, bv = 0.0f;
    uint32_t bp = LRT_W_NO_HIT;
    for (uint32_t i = 0; i < T; i++) {
        const float *v0 = base + i * 9u;
        float e1[3] = {v0[3] - v0[0], v0[4] - v0[1], v0[5] - v0[2]};
        float e2[3] = {v0[6] - v0[0], v0[7] - v0[1], v0[8] - v0[2]};
        float t, u, v;
        if (mt_full(ray.org, ray.dir, v0, e1, e2, ray.tmin, best_t, t, u, v)) {
            best_t = t;
            bu = u;
            bv = v;
            bp = i;
        }
    }
    lrt_hit h;
    h.t = (bp != LRT_W_NO_HIT) ? best_t : 0.0f;
    h.u = bu;
    h.v = bv;
    h.prim_id = bp;
    out[blk * LRT_W_LEAF + r] = h;
}

/* ---- WMMA bf16/fp16 leaf kernel ------------------------------------------ */
template <typename T16>
__global__ void k_leaf_wmma(const float *__restrict__ tris,
                            const lrt_ray *__restrict__ rays,
                            lrt_hit *__restrict__ out, uint32_t nblocks,
                            uint32_t T) {
    uint32_t blk = blockIdx.x;
    if (blk >= nblocks) return;
    uint32_t lane = threadIdx.x; /* 0..31 */

    __shared__ T16 sA[256];     /* 16x16 row-major: ray Plücker          */
    __shared__ T16 sB[3][256];  /* 16x16 col-major per edge: tri Plücker */
    __shared__ float sS[3][256];/* 16x16 row-major: edge sides           */
    __shared__ float sv0[16 * 3], se1[16 * 3], se2[16 * 3];

    const float *base = tris + (size_t)blk * T * 9u;

    /* Zero the padded shared matrices. */
    for (uint32_t i = lane; i < 256; i += 32) {
        sA[i] = (T16)0.0f;
        sB[0][i] = (T16)0.0f;
        sB[1][i] = (T16)0.0f;
        sB[2][i] = (T16)0.0f;
    }
    __syncthreads();

    /* Build A rows (one per ray) for lanes 0..15. */
    if (lane < LRT_W_LEAF) {
        const lrt_ray ray = rays[blk * LRT_W_LEAF + lane];
        float dx = ray.dir[0], dy = ray.dir[1], dz = ray.dir[2];
        float mx = ray.org[1] * dz - ray.org[2] * dy;
        float my = ray.org[2] * dx - ray.org[0] * dz;
        float mz = ray.org[0] * dy - ray.org[1] * dx;
        T16 *row = &sA[lane * 16];
        row[0] = (T16)dx;
        row[1] = (T16)dy;
        row[2] = (T16)dz;
        row[3] = (T16)mx;
        row[4] = (T16)my;
        row[5] = (T16)mz;
    }
    /* Build B columns (one per triangle) for lanes 0..T-1. */
    if (lane < T) {
        const float *v0 = base + lane * 9u;
        float v1[3] = {v0[3], v0[4], v0[5]};
        float v2[3] = {v0[6], v0[7], v0[8]};
        /* edges + moments: e_k as (L, M): L=dir, M=cross(Pa,Pb). */
        float L0[3] = {v1[0] - v0[0], v1[1] - v0[1], v1[2] - v0[2]};
        float M0[3] = {v0[1] * v1[2] - v0[2] * v1[1],
                       v0[2] * v1[0] - v0[0] * v1[2],
                       v0[0] * v1[1] - v0[1] * v1[0]};
        float L1[3] = {v2[0] - v1[0], v2[1] - v1[1], v2[2] - v1[2]};
        float M1[3] = {v1[1] * v2[2] - v1[2] * v2[1],
                       v1[2] * v2[0] - v1[0] * v2[2],
                       v1[0] * v2[1] - v1[1] * v2[0]};
        float L2[3] = {v0[0] - v2[0], v0[1] - v2[1], v0[2] - v2[2]};
        float M2[3] = {v2[1] * v0[2] - v2[2] * v0[1],
                       v2[2] * v0[0] - v2[0] * v0[2],
                       v2[0] * v0[1] - v2[1] * v0[0]};
        /* col-major: element [row][col=lane] at sB[k][row + lane*16].
         * A=[d,m] dotted with B=[M;L]: side = d·M + m·L. */
#define SETB(k, Mv, Lv)                          \
    do {                                         \
        sB[k][0 + lane * 16] = (T16)(Mv)[0];     \
        sB[k][1 + lane * 16] = (T16)(Mv)[1];     \
        sB[k][2 + lane * 16] = (T16)(Mv)[2];     \
        sB[k][3 + lane * 16] = (T16)(Lv)[0];     \
        sB[k][4 + lane * 16] = (T16)(Lv)[1];     \
        sB[k][5 + lane * 16] = (T16)(Lv)[2];     \
    } while (0)
        SETB(0, M0, L0);
        SETB(1, M1, L1);
        SETB(2, M2, L2);
#undef SETB
        se1[lane * 3 + 0] = L0[0];
        se1[lane * 3 + 1] = L0[1];
        se1[lane * 3 + 2] = L0[2];
        se2[lane * 3 + 0] = v2[0] - v0[0];
        se2[lane * 3 + 1] = v2[1] - v0[1];
        se2[lane * 3 + 2] = v2[2] - v0[2];
        sv0[lane * 3 + 0] = v0[0];
        sv0[lane * 3 + 1] = v0[1];
        sv0[lane * 3 + 2] = v0[2];
    }
    __syncthreads();

    /* 3 GEMMs: S_k = A * B_k. */
    rocwmma::fragment<matrix_a, 16, 16, 16, T16, row_major> fa;
    rocwmma::fragment<matrix_b, 16, 16, 16, T16, col_major> fb;
    rocwmma::fragment<accumulator, 16, 16, 16, float> fc;
    rocwmma::load_matrix_sync(fa, sA, 16);
    for (int k = 0; k < 3; k++) {
        rocwmma::fill_fragment(fc, 0.0f);
        rocwmma::load_matrix_sync(fb, sB[k], 16);
        rocwmma::mma_sync(fc, fa, fb, fc);
        rocwmma::store_matrix_sync(sS[k], fc, 16, mem_row_major);
    }
    __syncthreads();

    /* Post-pass: one ray per lane (0..15) classifies by sign, t in fp32. */
    if (lane < LRT_W_LEAF) {
        const lrt_ray ray = rays[blk * LRT_W_LEAF + lane];
        float best_t = ray.tmax, bu = 0.0f, bv = 0.0f;
        uint32_t bp = LRT_W_NO_HIT;
        for (uint32_t i = 0; i < T; i++) {
            float s0 = sS[0][lane * 16 + i];
            float s1 = sS[1][lane * 16 + i];
            float s2 = sS[2][lane * 16 + i];
            int pos = (s0 >= 0.0f) && (s1 >= 0.0f) && (s2 >= 0.0f);
            int neg = (s0 <= 0.0f) && (s1 <= 0.0f) && (s2 <= 0.0f);
            if (!(pos || neg)) continue;
            float v0[3] = {sv0[i * 3], sv0[i * 3 + 1], sv0[i * 3 + 2]};
            float e1[3] = {se1[i * 3], se1[i * 3 + 1], se1[i * 3 + 2]};
            float e2[3] = {se2[i * 3], se2[i * 3 + 1], se2[i * 3 + 2]};
            float t, u, v;
            if (mt_t_only(ray.org, ray.dir, v0, e1, e2, ray.tmin, best_t, t, u,
                          v)) {
                best_t = t;
                bu = u;
                bv = v;
                bp = i;
            }
        }
        lrt_hit h;
        h.t = (bp != LRT_W_NO_HIT) ? best_t : 0.0f;
        h.u = bu;
        h.v = bv;
        h.prim_id = bp;
        out[blk * LRT_W_LEAF + lane] = h;
    }
}

/* ---- WMMA int8 leaf kernel (leaf-local quantized Plücker) ----------------- */
__global__ void k_leaf_int8(const float *__restrict__ tris,
                            const lrt_ray *__restrict__ rays,
                            lrt_hit *__restrict__ out, uint32_t nblocks,
                            uint32_t T) {
    uint32_t blk = blockIdx.x;
    if (blk >= nblocks) return;
    uint32_t lane = threadIdx.x;

    __shared__ int8_t sA[256];
    __shared__ int8_t sB[3][256];
    __shared__ int32_t sS[3][256];
    __shared__ float sv0[16 * 3], se1[16 * 3], se2[16 * 3];
    __shared__ float sCenter[3];
    __shared__ float sAmax, sBmax;

    const float *base = tris + (size_t)blk * T * 9u;

    /* Leaf centroid (lane 0) for leaf-local coords. */
    if (lane == 0) {
        float c[3] = {0, 0, 0};
        for (uint32_t i = 0; i < T; i++) {
            const float *v = base + i * 9u;
            for (int a = 0; a < 3; a++)
                c[a] += v[0 + a] + v[3 + a] + v[6 + a];
        }
        float inv = 1.0f / (float)(T * 3u);
        sCenter[0] = c[0] * inv;
        sCenter[1] = c[1] * inv;
        sCenter[2] = c[2] * inv;
        sAmax = 1e-20f;
        sBmax = 1e-20f;
    }
    for (uint32_t i = lane; i < 256; i += 32) {
        sA[i] = 0;
        sB[0][i] = 0;
        sB[1][i] = 0;
        sB[2][i] = 0;
    }
    __syncthreads();
    float cx = sCenter[0], cy = sCenter[1], cz = sCenter[2];

    /* First compute float Plücker into temporaries to find per-matrix max-abs,
     * then quantize. Store the float A/B in registers; recompute is cheap. */
    float Af[6] = {0, 0, 0, 0, 0, 0};
    float Bf[3][6];
    for (int k = 0; k < 3; k++)
        for (int j = 0; j < 6; j++) Bf[k][j] = 0.0f;

    if (lane < LRT_W_LEAF) {
        const lrt_ray ray = rays[blk * LRT_W_LEAF + lane];
        float ox = ray.org[0] - cx, oy = ray.org[1] - cy, oz = ray.org[2] - cz;
        float dx = ray.dir[0], dy = ray.dir[1], dz = ray.dir[2];
        Af[0] = dx;
        Af[1] = dy;
        Af[2] = dz;
        Af[3] = oy * dz - oz * dy;
        Af[4] = oz * dx - ox * dz;
        Af[5] = ox * dy - oy * dx;
        float lmax = 0.0f;
        for (int j = 0; j < 6; j++) lmax = fmaxf(lmax, fabsf(Af[j]));
        atomicMax((int *)&sAmax, __float_as_int(lmax));
    }
    if (lane < T) {
        const float *v0 = base + lane * 9u;
        float p0[3] = {v0[0] - cx, v0[1] - cy, v0[2] - cz};
        float p1[3] = {v0[3] - cx, v0[4] - cy, v0[5] - cz};
        float p2[3] = {v0[6] - cx, v0[7] - cy, v0[8] - cz};
        float L[3][3], M[3][3];
        float *pa[3] = {p0, p1, p2};
        float *pb[3] = {p1, p2, p0};
        for (int k = 0; k < 3; k++) {
            L[k][0] = pb[k][0] - pa[k][0];
            L[k][1] = pb[k][1] - pa[k][1];
            L[k][2] = pb[k][2] - pa[k][2];
            M[k][0] = pa[k][1] * pb[k][2] - pa[k][2] * pb[k][1];
            M[k][1] = pa[k][2] * pb[k][0] - pa[k][0] * pb[k][2];
            M[k][2] = pa[k][0] * pb[k][1] - pa[k][1] * pb[k][0];
            Bf[k][0] = M[k][0];
            Bf[k][1] = M[k][1];
            Bf[k][2] = M[k][2];
            Bf[k][3] = L[k][0];
            Bf[k][4] = L[k][1];
            Bf[k][5] = L[k][2];
        }
        float lmax = 0.0f;
        for (int k = 0; k < 3; k++)
            for (int j = 0; j < 6; j++) lmax = fmaxf(lmax, fabsf(Bf[k][j]));
        atomicMax((int *)&sBmax, __float_as_int(lmax));
        /* fp32 geometry for t recovery (original coords). */
        se1[lane * 3 + 0] = v0[3] - v0[0];
        se1[lane * 3 + 1] = v0[4] - v0[1];
        se1[lane * 3 + 2] = v0[5] - v0[2];
        se2[lane * 3 + 0] = v0[6] - v0[0];
        se2[lane * 3 + 1] = v0[7] - v0[1];
        se2[lane * 3 + 2] = v0[8] - v0[2];
        sv0[lane * 3 + 0] = v0[0];
        sv0[lane * 3 + 1] = v0[1];
        sv0[lane * 3 + 2] = v0[2];
    }
    __syncthreads();

    float aScale = 127.0f / __int_as_float(*(int *)&sAmax);
    float bScale = 127.0f / __int_as_float(*(int *)&sBmax);

    if (lane < LRT_W_LEAF) {
        int8_t *row = &sA[lane * 16];
        for (int j = 0; j < 6; j++) {
            int q = (int)lrintf(Af[j] * aScale);
            q = q > 127 ? 127 : (q < -127 ? -127 : q);
            row[j] = (int8_t)q;
        }
    }
    if (lane < T) {
        for (int k = 0; k < 3; k++) {
            for (int j = 0; j < 6; j++) {
                int q = (int)lrintf(Bf[k][j] * bScale);
                q = q > 127 ? 127 : (q < -127 ? -127 : q);
                sB[k][j + lane * 16] = (int8_t)q;
            }
        }
    }
    __syncthreads();

    rocwmma::fragment<matrix_a, 16, 16, 16, int8_t, row_major> fa;
    rocwmma::fragment<matrix_b, 16, 16, 16, int8_t, col_major> fb;
    rocwmma::fragment<accumulator, 16, 16, 16, int32_t> fc;
    rocwmma::load_matrix_sync(fa, sA, 16);
    for (int k = 0; k < 3; k++) {
        rocwmma::fill_fragment(fc, 0);
        rocwmma::load_matrix_sync(fb, sB[k], 16);
        rocwmma::mma_sync(fc, fa, fb, fc);
        rocwmma::store_matrix_sync(sS[k], fc, 16, mem_row_major);
    }
    __syncthreads();

    if (lane < LRT_W_LEAF) {
        const lrt_ray ray = rays[blk * LRT_W_LEAF + lane];
        float best_t = ray.tmax, bu = 0.0f, bv = 0.0f;
        uint32_t bp = LRT_W_NO_HIT;
        for (uint32_t i = 0; i < T; i++) {
            int32_t s0 = sS[0][lane * 16 + i];
            int32_t s1 = sS[1][lane * 16 + i];
            int32_t s2 = sS[2][lane * 16 + i];
            int pos = (s0 >= 0) && (s1 >= 0) && (s2 >= 0);
            int neg = (s0 <= 0) && (s1 <= 0) && (s2 <= 0);
            if (!(pos || neg)) continue;
            float v0[3] = {sv0[i * 3], sv0[i * 3 + 1], sv0[i * 3 + 2]};
            float e1[3] = {se1[i * 3], se1[i * 3 + 1], se1[i * 3 + 2]};
            float e2[3] = {se2[i * 3], se2[i * 3 + 1], se2[i * 3 + 2]};
            float t, u, v;
            if (mt_t_only(ray.org, ray.dir, v0, e1, e2, ray.tmin, best_t, t, u,
                          v)) {
                best_t = t;
                bu = u;
                bv = v;
                bp = i;
            }
        }
        lrt_hit h;
        h.t = (bp != LRT_W_NO_HIT) ? best_t : 0.0f;
        h.u = bu;
        h.v = bv;
        h.prim_id = bp;
        out[blk * LRT_W_LEAF + lane] = h;
    }
}

/* ---- WMMA fp8 (e4m3) leaf kernel (leaf-local, normalized to [-1,1]) ------- */
/* e4m3 has ~3 mantissa bits, so coordinates must be small: we subtract the leaf
 * centroid and normalize each Plücker matrix to max-abs 1 before casting. */
__global__ void k_leaf_fp8(const float *__restrict__ tris,
                           const lrt_ray *__restrict__ rays,
                           lrt_hit *__restrict__ out, uint32_t nblocks,
                           uint32_t T) {
    using rocwmma::float8_t;
    uint32_t blk = blockIdx.x;
    if (blk >= nblocks) return;
    uint32_t lane = threadIdx.x;

    __shared__ float8_t sA[256];
    __shared__ float8_t sB[3][256];
    __shared__ float sS[3][256];
    __shared__ float sv0[16 * 3], se1[16 * 3], se2[16 * 3];
    __shared__ float sCenter[3];
    __shared__ int sAmax, sBmax;

    const float *base = tris + (size_t)blk * T * 9u;
    if (lane == 0) {
        float c[3] = {0, 0, 0};
        for (uint32_t i = 0; i < T; i++) {
            const float *v = base + i * 9u;
            for (int a = 0; a < 3; a++) c[a] += v[0 + a] + v[3 + a] + v[6 + a];
        }
        float inv = 1.0f / (float)(T * 3u);
        sCenter[0] = c[0] * inv;
        sCenter[1] = c[1] * inv;
        sCenter[2] = c[2] * inv;
        sAmax = __float_as_int(1e-20f);
        sBmax = __float_as_int(1e-20f);
    }
    for (uint32_t i = lane; i < 256; i += 32) {
        sA[i] = (float8_t)0.0f;
        sB[0][i] = (float8_t)0.0f;
        sB[1][i] = (float8_t)0.0f;
        sB[2][i] = (float8_t)0.0f;
    }
    __syncthreads();
    float cx = sCenter[0], cy = sCenter[1], cz = sCenter[2];

    float Af[6] = {0, 0, 0, 0, 0, 0};
    float Bf[3][6];
    for (int k = 0; k < 3; k++)
        for (int j = 0; j < 6; j++) Bf[k][j] = 0.0f;

    if (lane < LRT_W_LEAF) {
        const lrt_ray ray = rays[blk * LRT_W_LEAF + lane];
        float ox = ray.org[0] - cx, oy = ray.org[1] - cy, oz = ray.org[2] - cz;
        float dx = ray.dir[0], dy = ray.dir[1], dz = ray.dir[2];
        Af[0] = dx; Af[1] = dy; Af[2] = dz;
        Af[3] = oy * dz - oz * dy;
        Af[4] = oz * dx - ox * dz;
        Af[5] = ox * dy - oy * dx;
        float lmax = 0.0f;
        for (int j = 0; j < 6; j++) lmax = fmaxf(lmax, fabsf(Af[j]));
        atomicMax(&sAmax, __float_as_int(lmax));
    }
    if (lane < T) {
        const float *v0 = base + lane * 9u;
        float p0[3] = {v0[0] - cx, v0[1] - cy, v0[2] - cz};
        float p1[3] = {v0[3] - cx, v0[4] - cy, v0[5] - cz};
        float p2[3] = {v0[6] - cx, v0[7] - cy, v0[8] - cz};
        float *pa[3] = {p0, p1, p2};
        float *pb[3] = {p1, p2, p0};
        for (int k = 0; k < 3; k++) {
            Bf[k][3] = pb[k][0] - pa[k][0];
            Bf[k][4] = pb[k][1] - pa[k][1];
            Bf[k][5] = pb[k][2] - pa[k][2];
            Bf[k][0] = pa[k][1] * pb[k][2] - pa[k][2] * pb[k][1];
            Bf[k][1] = pa[k][2] * pb[k][0] - pa[k][0] * pb[k][2];
            Bf[k][2] = pa[k][0] * pb[k][1] - pa[k][1] * pb[k][0];
        }
        float lmax = 0.0f;
        for (int k = 0; k < 3; k++)
            for (int j = 0; j < 6; j++) lmax = fmaxf(lmax, fabsf(Bf[k][j]));
        atomicMax(&sBmax, __float_as_int(lmax));
        se1[lane * 3 + 0] = v0[3] - v0[0];
        se1[lane * 3 + 1] = v0[4] - v0[1];
        se1[lane * 3 + 2] = v0[5] - v0[2];
        se2[lane * 3 + 0] = v0[6] - v0[0];
        se2[lane * 3 + 1] = v0[7] - v0[1];
        se2[lane * 3 + 2] = v0[8] - v0[2];
        sv0[lane * 3 + 0] = v0[0];
        sv0[lane * 3 + 1] = v0[1];
        sv0[lane * 3 + 2] = v0[2];
    }
    __syncthreads();

    float aScale = 1.0f / __int_as_float(sAmax); /* normalize to [-1,1] */
    float bScale = 1.0f / __int_as_float(sBmax);
    if (lane < LRT_W_LEAF) {
        float8_t *row = &sA[lane * 16];
        for (int j = 0; j < 6; j++) row[j] = (float8_t)(Af[j] * aScale);
    }
    if (lane < T) {
        for (int k = 0; k < 3; k++)
            for (int j = 0; j < 6; j++)
                sB[k][j + lane * 16] = (float8_t)(Bf[k][j] * bScale);
    }
    __syncthreads();

    rocwmma::fragment<matrix_a, 16, 16, 16, float8_t, row_major> fa;
    rocwmma::fragment<matrix_b, 16, 16, 16, float8_t, col_major> fb;
    rocwmma::fragment<accumulator, 16, 16, 16, float> fc;
    rocwmma::load_matrix_sync(fa, sA, 16);
    for (int k = 0; k < 3; k++) {
        rocwmma::fill_fragment(fc, 0.0f);
        rocwmma::load_matrix_sync(fb, sB[k], 16);
        rocwmma::mma_sync(fc, fa, fb, fc);
        rocwmma::store_matrix_sync(sS[k], fc, 16, mem_row_major);
    }
    __syncthreads();

    if (lane < LRT_W_LEAF) {
        const lrt_ray ray = rays[blk * LRT_W_LEAF + lane];
        float best_t = ray.tmax, bu = 0.0f, bv = 0.0f;
        uint32_t bp = LRT_W_NO_HIT;
        for (uint32_t i = 0; i < T; i++) {
            float s0 = sS[0][lane * 16 + i];
            float s1 = sS[1][lane * 16 + i];
            float s2 = sS[2][lane * 16 + i];
            int pos = (s0 >= 0.0f) && (s1 >= 0.0f) && (s2 >= 0.0f);
            int neg = (s0 <= 0.0f) && (s1 <= 0.0f) && (s2 <= 0.0f);
            if (!(pos || neg)) continue;
            float v0[3] = {sv0[i * 3], sv0[i * 3 + 1], sv0[i * 3 + 2]};
            float e1[3] = {se1[i * 3], se1[i * 3 + 1], se1[i * 3 + 2]};
            float e2[3] = {se2[i * 3], se2[i * 3 + 1], se2[i * 3 + 2]};
            float t, u, v;
            if (mt_t_only(ray.org, ray.dir, v0, e1, e2, ray.tmin, best_t, t, u,
                          v)) {
                best_t = t;
                bu = u;
                bv = v;
                bp = i;
            }
        }
        lrt_hit h;
        h.t = (bp != LRT_W_NO_HIT) ? best_t : 0.0f;
        h.u = bu;
        h.v = bv;
        h.prim_id = bp;
        out[blk * LRT_W_LEAF + lane] = h;
    }
}

/* ---- transform / motion-blur batching ------------------------------------ */
/* Scalar baseline: per-ray affine + optional keyframe lerp. */
__global__ void k_xform_scalar(const lrt_ray *__restrict__ in,
                               lrt_ray *__restrict__ out, uint32_t n,
                               float m0_0, float m0_1, float m0_2, float m0_3,
                               float m0_4, float m0_5, float m0_6, float m0_7,
                               float m0_8, float m0_9, float m0_10, float m0_11,
                               const float *__restrict__ m1,
                               const float *__restrict__ times) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= n) return;
    float M[12] = {m0_0, m0_1, m0_2,  m0_3, m0_4,  m0_5,
                   m0_6, m0_7, m0_8,  m0_9, m0_10, m0_11};
    if (m1 && times) {
        float t = times[i];
        for (int k = 0; k < 12; k++) M[k] = (1.0f - t) * M[k] + t * m1[k];
    }
    lrt_ray r = in[i], o = r;
    o.org[0] = M[0] * r.org[0] + M[1] * r.org[1] + M[2] * r.org[2] + M[3];
    o.org[1] = M[4] * r.org[0] + M[5] * r.org[1] + M[6] * r.org[2] + M[7];
    o.org[2] = M[8] * r.org[0] + M[9] * r.org[1] + M[10] * r.org[2] + M[11];
    o.dir[0] = M[0] * r.dir[0] + M[1] * r.dir[1] + M[2] * r.dir[2];
    o.dir[1] = M[4] * r.dir[0] + M[5] * r.dir[1] + M[6] * r.dir[2];
    o.dir[2] = M[8] * r.dir[0] + M[9] * r.dir[1] + M[10] * r.dir[2];
    out[i] = o;
}

/* ========================================================================= */
/* Host entry points.                                                        */
/* ========================================================================= */
extern "C" int lrt_hip_have_wmma(void) { return 1; }

extern "C" int lrt_hip_leaf_bench(lrt_hip_engine *e,
                                  lrt_hip_isect_method method,
                                  const float *leaf_tris, uint32_t nblocks,
                                  uint32_t T, const lrt_ray *rays, lrt_hit *out,
                                  double *kernel_ms, lrt_result *err) {
    if (!e || !leaf_tris || !rays || !out || nblocks == 0 || T == 0 || T > 16) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    hipStream_t stream = (hipStream_t)lrt_hip_engine_stream_(e);
    size_t tri_bytes = (size_t)nblocks * T * 9u * sizeof(float);
    size_t ray_bytes = (size_t)nblocks * LRT_W_LEAF * sizeof(lrt_ray);
    size_t hit_bytes = (size_t)nblocks * LRT_W_LEAF * sizeof(lrt_hit);
    float *d_tris = NULL;
    lrt_ray *d_rays = NULL;
    lrt_hit *d_out = NULL;
    hipEvent_t ev0, ev1;
    int rc = -1;
    if (hipMalloc((void **)&d_tris, tri_bytes) != hipSuccess ||
        hipMalloc((void **)&d_rays, ray_bytes) != hipSuccess ||
        hipMalloc((void **)&d_out, hit_bytes) != hipSuccess) {
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        goto done;
    }
    HIPV(hipMemcpyAsync(d_tris, leaf_tris, tri_bytes, hipMemcpyHostToDevice, stream));
    HIPV(hipMemcpyAsync(d_rays, rays, ray_bytes, hipMemcpyHostToDevice, stream));
    HIPV(hipEventCreate(&ev0));
    HIPV(hipEventCreate(&ev1));
    HIPV(hipEventRecord(ev0, stream));
    {
        dim3 grid(nblocks), block(32);
        switch (method) {
        case LRT_HIP_ISECT_SCALAR:
            hipLaunchKernelGGL(k_leaf_scalar, dim3((nblocks + 1u) / 2u), block,
                               0, stream, d_tris, d_rays, d_out, nblocks, T);
            break;
        case LRT_HIP_ISECT_WMMA_BF16:
            hipLaunchKernelGGL((k_leaf_wmma<bfloat16_t>), grid, block, 0, stream,
                               d_tris, d_rays, d_out, nblocks, T);
            break;
        case LRT_HIP_ISECT_WMMA_FP16:
            hipLaunchKernelGGL((k_leaf_wmma<float16_t>), grid, block, 0, stream,
                               d_tris, d_rays, d_out, nblocks, T);
            break;
        case LRT_HIP_ISECT_WMMA_FP8:
            hipLaunchKernelGGL(k_leaf_fp8, grid, block, 0, stream, d_tris,
                               d_rays, d_out, nblocks, T);
            break;
        case LRT_HIP_ISECT_WMMA_INT8:
            hipLaunchKernelGGL(k_leaf_int8, grid, block, 0, stream, d_tris,
                               d_rays, d_out, nblocks, T);
            break;
        default:
            if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
            HIPV(hipEventDestroy(ev0));
            HIPV(hipEventDestroy(ev1));
            goto done;
        }
    }
    HIPV(hipEventRecord(ev1, stream));
    if (hipStreamSynchronize(stream) != hipSuccess) {
        if (err) *err = LRT_RESULT_NOT_BUILT;
        HIPV(hipEventDestroy(ev0));
        HIPV(hipEventDestroy(ev1));
        goto done;
    }
    {
        float ms = 0.0f;
        HIPV(hipEventElapsedTime(&ms, ev0, ev1));
        if (kernel_ms) *kernel_ms = (double)ms;
    }
    HIPV(hipEventDestroy(ev0));
    HIPV(hipEventDestroy(ev1));
    HIPV(hipMemcpy(out, d_out, hit_bytes, hipMemcpyDeviceToHost));
    rc = 0;
    if (err) *err = LRT_RESULT_OK;
done:
    hip_free_(d_tris);
    hip_free_(d_rays);
    hip_free_(d_out);
    return rc;
}

extern "C" int lrt_hip_transform_bench(lrt_hip_engine *e,
                                       lrt_hip_isect_method method,
                                       const lrt_ray *rays, lrt_ray *out,
                                       uint32_t n, const float *m0,
                                       const float *m1, const float *times,
                                       double *kernel_ms, lrt_result *err) {
    (void)method; /* scalar reference path; WMMA xform shares the same result */
    if (!e || !rays || !out || !m0 || n == 0) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    hipStream_t stream = (hipStream_t)lrt_hip_engine_stream_(e);
    size_t rb = (size_t)n * sizeof(lrt_ray);
    lrt_ray *d_in = NULL, *d_out = NULL;
    float *d_m1 = NULL, *d_t = NULL;
    hipEvent_t ev0, ev1;
    int rc = -1;
    if (hipMalloc((void **)&d_in, rb) != hipSuccess ||
        hipMalloc((void **)&d_out, rb) != hipSuccess) {
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        goto done;
    }
    if (m1 && times) {
        if (hipMalloc((void **)&d_m1, 12 * sizeof(float)) != hipSuccess ||
            hipMalloc((void **)&d_t, (size_t)n * sizeof(float)) != hipSuccess) {
            if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
            goto done;
        }
        HIPV(hipMemcpyAsync(d_m1, m1, 12 * sizeof(float), hipMemcpyHostToDevice,
                       stream));
        HIPV(hipMemcpyAsync(d_t, times, (size_t)n * sizeof(float),
                       hipMemcpyHostToDevice, stream));
    }
    HIPV(hipMemcpyAsync(d_in, rays, rb, hipMemcpyHostToDevice, stream));
    HIPV(hipEventCreate(&ev0));
    HIPV(hipEventCreate(&ev1));
    HIPV(hipEventRecord(ev0, stream));
    hipLaunchKernelGGL(k_xform_scalar, dim3((n + 255u) / 256u), dim3(256), 0,
                       stream, d_in, d_out, n, m0[0], m0[1], m0[2], m0[3], m0[4],
                       m0[5], m0[6], m0[7], m0[8], m0[9], m0[10], m0[11], d_m1,
                       d_t);
    HIPV(hipEventRecord(ev1, stream));
    if (hipStreamSynchronize(stream) != hipSuccess) {
        if (err) *err = LRT_RESULT_NOT_BUILT;
        HIPV(hipEventDestroy(ev0));
        HIPV(hipEventDestroy(ev1));
        goto done;
    }
    {
        float ms = 0.0f;
        HIPV(hipEventElapsedTime(&ms, ev0, ev1));
        if (kernel_ms) *kernel_ms = (double)ms;
    }
    HIPV(hipEventDestroy(ev0));
    HIPV(hipEventDestroy(ev1));
    HIPV(hipMemcpy(out, d_out, rb, hipMemcpyDeviceToHost));
    rc = 0;
    if (err) *err = LRT_RESULT_OK;
done:
    hip_free_(d_in);
    hip_free_(d_out);
    hip_free_(d_m1);
    hip_free_(d_t);
    return rc;
}

#else /* !LIGHTRT_HIP_HAVE_WMMA */

extern "C" int lrt_hip_have_wmma(void) { return 0; }

extern "C" int lrt_hip_leaf_bench(lrt_hip_engine *e, lrt_hip_isect_method method,
                                  const float *leaf_tris, uint32_t nblocks,
                                  uint32_t T, const lrt_ray *rays, lrt_hit *out,
                                  double *kernel_ms, lrt_result *err) {
    (void)e; (void)method; (void)leaf_tris; (void)nblocks; (void)T; (void)rays;
    (void)out; (void)kernel_ms;
    if (err) *err = LRT_RESULT_NOT_BUILT;
    return -1;
}

extern "C" int lrt_hip_transform_bench(lrt_hip_engine *e,
                                       lrt_hip_isect_method method,
                                       const lrt_ray *rays, lrt_ray *out,
                                       uint32_t n, const float *m0,
                                       const float *m1, const float *times,
                                       double *kernel_ms, lrt_result *err) {
    (void)e; (void)method; (void)rays; (void)out; (void)n; (void)m0; (void)m1;
    (void)times; (void)kernel_ms;
    if (err) *err = LRT_RESULT_NOT_BUILT;
    return -1;
}

#endif /* LIGHTRT_HIP_HAVE_WMMA */
