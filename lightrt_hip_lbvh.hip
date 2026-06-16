/*
 * lightrt_hip_lbvh.hip — full-GPU LBVH builder for the LightRT HIP backend.
 *
 * Everything runs on the GPU (no CPU hierarchy work):
 *   1. centroids + 30-bit Morton codes (k_centroids/k_morton, shared with the
 *      hybrid path's math),
 *   2. hipCUB radix sort of unique 64-bit keys (morton<<32 | tri_index) so the
 *      Karras tree has no duplicate-key degeneracies,
 *   3. a Karras (2012) binary radix tree (k_karras): determineRange + findSplit
 *      via __clzll on the sorted keys,
 *   4. bottom-up AABBs via the standard atomic-flag walk-up (k_bounds),
 *   5. emission directly into the trace kernel's BVH4 wide-node format as a
 *      binary (2-wide) tree (k_emit_nodes / k_emit_leaves) — one triangle per
 *      leaf block — so lrt_hip_scene_trace works unchanged.
 *
 * Compiled only when hipCUB is available (LIGHTRT_HIP_HAVE_HIPCUB); otherwise
 * lrt_hip_scene_build_gpu is a NOT_BUILT stub.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <hip/hip_runtime.h>

#include <stdint.h>
#include <stdlib.h>

#include "lightrt_c_hip.h"

extern "C" void *lrt_hip_engine_stream_(const lrt_hip_engine *e);
extern "C" lrt_hip_scene *lrt_hip_scene_make_(
    uint32_t *d_nodes, uint32_t *d_blocks, uint32_t node_count,
    uint32_t block_count, uint32_t node_stride, uint32_t block_stride,
    uint32_t root, uint32_t layout, uint32_t stack, uint32_t max_depth);

static inline void hip_free_l(void *p) {
    if (p) {
        hipError_t e_ = hipFree(p);
        (void)e_;
    }
}

/* Swallow [[nodiscard]] on fire-and-forget calls (errors surface at sync). */
#define HIPV(x)                 \
    do {                        \
        hipError_t hipv_ = (x); \
        (void)hipv_;            \
    } while (0)

#ifdef LIGHTRT_HIP_HAVE_HIPCUB

#include <hipcub/hipcub.hpp>

#define LBVH_LEAF_FLAG 0x80000000u /* working-array child tag (leaf vs internal) */
#define LBVH_SENTINEL 0xFFFFFFFFu
#define TRI_LEAF_BIT 0x80000000u /* final trace leaf-ref bit */
#define TRI_NO_HIT 0xFFFFFFFFu

/* ---- centroids + Morton (same math as the hybrid build_morton path) ------- */
__global__ void kl_centroids(const float *__restrict__ verts,
                             float *__restrict__ cen, uint32_t ntris) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= ntris) return;
    uint32_t vb = i * 9u;
    for (uint32_t a = 0; a < 3u; a++) {
        float v0 = verts[vb + 0u + a], v1 = verts[vb + 3u + a],
              v2 = verts[vb + 6u + a];
        cen[i * 3u + a] = 0.5f * (fminf(v0, fminf(v1, v2)) +
                                  fmaxf(v0, fmaxf(v1, v2)));
    }
}

__device__ float atomicMinF(float *addr, float val) {
    int *a = (int *)addr;
    int old = *a, assumed;
    do {
        assumed = old;
        if (__int_as_float(assumed) <= val) break;
        old = atomicCAS(a, assumed, __float_as_int(val));
    } while (assumed != old);
    return __int_as_float(old);
}
__device__ float atomicMaxF(float *addr, float val) {
    int *a = (int *)addr;
    int old = *a, assumed;
    do {
        assumed = old;
        if (__int_as_float(assumed) >= val) break;
        old = atomicCAS(a, assumed, __float_as_int(val));
    } while (assumed != old);
    return __int_as_float(old);
}

/* Centroid AABB reduction (block-local shared reduction + one atomic/block). */
__global__ void kl_cen_aabb(const float *__restrict__ cen, uint32_t ntris,
                            float *__restrict__ out /* lo[3],hi[3] */) {
    __shared__ float slo[3], shi[3];
    if (threadIdx.x < 3) {
        slo[threadIdx.x] = 1e30f;
        shi[threadIdx.x] = -1e30f;
    }
    __syncthreads();
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < ntris) {
        for (int a = 0; a < 3; a++) {
            float v = cen[i * 3u + a];
            atomicMinF(&slo[a], v);
            atomicMaxF(&shi[a], v);
        }
    }
    __syncthreads();
    if (threadIdx.x < 3) {
        atomicMinF(&out[threadIdx.x], slo[threadIdx.x]);
        atomicMaxF(&out[3 + threadIdx.x], shi[threadIdx.x]);
    }
}

/* Initialize the 6-float AABB accumulator to +/-inf (avoids a host upload). */
__global__ void kl_init6(float *__restrict__ aabb) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        aabb[0] = aabb[1] = aabb[2] = 1e30f;
        aabb[3] = aabb[4] = aabb[5] = -1e30f;
    }
}

/* Derive Morton base/scale (1024^3 grid) from the centroid AABB, on-device. */
__global__ void kl_basescale(const float *__restrict__ aabb,
                             float *__restrict__ bs /* base[3], scale[3] */) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        for (int a = 0; a < 3; a++) {
            float ext = aabb[3 + a] - aabb[a];
            bs[a] = aabb[a];
            bs[3 + a] = ext > 0.0f ? 1024.0f / ext : 0.0f;
        }
    }
}

/* 64-bit keys = (morton30 << 32) | tri_index, guaranteeing uniqueness. */
__global__ void kl_keys(const float *__restrict__ cen, uint32_t ntris,
                        const float *__restrict__ bs,
                        uint64_t *__restrict__ keys) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= ntris) return;
    float base[3] = {bs[0], bs[1], bs[2]};
    float scale[3] = {bs[3], bs[4], bs[5]};
    uint32_t q[3];
    for (int a = 0; a < 3; a++) {
        float fv = (cen[i * 3u + a] - base[a]) * scale[a];
        int qi = (int)fv;
        qi = qi < 0 ? 0 : (qi > 1023 ? 1023 : qi);
        q[a] = (uint32_t)qi;
    }
    uint32_t m = 0;
    for (int a = 0; a < 3; a++) {
        uint32_t v = q[a] & 0x3FFu;
        v = (v | (v << 16)) & 0x030000FFu;
        v = (v | (v << 8)) & 0x0300F00Fu;
        v = (v | (v << 4)) & 0x030C30C3u;
        v = (v | (v << 2)) & 0x09249249u;
        m |= v << (2 - a);
    }
    keys[i] = ((uint64_t)m << 32) | (uint64_t)i;
}

/* ---- Karras radix tree ---------------------------------------------------- */
__device__ __forceinline__ int delta(const uint64_t *keys, int n, int i,
                                      int j) {
    if (j < 0 || j >= n) return -1;
    uint64_t x = keys[i] ^ keys[j];
    return x ? __clzll(x) : (64 + __clzll((uint64_t)((uint32_t)i ^ (uint32_t)j)));
}

__global__ void kl_karras(const uint64_t *__restrict__ keys, uint32_t n,
                          uint32_t *__restrict__ childA,
                          uint32_t *__restrict__ childB,
                          uint32_t *__restrict__ parentInt,
                          uint32_t *__restrict__ parentLeaf) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= n - 1u) return;
    int ni = (int)n;

    /* determineRange */
    int d = (delta(keys, ni, i, i + 1) - delta(keys, ni, i, i - 1)) >= 0 ? 1 : -1;
    int dmin = delta(keys, ni, i, i - d);
    int lmax = 2;
    while (delta(keys, ni, i, i + lmax * d) > dmin) lmax <<= 1;
    int l = 0;
    for (int t = lmax >> 1; t >= 1; t >>= 1)
        if (delta(keys, ni, i, i + (l + t) * d) > dmin) l += t;
    int j = i + l * d;
    int first = i < j ? i : j;
    int last = i < j ? j : i;

    /* findSplit */
    int commonPrefix = delta(keys, ni, first, last);
    int split = first;
    int step = last - first;
    do {
        step = (step + 1) >> 1;
        int newSplit = split + step;
        if (newSplit < last &&
            delta(keys, ni, first, newSplit) > commonPrefix)
            split = newSplit;
    } while (step > 1);

    uint32_t a = (first == split) ? ((uint32_t)split | LBVH_LEAF_FLAG)
                                  : (uint32_t)split;
    uint32_t b = (last == split + 1) ? ((uint32_t)(split + 1) | LBVH_LEAF_FLAG)
                                     : (uint32_t)(split + 1);
    childA[i] = a;
    childB[i] = b;
    if (a & LBVH_LEAF_FLAG)
        parentLeaf[a & ~LBVH_LEAF_FLAG] = i;
    else
        parentInt[a] = i;
    if (b & LBVH_LEAF_FLAG)
        parentLeaf[b & ~LBVH_LEAF_FLAG] = i;
    else
        parentInt[b] = i;
}

/* ---- bottom-up bounds (atomic-flag walk-up) ------------------------------- */
__device__ __forceinline__ void leaf_aabb(const float *verts, uint32_t prim,
                                          float *lo, float *hi) {
    const float *v = verts + (size_t)prim * 9u;
    for (int a = 0; a < 3; a++) {
        float v0 = v[0 + a], v1 = v[3 + a], v2 = v[6 + a];
        lo[a] = fminf(v0, fminf(v1, v2));
        hi[a] = fmaxf(v0, fmaxf(v1, v2));
    }
}

__global__ void kl_bounds(const float *__restrict__ verts,
                          const uint64_t *__restrict__ keys, uint32_t n,
                          const uint32_t *__restrict__ childA,
                          const uint32_t *__restrict__ childB,
                          const uint32_t *__restrict__ parentInt,
                          const uint32_t *__restrict__ parentLeaf,
                          float *__restrict__ leafLo, float *__restrict__ leafHi,
                          float *__restrict__ intLo, float *__restrict__ intHi,
                          uint32_t *__restrict__ flags) {
    uint32_t L = blockIdx.x * blockDim.x + threadIdx.x;
    if (L >= n) return;
    uint32_t prim = (uint32_t)(keys[L] & 0xFFFFFFFFu);
    float lo[3], hi[3];
    leaf_aabb(verts, prim, lo, hi);
    for (int a = 0; a < 3; a++) {
        leafLo[L * 3 + a] = lo[a];
        leafHi[L * 3 + a] = hi[a];
    }
    __threadfence();
    uint32_t cur = parentLeaf[L];
    while (cur != LBVH_SENTINEL) {
        if (atomicAdd(&flags[cur], 1u) == 0u) return; /* first child: stop */
        /* second child arrived: both subtrees done -> union into intLo/intHi */
        uint32_t a = childA[cur], b = childB[cur];
        const float *aLo = (a & LBVH_LEAF_FLAG)
                               ? &leafLo[(a & ~LBVH_LEAF_FLAG) * 3]
                               : &intLo[a * 3];
        const float *aHi = (a & LBVH_LEAF_FLAG)
                               ? &leafHi[(a & ~LBVH_LEAF_FLAG) * 3]
                               : &intHi[a * 3];
        const float *bLo = (b & LBVH_LEAF_FLAG)
                               ? &leafLo[(b & ~LBVH_LEAF_FLAG) * 3]
                               : &intLo[b * 3];
        const float *bHi = (b & LBVH_LEAF_FLAG)
                               ? &leafHi[(b & ~LBVH_LEAF_FLAG) * 3]
                               : &intHi[b * 3];
        for (int k = 0; k < 3; k++) {
            intLo[cur * 3 + k] = fminf(aLo[k], bLo[k]);
            intHi[cur * 3 + k] = fmaxf(aHi[k], bHi[k]);
        }
        __threadfence();
        cur = parentInt[cur];
    }
}

/* ---- emit BVH4 wide-node format (binary tree: nchildren = 2) -------------- */
__device__ __forceinline__ uint32_t child_ref(uint32_t c) {
    /* working ref -> trace ref */
    if (c & LBVH_LEAF_FLAG) {
        uint32_t L = c & ~LBVH_LEAF_FLAG;
        return TRI_LEAF_BIT | (L << 4) | 1u; /* one triangle per leaf block */
    }
    return c; /* interior node index (bit31 == 0) */
}

__global__ void kl_emit_nodes(uint32_t *__restrict__ nodes, uint32_t ninternal,
                              const uint32_t *__restrict__ childA,
                              const uint32_t *__restrict__ childB,
                              const float *__restrict__ leafLo,
                              const float *__restrict__ leafHi,
                              const float *__restrict__ intLo,
                              const float *__restrict__ intHi) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= ninternal) return;
    const uint32_t W = 4u;          /* BVH4 format */
    uint32_t nb = i * (8u * W);     /* node stride = 32 words */
    uint32_t kids[2] = {childA[i], childB[i]};
    for (int s = 0; s < 2; s++) {
        uint32_t c = kids[s];
        const float *lo = (c & LBVH_LEAF_FLAG)
                              ? &leafLo[(c & ~LBVH_LEAF_FLAG) * 3]
                              : &intLo[c * 3];
        const float *hi = (c & LBVH_LEAF_FLAG)
                              ? &leafHi[(c & ~LBVH_LEAF_FLAG) * 3]
                              : &intHi[c * 3];
        nodes[nb + 0u * W + s] = __float_as_uint(lo[0]);
        nodes[nb + 1u * W + s] = __float_as_uint(lo[1]);
        nodes[nb + 2u * W + s] = __float_as_uint(lo[2]);
        nodes[nb + 3u * W + s] = __float_as_uint(hi[0]);
        nodes[nb + 4u * W + s] = __float_as_uint(hi[1]);
        nodes[nb + 5u * W + s] = __float_as_uint(hi[2]);
        nodes[nb + 6u * W + s] = child_ref(c);
    }
    nodes[nb + 7u * W] = 2u; /* nchildren */
}

__global__ void kl_emit_leaves(uint32_t *__restrict__ blocks, uint32_t nleaves,
                               const uint64_t *__restrict__ keys,
                               const float *__restrict__ verts) {
    uint32_t L = blockIdx.x * blockDim.x + threadIdx.x;
    if (L >= nleaves) return;
    const uint32_t W = 4u;       /* BVH4 leaf block (lrt_tri4), 40 words */
    uint32_t bb = L * (10u * W);
    uint32_t prim = (uint32_t)(keys[L] & 0xFFFFFFFFu);
    const float *v = verts + (size_t)prim * 9u;
    float v0x = v[0], v0y = v[1], v0z = v[2];
    blocks[bb + 0u * W + 0] = __float_as_uint(v0x);
    blocks[bb + 1u * W + 0] = __float_as_uint(v0y);
    blocks[bb + 2u * W + 0] = __float_as_uint(v0z);
    blocks[bb + 3u * W + 0] = __float_as_uint(v[3] - v0x);
    blocks[bb + 4u * W + 0] = __float_as_uint(v[4] - v0y);
    blocks[bb + 5u * W + 0] = __float_as_uint(v[5] - v0z);
    blocks[bb + 6u * W + 0] = __float_as_uint(v[6] - v0x);
    blocks[bb + 7u * W + 0] = __float_as_uint(v[7] - v0y);
    blocks[bb + 8u * W + 0] = __float_as_uint(v[8] - v0z);
    blocks[bb + 9u * W + 0] = prim;             /* prim_id[0] */
    blocks[bb + 9u * W + 1] = TRI_NO_HIT;       /* padding lanes */
    blocks[bb + 9u * W + 2] = TRI_NO_HIT;
    blocks[bb + 9u * W + 3] = TRI_NO_HIT;
}

/* ========================================================================= */
/* Host entry.                                                               */
/* ========================================================================= */
extern "C" int lrt_hip_have_gpu_build(void) { return 1; }

#define GRID(n) dim3(((n) + 255u) / 256u), dim3(256), 0, stream

/* Core builder over a DEVICE vertex buffer (caller owns d_verts). No host
 * readback: base/scale are derived on-device (kl_init6 + kl_cen_aabb +
 * kl_basescale), so the whole build stays GPU-resident. */
static lrt_hip_scene *build_gpu_core(lrt_hip_engine *e, const float *d_verts,
                                     uint32_t ntris, lrt_result *err) {
    hipStream_t stream = (hipStream_t)lrt_hip_engine_stream_(e);
    const uint32_t node_stride_b = 128u; /* BVH4 node bytes */
    const uint32_t block_stride_b = 160u;

    /* Device scratch + outputs. */
    float *d_cen = NULL;
    uint64_t *d_keys = NULL, *d_keys2 = NULL;
    uint32_t *d_childA = NULL, *d_childB = NULL, *d_parInt = NULL,
             *d_parLeaf = NULL, *d_flags = NULL;
    float *d_leafLo = NULL, *d_leafHi = NULL, *d_intLo = NULL, *d_intHi = NULL,
          *d_aabb = NULL, *d_bs = NULL;
    uint32_t *d_nodes = NULL, *d_blocks = NULL;
    void *d_tmp = NULL;
    lrt_hip_scene *scene = NULL;
    hipError_t hr;
    uint32_t ninternal = (ntris >= 1u) ? (ntris - 1u) : 0u;

    size_t nodes_bytes = (size_t)(ninternal ? ninternal : 1u) * node_stride_b;
    size_t blocks_bytes = (size_t)ntris * block_stride_b;

#define ALLOC(p, bytes)                                          \
    if ((hr = hipMalloc((void **)&(p), (bytes))) != hipSuccess) { \
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;                \
        goto done;                                               \
    }
    ALLOC(d_cen, (size_t)ntris * 3u * sizeof(float));
    ALLOC(d_keys, (size_t)ntris * sizeof(uint64_t));
    ALLOC(d_keys2, (size_t)ntris * sizeof(uint64_t));
    ALLOC(d_aabb, 6u * sizeof(float));
    ALLOC(d_bs, 6u * sizeof(float));
    ALLOC(d_nodes, nodes_bytes);
    ALLOC(d_blocks, blocks_bytes);
    if (ninternal) {
        ALLOC(d_childA, (size_t)ninternal * sizeof(uint32_t));
        ALLOC(d_childB, (size_t)ninternal * sizeof(uint32_t));
        ALLOC(d_parInt, (size_t)ninternal * sizeof(uint32_t));
        ALLOC(d_flags, (size_t)ninternal * sizeof(uint32_t));
        ALLOC(d_intLo, (size_t)ninternal * 3u * sizeof(float));
        ALLOC(d_intHi, (size_t)ninternal * 3u * sizeof(float));
    }
    ALLOC(d_parLeaf, (size_t)ntris * sizeof(uint32_t));
    ALLOC(d_leafLo, (size_t)ntris * 3u * sizeof(float));
    ALLOC(d_leafHi, (size_t)ntris * 3u * sizeof(float));
#undef ALLOC

    /* Single-triangle scene: one leaf block (prim 0), root is a leaf ref. */
    if (ntris == 1u) {
        uint64_t k0 = 0; /* prim index 0 in the low 32 bits */
        HIPV(hipMemsetAsync(d_blocks, 0, blocks_bytes, stream));
        HIPV(hipMemcpyAsync(d_keys, &k0, sizeof(k0), hipMemcpyHostToDevice, stream));
        hipLaunchKernelGGL(kl_emit_leaves, GRID(1u), d_blocks, 1u, d_keys,
                           d_verts);
        if (hipStreamSynchronize(stream) != hipSuccess) {
            if (err) *err = LRT_RESULT_NOT_BUILT;
            goto done;
        }
        scene = lrt_hip_scene_make_(d_nodes, d_blocks, 0u, 1u, node_stride_b,
                                    block_stride_b, TRI_LEAF_BIT | (0u << 4) | 1u,
                                    4u, 32u, 1u);
        if (scene) {
            d_nodes = NULL;
            d_blocks = NULL; /* owned by scene now */
            if (err) *err = LRT_RESULT_OK;
        }
        goto done;
    }

    /* 1. centroids + centroid AABB + base/scale, all on-device (no readback). */
    hipLaunchKernelGGL(kl_centroids, GRID(ntris), d_verts, d_cen, ntris);
    hipLaunchKernelGGL(kl_init6, dim3(1), dim3(1), 0, stream, d_aabb);
    hipLaunchKernelGGL(kl_cen_aabb, GRID(ntris), d_cen, ntris, d_aabb);
    hipLaunchKernelGGL(kl_basescale, dim3(1), dim3(1), 0, stream, d_aabb, d_bs);

    /* 2. keys + radix sort. */
    hipLaunchKernelGGL(kl_keys, GRID(ntris), d_cen, ntris, d_bs, d_keys);
    {
        size_t tmp_bytes = 0;
        HIPV(hipcub::DeviceRadixSort::SortKeys(NULL, tmp_bytes, d_keys, d_keys2,
                                          (int)ntris, 0, 64, stream));
        if (hipMalloc(&d_tmp, tmp_bytes) != hipSuccess) {
            if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
            goto done;
        }
        HIPV(hipcub::DeviceRadixSort::SortKeys(d_tmp, tmp_bytes, d_keys, d_keys2,
                                          (int)ntris, 0, 64, stream));
    }
    /* sorted keys now in d_keys2; use it as the key array. */

    /* 3. Karras tree (init parents to sentinel, flags to 0). */
    HIPV(hipMemsetAsync(d_parInt, 0xFF, (size_t)ninternal * sizeof(uint32_t), stream));
    HIPV(hipMemsetAsync(d_parLeaf, 0xFF, (size_t)ntris * sizeof(uint32_t), stream));
    HIPV(hipMemsetAsync(d_flags, 0, (size_t)ninternal * sizeof(uint32_t), stream));
    hipLaunchKernelGGL(kl_karras, GRID(ninternal), d_keys2, ntris, d_childA,
                       d_childB, d_parInt, d_parLeaf);

    /* 4. bottom-up bounds. */
    hipLaunchKernelGGL(kl_bounds, GRID(ntris), d_verts, d_keys2, ntris, d_childA,
                       d_childB, d_parInt, d_parLeaf, d_leafLo, d_leafHi,
                       d_intLo, d_intHi, d_flags);

    /* 5. emit BVH4 binary tree. */
    HIPV(hipMemsetAsync(d_nodes, 0, nodes_bytes, stream));
    HIPV(hipMemsetAsync(d_blocks, 0, blocks_bytes, stream));
    hipLaunchKernelGGL(kl_emit_nodes, GRID(ninternal), d_nodes, ninternal,
                       d_childA, d_childB, d_leafLo, d_leafHi, d_intLo, d_intHi);
    hipLaunchKernelGGL(kl_emit_leaves, GRID(ntris), d_blocks, ntris, d_keys2,
                       d_verts);

    if ((hr = hipStreamSynchronize(stream)) != hipSuccess) {
        if (err) *err = LRT_RESULT_NOT_BUILT;
        goto done;
    }

    /* Karras radix tree depth is bounded by the 64-bit key length, so a 256
     * traversal stack (and 64 refit passes) always suffices. */
    scene = lrt_hip_scene_make_(d_nodes, d_blocks, ninternal, ntris,
                                node_stride_b, block_stride_b, 0u, 4u, 256u, 64u);
    if (scene) {
        d_nodes = NULL;
        d_blocks = NULL; /* ownership transferred */
        if (err) *err = LRT_RESULT_OK;
    } else if (err) {
        *err = LRT_RESULT_OUT_OF_MEMORY;
    }

done:
    hip_free_l(d_cen);
    hip_free_l(d_keys);
    hip_free_l(d_keys2);
    hip_free_l(d_aabb);
    hip_free_l(d_bs);
    hip_free_l(d_childA);
    hip_free_l(d_childB);
    hip_free_l(d_parInt);
    hip_free_l(d_parLeaf);
    hip_free_l(d_flags);
    hip_free_l(d_leafLo);
    hip_free_l(d_leafHi);
    hip_free_l(d_intLo);
    hip_free_l(d_intHi);
    hip_free_l(d_tmp);
    hip_free_l(d_nodes);
    hip_free_l(d_blocks);
    return scene;
}

/* Host-vertex entry: upload the soup once (input H2D, not a per-frame readback)
 * then build entirely on the GPU. */
extern "C" lrt_hip_scene *lrt_hip_scene_build_gpu(lrt_hip_engine *e,
                                                  const float *vertices,
                                                  uint32_t ntris,
                                                  lrt_result *err) {
    if (!e || !vertices || ntris == 0) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return NULL;
    }
    hipStream_t stream = (hipStream_t)lrt_hip_engine_stream_(e);
    size_t vbytes = (size_t)ntris * 9u * sizeof(float);
    float *d_verts = NULL;
    if (hipMalloc((void **)&d_verts, vbytes) != hipSuccess) {
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return NULL;
    }
    if (hipMemcpyAsync(d_verts, vertices, vbytes, hipMemcpyHostToDevice,
                       stream) != hipSuccess) {
        hip_free_l(d_verts);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return NULL;
    }
    lrt_hip_scene *scene = build_gpu_core(e, d_verts, ntris, err);
    hip_free_l(d_verts);
    return scene;
}

/* Device-vertex entry: vertices already resident (animated on the GPU). No H2D
 * and no D2H — the whole build is GPU-resident. */
extern "C" lrt_hip_scene *lrt_hip_scene_build_gpu_device(
    lrt_hip_engine *e, const lrt_hip_dbuffer *vertices, uint32_t ntris,
    lrt_result *err) {
    if (!e || !vertices || ntris == 0 ||
        lrt_hip_dbuffer_size(vertices) < (size_t)ntris * 9u * sizeof(float)) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return NULL;
    }
    const float *d_verts =
        (const float *)lrt_hip_dbuffer_ptr((lrt_hip_dbuffer *)vertices);
    return build_gpu_core(e, d_verts, ntris, err);
}

#else /* !LIGHTRT_HIP_HAVE_HIPCUB */

extern "C" int lrt_hip_have_gpu_build(void) { return 0; }

extern "C" lrt_hip_scene *lrt_hip_scene_build_gpu(lrt_hip_engine *e,
                                                  const float *vertices,
                                                  uint32_t ntris,
                                                  lrt_result *err) {
    (void)e;
    (void)vertices;
    (void)ntris;
    if (err) *err = LRT_RESULT_NOT_BUILT;
    return NULL;
}

extern "C" lrt_hip_scene *lrt_hip_scene_build_gpu_device(
    lrt_hip_engine *e, const lrt_hip_dbuffer *vertices, uint32_t ntris,
    lrt_result *err) {
    (void)e;
    (void)vertices;
    (void)ntris;
    if (err) *err = LRT_RESULT_NOT_BUILT;
    return NULL;
}

#endif /* LIGHTRT_HIP_HAVE_HIPCUB */
