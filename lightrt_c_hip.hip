/*
 * lightrt_c_hip.hip — HIP (ROCm/AMD) GPU backend for the LightRT C11 triangle
 * kernel. Compiled by hipcc as C++; all public symbols are extern "C" so the
 * pure-C library and benchmark link against them directly.
 *
 * Phase 1 (this file): fp32 device-resident trace (closest-hit + occlusion) and
 * a hybrid GPU-Morton LBVH build, ported byte-for-byte from the Vulkan compute
 * path (vk/shaders/trace_bvh.comp, build_morton.comp). The trace kernel reads
 * the SAME node/leaf memory image the CPU builder produces (uploaded verbatim
 * from the LRTS serialization), so hits match lrt_tri_intersect1.
 *
 * Phase 2 hooks (lrt_hip_scene_trace_ex modes) currently fall back to fp32.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <hip/hip_runtime.h>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lightrt_c_hip.h"

/* GPU-assisted build hook implemented in lightrt_c_tri.c (not a public ABI). */
extern "C" lrt_tri_scene *lrt_tri_scene_build_lbvh_morton(const float *vertices,
                                                          size_t ntris,
                                                          const uint32_t *morton,
                                                          lrt_tri_layout layout,
                                                          unsigned max_leaf_size,
                                                          lrt_result *err);

/* ------------------------------------------------------------------------- */
/* LRTS serialization header (must match lightrt_c_tri.c / lightrt_c_vk.c).   */
/* ------------------------------------------------------------------------- */
typedef struct hip_lrts_header {
    char magic[4];
    uint32_t version;
    uint32_t endian;
    uint32_t flags;
    uint32_t layout;
    uint32_t prim_kind;
    uint32_t node_count;
    uint32_t block_count;
    uint32_t root;
    uint32_t node_stride;
    uint32_t block_stride;
    uint32_t reserved0;
    float root_lo[3];
    float root_hi[3];
    uint64_t node_offset;
    uint64_t block_offset;
    uint64_t file_size;
} hip_lrts_header;

/* ------------------------------------------------------------------------- */
/* Engine / scene.                                                           */
/* ------------------------------------------------------------------------- */
struct lrt_hip_engine {
    int device;
    hipStream_t stream;
    uint32_t caps;
    char device_name[256];
    char err[512];

    /* Growable ray/hit/occlusion scratch reused across trace calls. */
    void *d_rays;
    void *d_hits;
    void *d_occ;
    size_t cap_rays;  /* bytes */
    size_t cap_hits;  /* bytes */
    size_t cap_occ;   /* bytes */
};

struct lrt_hip_scene {
    uint32_t *d_nodes;
    uint32_t *d_blocks;
    uint32_t node_count;
    uint32_t block_count;
    uint32_t node_stride;  /* bytes */
    uint32_t block_stride; /* bytes */
    uint32_t root;
    uint32_t layout;    /* 4 or 8 */
    uint32_t stack;     /* traversal stack depth bucket (32/64/128/256) */
    uint32_t max_depth; /* wide-tree depth (refit bottom-up pass count) */
    size_t mem_bytes;
};

/* hipFree is [[nodiscard]]; this swallows the result at teardown/cleanup sites
 * where there is nothing useful to do with a free error. */
static inline void hip_free(void *p) {
    if (p) {
        hipError_t st = hipFree(p);
        (void)st;
    }
}

static void hip_set_err(lrt_hip_engine *e, const char *msg) {
    if (!e) return;
    snprintf(e->err, sizeof(e->err), "%s", msg ? msg : "");
}

static void hip_set_err_hip(lrt_hip_engine *e, const char *where,
                            hipError_t st) {
    if (!e) return;
    snprintf(e->err, sizeof(e->err), "%s: %s", where, hipGetErrorString(st));
}

/* trace_stack_for: identical bucketing to lightrt_c_vk.c. */
static uint32_t trace_stack_for(uint32_t max_depth, uint32_t w) {
    uint32_t need = max_depth * (w - 1u) + w + 1u;
    static const uint32_t buckets[] = {32u, 64u, 128u, 256u};
    for (int i = 0; i < 4; i++)
        if (need <= buckets[i]) return buckets[i];
    return 0; /* too deep for the compute path */
}

/* ========================================================================= */
/* fp32 trace kernel — port of vk/shaders/trace_bvh.comp.                     */
/* ========================================================================= */
#define LRT_HIP_LEAF_BIT 0x80000000u
#define LRT_HIP_NO_HIT 0xFFFFFFFFu
#define LRT_HIP_INVD_MAX 1e18f

__device__ __forceinline__ float fu(uint32_t i) { return __uint_as_float(i); }

template <unsigned W, unsigned STACK>
__launch_bounds__(64) __global__
    void k_trace(const uint32_t *__restrict__ nodes,
                 const uint32_t *__restrict__ blocks,
                 const uint32_t *__restrict__ rays, uint32_t *__restrict__ hits,
                 uint32_t root, uint32_t ray_count) {
    const uint32_t gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= ray_count) return;

    constexpr uint32_t node_stride = 8u * W;
    constexpr uint32_t block_stride = 10u * W;
    constexpr uint32_t prim_off = 9u * W;

    const uint32_t rb = gid * 8u;
    float orgx = fu(rays[rb + 0u]), orgy = fu(rays[rb + 1u]),
          orgz = fu(rays[rb + 2u]);
    float tmin = fu(rays[rb + 3u]);
    float dirx = fu(rays[rb + 4u]), diry = fu(rays[rb + 5u]),
          dirz = fu(rays[rb + 6u]);
    float tmax = fu(rays[rb + 7u]);

    /* invd with the exact clamp from tri_ray_setup. */
    float invd[3];
    float dd[3] = {dirx, diry, dirz};
    for (int k = 0; k < 3; k++) {
        float d = dd[k];
        float inv = 1.0f / d;
        if (!(inv >= -LRT_HIP_INVD_MAX && inv <= LRT_HIP_INVD_MAX)) {
            float s = (d == 0.0f) ? 1.0f : d;
            inv = (s < 0.0f) ? -LRT_HIP_INVD_MAX : LRT_HIP_INVD_MAX;
        }
        invd[k] = inv;
    }
    const float invdx = invd[0], invdy = invd[1], invdz = invd[2];

    float best_t = tmax;
    float best_u = 0.0f, best_v = 0.0f;
    uint32_t best_prim = LRT_HIP_NO_HIT;

    uint32_t stk_ref[STACK];
    float stk_tn[STACK];
    int sp = 0;
    stk_ref[0] = root;
    stk_tn[0] = tmin;
    sp = 1;

    while (sp > 0) {
        sp--;
        uint32_t ref = stk_ref[sp];
        float tnear_e = stk_tn[sp];
        if (tnear_e >= best_t) continue;

        if ((ref & LRT_HIP_LEAF_BIT) != 0u) {
            uint32_t blk0 = (ref & 0x7FFFFFFFu) >> 4u;
            uint32_t nblk = ref & 0xFu;
            for (uint32_t b = 0u; b < nblk; b++) {
                uint32_t bb = (blk0 + b) * block_stride;
                for (uint32_t lane = 0u; lane < W; lane++) {
                    uint32_t prim = blocks[bb + prim_off + lane];
                    if (prim == LRT_HIP_NO_HIT) continue;
                    float v0x = fu(blocks[bb + 0u * W + lane]);
                    float v0y = fu(blocks[bb + 1u * W + lane]);
                    float v0z = fu(blocks[bb + 2u * W + lane]);
                    float e1x = fu(blocks[bb + 3u * W + lane]);
                    float e1y = fu(blocks[bb + 4u * W + lane]);
                    float e1z = fu(blocks[bb + 5u * W + lane]);
                    float e2x = fu(blocks[bb + 6u * W + lane]);
                    float e2y = fu(blocks[bb + 7u * W + lane]);
                    float e2z = fu(blocks[bb + 8u * W + lane]);
                    float px = diry * e2z - dirz * e2y;
                    float py = dirz * e2x - dirx * e2z;
                    float pz = dirx * e2y - diry * e2x;
                    float det = e1x * px + e1y * py + e1z * pz;
                    if (det > -1e-12f && det < 1e-12f) continue;
                    float inv_det = 1.0f / det;
                    float tvx = orgx - v0x;
                    float tvy = orgy - v0y;
                    float tvz = orgz - v0z;
                    float uu = (tvx * px + tvy * py + tvz * pz) * inv_det;
                    if (uu < 0.0f || uu > 1.0f) continue;
                    float qx = tvy * e1z - tvz * e1y;
                    float qy = tvz * e1x - tvx * e1z;
                    float qz = tvx * e1y - tvy * e1x;
                    float vv = (dirx * qx + diry * qy + dirz * qz) * inv_det;
                    if (vv < 0.0f || uu + vv > 1.0f) continue;
                    float tt = (e2x * qx + e2y * qy + e2z * qz) * inv_det;
                    if (tt < tmin || tt >= best_t) continue;
                    best_t = tt;
                    best_u = uu;
                    best_v = vv;
                    best_prim = prim;
                }
            }
            continue;
        }

        /* Interior node. */
        uint32_t nb = (ref & 0x7FFFFFFFu) * node_stride;
        uint32_t nchildren = nodes[nb + 7u * W];

        uint32_t hit_ref[8];
        float hit_tn[8];
        int nhit = 0;
        for (uint32_t i = 0u; i < nchildren; i++) {
            float lo_x = fu(nodes[nb + 0u * W + i]);
            float lo_y = fu(nodes[nb + 1u * W + i]);
            float lo_z = fu(nodes[nb + 2u * W + i]);
            float hi_x = fu(nodes[nb + 3u * W + i]);
            float hi_y = fu(nodes[nb + 4u * W + i]);
            float hi_z = fu(nodes[nb + 5u * W + i]);
            float tlx = (lo_x - orgx) * invdx;
            float thx = (hi_x - orgx) * invdx;
            float tly = (lo_y - orgy) * invdy;
            float thy = (hi_y - orgy) * invdy;
            float tlz = (lo_z - orgz) * invdz;
            float thz = (hi_z - orgz) * invdz;
            float tnx = fminf(tlx, thx), tfx = fmaxf(tlx, thx);
            float tny = fminf(tly, thy), tfy = fmaxf(tly, thy);
            float tnz = fminf(tlz, thz), tfz = fmaxf(tlz, thz);
            float tnear = fmaxf(fmaxf(tnx, tny), fmaxf(tnz, tmin));
            float tfar = fminf(fminf(tfx, tfy), fminf(tfz, best_t));
            if (tnear <= tfar) {
                int j = nhit++;
                while (j > 0 && hit_tn[j - 1] > tnear) {
                    hit_tn[j] = hit_tn[j - 1];
                    hit_ref[j] = hit_ref[j - 1];
                    j--;
                }
                hit_tn[j] = tnear;
                hit_ref[j] = nodes[nb + 6u * W + i];
            }
        }
        if ((uint32_t)sp + (uint32_t)nhit > STACK) {
            best_prim = LRT_HIP_NO_HIT; /* depth-capped: never hit */
            break;
        }
        for (int i = nhit - 1; i >= 0; i--) {
            stk_ref[sp] = hit_ref[i];
            stk_tn[sp] = hit_tn[i];
            sp++;
        }
    }

    uint32_t hb = gid * 4u;
    hits[hb + 0u] =
        __float_as_uint(best_prim != LRT_HIP_NO_HIT ? best_t : 0.0f);
    hits[hb + 1u] = __float_as_uint(best_u);
    hits[hb + 2u] = __float_as_uint(best_v);
    hits[hb + 3u] = best_prim;
}

/* Any-hit / occlusion: same traversal, early-out on the first triangle within
 * [tmin, tmax). No nearest tracking, no insertion sort needed for correctness
 * (any order is fine), but we keep the same push order for simplicity. */
template <unsigned W, unsigned STACK>
__launch_bounds__(64) __global__
    void k_occluded(const uint32_t *__restrict__ nodes,
                    const uint32_t *__restrict__ blocks,
                    const uint32_t *__restrict__ rays,
                    uint8_t *__restrict__ occ, uint32_t root,
                    uint32_t ray_count) {
    const uint32_t gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= ray_count) return;

    constexpr uint32_t node_stride = 8u * W;
    constexpr uint32_t block_stride = 10u * W;
    constexpr uint32_t prim_off = 9u * W;

    const uint32_t rb = gid * 8u;
    float orgx = fu(rays[rb + 0u]), orgy = fu(rays[rb + 1u]),
          orgz = fu(rays[rb + 2u]);
    float tmin = fu(rays[rb + 3u]);
    float dirx = fu(rays[rb + 4u]), diry = fu(rays[rb + 5u]),
          dirz = fu(rays[rb + 6u]);
    float tmax = fu(rays[rb + 7u]);

    float invd[3];
    float dd[3] = {dirx, diry, dirz};
    for (int k = 0; k < 3; k++) {
        float d = dd[k];
        float inv = 1.0f / d;
        if (!(inv >= -LRT_HIP_INVD_MAX && inv <= LRT_HIP_INVD_MAX)) {
            float s = (d == 0.0f) ? 1.0f : d;
            inv = (s < 0.0f) ? -LRT_HIP_INVD_MAX : LRT_HIP_INVD_MAX;
        }
        invd[k] = inv;
    }
    const float invdx = invd[0], invdy = invd[1], invdz = invd[2];

    uint8_t hit = 0u;
    uint32_t stk_ref[STACK];
    float stk_tn[STACK];
    int sp = 0;
    stk_ref[0] = root;
    stk_tn[0] = tmin;
    sp = 1;

    while (sp > 0 && !hit) {
        sp--;
        uint32_t ref = stk_ref[sp];
        float tnear_e = stk_tn[sp];
        if (tnear_e >= tmax) continue;

        if ((ref & LRT_HIP_LEAF_BIT) != 0u) {
            uint32_t blk0 = (ref & 0x7FFFFFFFu) >> 4u;
            uint32_t nblk = ref & 0xFu;
            for (uint32_t b = 0u; b < nblk && !hit; b++) {
                uint32_t bb = (blk0 + b) * block_stride;
                for (uint32_t lane = 0u; lane < W; lane++) {
                    uint32_t prim = blocks[bb + prim_off + lane];
                    if (prim == LRT_HIP_NO_HIT) continue;
                    float v0x = fu(blocks[bb + 0u * W + lane]);
                    float v0y = fu(blocks[bb + 1u * W + lane]);
                    float v0z = fu(blocks[bb + 2u * W + lane]);
                    float e1x = fu(blocks[bb + 3u * W + lane]);
                    float e1y = fu(blocks[bb + 4u * W + lane]);
                    float e1z = fu(blocks[bb + 5u * W + lane]);
                    float e2x = fu(blocks[bb + 6u * W + lane]);
                    float e2y = fu(blocks[bb + 7u * W + lane]);
                    float e2z = fu(blocks[bb + 8u * W + lane]);
                    float px = diry * e2z - dirz * e2y;
                    float py = dirz * e2x - dirx * e2z;
                    float pz = dirx * e2y - diry * e2x;
                    float det = e1x * px + e1y * py + e1z * pz;
                    if (det > -1e-12f && det < 1e-12f) continue;
                    float inv_det = 1.0f / det;
                    float tvx = orgx - v0x;
                    float tvy = orgy - v0y;
                    float tvz = orgz - v0z;
                    float uu = (tvx * px + tvy * py + tvz * pz) * inv_det;
                    if (uu < 0.0f || uu > 1.0f) continue;
                    float qx = tvy * e1z - tvz * e1y;
                    float qy = tvz * e1x - tvx * e1z;
                    float qz = tvx * e1y - tvy * e1x;
                    float vv = (dirx * qx + diry * qy + dirz * qz) * inv_det;
                    if (vv < 0.0f || uu + vv > 1.0f) continue;
                    float tt = (e2x * qx + e2y * qy + e2z * qz) * inv_det;
                    if (tt < tmin || tt >= tmax) continue;
                    hit = 1u;
                    break;
                }
            }
            continue;
        }

        uint32_t nb = (ref & 0x7FFFFFFFu) * node_stride;
        uint32_t nchildren = nodes[nb + 7u * W];
        for (uint32_t i = 0u; i < nchildren; i++) {
            float lo_x = fu(nodes[nb + 0u * W + i]);
            float lo_y = fu(nodes[nb + 1u * W + i]);
            float lo_z = fu(nodes[nb + 2u * W + i]);
            float hi_x = fu(nodes[nb + 3u * W + i]);
            float hi_y = fu(nodes[nb + 4u * W + i]);
            float hi_z = fu(nodes[nb + 5u * W + i]);
            float tlx = (lo_x - orgx) * invdx;
            float thx = (hi_x - orgx) * invdx;
            float tly = (lo_y - orgy) * invdy;
            float thy = (hi_y - orgy) * invdy;
            float tlz = (lo_z - orgz) * invdz;
            float thz = (hi_z - orgz) * invdz;
            float tnear = fmaxf(fmaxf(fminf(tlx, thx), fminf(tly, thy)),
                                fmaxf(fminf(tlz, thz), tmin));
            float tfar = fminf(fminf(fmaxf(tlx, thx), fmaxf(tly, thy)),
                               fminf(fmaxf(tlz, thz), tmax));
            if (tnear <= tfar) {
                if ((uint32_t)sp >= STACK) {
                    hit = 0u;
                    sp = 0;
                    break;
                }
                stk_ref[sp] = nodes[nb + 6u * W + i];
                stk_tn[sp] = tnear;
                sp++;
            }
        }
    }

    occ[gid] = hit;
}

/* ========================================================================= */
/* Build kernels — port of vk/shaders/build_morton.comp.                      */
/* ========================================================================= */
__device__ __forceinline__ uint32_t expand10(uint32_t v) {
    v &= 0x3FFu;
    v = (v | (v << 16)) & 0x030000FFu;
    v = (v | (v << 8)) & 0x0300F00Fu;
    v = (v | (v << 4)) & 0x030C30C3u;
    v = (v | (v << 2)) & 0x09249249u;
    return v;
}

__global__ void k_centroids(const float *__restrict__ verts,
                            float *__restrict__ centroids, uint32_t ntris) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= ntris) return;
    uint32_t vb = i * 9u;
    for (uint32_t a = 0u; a < 3u; a++) {
        float v0 = verts[vb + 0u + a];
        float v1 = verts[vb + 3u + a];
        float v2 = verts[vb + 6u + a];
        float lo = fminf(v0, fminf(v1, v2));
        float hi = fmaxf(v0, fmaxf(v1, v2));
        centroids[i * 3u + a] = 0.5f * (lo + hi);
    }
}

__global__ void k_morton(const float *__restrict__ centroids,
                         uint32_t *__restrict__ morton, uint32_t ntris,
                         float base0, float base1, float base2, float scale0,
                         float scale1, float scale2) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= ntris) return;
    float base[3] = {base0, base1, base2};
    float scale[3] = {scale0, scale1, scale2};
    uint32_t q[3];
    for (uint32_t a = 0u; a < 3u; a++) {
        float c = centroids[i * 3u + a];
        float fv = (c - base[a]) * scale[a];
        int qi = (int)fv; /* truncation toward zero, matches (int32_t)v */
        if (qi < 0) qi = 0;
        if (qi > 1023) qi = 1023;
        q[a] = (uint32_t)qi;
    }
    morton[i] = (expand10(q[0]) << 2) | (expand10(q[1]) << 1) | expand10(q[2]);
}

/* ========================================================================= */
/* Refit kernels — update leaf vertices + node bounds in place (animation).    */
/* ========================================================================= */
/* Rewrite every leaf block's v0/e1/e2 from new vertex positions (prim_id ->
 * vertices[prim*9]). One thread per (block, lane). */
template <unsigned W>
__global__ void k_refit_leaves(uint32_t *__restrict__ blocks,
                               const float *__restrict__ verts,
                               uint32_t block_count, uint32_t ntris) {
    constexpr uint32_t block_stride = 10u * W;
    constexpr uint32_t prim_off = 9u * W;
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    uint32_t total = block_count * W;
    if (idx >= total) return;
    uint32_t b = idx / W, lane = idx % W;
    uint32_t bb = b * block_stride;
    uint32_t prim = blocks[bb + prim_off + lane];
    if (prim == LRT_HIP_NO_HIT || prim >= ntris) return;
    const float *v = verts + (size_t)prim * 9u;
    float v0x = v[0], v0y = v[1], v0z = v[2];
    blocks[bb + 0u * W + lane] = __float_as_uint(v0x);
    blocks[bb + 1u * W + lane] = __float_as_uint(v0y);
    blocks[bb + 2u * W + lane] = __float_as_uint(v0z);
    blocks[bb + 3u * W + lane] = __float_as_uint(v[3] - v0x);
    blocks[bb + 4u * W + lane] = __float_as_uint(v[4] - v0y);
    blocks[bb + 5u * W + lane] = __float_as_uint(v[5] - v0z);
    blocks[bb + 6u * W + lane] = __float_as_uint(v[6] - v0x);
    blocks[bb + 7u * W + lane] = __float_as_uint(v[7] - v0y);
    blocks[bb + 8u * W + lane] = __float_as_uint(v[8] - v0z);
}

/* Recompute each node's per-child AABB slots. Leaf children union their block
 * triangles; interior children union the child node's own slots. Run repeatedly
 * (>= max_depth+1 passes): leaf bounds are exact after pass 1, interior bounds
 * propagate one level per pass (parent index < child index by construction). */
template <unsigned W>
__global__ void k_refit_nodes(uint32_t *__restrict__ nodes,
                              const uint32_t *__restrict__ blocks,
                              uint32_t node_count) {
    constexpr uint32_t node_stride = 8u * W;
    constexpr uint32_t block_stride = 10u * W;
    constexpr uint32_t prim_off = 9u * W;
    uint32_t n = blockIdx.x * blockDim.x + threadIdx.x;
    if (n >= node_count) return;
    uint32_t nb = n * node_stride;
    uint32_t nchildren = nodes[nb + 7u * W];
    for (uint32_t i = 0; i < nchildren; i++) {
        uint32_t ref = nodes[nb + 6u * W + i];
        float lo0 = 1e30f, lo1 = 1e30f, lo2 = 1e30f;
        float hi0 = -1e30f, hi1 = -1e30f, hi2 = -1e30f;
        if ((ref & LRT_HIP_LEAF_BIT) != 0u) {
            uint32_t blk0 = (ref & 0x7FFFFFFFu) >> 4u;
            uint32_t nblk = ref & 0xFu;
            for (uint32_t b = 0; b < nblk; b++) {
                uint32_t bb = (blk0 + b) * block_stride;
                for (uint32_t lane = 0; lane < W; lane++) {
                    uint32_t prim = blocks[bb + prim_off + lane];
                    if (prim == LRT_HIP_NO_HIT) continue;
                    float v0x = fu(blocks[bb + 0u * W + lane]);
                    float v0y = fu(blocks[bb + 1u * W + lane]);
                    float v0z = fu(blocks[bb + 2u * W + lane]);
                    float e1x = fu(blocks[bb + 3u * W + lane]);
                    float e1y = fu(blocks[bb + 4u * W + lane]);
                    float e1z = fu(blocks[bb + 5u * W + lane]);
                    float e2x = fu(blocks[bb + 6u * W + lane]);
                    float e2y = fu(blocks[bb + 7u * W + lane]);
                    float e2z = fu(blocks[bb + 8u * W + lane]);
                    float v1x = v0x + e1x, v1y = v0y + e1y, v1z = v0z + e1z;
                    float v2x = v0x + e2x, v2y = v0y + e2y, v2z = v0z + e2z;
                    lo0 = fminf(lo0, fminf(v0x, fminf(v1x, v2x)));
                    lo1 = fminf(lo1, fminf(v0y, fminf(v1y, v2y)));
                    lo2 = fminf(lo2, fminf(v0z, fminf(v1z, v2z)));
                    hi0 = fmaxf(hi0, fmaxf(v0x, fmaxf(v1x, v2x)));
                    hi1 = fmaxf(hi1, fmaxf(v0y, fmaxf(v1y, v2y)));
                    hi2 = fmaxf(hi2, fmaxf(v0z, fmaxf(v1z, v2z)));
                }
            }
        } else {
            uint32_t c = ref & 0x7FFFFFFFu;
            uint32_t cb = c * node_stride;
            uint32_t cn = nodes[cb + 7u * W];
            for (uint32_t j = 0; j < cn; j++) {
                lo0 = fminf(lo0, fu(nodes[cb + 0u * W + j]));
                lo1 = fminf(lo1, fu(nodes[cb + 1u * W + j]));
                lo2 = fminf(lo2, fu(nodes[cb + 2u * W + j]));
                hi0 = fmaxf(hi0, fu(nodes[cb + 3u * W + j]));
                hi1 = fmaxf(hi1, fu(nodes[cb + 4u * W + j]));
                hi2 = fmaxf(hi2, fu(nodes[cb + 5u * W + j]));
            }
        }
        nodes[nb + 0u * W + i] = __float_as_uint(lo0);
        nodes[nb + 1u * W + i] = __float_as_uint(lo1);
        nodes[nb + 2u * W + i] = __float_as_uint(lo2);
        nodes[nb + 3u * W + i] = __float_as_uint(hi0);
        nodes[nb + 4u * W + i] = __float_as_uint(hi1);
        nodes[nb + 5u * W + i] = __float_as_uint(hi2);
    }
}

/* ========================================================================= */
/* Trace launchers (compile-time W/STACK dispatch).                           */
/* ========================================================================= */
#define HIP_GRID(n) (((n) + 63u) / 64u), 64u, 0, e->stream

static hipError_t launch_trace(lrt_hip_engine *e, const lrt_hip_scene *s,
                               const uint32_t *d_rays, uint32_t *d_hits,
                               uint32_t n) {
    const uint32_t W = s->layout, S = s->stack, root = s->root;
#define LAUNCH(w, st)                                                          \
    hipLaunchKernelGGL((k_trace<w, st>), dim3(((n) + 63u) / 64u), dim3(64), 0, \
                       e->stream, s->d_nodes, s->d_blocks, d_rays, d_hits,     \
                       root, n)
    if (W == 4u) {
        if (S == 32u) LAUNCH(4, 32);
        else if (S == 64u) LAUNCH(4, 64);
        else if (S == 128u) LAUNCH(4, 128);
        else LAUNCH(4, 256);
    } else {
        if (S == 32u) LAUNCH(8, 32);
        else if (S == 64u) LAUNCH(8, 64);
        else if (S == 128u) LAUNCH(8, 128);
        else LAUNCH(8, 256);
    }
#undef LAUNCH
    return hipGetLastError();
}

static hipError_t launch_occluded(lrt_hip_engine *e, const lrt_hip_scene *s,
                                  const uint32_t *d_rays, uint8_t *d_occ,
                                  uint32_t n) {
    const uint32_t W = s->layout, S = s->stack, root = s->root;
#define LAUNCH(w, st)                                                          \
    hipLaunchKernelGGL((k_occluded<w, st>), dim3(((n) + 63u) / 64u), dim3(64), \
                       0, e->stream, s->d_nodes, s->d_blocks, d_rays, d_occ,   \
                       root, n)
    if (W == 4u) {
        if (S == 32u) LAUNCH(4, 32);
        else if (S == 64u) LAUNCH(4, 64);
        else if (S == 128u) LAUNCH(4, 128);
        else LAUNCH(4, 256);
    } else {
        if (S == 32u) LAUNCH(8, 32);
        else if (S == 64u) LAUNCH(8, 64);
        else if (S == 128u) LAUNCH(8, 128);
        else LAUNCH(8, 256);
    }
#undef LAUNCH
    return hipGetLastError();
}

/* ========================================================================= */
/* Engine.                                                                   */
/* ========================================================================= */
extern "C" lrt_hip_engine *lrt_hip_engine_create(
    const lrt_hip_engine_options *opts, lrt_result *err) {
    int ndev = 0;
    if (hipGetDeviceCount(&ndev) != hipSuccess || ndev <= 0) {
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return NULL;
    }
    int dev = (opts && opts->device_index >= 0) ? opts->device_index : 0;
    if (dev >= ndev) dev = 0;

    hipDeviceProp_t prop;
    if (hipGetDeviceProperties(&prop, dev) != hipSuccess) {
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return NULL;
    }
    if (hipSetDevice(dev) != hipSuccess) {
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return NULL;
    }

    lrt_hip_engine *e = (lrt_hip_engine *)calloc(1, sizeof(lrt_hip_engine));
    if (!e) {
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return NULL;
    }
    e->device = dev;
    if (hipStreamCreate(&e->stream) != hipSuccess) {
        free(e);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return NULL;
    }
    snprintf(e->device_name, sizeof(e->device_name), "%s", prop.name);
    e->caps = LRT_HIP_CAP_COMPUTE;

    /* WMMA / matrix-core capability inferred from arch (gfx11xx, gfx12xx). */
    const char *arch = prop.gcnArchName;
    if (strstr(arch, "gfx11") || strstr(arch, "gfx12")) {
        e->caps |= LRT_HIP_CAP_WMMA | LRT_HIP_CAP_INT8 | LRT_HIP_CAP_INT4;
    }
    if (strstr(arch, "gfx12")) {
        e->caps |= LRT_HIP_CAP_FP8;
    }

    if (err) *err = LRT_RESULT_OK;
    return e;
}

extern "C" void lrt_hip_engine_destroy(lrt_hip_engine *e) {
    if (!e) return;
    hip_free(e->d_rays);
    hip_free(e->d_hits);
    hip_free(e->d_occ);
    if (e->stream) { hipError_t st = hipStreamDestroy(e->stream); (void)st; }
    free(e);
}

extern "C" uint32_t lrt_hip_engine_caps(const lrt_hip_engine *e) {
    return e ? e->caps : 0u;
}

extern "C" const char *lrt_hip_engine_device_name(const lrt_hip_engine *e) {
    return e ? e->device_name : "";
}

extern "C" const char *lrt_hip_engine_last_error(const lrt_hip_engine *e) {
    return e ? e->err : "";
}

/* Internal: expose the engine stream to the WMMA TU (lightrt_hip_wmma.hip)
 * without sharing the struct definition. Not in the public header. */
extern "C" void *lrt_hip_engine_stream_(const lrt_hip_engine *e) {
    return e ? (void *)e->stream : NULL;
}

/* Grow a device scratch buffer to at least `need` bytes. */
static int hip_grow(lrt_hip_engine *e, void **buf, size_t *cap, size_t need) {
    if (*cap >= need && *buf) return 1;
    hip_free(*buf);
    *buf = NULL;
    *cap = 0;
    size_t alloc = need + need / 2u; /* 1.5x headroom */
    if (hipMalloc(buf, alloc) != hipSuccess) {
        *buf = NULL;
        return 0;
    }
    *cap = alloc;
    return 1;
}

/* ========================================================================= */
/* Resident scene upload / trace.                                            */
/* ========================================================================= */
extern "C" lrt_hip_scene *lrt_hip_scene_upload(lrt_hip_engine *e,
                                               const lrt_tri_scene *s,
                                               lrt_result *err) {
    if (!e || !s) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return NULL;
    }
    void *blob = NULL;
    size_t blob_n = 0;
    lrt_result sr = lrt_tri_scene_save_to_memory(s, &blob, &blob_n);
    if (sr != LRT_RESULT_OK) {
        hip_set_err(e, "scene not GPU-traceable (quantized/curve/user?)");
        if (err) *err = sr;
        return NULL;
    }
    const hip_lrts_header *h = (const hip_lrts_header *)blob;
    uint32_t w = h->layout;
    if (w != 4u && w != 8u) {
        free(blob);
        hip_set_err(e, "unsupported BVH layout for GPU trace");
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return NULL;
    }

    lrt_tri_stats st;
    lrt_tri_scene_stats(s, &st);
    uint32_t stack = trace_stack_for(st.max_depth, w);
    if (stack == 0) {
        free(blob);
        hip_set_err(e, "BVH too deep for the GPU compute stack");
        if (err) *err = LRT_RESULT_TRAVERSAL_OVERFLOW;
        return NULL;
    }

    lrt_hip_scene *sc = (lrt_hip_scene *)calloc(1, sizeof(lrt_hip_scene));
    if (!sc) {
        free(blob);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return NULL;
    }
    sc->node_count = h->node_count;
    sc->block_count = h->block_count;
    sc->node_stride = h->node_stride;
    sc->block_stride = h->block_stride;
    sc->root = h->root;
    sc->layout = w;
    sc->stack = stack;
    sc->max_depth = st.max_depth;

    size_t nodes_bytes = (size_t)h->node_count * h->node_stride;
    size_t blocks_bytes = (size_t)h->block_count * h->block_stride;
    sc->mem_bytes = nodes_bytes + blocks_bytes;

    hipError_t hr;
    if ((hr = hipMalloc((void **)&sc->d_nodes, nodes_bytes)) != hipSuccess ||
        (hr = hipMalloc((void **)&sc->d_blocks, blocks_bytes)) != hipSuccess) {
        hip_set_err_hip(e, "hipMalloc(scene)", hr);
        hip_free(sc->d_nodes);
        free(sc);
        free(blob);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return NULL;
    }
    if ((hr = hipMemcpy(sc->d_nodes, (const char *)blob + h->node_offset,
                        nodes_bytes, hipMemcpyHostToDevice)) != hipSuccess ||
        (hr = hipMemcpy(sc->d_blocks, (const char *)blob + h->block_offset,
                        blocks_bytes, hipMemcpyHostToDevice)) != hipSuccess) {
        hip_set_err_hip(e, "hipMemcpy(scene)", hr);
        hip_free(sc->d_nodes);
        hip_free(sc->d_blocks);
        free(sc);
        free(blob);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return NULL;
    }
    free(blob);
    if (err) *err = LRT_RESULT_OK;
    return sc;
}

extern "C" void lrt_hip_scene_free(lrt_hip_engine *e, lrt_hip_scene *s) {
    (void)e;
    if (!s) return;
    hip_free(s->d_nodes);
    hip_free(s->d_blocks);
    free(s);
}

extern "C" int lrt_hip_scene_trace(lrt_hip_engine *e, lrt_hip_scene *s,
                                   const lrt_ray *rays, uint32_t n,
                                   lrt_hit *out, lrt_result *err) {
    if (!e || !s || (n && (!rays || !out))) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    if (n == 0) {
        if (err) *err = LRT_RESULT_OK;
        return 0;
    }
    size_t rbytes = (size_t)n * sizeof(lrt_ray);
    size_t hbytes = (size_t)n * sizeof(lrt_hit);
    if (!hip_grow(e, &e->d_rays, &e->cap_rays, rbytes) ||
        !hip_grow(e, &e->d_hits, &e->cap_hits, hbytes)) {
        hip_set_err(e, "device scratch allocation failed");
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return -1;
    }
    hipError_t hr;
    if ((hr = hipMemcpyAsync(e->d_rays, rays, rbytes, hipMemcpyHostToDevice,
                             e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipMemcpyAsync(rays)", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return -1;
    }
    if ((hr = launch_trace(e, s, (const uint32_t *)e->d_rays,
                           (uint32_t *)e->d_hits, n)) != hipSuccess) {
        hip_set_err_hip(e, "k_trace launch", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
    if ((hr = hipMemcpyAsync(out, e->d_hits, hbytes, hipMemcpyDeviceToHost,
                             e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipMemcpyAsync(hits)", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return -1;
    }
    if ((hr = hipStreamSynchronize(e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipStreamSynchronize", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
    int hits = 0;
    for (uint32_t i = 0; i < n; i++)
        if (out[i].prim_id != LRT_TRI_NO_HIT) hits++;
    if (err) *err = LRT_RESULT_OK;
    return hits;
}

extern "C" int lrt_hip_scene_occluded(lrt_hip_engine *e, lrt_hip_scene *s,
                                      const lrt_ray *rays, uint32_t n,
                                      uint8_t *occluded, lrt_result *err) {
    if (!e || !s || (n && (!rays || !occluded))) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    if (n == 0) {
        if (err) *err = LRT_RESULT_OK;
        return 0;
    }
    size_t rbytes = (size_t)n * sizeof(lrt_ray);
    size_t obytes = (size_t)n * sizeof(uint8_t);
    if (!hip_grow(e, &e->d_rays, &e->cap_rays, rbytes) ||
        !hip_grow(e, &e->d_occ, &e->cap_occ, obytes)) {
        hip_set_err(e, "device scratch allocation failed");
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return -1;
    }
    hipError_t hr;
    if ((hr = hipMemcpyAsync(e->d_rays, rays, rbytes, hipMemcpyHostToDevice,
                             e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipMemcpyAsync(rays)", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return -1;
    }
    if ((hr = launch_occluded(e, s, (const uint32_t *)e->d_rays,
                              (uint8_t *)e->d_occ, n)) != hipSuccess) {
        hip_set_err_hip(e, "k_occluded launch", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
    if ((hr = hipMemcpyAsync(occluded, e->d_occ, obytes, hipMemcpyDeviceToHost,
                             e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipMemcpyAsync(occ)", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return -1;
    }
    if ((hr = hipStreamSynchronize(e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipStreamSynchronize", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
    int nocc = 0;
    for (uint32_t i = 0; i < n; i++)
        if (occluded[i]) nocc++;
    if (err) *err = LRT_RESULT_OK;
    return nocc;
}

extern "C" int lrt_hip_scene_refit(lrt_hip_engine *e, lrt_hip_scene *s,
                                   const float *vertices, uint32_t ntris,
                                   lrt_result *err) {
    if (!e || !s || !vertices || ntris == 0) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    size_t vbytes = (size_t)ntris * 9u * sizeof(float);
    float *d_verts = NULL;
    hipError_t hr;
    if ((hr = hipMalloc((void **)&d_verts, vbytes)) != hipSuccess) {
        hip_set_err_hip(e, "hipMalloc(refit verts)", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return -1;
    }
    if ((hr = hipMemcpyAsync(d_verts, vertices, vbytes, hipMemcpyHostToDevice,
                             e->stream)) != hipSuccess) {
        hip_free(d_verts);
        hip_set_err_hip(e, "hipMemcpyAsync(refit verts)", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return -1;
    }
    const uint32_t W = s->layout;
    /* 1. Rewrite leaf vertices. */
    uint32_t leaf_threads = s->block_count * W;
    uint32_t lg = (leaf_threads + 255u) / 256u;
    if (W == 4u)
        hipLaunchKernelGGL((k_refit_leaves<4>), dim3(lg), dim3(256), 0,
                           e->stream, s->d_blocks, d_verts, s->block_count,
                           ntris);
    else
        hipLaunchKernelGGL((k_refit_leaves<8>), dim3(lg), dim3(256), 0,
                           e->stream, s->d_blocks, d_verts, s->block_count,
                           ntris);
    /* 2. Bottom-up node bounds: max_depth+1 passes (parent index < child). */
    uint32_t ng = (s->node_count + 255u) / 256u;
    uint32_t passes = s->max_depth + 1u;
    for (uint32_t p = 0; p < passes; p++) {
        if (W == 4u)
            hipLaunchKernelGGL((k_refit_nodes<4>), dim3(ng), dim3(256), 0,
                               e->stream, s->d_nodes, s->d_blocks,
                               s->node_count);
        else
            hipLaunchKernelGGL((k_refit_nodes<8>), dim3(ng), dim3(256), 0,
                               e->stream, s->d_nodes, s->d_blocks,
                               s->node_count);
    }
    if ((hr = hipStreamSynchronize(e->stream)) != hipSuccess) {
        hip_free(d_verts);
        hip_set_err_hip(e, "hipStreamSynchronize(refit)", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
    hip_free(d_verts);
    if (err) *err = LRT_RESULT_OK;
    return 0;
}

extern "C" int lrt_hip_scene_trace_ex(lrt_hip_engine *e, lrt_hip_scene *s,
                                      lrt_hip_trace_mode mode,
                                      const lrt_ray *rays, uint32_t n,
                                      lrt_hit *out, lrt_result *err) {
    /* Phase 2 modes not yet implemented: fall back to the exact fp32 path. */
    (void)mode;
    return lrt_hip_scene_trace(e, s, rays, n, out, err);
}

extern "C" int lrt_hip_trace_scene(lrt_hip_engine *e, const lrt_tri_scene *s,
                                   const lrt_ray *rays, uint32_t n,
                                   lrt_hit *out, lrt_result *err) {
    lrt_hip_scene *sc = lrt_hip_scene_upload(e, s, err);
    if (!sc) return -1;
    int r = lrt_hip_scene_trace(e, sc, rays, n, out, err);
    lrt_hip_scene_free(e, sc);
    return r;
}

/* ========================================================================= */
/* Path B: GPU-Morton build front end -> CPU LBVH finish.                     */
/* ========================================================================= */
extern "C" int lrt_hip_build_scene(lrt_hip_engine *e, const float *vertices,
                                   uint32_t ntris, lrt_tri_layout layout,
                                   lrt_tri_scene **out, lrt_result *err) {
    if (!e || !vertices || !out || ntris == 0) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    if (layout != LRT_TRI_LAYOUT_BVH4 && layout != LRT_TRI_LAYOUT_BVH8 &&
        layout != LRT_TRI_LAYOUT_AUTO) {
        hip_set_err(e, "GPU build supports BVH4/BVH8 only");
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }

    size_t vbytes = (size_t)ntris * 9u * sizeof(float);
    size_t cbytes = (size_t)ntris * 3u * sizeof(float);
    size_t mbytes = (size_t)ntris * sizeof(uint32_t);

    float *d_verts = NULL, *d_cen = NULL;
    uint32_t *d_morton = NULL;
    float *cen = NULL;
    uint32_t *morton = NULL;
    int rc = -1;
    hipError_t hr;

    if ((hr = hipMalloc((void **)&d_verts, vbytes)) != hipSuccess ||
        (hr = hipMalloc((void **)&d_cen, cbytes)) != hipSuccess ||
        (hr = hipMalloc((void **)&d_morton, mbytes)) != hipSuccess) {
        hip_set_err_hip(e, "hipMalloc(build)", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        goto done;
    }
    cen = (float *)malloc(cbytes);
    morton = (uint32_t *)malloc(mbytes);
    if (!cen || !morton) {
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        goto done;
    }

    if ((hr = hipMemcpyAsync(d_verts, vertices, vbytes, hipMemcpyHostToDevice,
                             e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipMemcpyAsync(verts)", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        goto done;
    }

    /* Pass 0: centroids on GPU. */
    hipLaunchKernelGGL(k_centroids, dim3((ntris + 63u) / 64u), dim3(64), 0,
                       e->stream, d_verts, d_cen, ntris);
    if ((hr = hipMemcpyAsync(cen, d_cen, cbytes, hipMemcpyDeviceToHost,
                             e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipMemcpyAsync(cen)", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        goto done;
    }
    if ((hr = hipStreamSynchronize(e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipStreamSynchronize", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        goto done;
    }

    /* CPU reduction: centroid AABB -> base/scale (1024^3 grid). */
    {
        float clo[3] = {cen[0], cen[1], cen[2]};
        float chi[3] = {cen[0], cen[1], cen[2]};
        for (uint32_t i = 0; i < ntris; i++) {
            for (int a = 0; a < 3; a++) {
                float v = cen[(size_t)i * 3 + a];
                if (v < clo[a]) clo[a] = v;
                if (v > chi[a]) chi[a] = v;
            }
        }
        float base[3], scale[3];
        for (int a = 0; a < 3; a++) {
            float ext = chi[a] - clo[a];
            base[a] = clo[a];
            scale[a] = ext > 0.0f ? 1024.0f / ext : 0.0f;
        }

        /* Pass 1: Morton codes on GPU. */
        hipLaunchKernelGGL(k_morton, dim3((ntris + 63u) / 64u), dim3(64), 0,
                           e->stream, d_cen, d_morton, ntris, base[0], base[1],
                           base[2], scale[0], scale[1], scale[2]);
        if ((hr = hipMemcpyAsync(morton, d_morton, mbytes,
                                 hipMemcpyDeviceToHost, e->stream)) !=
            hipSuccess) {
            hip_set_err_hip(e, "hipMemcpyAsync(morton)", hr);
            if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
            goto done;
        }
        if ((hr = hipStreamSynchronize(e->stream)) != hipSuccess) {
            hip_set_err_hip(e, "hipStreamSynchronize", hr);
            if (err) *err = LRT_RESULT_NOT_BUILT;
            goto done;
        }
    }

    /* CPU finishes the LBVH from the GPU-computed Morton codes. */
    {
        lrt_tri_layout lay =
            (layout == LRT_TRI_LAYOUT_AUTO) ? LRT_TRI_LAYOUT_BVH4 : layout;
        lrt_result br = LRT_RESULT_OK;
        lrt_tri_scene *scene = lrt_tri_scene_build_lbvh_morton(
            vertices, ntris, morton, lay, 0, &br);
        if (!scene) {
            if (err) *err = br;
            goto done;
        }
        *out = scene;
        rc = 0;
        if (err) *err = LRT_RESULT_OK;
    }

done:
    hip_free(d_verts);
    hip_free(d_cen);
    hip_free(d_morton);
    free(cen);
    free(morton);
    return rc;
}
