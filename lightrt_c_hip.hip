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
    uint32_t layout;     /* 4 or 8 */
    uint32_t stack;      /* traversal stack depth bucket (32/64/128/256) */
    uint32_t max_depth;  /* wide-tree depth (refit bottom-up pass count) */
    uint32_t prim_kind;  /* TRI_PRIM_* (0 = triangle) */
    uint32_t point_type; /* lrt_tri_point_type (point scenes only) */
    size_t mem_bytes;
};

/* prim_kind values mirrored from lightrt_c_tri.c (kept in sync). */
#define HIP_PRIM_TRI 0u
#define HIP_PRIM_RLCURVE 5u
#define HIP_PRIM_SPHERE 3u
#define HIP_PRIM_POINT 6u
#define HIP_PRIM_FLATCURVE 7u
#define HIP_PRIM_BEZCURVE 8u
#define HIP_PRIM_QUAD 9u
#define HIP_PRIM_TETRA 10u
#define HIP_PRIM_SDF 11u
#define HIP_SDF_SPHERE 0u
#define HIP_SDF_BOX 1u
#define HIP_SDF_TORUS 2u
#define HIP_POINT_SPHERE 0u
#define HIP_POINT_DISC 1u
#define HIP_POINT_ORIENTED_DISC 2u

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

    const size_t rb = (size_t)gid * 8u;
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
                size_t bb = (size_t)(blk0 + b) * block_stride;
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
        size_t nb = (size_t)(ref & 0x7FFFFFFFu) * node_stride;
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
        /* Stack would overflow (unreachable for scenes accepted by
         * trace_stack_for, which sizes STACK to the tree depth). Degrade
         * gracefully: stop and return the closest hit found so far rather than
         * resetting it to a miss. */
        if ((uint32_t)sp + (uint32_t)nhit > STACK) break;
        for (int i = nhit - 1; i >= 0; i--) {
            stk_ref[sp] = hit_ref[i];
            stk_tn[sp] = hit_tn[i];
            sp++;
        }
    }

    size_t hb = (size_t)gid * 4u;
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

    const size_t rb = (size_t)gid * 8u;
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
                size_t bb = (size_t)(blk0 + b) * block_stride;
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

        size_t nb = (size_t)(ref & 0x7FFFFFFFu) * node_stride;
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
                /* Stack would overflow (unreachable for scenes accepted by
                 * trace_stack_for). Degrade conservatively: report occluded so
                 * a too-deep BVH causes a spurious shadow rather than a light
                 * leak. */
                if ((uint32_t)sp >= STACK) {
                    hit = 1u;
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
/* Analytic primitives (sphere / point / quad / tetra) — BVH4, runtime kind.  */
/* Ported byte-for-byte from the CPU scalar intersectors for hit parity.       */
/* ========================================================================= */
#define HIP_INV_2PI 0.15915494309189535f
#define HIP_INV_PI 0.3183098861837907f

/* Moller-Trumbore on an explicit triangle (matches tri_mt_one). */
__device__ __forceinline__ bool hp_mt(float ox, float oy, float oz, float dx,
                                      float dy, float dz, float v0x, float v0y,
                                      float v0z, float v1x, float v1y, float v1z,
                                      float v2x, float v2y, float v2z,
                                      float tmin, float tbest, float *t,
                                      float *u, float *v) {
    float e1x = v1x - v0x, e1y = v1y - v0y, e1z = v1z - v0z;
    float e2x = v2x - v0x, e2y = v2y - v0y, e2z = v2z - v0z;
    float px = dy * e2z - dz * e2y, py = dz * e2x - dx * e2z,
          pz = dx * e2y - dy * e2x;
    float det = e1x * px + e1y * py + e1z * pz;
    if (det > -1e-12f && det < 1e-12f) return false;
    float inv = 1.0f / det;
    float tvx = ox - v0x, tvy = oy - v0y, tvz = oz - v0z;
    float uu = (tvx * px + tvy * py + tvz * pz) * inv;
    if (uu < 0.0f || uu > 1.0f) return false;
    float qx = tvy * e1z - tvz * e1y, qy = tvz * e1x - tvx * e1z,
          qz = tvx * e1y - tvy * e1x;
    float vv = (dx * qx + dy * qy + dz * qz) * inv;
    if (vv < 0.0f || uu + vv > 1.0f) return false;
    float tt = (e2x * qx + e2y * qy + e2z * qz) * inv;
    if (tt < tmin || tt >= tbest) return false;
    *t = tt; *u = uu; *v = vv;
    return true;
}

/* ---- flat (ribbon) linear curve, port of tri_flat_isect_one -------------- */
__device__ __forceinline__ bool hp_flat_one(float ox, float oy, float oz,
                                            float dx, float dy, float dz,
                                            const float p0[3], float r0,
                                            const float p1[3], float r1,
                                            float tmin, float best_t, float *t,
                                            float *u) {
    float Tx = p1[0] - p0[0], Ty = p1[1] - p0[1], Tz = p1[2] - p0[2];
    float bx = Ty * dz - Tz * dy, by = Tz * dx - Tx * dz, bz = Tx * dy - Ty * dx;
    float bl2 = bx * bx + by * by + bz * bz;
    if (bl2 <= 1e-20f) return false;
    float invb = 1.0f / sqrtf(bl2);
    bx *= invb; by *= invb; bz *= invb;
    float q[4][3] = {
        {p0[0] + r0 * bx, p0[1] + r0 * by, p0[2] + r0 * bz},
        {p1[0] + r1 * bx, p1[1] + r1 * by, p1[2] + r1 * bz},
        {p1[0] - r1 * bx, p1[1] - r1 * by, p1[2] - r1 * bz},
        {p0[0] - r0 * bx, p0[1] - r0 * by, p0[2] - r0 * bz}};
    float Tl2 = Tx * Tx + Ty * Ty + Tz * Tz;
    float best = best_t, hit_s = 0.0f;
    int hit = 0;
    for (int tri = 0; tri < 2; tri++) {
        const float *a = q[0];
        const float *bb = tri == 0 ? q[1] : q[2];
        const float *cc = tri == 0 ? q[2] : q[3];
        float e1x = bb[0] - a[0], e1y = bb[1] - a[1], e1z = bb[2] - a[2];
        float e2x = cc[0] - a[0], e2y = cc[1] - a[1], e2z = cc[2] - a[2];
        float px = dy * e2z - dz * e2y, py = dz * e2x - dx * e2z,
              pz = dx * e2y - dy * e2x;
        float det = e1x * px + e1y * py + e1z * pz;
        if (det > -1e-12f && det < 1e-12f) continue;
        float inv = 1.0f / det;
        float tvx = ox - a[0], tvy = oy - a[1], tvz = oz - a[2];
        float uu = (tvx * px + tvy * py + tvz * pz) * inv;
        if (uu < 0.0f || uu > 1.0f) continue;
        float qx = tvy * e1z - tvz * e1y, qy = tvz * e1x - tvx * e1z,
              qz = tvx * e1y - tvy * e1x;
        float vv = (dx * qx + dy * qy + dz * qz) * inv;
        if (vv < 0.0f || uu + vv > 1.0f) continue;
        float tt = (e2x * qx + e2y * qy + e2z * qz) * inv;
        if (tt < tmin || tt >= best) continue;
        best = tt;
        hit = 1;
        float hpx = ox + tt * dx, hpy = oy + tt * dy, hpz = oz + tt * dz;
        float s = Tl2 > 0.0f ? ((hpx - p0[0]) * Tx + (hpy - p0[1]) * Ty +
                                (hpz - p0[2]) * Tz) / Tl2
                             : 0.0f;
        hit_s = s < 0.0f ? 0.0f : (s > 1.0f ? 1.0f : s);
    }
    if (hit) { *t = best; *u = hit_s; }
    return hit != 0;
}

/* ---- round-linear (tapered cone) curve, port of tri_rlc_isect_one --------- */
#define HIP_INF_F 3.402823466e+38f
#define HIP_RLC_ULP 1.1920929e-7f
#define HIP_RLC_MIN_A 1e-18f

__device__ __forceinline__ bool hp_rlc_in_cone(const float cp0[3], float cr0,
                                               const float cp1[3], float cr1,
                                               const float p[3]) {
    if (!(cp1[0] < HIP_INF_F) || !(cp0[0] < HIP_INF_F)) return false;
    float dPx = cp1[0] - cp0[0], dPy = cp1[1] - cp0[1], dPz = cp1[2] - cp0[2];
    float dPdP = dPx * dPx + dPy * dPy + dPz * dPz;
    float dr = cr1 - cr0, r0dr = cr0 * dr, g = dPdP - dr * dr;
    float p0px = p[0] - cp0[0], p0py = p[1] - cp0[1], p0pz = p[2] - cp0[2];
    float y = p0px * dPx + p0py * dPy + p0pz * dPz;
    if (!(y > -r0dr + HIP_RLC_ULP)) return false;
    if (!(y < -cr1 * dr + dPdP)) return false;
    float p0p2 = p0px * p0px + p0py * p0py + p0pz * p0pz;
    return (p0p2 * g - y * y) < (dPdP * cr0 * cr0 + 2.0f * r0dr * y);
}
__device__ __forceinline__ bool hp_rlc_clip_plane(const float cp0[3], float cr0,
                                                  const float cp1[3], float cr1,
                                                  const float p[3]) {
    if (!(cp1[0] < HIP_INF_F) || !(cp0[0] < HIP_INF_F)) return false;
    float dPx = cp1[0] - cp0[0], dPy = cp1[1] - cp0[1], dPz = cp1[2] - cp0[2];
    float r0dr = cr0 * (cr1 - cr0);
    float p0px = p[0] - cp0[0], p0py = p[1] - cp0[1], p0pz = p[2] - cp0[2];
    float y = p0px * dPx + p0py * dPy + p0pz * dPz;
    return y > -r0dr;
}

__device__ __forceinline__ bool hp_rlc_one(float ox0, float oy0, float oz0,
                                           float dirx, float diry, float dirz,
                                           const float p0[3], float r0,
                                           const float p1[3], float r1,
                                           const float pL[3], float rL,
                                           const float pR[3], float rR,
                                           float tmin, float best_t, float *t_out,
                                           float *u_out) {
    const float POS_INF = HIP_INF_F, NEG_INF = -HIP_INF_F;
    float dOdO = dirx * dirx + diry * diry + dirz * dirz;
    if (dOdO <= 0.0f) return false;
    float rcp_dOdO = 1.0f / dOdO;
    float cx = 0.5f * (p0[0] + p1[0]), cy = 0.5f * (p0[1] + p1[1]),
          cz = 0.5f * (p0[2] + p1[2]);
    float dt = ((cx - ox0) * dirx + (cy - oy0) * diry + (cz - oz0) * dirz) *
               rcp_dOdO;
    float ox = ox0 + dt * dirx, oy = oy0 + dt * diry, oz = oz0 + dt * dirz;
    float dPx = p1[0] - p0[0], dPy = p1[1] - p0[1], dPz = p1[2] - p0[2];
    float dPdP = dPx * dPx + dPy * dPy + dPz * dPz;
    float dr = r1 - r0, r0dr = r0 * dr, g = dPdP - dr * dr;
    float Ox = ox - p0[0], Oy = oy - p0[1], Oz = oz - p0[2];
    float OdP = Ox * dPx + Oy * dPy + Oz * dPz;
    float dOdP = dirx * dPx + diry * dPy + dirz * dPz;
    float yp = OdP + r0dr;
    float t_cone_lo = POS_INF, t_cone_hi = NEG_INF, y_cone_lo = 0.0f,
          y_cone_hi = 0.0f;
    int cone_valid = 0;
    {
        float OO = Ox * Ox + Oy * Oy + Oz * Oz;
        float OdO = dirx * Ox + diry * Oy + dirz * Oz;
        float A = g * dOdO - dOdP * dOdP;
        float B = 2.0f * (g * OdO - dOdP * yp);
        float C = g * OO - OdP * OdP - r0 * r0 * dPdP - 2.0f * r0dr * OdP;
        float D = B * B - 4.0f * A * C;
        if (D >= 0.0f && g > 0.0f && (A > HIP_RLC_MIN_A || A < -HIP_RLC_MIN_A)) {
            cone_valid = 1;
            float Q = sqrtf(D), rcp_2A = 1.0f / (2.0f * A);
            float tf = (-B - Q) * rcp_2A, yf = yp + tf * dOdP;
            if (yf > -HIP_RLC_ULP && yf <= g) { t_cone_lo = tf; y_cone_lo = yf; }
            float tb = (-B + Q) * rcp_2A, yb = yp + tb * dOdP;
            if (yb > -HIP_RLC_ULP && yb <= g) { t_cone_hi = tb; y_cone_hi = yb; }
        }
    }
    if (!cone_valid && g > 0.0f) return false;
    if (t_cone_lo != POS_INF) {
        float hp[3] = {ox + t_cone_lo * dirx, oy + t_cone_lo * diry,
                       oz + t_cone_lo * dirz};
        if (hp_rlc_in_cone(p0, r0, pL, rL, hp) ||
            hp_rlc_in_cone(p1, r1, pR, rR, hp))
            t_cone_lo = POS_INF;
    }
    if (t_cone_hi != NEG_INF) {
        float hp[3] = {ox + t_cone_hi * dirx, oy + t_cone_hi * diry,
                       oz + t_cone_hi * dirz};
        if (hp_rlc_in_cone(p0, r0, pL, rL, hp) ||
            hp_rlc_in_cone(p1, r1, pR, rR, hp))
            t_cone_hi = NEG_INF;
    }
    float t_sph1_lo = POS_INF, t_sph1_hi = NEG_INF;
    {
        float O1x = ox - p1[0], O1y = oy - p1[1], O1z = oz - p1[2];
        float O1dO = O1x * dirx + O1y * diry + O1z * dirz;
        float O1O1 = O1x * O1x + O1y * O1y + O1z * O1z;
        float h2 = O1dO * O1dO - dOdO * (O1O1 - r1 * r1);
        if (h2 >= 0.0f) {
            float rhs = sqrtf(h2);
            float tf = (-O1dO - rhs) * rcp_dOdO;
            float hf[3] = {ox + tf * dirx, oy + tf * diry, oz + tf * dirz};
            if (yp + tf * dOdP > g && !hp_rlc_clip_plane(p1, r1, pR, rR, hf))
                t_sph1_lo = tf;
            float tb = (-O1dO + rhs) * rcp_dOdO;
            float hb[3] = {ox + tb * dirx, oy + tb * diry, oz + tb * dirz};
            if (yp + tb * dOdP > g && !hp_rlc_clip_plane(p1, r1, pR, rR, hb))
                t_sph1_hi = tb;
        }
    }
    float t_sph0_lo = POS_INF, t_sph0_hi = NEG_INF;
    if (!(pL[0] < HIP_INF_F)) {
        float O0x = ox - p0[0], O0y = oy - p0[1], O0z = oz - p0[2];
        float O0dO = O0x * dirx + O0y * diry + O0z * dirz;
        float O0O0 = O0x * O0x + O0y * O0y + O0z * O0z;
        float h2 = O0dO * O0dO - dOdO * (O0O0 - r0 * r0);
        if (h2 >= 0.0f) {
            float rhs = sqrtf(h2);
            float tf = (-O0dO - rhs) * rcp_dOdO;
            if (yp + tf * dOdP < 0.0f) t_sph0_lo = tf;
            float tb = (-O0dO + rhs) * rcp_dOdO;
            if (yp + tb * dOdP < 0.0f) t_sph0_hi = tb;
        }
    }
    float t_sph_lo = fminf(t_sph0_lo, t_sph1_lo);
    float lo = fminf(t_cone_lo, t_sph_lo);
    float t_sph_hi = fmaxf(t_sph0_hi, t_sph1_hi);
    float hi = fmaxf(t_cone_hi, t_sph_hi);
    int lo_valid = (lo != POS_INF) && (dt + lo >= tmin) && (dt + lo < best_t);
    int hi_valid = (hi != NEG_INF) && (dt + hi >= tmin) && (dt + hi < best_t);
    if (!lo_valid && !hi_valid) return false;
    float tloc = lo_valid ? lo : hi;
    float u;
    if (tloc == t_cone_lo || tloc == t_cone_hi) {
        float y = (tloc == t_cone_lo) ? y_cone_lo : y_cone_hi;
        u = g > 0.0f ? y / g : 0.0f;
        u = u < 0.0f ? 0.0f : (u > 1.0f ? 1.0f : u);
    } else if (tloc == t_sph0_lo || tloc == t_sph0_hi) {
        u = 0.0f;
    } else {
        u = 1.0f;
    }
    *t_out = dt + tloc;
    *u_out = u;
    return true;
}

/* ---- cubic Bezier (round) curve, port of tri_bez_isect_one --------------- */
__device__ __forceinline__ void hp_bez_eval(const float cp[16], float u,
                                            float P[4], float dP[4],
                                            float ddP[4]) {
    float u1 = 1.0f - u;
    for (int c = 0; c < 4; c++) {
        float B0 = cp[c], B1 = cp[4 + c], B2 = cp[8 + c], B3 = cp[12 + c];
        P[c] = u1 * u1 * u1 * B0 + 3.0f * u1 * u1 * u * B1 +
               3.0f * u1 * u * u * B2 + u * u * u * B3;
        float e0 = B1 - B0, e1 = B2 - B1, e2 = B3 - B2;
        dP[c] = 3.0f * (u1 * u1 * e0 + 2.0f * u1 * u * e1 + u * u * e2);
        ddP[c] = 6.0f * (u1 * (B2 - 2.0f * B1 + B0) + u * (B3 - 2.0f * B2 + B1));
    }
}

__device__ __forceinline__ bool hp_bez_newton(const float cp[16],
                                              const float dir[3], float tmin,
                                              float u, float t, float best_t,
                                              float *t_out, float *u_out) {
    for (int it = 0; it < 8; it++) {
        float P[4], dP[4], ddP[4];
        hp_bez_eval(cp, u, P, dP, ddP);
        float Rx = t * dir[0] - P[0], Ry = t * dir[1] - P[1],
              Rz = t * dir[2] - P[2];
        float dpd = dP[0] * dP[0] + dP[1] * dP[1] + dP[2] * dP[2];
        if (dpd < 1e-20f) return false;
        float rcpl = 1.0f / sqrtf(dpd);
        float Tx = dP[0] * rcpl, Ty = dP[1] * rcpl, Tz = dP[2] * rcpl;
        float Tdd = Tx * ddP[0] + Ty * ddP[1] + Tz * ddP[2];
        float dTx = (ddP[0] - Tx * Tdd) * rcpl, dTy = (ddP[1] - Ty * Tdd) * rcpl,
              dTz = (ddP[2] - Tz * Tdd) * rcpl;
        float f = Rx * Tx + Ry * Ty + Rz * Tz;
        float dfdu = (-dP[0] * Tx - dP[1] * Ty - dP[2] * Tz) +
                     (Rx * dTx + Ry * dTy + Rz * dTz);
        float dfdt = dir[0] * Tx + dir[1] * Ty + dir[2] * Tz;
        float RR = Rx * Rx + Ry * Ry + Rz * Rz;
        float K = RR - f * f;
        if (K < 1e-20f) K = 1e-20f;
        float sqrtK = sqrtf(K), rsK = 1.0f / sqrtK;
        float r = P[3] > 0.0f ? P[3] : 0.0f;
        float g = sqrtK - r;
        float RdRdu = -(Rx * dP[0] + Ry * dP[1] + Rz * dP[2]);
        float RdRdt = Rx * dir[0] + Ry * dir[1] + Rz * dir[2];
        float dgdu = (RdRdu - f * dfdu) * rsK - dP[3];
        float dgdt = (RdRdt - f * dfdt) * rsK;
        float det = dfdu * dgdt - dfdt * dgdu;
        if (fabsf(det) < 1e-20f) return false;
        float invd = 1.0f / det;
        u -= (dgdt * f - dfdt * g) * invd;
        t -= (dfdu * g - dgdu * f) * invd;
        float lenR = sqrtf(RR);
        float eps = 1e-5f * (1.0f + lenR);
        if (fabsf(f) < eps && fabsf(g) < eps) {
            if (t >= tmin && t < best_t && u >= 0.0f && u <= 1.0f) {
                *t_out = t; *u_out = u; return true;
            }
            return false;
        }
    }
    return false;
}

__device__ __forceinline__ bool hp_cone_seed(const float dir[3], float tmin,
                                             float best, const float p0[3],
                                             float r0, const float p1[3],
                                             float r1, float *t_out,
                                             float *s_out) {
    float dOdO = dir[0] * dir[0] + dir[1] * dir[1] + dir[2] * dir[2];
    if (dOdO <= 0.0f) return false;
    float rcp_dOdO = 1.0f / dOdO;
    float cx = 0.5f * (p0[0] + p1[0]), cy = 0.5f * (p0[1] + p1[1]),
          cz = 0.5f * (p0[2] + p1[2]);
    float dt = (cx * dir[0] + cy * dir[1] + cz * dir[2]) * rcp_dOdO;
    float ox = dt * dir[0], oy = dt * dir[1], oz = dt * dir[2];
    float dPx = p1[0] - p0[0], dPy = p1[1] - p0[1], dPz = p1[2] - p0[2];
    float dPdP = dPx * dPx + dPy * dPy + dPz * dPz;
    float dr = r1 - r0, r0dr = r0 * dr, g = dPdP - dr * dr;
    float Ox = ox - p0[0], Oy = oy - p0[1], Oz = oz - p0[2];
    float OdP = Ox * dPx + Oy * dPy + Oz * dPz;
    float dOdP = dir[0] * dPx + dir[1] * dPy + dir[2] * dPz;
    float yp = OdP + r0dr;
    float lo = best, slo = 0.0f;
    int hit = 0;
    if (g > 0.0f) {
        float OO = Ox * Ox + Oy * Oy + Oz * Oz;
        float OdO = dir[0] * Ox + dir[1] * Oy + dir[2] * Oz;
        float A = g * dOdO - dOdP * dOdP;
        float B = 2.0f * (g * OdO - dOdP * yp);
        float C = g * OO - OdP * OdP - r0 * r0 * dPdP - 2.0f * r0dr * OdP;
        float D = B * B - 4.0f * A * C;
        if (D >= 0.0f && (A > 1e-18f || A < -1e-18f)) {
            float Q = sqrtf(D), rcp2A = 1.0f / (2.0f * A);
            for (int k = 0; k < 2; k++) {
                float tl = (k == 0 ? (-B - Q) : (-B + Q)) * rcp2A;
                float y = yp + tl * dOdP;
                if (y > -1.2e-7f && y <= g) {
                    float tw = dt + tl;
                    if (tw >= tmin && tw < lo) {
                        lo = tw;
                        float s = y / g;
                        slo = s < 0.0f ? 0.0f : (s > 1.0f ? 1.0f : s);
                        hit = 1;
                    }
                }
            }
        }
    }
    for (int e = 0; e < 2; e++) {
        const float *c = e ? p1 : p0;
        float rc2 = e ? r1 : r0;
        float Ex = ox - c[0], Ey = oy - c[1], Ez = oz - c[2];
        float EdO = Ex * dir[0] + Ey * dir[1] + Ez * dir[2];
        float h2 = EdO * EdO - dOdO * (Ex * Ex + Ey * Ey + Ez * Ez - rc2 * rc2);
        if (h2 < 0.0f) continue;
        float tl = (-EdO - sqrtf(h2)) * rcp_dOdO;
        float y = yp + tl * dOdP;
        if (e ? (y > g) : (y < 0.0f)) {
            float tw = dt + tl;
            if (tw >= tmin && tw < lo) { lo = tw; slo = e ? 1.0f : 0.0f; hit = 1; }
        }
    }
    if (hit) { *t_out = lo; *s_out = slo; }
    return hit != 0;
}

/* Adaptive subdivision + cone-seed + Newton (port of tri_bez_isect_one). */
__device__ __forceinline__ bool hp_bez_one(float ox, float oy, float oz,
                                           float dx, float dy, float dz,
                                           const float cp_in[16], float tmin,
                                           float best_t, float *t_out,
                                           float *u_out) {
    float cp[16];
    for (int k = 0; k < 4; k++) {
        cp[k * 4 + 0] = cp_in[k * 4 + 0] - ox;
        cp[k * 4 + 1] = cp_in[k * 4 + 1] - oy;
        cp[k * 4 + 2] = cp_in[k * 4 + 2] - oz;
        cp[k * 4 + 3] = cp_in[k * 4 + 3];
    }
    const float dir[3] = {dx, dy, dz};
    float best = best_t, bu = 0.0f;
    int hit = 0;
    const int BEZ_MAXDEPTH = 5;
    struct { float a, b; int depth; } stk[2 * 5 + 2];
    int sp = 0;
    stk[0].a = 0.0f; stk[0].b = 1.0f; stk[0].depth = 0; sp = 1;
    while (sp > 0) {
        float a = stk[--sp].a, b = stk[sp].b;
        int depth = stk[sp].depth;
        float h = b - a;
        float Pa[4], dPa[4], dda[4], Pb[4], dPb[4], ddb[4];
        hp_bez_eval(cp, a, Pa, dPa, dda);
        hp_bez_eval(cp, b, Pb, dPb, ddb);
        float cxd = Pb[0] - Pa[0], cyd = Pb[1] - Pa[1], czd = Pb[2] - Pa[2];
        float cl2 = cxd * cxd + cyd * cyd + czd * czd;
        float maxperp = 0.0f;
        if (cl2 > 1e-20f) {
            float inv = 1.0f / cl2;
            float mid[2][3] = {
                {Pa[0] + dPa[0] * h / 3.0f, Pa[1] + dPa[1] * h / 3.0f,
                 Pa[2] + dPa[2] * h / 3.0f},
                {Pb[0] - dPb[0] * h / 3.0f, Pb[1] - dPb[1] * h / 3.0f,
                 Pb[2] - dPb[2] * h / 3.0f}};
            for (int m = 0; m < 2; m++) {
                float wx = mid[m][0] - Pa[0], wy = mid[m][1] - Pa[1],
                      wz = mid[m][2] - Pa[2];
                float tt = (wx * cxd + wy * cyd + wz * czd) * inv;
                float ddx = wx - tt * cxd, ddy = wy - tt * cyd,
                      ddz = wz - tt * czd;
                float d2 = ddx * ddx + ddy * ddy + ddz * ddz;
                if (d2 > maxperp) maxperp = d2;
            }
            maxperp = sqrtf(maxperp);
        }
        float r1w = Pa[3] + dPa[3] * h / 3.0f, r2w = Pb[3] - dPb[3] * h / 3.0f;
        float r0c = Pa[3] > r1w ? Pa[3] : r1w;
        float r3c = Pb[3] > r2w ? Pb[3] : r2w;
        r0c = (r0c > 0.0f ? r0c : 0.0f) + maxperp;
        r3c = (r3c > 0.0f ? r3c : 0.0f) + maxperp;
        float rcap = r0c > r3c ? r0c : r3c;
        {
            float a_ = dir[0] * dir[0] + dir[1] * dir[1] + dir[2] * dir[2];
            float bb = dir[0] * cxd + dir[1] * cyd + dir[2] * czd;
            float cc = cl2;
            float w0x = -Pa[0], w0y = -Pa[1], w0z = -Pa[2];
            float dd = dir[0] * w0x + dir[1] * w0y + dir[2] * w0z;
            float ed = cxd * w0x + cyd * w0y + czd * w0z;
            float den = a_ * cc - bb * bb;
            float ss = den > 1e-20f ? (a_ * ed - bb * dd) / den : 0.0f;
            ss = ss < 0.0f ? 0.0f : (ss > 1.0f ? 1.0f : ss);
            float tr = (bb * ss - dd) / (a_ > 1e-20f ? a_ : 1e-20f);
            tr = tr < tmin ? tmin : (tr > best ? best : tr);
            ss = (bb * tr + ed) / (cc > 1e-20f ? cc : 1e-20f);
            ss = ss < 0.0f ? 0.0f : (ss > 1.0f ? 1.0f : ss);
            float gx = tr * dir[0] - (Pa[0] + ss * cxd);
            float gy = tr * dir[1] - (Pa[1] + ss * cyd);
            float gz = tr * dir[2] - (Pa[2] + ss * czd);
            if (gx * gx + gy * gy + gz * gz > rcap * rcap) continue;
        }
        if (depth >= BEZ_MAXDEPTH) {
            if (r0c > 0.0f || r3c > 0.0f) {
                float P0p[3] = {Pa[0], Pa[1], Pa[2]};
                float P3p[3] = {Pb[0], Pb[1], Pb[2]};
                float tseg, s;
                if (hp_cone_seed(dir, tmin, best, P0p, r0c, P3p, r3c, &tseg,
                                 &s)) {
                    float th, uh;
                    if (hp_bez_newton(cp, dir, tmin, a + s * h, tseg, best, &th,
                                      &uh)) {
                        best = th; bu = uh; hit = 1;
                    } else {
                        best = tseg; bu = a + s * h; hit = 1;
                    }
                }
            }
        } else {
            float m = 0.5f * (a + b);
            stk[sp].a = a; stk[sp].b = m; stk[sp].depth = depth + 1; sp++;
            stk[sp].a = m; stk[sp].b = b; stk[sp].depth = depth + 1; sp++;
        }
    }
    if (hit) { *t_out = best; *u_out = bu; }
    return hit != 0;
}

/* ---- built-in SDF / implicit primitives (port of tri_sdf_*) -------------- */
__device__ __forceinline__ float hp_sdf_eval(uint32_t type, float px, float py,
                                             float pz, float p0, float p1,
                                             float p2) {
    if (type == HIP_SDF_SPHERE) return sqrtf(px * px + py * py + pz * pz) - p0;
    if (type == HIP_SDF_BOX) {
        float qx = fabsf(px) - p0, qy = fabsf(py) - p1, qz = fabsf(pz) - p2;
        float mx = fmaxf(qx, 0.0f), my = fmaxf(qy, 0.0f), mz = fmaxf(qz, 0.0f);
        float outside = sqrtf(mx * mx + my * my + mz * mz);
        float inside = fminf(fmaxf(qx, fmaxf(qy, qz)), 0.0f);
        return outside + inside;
    }
    float lxz = sqrtf(px * px + pz * pz) - p0;
    return sqrtf(lxz * lxz + py * py) - p1;
}

__device__ __forceinline__ bool hp_sdf_one(float ox, float oy, float oz,
                                           float dx, float dy, float dz,
                                           float cx, float cy, float cz,
                                           float brad, uint32_t type, float p0,
                                           float p1, float p2, float tmin,
                                           float best_t, float *t_out) {
    float dOdO = dx * dx + dy * dy + dz * dz;
    if (dOdO <= 1e-20f || brad <= 0.0f) return false;
    float ocx = ox - cx, ocy = oy - cy, ocz = oz - cz;
    float b = ocx * dx + ocy * dy + ocz * dz;
    float c = ocx * ocx + ocy * ocy + ocz * ocz - brad * brad;
    float disc = b * b - dOdO * c;
    if (disc < 0.0f) return false;
    float sq = sqrtf(disc), inv = 1.0f / dOdO;
    float t0 = (-b - sq) * inv, t1 = (-b + sq) * inv;
    float tlo = fmaxf(tmin, t0), thi = fminf(best_t, t1);
    if (tlo >= thi) return false;
    float invdl = 1.0f / sqrtf(dOdO);
    float t = tlo;
    for (int i = 0; i < 128; i++) {
        float px = ox + t * dx - cx, py = oy + t * dy - cy,
              pz = oz + t * dz - cz;
        float d = hp_sdf_eval(type, px, py, pz, p0, p1, p2);
        if (d < 1e-4f) { *t_out = t; return true; }
        t += d * invdl;
        if (t >= thi) break;
    }
    return false;
}

/* One leaf block (4 lanes) against the ray, for the given prim_kind. blk = base
 * word index of the block; bsw = block stride in words. Updates best_*. */
__device__ __forceinline__ void hp_leaf(const uint32_t *__restrict__ blocks,
                                        uint32_t blk, uint32_t prim_kind,
                                        uint32_t point_type, float ox, float oy,
                                        float oz, float dx, float dy, float dz,
                                        float tmin, float *best_t, float *best_u,
                                        float *best_v, uint32_t *best_prim) {
    if (prim_kind == HIP_PRIM_SPHERE) {
        for (uint32_t l = 0; l < 4u; l++) {
            uint32_t prim = blocks[blk + 16u + l];
            if (prim == LRT_HIP_NO_HIT) continue;
            float cx = fu(blocks[blk + 0u + l]), cy = fu(blocks[blk + 4u + l]),
                  cz = fu(blocks[blk + 8u + l]), r = fu(blocks[blk + 12u + l]);
            if (r <= 0.0f) continue;
            float ocx = ox - cx, ocy = oy - cy, ocz = oz - cz;
            float a = dx * dx + dy * dy + dz * dz;
            if (a <= 1e-20f) continue;
            float b = ocx * dx + ocy * dy + ocz * dz;
            float c = ocx * ocx + ocy * ocy + ocz * ocz - r * r;
            float disc = b * b - a * c;
            if (disc < 0.0f) continue;
            float sq = sqrtf(disc), inv_a = 1.0f / a;
            float tt = (-b - sq) * inv_a;
            if (tt < tmin || tt >= *best_t) {
                tt = (-b + sq) * inv_a;
                if (tt < tmin || tt >= *best_t) continue;
            }
            float nx = (ocx + tt * dx) / r, ny = (ocy + tt * dy) / r,
                  nz = (ocz + tt * dz) / r;
            float cl = ny < -1.0f ? -1.0f : (ny > 1.0f ? 1.0f : ny);
            *best_t = tt;
            *best_u = atan2f(nz, nx) * HIP_INV_2PI + 0.5f;
            *best_v = acosf(cl) * HIP_INV_PI;
            *best_prim = prim;
        }
    } else if (prim_kind == HIP_PRIM_POINT) {
        for (uint32_t l = 0; l < 4u; l++) {
            uint32_t prim = blocks[blk + 28u + l];
            if (prim == LRT_HIP_NO_HIT) continue;
            float cx = fu(blocks[blk + 0u + l]), cy = fu(blocks[blk + 4u + l]),
                  cz = fu(blocks[blk + 8u + l]), r = fu(blocks[blk + 12u + l]);
            float dOdO = dx * dx + dy * dy + dz * dz;
            if (dOdO <= 0.0f) continue;
            float c0x = cx - ox, c0y = cy - oy, c0z = cz - oz;
            if (point_type == HIP_POINT_ORIENTED_DISC) {
                float nx = fu(blocks[blk + 16u + l]),
                      ny = fu(blocks[blk + 20u + l]),
                      nz = fu(blocks[blk + 24u + l]);
                float div = dx * nx + dy * ny + dz * nz;
                if (div == 0.0f) continue;
                float t = (c0x * nx + c0y * ny + c0z * nz) / div;
                if (t < tmin || t >= *best_t) continue;
                float hx = ox + t * dx - cx, hy = oy + t * dy - cy,
                      hz = oz + t * dz - cz;
                if (hx * hx + hy * hy + hz * hz >= r * r) continue;
                *best_t = t; *best_u = 0.0f; *best_v = 0.0f; *best_prim = prim;
                continue;
            }
            float rd2 = 1.0f / dOdO;
            float projC0 = (c0x * dx + c0y * dy + c0z * dz) * rd2;
            float perpx = c0x - projC0 * dx, perpy = c0y - projC0 * dy,
                  perpz = c0z - projC0 * dz;
            float l2 = perpx * perpx + perpy * perpy + perpz * perpz;
            float r2 = r * r;
            if (l2 > r2) continue;
            if (point_type == HIP_POINT_DISC) {
                if (projC0 < tmin || projC0 >= *best_t) continue;
                *best_t = projC0; *best_u = 0.0f; *best_v = 0.0f;
                *best_prim = prim;
                continue;
            }
            float td = sqrtf((r2 - l2) * rd2);
            float tf = projC0 - td;
            if (tf >= tmin && tf < *best_t) {
                *best_t = tf; *best_u = 0.0f; *best_v = 0.0f; *best_prim = prim;
                continue;
            }
            float tb = projC0 + td;
            if (tb >= tmin && tb < *best_t) {
                *best_t = tb; *best_u = 0.0f; *best_v = 0.0f; *best_prim = prim;
            }
        }
    } else if (prim_kind == HIP_PRIM_FLATCURVE) { /* lrt_flat4: 36 words */
        for (uint32_t l = 0; l < 4u; l++) {
            uint32_t prim = blocks[blk + 32u + l];
            if (prim == LRT_HIP_NO_HIT) continue;
            float p0[3] = {fu(blocks[blk + 0u + l]), fu(blocks[blk + 4u + l]),
                           fu(blocks[blk + 8u + l])};
            float r0 = fu(blocks[blk + 12u + l]);
            float p1[3] = {fu(blocks[blk + 16u + l]), fu(blocks[blk + 20u + l]),
                           fu(blocks[blk + 24u + l])};
            float r1 = fu(blocks[blk + 28u + l]);
            float t, u;
            if (hp_flat_one(ox, oy, oz, dx, dy, dz, p0, r0, p1, r1, tmin,
                            *best_t, &t, &u)) {
                *best_t = t; *best_u = u; *best_v = 0.0f; *best_prim = prim;
            }
        }
    } else if (prim_kind == HIP_PRIM_RLCURVE) { /* lrt_rlc4: 68 words */
        for (uint32_t l = 0; l < 4u; l++) {
            uint32_t prim = blocks[blk + 64u + l];
            if (prim == LRT_HIP_NO_HIT) continue;
            float p0[3] = {fu(blocks[blk + 0u + l]), fu(blocks[blk + 4u + l]),
                           fu(blocks[blk + 8u + l])};
            float r0 = fu(blocks[blk + 12u + l]);
            float p1[3] = {fu(blocks[blk + 16u + l]), fu(blocks[blk + 20u + l]),
                           fu(blocks[blk + 24u + l])};
            float r1 = fu(blocks[blk + 28u + l]);
            float pL[3] = {fu(blocks[blk + 32u + l]), fu(blocks[blk + 36u + l]),
                           fu(blocks[blk + 40u + l])};
            float rL = fu(blocks[blk + 44u + l]);
            float pR[3] = {fu(blocks[blk + 48u + l]), fu(blocks[blk + 52u + l]),
                           fu(blocks[blk + 56u + l])};
            float rR = fu(blocks[blk + 60u + l]);
            float t, u;
            if (hp_rlc_one(ox, oy, oz, dx, dy, dz, p0, r0, p1, r1, pL, rL, pR,
                           rR, tmin, *best_t, &t, &u)) {
                *best_t = t; *best_u = u; *best_v = 0.0f; *best_prim = prim;
            }
        }
    } else if (prim_kind == HIP_PRIM_SDF) { /* lrt_sdf4: 36 words */
        for (uint32_t l = 0; l < 4u; l++) {
            uint32_t prim = blocks[blk + 32u + l];
            if (prim == LRT_HIP_NO_HIT) continue;
            float cx = fu(blocks[blk + 0u + l]), cy = fu(blocks[blk + 4u + l]),
                  cz = fu(blocks[blk + 8u + l]), brad = fu(blocks[blk + 12u + l]);
            uint32_t type = blocks[blk + 16u + l];
            float p0 = fu(blocks[blk + 20u + l]), p1 = fu(blocks[blk + 24u + l]),
                  p2 = fu(blocks[blk + 28u + l]);
            float t;
            if (hp_sdf_one(ox, oy, oz, dx, dy, dz, cx, cy, cz, brad, type, p0,
                           p1, p2, tmin, *best_t, &t)) {
                *best_t = t; *best_u = 0.0f; *best_v = 0.0f; *best_prim = prim;
            }
        }
    } else if (prim_kind == HIP_PRIM_BEZCURVE) { /* lrt_bez4: 68 words */
        for (uint32_t l = 0; l < 4u; l++) {
            uint32_t prim = blocks[blk + 64u + l];
            if (prim == LRT_HIP_NO_HIT) continue;
            float cp[16];
            for (int k = 0; k < 4; k++) {
                cp[k * 4 + 0] = fu(blocks[blk + (uint32_t)(k * 16 + 0) + l]);
                cp[k * 4 + 1] = fu(blocks[blk + (uint32_t)(k * 16 + 4) + l]);
                cp[k * 4 + 2] = fu(blocks[blk + (uint32_t)(k * 16 + 8) + l]);
                cp[k * 4 + 3] = fu(blocks[blk + (uint32_t)(k * 16 + 12) + l]);
            }
            float t, u;
            if (hp_bez_one(ox, oy, oz, dx, dy, dz, cp, tmin, *best_t, &t, &u)) {
                *best_t = t; *best_u = u; *best_v = 0.0f; *best_prim = prim;
            }
        }
    } else { /* QUAD or TETRA: 4-point leaf (52 words) */
        for (uint32_t l = 0; l < 4u; l++) {
            uint32_t prim = blocks[blk + 48u + l];
            if (prim == LRT_HIP_NO_HIT) continue;
            float x0 = fu(blocks[blk + 0u + l]), y0 = fu(blocks[blk + 4u + l]),
                  z0 = fu(blocks[blk + 8u + l]);
            float x1 = fu(blocks[blk + 12u + l]), y1 = fu(blocks[blk + 16u + l]),
                  z1 = fu(blocks[blk + 20u + l]);
            float x2 = fu(blocks[blk + 24u + l]), y2 = fu(blocks[blk + 28u + l]),
                  z2 = fu(blocks[blk + 32u + l]);
            float x3 = fu(blocks[blk + 36u + l]), y3 = fu(blocks[blk + 40u + l]),
                  z3 = fu(blocks[blk + 44u + l]);
            float t, u, v;
            if (prim_kind == HIP_PRIM_QUAD) {
                if (hp_mt(ox, oy, oz, dx, dy, dz, x0, y0, z0, x1, y1, z1, x2, y2,
                          z2, tmin, *best_t, &t, &u, &v)) {
                    *best_t = t; *best_u = u; *best_v = v; *best_prim = prim;
                }
                if (hp_mt(ox, oy, oz, dx, dy, dz, x0, y0, z0, x2, y2, z2, x3, y3,
                          z3, tmin, *best_t, &t, &u, &v)) {
                    *best_t = t; *best_u = u; *best_v = v; *best_prim = prim;
                }
            } else { /* TETRA: 4 faces (0,1,2)(0,1,3)(0,2,3)(1,2,3) */
                float P[4][3] = {{x0, y0, z0}, {x1, y1, z1},
                                 {x2, y2, z2}, {x3, y3, z3}};
                const int F[4][3] = {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}};
                for (int f = 0; f < 4; f++) {
                    if (hp_mt(ox, oy, oz, dx, dy, dz, P[F[f][0]][0],
                              P[F[f][0]][1], P[F[f][0]][2], P[F[f][1]][0],
                              P[F[f][1]][1], P[F[f][1]][2], P[F[f][2]][0],
                              P[F[f][2]][1], P[F[f][2]][2], tmin, *best_t, &t,
                              &u, &v)) {
                        *best_t = t; *best_u = u; *best_v = v; *best_prim = prim;
                    }
                }
            }
        }
    }
}

/* BVH4 analytic-primitive closest-hit (node_stride = 32 words; runtime kind). */
template <unsigned STACK>
__launch_bounds__(64) __global__
    void k_trace_prim(const uint32_t *__restrict__ nodes,
                      const uint32_t *__restrict__ blocks,
                      const uint32_t *__restrict__ rays,
                      uint32_t *__restrict__ hits, uint32_t root,
                      uint32_t ray_count, uint32_t prim_kind,
                      uint32_t point_type, uint32_t bsw) {
    const uint32_t gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= ray_count) return;
    constexpr uint32_t W = 4u, node_stride = 8u * W;
    const size_t rb = (size_t)gid * 8u;
    float ox = fu(rays[rb + 0]), oy = fu(rays[rb + 1]), oz = fu(rays[rb + 2]);
    float tmin = fu(rays[rb + 3]);
    float dx = fu(rays[rb + 4]), dy = fu(rays[rb + 5]), dz = fu(rays[rb + 6]);
    float tmax = fu(rays[rb + 7]);
    float invd[3];
    float dd[3] = {dx, dy, dz};
    for (int k = 0; k < 3; k++) {
        float d = dd[k], inv = 1.0f / d;
        if (!(inv >= -LRT_HIP_INVD_MAX && inv <= LRT_HIP_INVD_MAX)) {
            float s = (d == 0.0f) ? 1.0f : d;
            inv = (s < 0.0f) ? -LRT_HIP_INVD_MAX : LRT_HIP_INVD_MAX;
        }
        invd[k] = inv;
    }
    float invdx = invd[0], invdy = invd[1], invdz = invd[2];
    float best_t = tmax, best_u = 0.0f, best_v = 0.0f;
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
        if (stk_tn[sp] >= best_t) continue;
        if ((ref & LRT_HIP_LEAF_BIT) != 0u) {
            uint32_t blk0 = (ref & 0x7FFFFFFFu) >> 4u, nblk = ref & 0xFu;
            for (uint32_t b = 0; b < nblk; b++)
                hp_leaf(blocks, (blk0 + b) * bsw, prim_kind, point_type, ox, oy,
                        oz, dx, dy, dz, tmin, &best_t, &best_u, &best_v,
                        &best_prim);
            continue;
        }
        size_t nb = (size_t)(ref & 0x7FFFFFFFu) * node_stride;
        uint32_t nchildren = nodes[nb + 7u * W];
        uint32_t hit_ref[4];
        float hit_tn[4];
        int nhit = 0;
        for (uint32_t i = 0; i < nchildren; i++) {
            float lo_x = fu(nodes[nb + 0u * W + i]), lo_y = fu(nodes[nb + 1u * W + i]),
                  lo_z = fu(nodes[nb + 2u * W + i]);
            float hi_x = fu(nodes[nb + 3u * W + i]), hi_y = fu(nodes[nb + 4u * W + i]),
                  hi_z = fu(nodes[nb + 5u * W + i]);
            float tlx = (lo_x - ox) * invdx, thx = (hi_x - ox) * invdx;
            float tly = (lo_y - oy) * invdy, thy = (hi_y - oy) * invdy;
            float tlz = (lo_z - oz) * invdz, thz = (hi_z - oz) * invdz;
            float tnear = fmaxf(fmaxf(fminf(tlx, thx), fminf(tly, thy)),
                                fmaxf(fminf(tlz, thz), tmin));
            float tfar = fminf(fminf(fmaxf(tlx, thx), fmaxf(tly, thy)),
                               fminf(fmaxf(tlz, thz), best_t));
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
        if ((uint32_t)sp + (uint32_t)nhit > STACK) break;
        for (int i = nhit - 1; i >= 0; i--) {
            stk_ref[sp] = hit_ref[i];
            stk_tn[sp] = hit_tn[i];
            sp++;
        }
    }
    uint32_t hb = gid * 4u;
    hits[hb + 0] = __float_as_uint(best_prim != LRT_HIP_NO_HIT ? best_t : 0.0f);
    hits[hb + 1] = __float_as_uint(best_u);
    hits[hb + 2] = __float_as_uint(best_v);
    hits[hb + 3] = best_prim;
}

/* BVH4 analytic-primitive any-hit (occlusion). */
template <unsigned STACK>
__launch_bounds__(64) __global__
    void k_occluded_prim(const uint32_t *__restrict__ nodes,
                         const uint32_t *__restrict__ blocks,
                         const uint32_t *__restrict__ rays,
                         uint8_t *__restrict__ occ, uint32_t root,
                         uint32_t ray_count, uint32_t prim_kind,
                         uint32_t point_type, uint32_t bsw) {
    const uint32_t gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= ray_count) return;
    constexpr uint32_t W = 4u, node_stride = 8u * W;
    const size_t rb = (size_t)gid * 8u;
    float ox = fu(rays[rb + 0]), oy = fu(rays[rb + 1]), oz = fu(rays[rb + 2]);
    float tmin = fu(rays[rb + 3]);
    float dx = fu(rays[rb + 4]), dy = fu(rays[rb + 5]), dz = fu(rays[rb + 6]);
    float tmax = fu(rays[rb + 7]);
    float invd[3];
    float dd[3] = {dx, dy, dz};
    for (int k = 0; k < 3; k++) {
        float d = dd[k], inv = 1.0f / d;
        if (!(inv >= -LRT_HIP_INVD_MAX && inv <= LRT_HIP_INVD_MAX)) {
            float s = (d == 0.0f) ? 1.0f : d;
            inv = (s < 0.0f) ? -LRT_HIP_INVD_MAX : LRT_HIP_INVD_MAX;
        }
        invd[k] = inv;
    }
    float invdx = invd[0], invdy = invd[1], invdz = invd[2];
    uint8_t hit = 0u;
    uint32_t stk_ref[STACK];
    int sp = 0;
    stk_ref[0] = root;
    sp = 1;
    while (sp > 0 && !hit) {
        uint32_t ref = stk_ref[--sp];
        if ((ref & LRT_HIP_LEAF_BIT) != 0u) {
            uint32_t blk0 = (ref & 0x7FFFFFFFu) >> 4u, nblk = ref & 0xFu;
            for (uint32_t b = 0; b < nblk && !hit; b++) {
                float bt = tmax, bu = 0.0f, bv = 0.0f;
                uint32_t bp = LRT_HIP_NO_HIT;
                hp_leaf(blocks, (blk0 + b) * bsw, prim_kind, point_type, ox, oy,
                        oz, dx, dy, dz, tmin, &bt, &bu, &bv, &bp);
                if (bp != LRT_HIP_NO_HIT) hit = 1u;
            }
            continue;
        }
        size_t nb = (size_t)(ref & 0x7FFFFFFFu) * node_stride;
        uint32_t nchildren = nodes[nb + 7u * W];
        for (uint32_t i = 0; i < nchildren; i++) {
            float lo_x = fu(nodes[nb + 0u * W + i]), lo_y = fu(nodes[nb + 1u * W + i]),
                  lo_z = fu(nodes[nb + 2u * W + i]);
            float hi_x = fu(nodes[nb + 3u * W + i]), hi_y = fu(nodes[nb + 4u * W + i]),
                  hi_z = fu(nodes[nb + 5u * W + i]);
            float tlx = (lo_x - ox) * invdx, thx = (hi_x - ox) * invdx;
            float tly = (lo_y - oy) * invdy, thy = (hi_y - oy) * invdy;
            float tlz = (lo_z - oz) * invdz, thz = (hi_z - oz) * invdz;
            float tnear = fmaxf(fmaxf(fminf(tlx, thx), fminf(tly, thy)),
                                fmaxf(fminf(tlz, thz), tmin));
            float tfar = fminf(fminf(fmaxf(tlx, thx), fmaxf(tly, thy)),
                               fminf(fmaxf(tlz, thz), tmax));
            if (tnear <= tfar) {
                if ((uint32_t)sp >= STACK) { hit = 1u; break; }
                stk_ref[sp++] = nodes[nb + 6u * W + i];
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
    size_t vb = (size_t)i * 9u;
    for (uint32_t a = 0u; a < 3u; a++) {
        float v0 = verts[vb + 0u + a];
        float v1 = verts[vb + 3u + a];
        float v2 = verts[vb + 6u + a];
        float lo = fminf(v0, fminf(v1, v2));
        float hi = fmaxf(v0, fmaxf(v1, v2));
        centroids[(size_t)i * 3u + a] = 0.5f * (lo + hi);
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
        float c = centroids[(size_t)i * 3u + a];
        float fv = (c - base[a]) * scale[a];
        int qi = (int)fv; /* truncation toward zero, matches (int32_t)v */
        if (qi < 0) qi = 0;
        if (qi > 1023) qi = 1023;
        q[a] = (uint32_t)qi;
    }
    morton[i] = (expand10(q[0]) << 2) | (expand10(q[1]) << 1) | expand10(q[2]);
}

/* ========================================================================= */
/* GPU primary-ray generation (pinhole camera) -> device ray buffer.           */
/* ========================================================================= */
__global__ void k_raygen_camera(uint32_t *__restrict__ rays, uint32_t width,
                                uint32_t height, float ox, float oy, float oz,
                                float llx, float lly, float llz, float hx,
                                float hy, float hz, float vx, float vy, float vz,
                                float tmin, float tmax) {
    uint32_t gid = blockIdx.x * blockDim.x + threadIdx.x;
    uint32_t n = width * height;
    if (gid >= n) return;
    uint32_t px = gid % width, py = gid / width;
    float sx = ((float)px + 0.5f) / (float)width;
    float sy = ((float)py + 0.5f) / (float)height;
    float dx = llx + sx * hx + sy * vx - ox;
    float dy = lly + sx * hy + sy * vy - oy;
    float dz = llz + sx * hz + sy * vz - oz;
    size_t rb = (size_t)gid * 8u;
    rays[rb + 0] = __float_as_uint(ox);
    rays[rb + 1] = __float_as_uint(oy);
    rays[rb + 2] = __float_as_uint(oz);
    rays[rb + 3] = __float_as_uint(tmin);
    rays[rb + 4] = __float_as_uint(dx);
    rays[rb + 5] = __float_as_uint(dy);
    rays[rb + 6] = __float_as_uint(dz);
    rays[rb + 7] = __float_as_uint(tmax);
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
    size_t bb = (size_t)b * block_stride;
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
    size_t nb = (size_t)n * node_stride;
    uint32_t nchildren = nodes[nb + 7u * W];
    for (uint32_t i = 0; i < nchildren; i++) {
        uint32_t ref = nodes[nb + 6u * W + i];
        float lo0 = 1e30f, lo1 = 1e30f, lo2 = 1e30f;
        float hi0 = -1e30f, hi1 = -1e30f, hi2 = -1e30f;
        if ((ref & LRT_HIP_LEAF_BIT) != 0u) {
            uint32_t blk0 = (ref & 0x7FFFFFFFu) >> 4u;
            uint32_t nblk = ref & 0xFu;
            for (uint32_t b = 0; b < nblk; b++) {
                size_t bb = (size_t)(blk0 + b) * block_stride;
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
            size_t cb = (size_t)c * node_stride;
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

static hipError_t launch_trace(lrt_hip_engine *e, const lrt_hip_scene *s,
                               const uint32_t *d_rays, uint32_t *d_hits,
                               uint32_t n) {
    const uint32_t W = s->layout, S = s->stack, root = s->root;
    if (s->prim_kind != HIP_PRIM_TRI) {
        uint32_t bsw = s->block_stride / 4u; /* block stride in words */
#define LAUNCHP(st)                                                            \
    hipLaunchKernelGGL((k_trace_prim<st>), dim3(((n) + 63u) / 64u), dim3(64),  \
                       0, e->stream, s->d_nodes, s->d_blocks, d_rays, d_hits,  \
                       root, n, s->prim_kind, s->point_type, bsw)
        if (S == 32u) LAUNCHP(32);
        else if (S == 64u) LAUNCHP(64);
        else if (S == 128u) LAUNCHP(128);
        else LAUNCHP(256);
#undef LAUNCHP
        return hipGetLastError();
    }
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
    if (s->prim_kind != HIP_PRIM_TRI) {
        uint32_t bsw = s->block_stride / 4u;
#define LAUNCHP(st)                                                            \
    hipLaunchKernelGGL((k_occluded_prim<st>), dim3(((n) + 63u) / 64u),         \
                       dim3(64), 0, e->stream, s->d_nodes, s->d_blocks, d_rays, \
                       d_occ, root, n, s->prim_kind, s->point_type, bsw)
        if (S == 32u) LAUNCHP(32);
        else if (S == 64u) LAUNCHP(64);
        else if (S == 128u) LAUNCHP(128);
        else LAUNCHP(256);
#undef LAUNCHP
        return hipGetLastError();
    }
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

/* Internal: expose the engine stream to other HIP TUs (lightrt_hip_wmma.hip,
 * lightrt_hip_lbvh.hip) without sharing the struct definition. Not public. */
extern "C" void *lrt_hip_engine_stream_(const lrt_hip_engine *e) {
    return e ? (void *)e->stream : NULL;
}

/* Internal: wrap GPU-built device buffers in a resident scene (lrt_hip_scene_free
 * owns/frees d_nodes and d_blocks). Used by the full-GPU LBVH builder. */
extern "C" lrt_hip_scene *lrt_hip_scene_make_(uint32_t *d_nodes,
                                              uint32_t *d_blocks,
                                              uint32_t node_count,
                                              uint32_t block_count,
                                              uint32_t node_stride,
                                              uint32_t block_stride,
                                              uint32_t root, uint32_t layout,
                                              uint32_t stack,
                                              uint32_t max_depth) {
    lrt_hip_scene *sc = (lrt_hip_scene *)calloc(1, sizeof(lrt_hip_scene));
    if (!sc) return NULL;
    sc->d_nodes = d_nodes;
    sc->d_blocks = d_blocks;
    sc->node_count = node_count;
    sc->block_count = block_count;
    sc->node_stride = node_stride;
    sc->block_stride = block_stride;
    sc->root = root;
    sc->layout = layout;
    sc->stack = stack;
    sc->max_depth = max_depth;
    sc->mem_bytes = (size_t)node_count * node_stride +
                    (size_t)block_count * block_stride;
    return sc;
}

/* Grow a device scratch buffer to at least `need` bytes. */
static int hip_grow(lrt_hip_engine *e, void **buf, size_t *cap, size_t need) {
    (void)e;
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
    /* Supported on GPU: triangles (BVH4/BVH8) + analytic/curve BVH4 prims
     * (sphere/point/quad/tetra/round-linear/flat). Bezier is Phase D. */
    uint32_t pk = h->prim_kind;
    int bvh4_prim = (pk == HIP_PRIM_SPHERE || pk == HIP_PRIM_POINT ||
                     pk == HIP_PRIM_QUAD || pk == HIP_PRIM_TETRA ||
                     pk == HIP_PRIM_RLCURVE || pk == HIP_PRIM_FLATCURVE ||
                     pk == HIP_PRIM_BEZCURVE || pk == HIP_PRIM_SDF);
    if (pk != HIP_PRIM_TRI && !bvh4_prim) {
        free(blob);
        hip_set_err(e, "prim_kind not GPU-traceable (user/sdf/qtri)");
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return NULL;
    }
    if (bvh4_prim && w != 4u) {
        free(blob);
        hip_set_err(e, "non-triangle primitives are BVH4 only");
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
    sc->prim_kind = pk;
    sc->point_type = h->reserved0;

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

/* Enqueue the refit kernels (leaf rewrite + bottom-up bounds) against a DEVICE
 * vertex buffer. No allocation, copy, or sync — the caller owns those. */
static void refit_core(lrt_hip_engine *e, lrt_hip_scene *s,
                       const float *d_verts, uint32_t ntris) {
    const uint32_t W = s->layout;
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
}

extern "C" int lrt_hip_scene_refit(lrt_hip_engine *e, lrt_hip_scene *s,
                                   const float *vertices, uint32_t ntris,
                                   lrt_result *err) {
    if (!e || !s || !vertices || ntris == 0 || s->prim_kind != HIP_PRIM_TRI) {
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
    refit_core(e, s, d_verts, ntris);
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

/* ========================================================================= */
/* Fully GPU-resident dynamic pipeline (no per-frame PCIe readback).          */
/* ========================================================================= */
struct lrt_hip_dbuffer {
    void *ptr;
    size_t size;
};

extern "C" lrt_hip_dbuffer *lrt_hip_dbuffer_alloc(lrt_hip_engine *e,
                                                  size_t bytes,
                                                  lrt_result *err) {
    if (!e || bytes == 0) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return NULL;
    }
    lrt_hip_dbuffer *b = (lrt_hip_dbuffer *)calloc(1, sizeof(lrt_hip_dbuffer));
    if (!b) {
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return NULL;
    }
    if (hipMalloc(&b->ptr, bytes) != hipSuccess) {
        free(b);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return NULL;
    }
    b->size = bytes;
    if (err) *err = LRT_RESULT_OK;
    return b;
}

extern "C" void lrt_hip_dbuffer_free(lrt_hip_engine *e, lrt_hip_dbuffer *b) {
    (void)e;
    if (!b) return;
    hip_free(b->ptr);
    free(b);
}

extern "C" void *lrt_hip_dbuffer_ptr(lrt_hip_dbuffer *b) {
    return b ? b->ptr : NULL;
}

extern "C" size_t lrt_hip_dbuffer_size(const lrt_hip_dbuffer *b) {
    return b ? b->size : 0;
}

extern "C" int lrt_hip_dbuffer_upload(lrt_hip_engine *e, lrt_hip_dbuffer *b,
                                      const void *src, size_t bytes,
                                      lrt_result *err) {
    if (!e || !b || !src || bytes > b->size) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    hipError_t hr = hipMemcpy(b->ptr, src, bytes, hipMemcpyHostToDevice);
    if (hr != hipSuccess) {
        hip_set_err_hip(e, "dbuffer upload", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return -1;
    }
    if (err) *err = LRT_RESULT_OK;
    return 0;
}

extern "C" int lrt_hip_dbuffer_download(lrt_hip_engine *e,
                                        const lrt_hip_dbuffer *b, void *dst,
                                        size_t bytes, lrt_result *err) {
    if (!e || !b || !dst || bytes > b->size) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    hipError_t hr = hipMemcpy(dst, b->ptr, bytes, hipMemcpyDeviceToHost);
    if (hr != hipSuccess) {
        hip_set_err_hip(e, "dbuffer download", hr);
        if (err) *err = LRT_RESULT_OUT_OF_MEMORY;
        return -1;
    }
    if (err) *err = LRT_RESULT_OK;
    return 0;
}

extern "C" int lrt_hip_raygen_camera(lrt_hip_engine *e, lrt_hip_dbuffer *rays,
                                     uint32_t width, uint32_t height,
                                     const float origin[3],
                                     const float lower_left[3],
                                     const float horizontal[3],
                                     const float vertical[3], float tmin,
                                     float tmax, lrt_result *err) {
    uint32_t n = width * height;
    if (!e || !rays || n == 0 || rays->size < (size_t)n * sizeof(lrt_ray)) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    hipLaunchKernelGGL(k_raygen_camera, dim3((n + 63u) / 64u), dim3(64), 0,
                       e->stream, (uint32_t *)rays->ptr, width, height,
                       origin[0], origin[1], origin[2], lower_left[0],
                       lower_left[1], lower_left[2], horizontal[0],
                       horizontal[1], horizontal[2], vertical[0], vertical[1],
                       vertical[2], tmin, tmax);
    hipError_t hr = hipGetLastError();
    if (hr != hipSuccess) {
        hip_set_err_hip(e, "k_raygen_camera", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
    if (err) *err = LRT_RESULT_OK;
    return 0;
}

extern "C" int lrt_hip_scene_trace_device(lrt_hip_engine *e, lrt_hip_scene *s,
                                          const lrt_hip_dbuffer *rays,
                                          uint32_t n, lrt_hip_dbuffer *hits,
                                          lrt_result *err) {
    if (!e || !s || !rays || !hits || n == 0 ||
        rays->size < (size_t)n * sizeof(lrt_ray) ||
        hits->size < (size_t)n * sizeof(lrt_hit)) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    hipError_t hr = launch_trace(e, s, (const uint32_t *)rays->ptr,
                                 (uint32_t *)hits->ptr, n);
    if (hr != hipSuccess) {
        hip_set_err_hip(e, "k_trace launch (device)", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
    if ((hr = hipStreamSynchronize(e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipStreamSynchronize", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
    if (err) *err = LRT_RESULT_OK;
    return 0;
}

extern "C" int lrt_hip_scene_occluded_device(lrt_hip_engine *e,
                                             lrt_hip_scene *s,
                                             const lrt_hip_dbuffer *rays,
                                             uint32_t n,
                                             lrt_hip_dbuffer *occluded,
                                             lrt_result *err) {
    if (!e || !s || !rays || !occluded || n == 0 ||
        rays->size < (size_t)n * sizeof(lrt_ray) ||
        occluded->size < (size_t)n) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    hipError_t hr = launch_occluded(e, s, (const uint32_t *)rays->ptr,
                                    (uint8_t *)occluded->ptr, n);
    if (hr != hipSuccess) {
        hip_set_err_hip(e, "k_occluded launch (device)", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
    if ((hr = hipStreamSynchronize(e->stream)) != hipSuccess) {
        hip_set_err_hip(e, "hipStreamSynchronize", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
    if (err) *err = LRT_RESULT_OK;
    return 0;
}

extern "C" int lrt_hip_scene_refit_device(lrt_hip_engine *e, lrt_hip_scene *s,
                                          const lrt_hip_dbuffer *vertices,
                                          uint32_t ntris, lrt_result *err) {
    if (!e || !s || !vertices || ntris == 0 || s->prim_kind != HIP_PRIM_TRI ||
        vertices->size < (size_t)ntris * 9u * sizeof(float)) {
        if (err) *err = LRT_RESULT_INVALID_ARGUMENT;
        return -1;
    }
    refit_core(e, s, (const float *)vertices->ptr, ntris);
    hipError_t hr = hipStreamSynchronize(e->stream);
    if (hr != hipSuccess) {
        hip_set_err_hip(e, "hipStreamSynchronize(refit_device)", hr);
        if (err) *err = LRT_RESULT_NOT_BUILT;
        return -1;
    }
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
