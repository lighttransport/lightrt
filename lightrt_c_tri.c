/*
 * lightrt_c_tri.c — C11 triangle-native fp32 wide BVH (implementation).
 *
 * Pipeline:
 *   1. Precompute per-triangle AABBs + centroids (one pass, arena allocated).
 *   2. Build a binary BVH with binned SAH (16 bins, all three axes accumulated
 *      in a single pass over the primitives of each node).
 *   3. Collapse the binary tree into a wide BVH (4- or 8-ary) with SoA child
 *      bounds, emitted in DFS order. Leaf triangles are swizzled into 4-wide
 *      SoA blocks (lrt_tri4) with precomputed edges; the prim-index
 *      indirection of the binary tree dies here.
 *
 * Traversal: one ray vs all children of a wide node per step (scalar, SSE4 for
 * BVH4, AVX2 for BVH8), ordered stack with deferred tnear culling, 4-wide SoA
 * Moller-Trumbore per leaf block.
 *
 * The slab test uses (bound - org) * invd with infinite invd components
 * replaced by +/-FLT_MAX at ray setup, which cannot produce NaN (0 * FLT_MAX
 * is 0), so the SIMD min/max slab needs no NaN handling.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "lightrt_c_tri.h"

#include <float.h>
#include <math.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------------- */
/* SIMD detection (compile-time; scalar fallback always available).          */
/* ------------------------------------------------------------------------- */
#if defined(__AVX2__) && defined(__FMA__)
#define LRT_TRI_HAS_AVX2 1
#else
#define LRT_TRI_HAS_AVX2 0
#endif
#if defined(__SSE4_1__) || LRT_TRI_HAS_AVX2
#define LRT_TRI_HAS_SSE4 1
#else
#define LRT_TRI_HAS_SSE4 0
#endif

#if LRT_TRI_HAS_SSE4
#include <immintrin.h>
#endif

/* ------------------------------------------------------------------------- */
/* Tunables.                                                                 */
/* ------------------------------------------------------------------------- */
#define TRI_NUM_BINS 16u
#define TRI_DEFAULT_LEAF 60u
#define TRI_MAX_LEAF 60u /* hard cap from the leaf-ref encoding (15 blocks) */
#define TRI_TRAV_COST 1.0f
#define TRI_ISECT_COST 1.0f
#define TRI_MAX_DEPTH 96u
#define TRI_MEDIAN_DEPTH 48u /* force median splits beyond this depth */
/* Wide-tree depth <= binary depth (TRI_MAX_DEPTH); each level leaves at most
 * width-1 entries on the stack -> 96*7 = 672 worst case for BVH8. */
#define TRI_STACK_SIZE 1024
#define TRI_INF_F 3.402823466e+38f

/* Child reference: bit31 = leaf. Inner: bits30..0 = wide-node index.
 * Leaf: bits30..4 = first lrt_tri4 block index, bits3..0 = block count. */
#define TRI_REF_LEAF_BIT 0x80000000u
#define TRI_REF_IS_LEAF(r) (((r) & TRI_REF_LEAF_BIT) != 0u)
#define TRI_REF_NODE(r) ((r) & 0x7FFFFFFFu)
#define TRI_REF_BLOCK(r) (((r) & 0x7FFFFFFFu) >> 4)
#define TRI_REF_NBLOCKS(r) ((r) & 0xFu)
#define TRI_MAKE_LEAF_REF(block, nblocks) \
    (TRI_REF_LEAF_BIT | ((uint32_t)(block) << 4) | (uint32_t)(nblocks))
#define TRI_MAKE_NODE_REF(idx) ((uint32_t)(idx))

/* ------------------------------------------------------------------------- */
/* Data structures.                                                          */
/* ------------------------------------------------------------------------- */

/* 4-wide node: SoA child bounds, 128 bytes = 2 cache lines. */
typedef struct lrt_bvh4_node {
    float lo_x[4], lo_y[4], lo_z[4];
    float hi_x[4], hi_y[4], hi_z[4];
    uint32_t child[4]; /* child refs; empty slots: 0 with inverted bounds */
    uint32_t nchildren;
    uint32_t _pad[3];
} lrt_bvh4_node;

/* 8-wide node: 256 bytes = 4 cache lines. */
typedef struct lrt_bvh8_node {
    float lo_x[8], lo_y[8], lo_z[8];
    float hi_x[8], hi_y[8], hi_z[8];
    uint32_t child[8];
    uint32_t nchildren;
    uint32_t _pad[7];
} lrt_bvh8_node;

/* Quantized 8-wide node: child bounds as 8-bit offsets on a node-local grid
 * (org + q * scale, quantization rounded outward so decoded boxes always
 * contain the true ones). 128 bytes = 2 cache lines. */
typedef struct lrt_bvh8q_node {
    float org[3];
    float scale[3];
    uint32_t nchildren;
    uint8_t qlo_x[8], qlo_y[8], qlo_z[8]; /* empty slots: qlo=255 */
    uint8_t qhi_x[8], qhi_y[8], qhi_z[8]; /* empty slots: qhi=0   */
    uint32_t child[8];
    uint32_t _pad[5];
} lrt_bvh8q_node;

/* Triangle blocks: SoA with precomputed edges, sized to the traversal SIMD
 * width (4 for BVH4/SSE, 8 for BVH8/AVX2). Both share the same generic float
 * layout — 9 arrays of `width` floats (v0xyz, e1xyz, e2xyz) followed by
 * `width` uint32 prim ids — so scalar code can address either width. Padding
 * lanes carry prim_id = LRT_TRI_NO_HIT and all-zero vertices (zero det ->
 * never hit). lrt_tri4 = 160 bytes, lrt_tri8 = 320 bytes. */
typedef struct lrt_tri4 {
    float v0x[4], v0y[4], v0z[4];
    float e1x[4], e1y[4], e1z[4];
    float e2x[4], e2y[4], e2z[4];
    uint32_t prim_id[4];
} lrt_tri4;

typedef struct lrt_tri8 {
    float v0x[8], v0y[8], v0z[8];
    float e1x[8], e1y[8], e1z[8];
    float e2x[8], e2y[8], e2z[8];
    uint32_t prim_id[8];
} lrt_tri8;

struct lrt_tri_scene {
    int layout;    /* traversal width: 4 or 8 */
    int quantized; /* nodes8q used instead of nodes8 */
    uint32_t root;
    lrt_bvh4_node *nodes4;
    lrt_bvh8_node *nodes8;
    lrt_bvh8q_node *nodes8q;
    uint32_t node_count;
    void *blocks; /* lrt_tri4[] when layout==4, lrt_tri8[] when layout==8 */
    uint32_t block_count;
    lrt_tri_stats stats;
    const char *kernel_name;
};

static inline size_t tri_block_size(int width) {
    return width == 4 ? sizeof(lrt_tri4) : sizeof(lrt_tri8);
}

/* Generic view of a block: 9 float arrays then the prim_id array. */
static inline const float *tri_block_floats(const void *blocks, uint32_t idx,
                                            int width) {
    return (const float *)((const char *)blocks +
                           (size_t)idx * tri_block_size(width));
}

/* Binary build node (arena, freed after collapse). */
typedef struct tri_bnode {
    float lo[3], hi[3];
    uint32_t a, b;  /* inner: left/right node indices; leaf: a = index offset */
    uint32_t count; /* 0 = inner, >0 = leaf primitive count */
} tri_bnode;

/* Build context. For parallel builds each worker gets a copy with a private
 * [node_next, node_end) slice of the shared bnodes arena and a disjoint range
 * of the shared indices array, so no synchronization is needed. */
typedef struct tri_build_ctx {
    const float *verts; /* caller soup, 9*ntris */
    size_t ntris;
    float *plo;      /* 3*ntris */
    float *phi;      /* 3*ntris */
    float *cen;      /* 3*ntris */
    uint32_t *indices;
    tri_bnode *bnodes;  /* shared arena */
    uint32_t node_next; /* this worker's allocation cursor */
    uint32_t node_end;  /* end of this worker's slice */
    uint32_t max_leaf;
    uint32_t block_shift; /* log2 of the leaf SIMD width (2 or 3) */
    lrt_tri_quality quality;
    int failed;
    /* intra-node parallelism for the big nodes near the root (serial part of
     * the subtree-parallel build); 0/1 = off */
    unsigned par_threads;
    uint32_t *par_scratch; /* ntris u32 scatter buffer (when par_threads > 1) */
    /* LBVH (LRT_TRI_BUILD_FAST): Morton-sorted keys, (morton30 << 32) | prim,
     * index-aligned with the sorted indices[]. NULL for SAH builds. */
    const uint64_t *lbvh_keys;
    uint32_t lbvh_leaf; /* LBVH leaf size (fixed; no SAH leaf decision) */
} tri_build_ctx;

/* ------------------------------------------------------------------------- */
/* Helpers.                                                                  */
/* ------------------------------------------------------------------------- */

static void *tri_aligned_alloc(size_t align, size_t size) {
    size = (size + align - 1u) & ~(align - 1u);
#if defined(_MSC_VER)
    return _aligned_malloc(size, align);
#else
    return aligned_alloc(align, size);
#endif
}

static void tri_aligned_free(void *p) {
#if defined(_MSC_VER)
    _aligned_free(p);
#else
    free(p);
#endif
}

static inline float tri_minf(float a, float b) { return a < b ? a : b; }
static inline float tri_maxf(float a, float b) { return a > b ? a : b; }

static inline float tri_surface_area(const float lo[3], const float hi[3]) {
    float dx = hi[0] - lo[0], dy = hi[1] - lo[1], dz = hi[2] - lo[2];
    if (dx < 0.0f || dy < 0.0f || dz < 0.0f) return 0.0f;
    return 2.0f * (dx * dy + dy * dz + dz * dx);
}

static inline void tri_box_reset(float lo[3], float hi[3]) {
    lo[0] = lo[1] = lo[2] = TRI_INF_F;
    hi[0] = hi[1] = hi[2] = -TRI_INF_F;
}

static inline void tri_box_expand(float lo[3], float hi[3], const float plo[3],
                                  const float phi[3]) {
    for (int a = 0; a < 3; a++) {
        lo[a] = tri_minf(lo[a], plo[a]);
        hi[a] = tri_maxf(hi[a], phi[a]);
    }
}

static inline int tri_longest_axis(const float lo[3], const float hi[3]) {
    float dx = hi[0] - lo[0], dy = hi[1] - lo[1], dz = hi[2] - lo[2];
    if (dx > dy && dx > dz) return 0;
    if (dy > dz) return 1;
    return 2;
}

/* Leaves are intersected one SIMD block at a time, so SAH counts blocks of
 * the traversal width, not triangles (Embree's blockSize model). */
static inline float tri_sah_blocks(uint32_t n, uint32_t block_shift) {
    return (float)((n + (1u << block_shift) - 1u) >> block_shift);
}

/* SAH bin (file scope: shared by the serial and parallel binning paths). */
typedef struct tri_bin {
    float lo[3], hi[3];
    uint32_t count;
} tri_bin;

/* ------------------------------------------------------------------------- */
/* Parallel-for helper (C11 threads).                                        */
/* ------------------------------------------------------------------------- */
#if !defined(__STDC_NO_THREADS__)
#include <threads.h>

#define TRI_PAR_NODE_MIN (1u << 16) /* intra-node parallelism above this */
#define TRI_PAR_MAX_THREADS 32u
/* Binning/partition passes are memory-bound and spawn threads per call;
 * beyond ~8 helpers they cost more than they return (measured on a 16-core
 * Threadripper 1950X: 8 threads beat 16/32 for the intra-node passes). */
#define TRI_PAR_NODE_THREADS 8u

typedef struct tri_pfor_job {
    void (*fn)(void *arg, unsigned chunk, uint32_t begin, uint32_t end);
    void *arg;
    uint32_t n;
    unsigned nchunks;
    atomic_uint next;
} tri_pfor_job;

static int tri_pfor_worker(void *p) {
    tri_pfor_job *job = (tri_pfor_job *)p;
    for (;;) {
        unsigned c =
            atomic_fetch_add_explicit(&job->next, 1u, memory_order_relaxed);
        if (c >= job->nchunks) return 0;
        uint32_t begin = (uint32_t)(((uint64_t)job->n * c) / job->nchunks);
        uint32_t end = (uint32_t)(((uint64_t)job->n * (c + 1u)) / job->nchunks);
        job->fn(job->arg, c, begin, end);
    }
}

/* Run fn over [0,n) split into `threads` contiguous chunks. Chunk boundaries
 * depend only on (n, threads), so results are deterministic. */
static void tri_parallel_for(uint32_t n, unsigned threads,
                             void (*fn)(void *, unsigned, uint32_t, uint32_t),
                             void *arg) {
    if (threads > TRI_PAR_MAX_THREADS) threads = TRI_PAR_MAX_THREADS;
    if (threads < 1) threads = 1;
    tri_pfor_job job = {fn, arg, n, threads, 0};
    atomic_init(&job.next, 0u);
    thrd_t tids[TRI_PAR_MAX_THREADS];
    unsigned spawned = 0;
    for (unsigned i = 0; i + 1 < threads; i++) {
        if (thrd_create(&tids[i], tri_pfor_worker, &job) != thrd_success) break;
        spawned++;
    }
    tri_pfor_worker(&job); /* the calling thread participates */
    for (unsigned i = 0; i < spawned; i++) thrd_join(tids[i], NULL);
}
#endif /* !__STDC_NO_THREADS__ */

/* ------------------------------------------------------------------------- */
/* Binary SAH build.                                                         */
/* ------------------------------------------------------------------------- */

#if !defined(__STDC_NO_THREADS__)
/* Parallel 3-axis binning over indices[first+begin, first+end) per chunk. */
typedef struct tri_bin_job {
    const tri_build_ctx *c;
    uint32_t first;
    const float *amin;
    const float *ascale;
    const int *axis_ok;
    tri_bin (*bins)[3][TRI_NUM_BINS]; /* one set per chunk */
} tri_bin_job;

static void tri_bin_chunk(void *arg, unsigned chunk, uint32_t begin,
                          uint32_t end) {
    tri_bin_job *j = (tri_bin_job *)arg;
    const tri_build_ctx *c = j->c;
    tri_bin(*bins)[TRI_NUM_BINS] = j->bins[chunk];
    for (int a = 0; a < 3; a++) {
        for (uint32_t b = 0; b < TRI_NUM_BINS; b++) {
            tri_box_reset(bins[a][b].lo, bins[a][b].hi);
            bins[a][b].count = 0;
        }
    }
    for (uint32_t i = begin; i < end; i++) {
        uint32_t p = c->indices[j->first + i];
        const float *pl = &c->plo[(size_t)p * 3];
        const float *ph = &c->phi[(size_t)p * 3];
        const float *pc = &c->cen[(size_t)p * 3];
        for (int a = 0; a < 3; a++) {
            if (!j->axis_ok[a]) continue;
            uint32_t b = (uint32_t)((pc[a] - j->amin[a]) * j->ascale[a]);
            if (b >= TRI_NUM_BINS) b = TRI_NUM_BINS - 1;
            tri_box_expand(bins[a][b].lo, bins[a][b].hi, pl, ph);
            bins[a][b].count++;
        }
    }
}

/* Parallel two-pass partition: count per chunk, prefix-sum, scatter into the
 * scratch buffer, copy back. */
typedef struct tri_part_job {
    tri_build_ctx *c;
    uint32_t first;
    int axis;
    float pos;
    uint32_t nleft[TRI_PAR_MAX_THREADS];
    uint32_t left_off[TRI_PAR_MAX_THREADS];
    uint32_t right_off[TRI_PAR_MAX_THREADS];
    uint32_t mid;
} tri_part_job;

static void tri_part_count(void *arg, unsigned chunk, uint32_t begin,
                           uint32_t end) {
    tri_part_job *j = (tri_part_job *)arg;
    const tri_build_ctx *c = j->c;
    uint32_t nl = 0;
    for (uint32_t i = begin; i < end; i++) {
        uint32_t p = c->indices[j->first + i];
        nl += c->cen[(size_t)p * 3 + j->axis] < j->pos;
    }
    j->nleft[chunk] = nl;
}

static void tri_part_scatter(void *arg, unsigned chunk, uint32_t begin,
                             uint32_t end) {
    tri_part_job *j = (tri_part_job *)arg;
    const tri_build_ctx *c = j->c;
    uint32_t *out = c->par_scratch + j->first;
    uint32_t lo = j->left_off[chunk];
    uint32_t ro = j->mid + j->right_off[chunk];
    for (uint32_t i = begin; i < end; i++) {
        uint32_t p = c->indices[j->first + i];
        if (c->cen[(size_t)p * 3 + j->axis] < j->pos) {
            out[lo++] = p;
        } else {
            out[ro++] = p;
        }
    }
}

static void tri_part_copyback(void *arg, unsigned chunk, uint32_t begin,
                              uint32_t end) {
    tri_part_job *j = (tri_part_job *)arg;
    (void)chunk;
    memcpy(j->c->indices + j->first + begin, j->c->par_scratch + j->first + begin,
           (size_t)(end - begin) * sizeof(uint32_t));
}
#endif /* !__STDC_NO_THREADS__ */

/* Per-triangle AABB + centroid precompute. Returns non-zero on non-finite
 * input. Parallelized by chunks when threads > 1. */
typedef struct tri_precompute_job {
    tri_build_ctx *c;
    atomic_int bad;
} tri_precompute_job;

static void tri_precompute_chunk_impl(tri_build_ctx *c, uint32_t begin,
                                      uint32_t end, int *bad_out) {
    int bad = 0;
    for (uint32_t i = begin; i < end; i++) {
        const float *v = &c->verts[(size_t)i * 9];
        for (int a = 0; a < 3; a++) {
            /* check the vertices, not min/max results: minf/maxf comparisons
             * are false for NaN and would swallow it */
            if (!isfinite(v[a]) || !isfinite(v[3 + a]) || !isfinite(v[6 + a])) {
                bad = 1;
            }
            float lo = tri_minf(v[a], tri_minf(v[3 + a], v[6 + a]));
            float hi = tri_maxf(v[a], tri_maxf(v[3 + a], v[6 + a]));
            c->plo[(size_t)i * 3 + a] = lo;
            c->phi[(size_t)i * 3 + a] = hi;
            c->cen[(size_t)i * 3 + a] = 0.5f * (lo + hi);
        }
        c->indices[i] = i;
    }
    if (bad) *bad_out = 1;
}

#if !defined(__STDC_NO_THREADS__)
static void tri_precompute_chunk(void *arg, unsigned chunk, uint32_t begin,
                                 uint32_t end) {
    (void)chunk;
    tri_precompute_job *j = (tri_precompute_job *)arg;
    int bad = 0;
    tri_precompute_chunk_impl(j->c, begin, end, &bad);
    if (bad) atomic_store_explicit(&j->bad, 1, memory_order_relaxed);
}
#endif

static int tri_precompute(tri_build_ctx *c, unsigned threads) {
#if !defined(__STDC_NO_THREADS__)
    if (threads > 1 && c->ntris >= TRI_PAR_NODE_MIN) {
        tri_precompute_job j;
        j.c = c;
        atomic_init(&j.bad, 0);
        tri_parallel_for((uint32_t)c->ntris, threads, tri_precompute_chunk, &j);
        return atomic_load(&j.bad);
    }
#else
    (void)threads;
#endif
    int bad = 0;
    tri_precompute_chunk_impl(c, 0, (uint32_t)c->ntris, &bad);
    return bad;
}

/* Partition indices[first, first+num) by centroid[axis] < pos; returns the
 * left-side count. Uses the parallel path for large nodes when enabled. */
static uint32_t tri_partition(tri_build_ctx *c, uint32_t first, uint32_t num,
                              int axis, float pos) {
#if !defined(__STDC_NO_THREADS__)
    if (c->par_threads > 1 && c->par_scratch && num >= TRI_PAR_NODE_MIN) {
        tri_part_job j;
        j.c = c;
        j.first = first;
        j.axis = axis;
        j.pos = pos;
        unsigned threads = c->par_threads;
        if (threads > TRI_PAR_NODE_THREADS) threads = TRI_PAR_NODE_THREADS;
        tri_parallel_for(num, threads, tri_part_count, &j);
        uint32_t mid = 0, racc = 0;
        for (unsigned t = 0; t < threads; t++) mid += j.nleft[t];
        uint32_t lacc = 0;
        for (unsigned t = 0; t < threads; t++) {
            uint32_t begin = (uint32_t)(((uint64_t)num * t) / threads);
            uint32_t end = (uint32_t)(((uint64_t)num * (t + 1u)) / threads);
            j.left_off[t] = lacc;
            j.right_off[t] = racc;
            lacc += j.nleft[t];
            racc += (end - begin) - j.nleft[t];
        }
        j.mid = mid;
        tri_parallel_for(num, threads, tri_part_scatter, &j);
        tri_parallel_for(num, threads, tri_part_copyback, &j);
        return mid;
    }
#endif
    uint32_t mid = 0;
    for (uint32_t i = 0; i < num; i++) {
        uint32_t p = c->indices[first + i];
        if (c->cen[(size_t)p * 3 + axis] < pos) {
            uint32_t tmp = c->indices[first + i];
            c->indices[first + i] = c->indices[first + mid];
            c->indices[first + mid] = tmp;
            mid++;
        }
    }
    return mid;
}

/* Allocate and fill one binary node over indices[first, first+num): computes
 * bounds, makes it a leaf, or picks a split and partitions the range. Returns
 * the node index; *out_mid > 0 iff the node is inner (split position). */
static uint32_t tri_build_node(tri_build_ctx *c, uint32_t first, uint32_t num,
                               uint32_t depth, uint32_t *out_mid) {
    *out_mid = 0;
    if (c->failed) return 0;
    if (c->node_next >= c->node_end) {
        c->failed = 1;
        return 0;
    }

    const float *plo = c->plo;
    const float *phi = c->phi;
    const float *cen = c->cen;
    uint32_t *indices = c->indices;

    /* Node bounds + centroid bounds in one pass. */
    float nlo[3], nhi[3], clo[3], chi[3];
    tri_box_reset(nlo, nhi);
    tri_box_reset(clo, chi);
    for (uint32_t i = 0; i < num; i++) {
        uint32_t p = indices[first + i];
        tri_box_expand(nlo, nhi, &plo[(size_t)p * 3], &phi[(size_t)p * 3]);
        for (int a = 0; a < 3; a++) {
            float ce = cen[(size_t)p * 3 + a];
            clo[a] = tri_minf(clo[a], ce);
            chi[a] = tri_maxf(chi[a], ce);
        }
    }

    uint32_t node_idx = c->node_next++;
    tri_bnode *node = &c->bnodes[node_idx];
    for (int a = 0; a < 3; a++) {
        node->lo[a] = nlo[a];
        node->hi[a] = nhi[a];
    }

    /* One block (or the user's cap, if tighter) is always a leaf; larger
     * ranges up to max_leaf become leaves only when SAH favors it below. */
    uint32_t block_width = 1u << c->block_shift;
    uint32_t always_leaf = c->max_leaf < block_width ? c->max_leaf : block_width;
    if (num <= always_leaf) {
        node->a = first;
        node->b = 0;
        node->count = num;
        return node_idx;
    }

    int best_axis = -1;
    float best_pos = 0.0f;
    int use_median = (c->quality == LRT_TRI_BUILD_FAST) ||
                     depth >= TRI_MEDIAN_DEPTH;

    if (!use_median) {
        /* Binned SAH: one pass over the primitives bins all three axes. */
        tri_bin bins[3][TRI_NUM_BINS];
        float amin[3], ascale[3];
        int axis_ok[3];
        for (int a = 0; a < 3; a++) {
            amin[a] = clo[a];
            float ext = chi[a] - clo[a];
            axis_ok[a] = ext > 1e-6f;
            ascale[a] = axis_ok[a] ? (float)TRI_NUM_BINS / ext : 0.0f;
            for (uint32_t b = 0; b < TRI_NUM_BINS; b++) {
                tri_box_reset(bins[a][b].lo, bins[a][b].hi);
                bins[a][b].count = 0;
            }
        }

#if !defined(__STDC_NO_THREADS__)
        if (c->par_threads > 1 && num >= TRI_PAR_NODE_MIN) {
            unsigned threads = c->par_threads;
            if (threads > TRI_PAR_NODE_THREADS) threads = TRI_PAR_NODE_THREADS;
            /* only reached from the single-threaded frontier expansion
             * (worker contexts run with par_threads == 0) */
            static tri_bin chunk_bins[TRI_PAR_MAX_THREADS][3][TRI_NUM_BINS];
            tri_bin_job j = {c, first, amin, ascale, axis_ok, chunk_bins};
            tri_parallel_for(num, threads, tri_bin_chunk, &j);
            for (unsigned t = 0; t < threads; t++) {
                for (int a = 0; a < 3; a++) {
                    for (uint32_t b = 0; b < TRI_NUM_BINS; b++) {
                        tri_box_expand(bins[a][b].lo, bins[a][b].hi,
                                       chunk_bins[t][a][b].lo,
                                       chunk_bins[t][a][b].hi);
                        bins[a][b].count += chunk_bins[t][a][b].count;
                    }
                }
            }
        } else
#endif
        {
            for (uint32_t i = 0; i < num; i++) {
                uint32_t p = indices[first + i];
                const float *pl = &plo[(size_t)p * 3];
                const float *ph = &phi[(size_t)p * 3];
                const float *pc = &cen[(size_t)p * 3];
                for (int a = 0; a < 3; a++) {
                    if (!axis_ok[a]) continue;
                    uint32_t b = (uint32_t)((pc[a] - amin[a]) * ascale[a]);
                    if (b >= TRI_NUM_BINS) b = TRI_NUM_BINS - 1;
                    tri_box_expand(bins[a][b].lo, bins[a][b].hi, pl, ph);
                    bins[a][b].count++;
                }
            }
        }

        float parent_area = tri_surface_area(nlo, nhi);
        if (parent_area <= 0.0f) parent_area = 1.0f;
        float best_cost = TRI_INF_F;

        for (int a = 0; a < 3; a++) {
            if (!axis_ok[a]) continue;
            /* Left prefix sweep. */
            float left_area[TRI_NUM_BINS];
            uint32_t left_cnt[TRI_NUM_BINS];
            float run_lo[3], run_hi[3];
            uint32_t run = 0;
            tri_box_reset(run_lo, run_hi);
            for (uint32_t b = 0; b < TRI_NUM_BINS; b++) {
                tri_box_expand(run_lo, run_hi, bins[a][b].lo, bins[a][b].hi);
                run += bins[a][b].count;
                left_area[b] = tri_surface_area(run_lo, run_hi);
                left_cnt[b] = run;
            }
            /* Right suffix sweep, evaluating each split plane. */
            tri_box_reset(run_lo, run_hi);
            run = 0;
            for (uint32_t b = TRI_NUM_BINS - 1; b > 0; b--) {
                tri_box_expand(run_lo, run_hi, bins[a][b].lo, bins[a][b].hi);
                run += bins[a][b].count;
                uint32_t lc = left_cnt[b - 1];
                if (lc == 0 || run == 0) continue;
                float cost = TRI_TRAV_COST +
                             TRI_ISECT_COST *
                                 (tri_sah_blocks(lc, c->block_shift) *
                                      left_area[b - 1] +
                                  tri_sah_blocks(run, c->block_shift) *
                                      tri_surface_area(run_lo, run_hi)) /
                                 parent_area;
                if (cost < best_cost) {
                    best_cost = cost;
                    best_axis = a;
                    best_pos = amin[a] + (float)b / ascale[a];
                }
            }
        }

        /* If no profitable split exists, prefer a leaf when small enough. */
        float leaf_cost = TRI_ISECT_COST * tri_sah_blocks(num, c->block_shift);
        if (best_axis < 0 || best_cost >= leaf_cost) {
            if (num <= c->max_leaf) {
                node->a = first;
                node->b = 0;
                node->count = num;
                return node_idx;
            }
            use_median = 1; /* must keep splitting; fall back to median */
        }
    }

    uint32_t mid;
    if (use_median || best_axis < 0) {
        /* Object-median split on the longest centroid axis. A centroid-
         * threshold partition at the midpoint approximates the median; exact
         * balance is restored by the num/2 fallback below. */
        int axis = tri_longest_axis(clo, chi);
        mid = tri_partition(c, first, num, axis, 0.5f * (clo[axis] + chi[axis]));
    } else {
        mid = tri_partition(c, first, num, best_axis, best_pos);
    }
    if (mid == 0 || mid == num) mid = num / 2; /* fallback: median by index */

    if (depth + 1 >= TRI_MAX_DEPTH) {
        /* Pathological recursion: clamp into a (possibly oversized) chain of
         * leaves by splitting evenly; depth grows by log2 only. */
        mid = num / 2;
    }

    node->count = 0;
    *out_mid = mid;
    return node_idx;
}

static uint32_t tri_build_recursive(tri_build_ctx *c, uint32_t first,
                                    uint32_t num, uint32_t depth) {
    uint32_t mid;
    uint32_t node_idx = tri_build_node(c, first, num, depth, &mid);
    if (c->failed || mid == 0) return node_idx; /* leaf (or failure) */

    uint32_t left = tri_build_recursive(c, first, mid, depth + 1);
    uint32_t right = tri_build_recursive(c, first + mid, num - mid, depth + 1);
    if (c->failed) return 0;

    tri_bnode *node = &c->bnodes[node_idx];
    node->a = left;
    node->b = right;
    return node_idx;
}

/* ---- LBVH (Morton) fast build ---------------------------------------------
 *
 * LRT_TRI_BUILD_FAST: quantize centroids to 30-bit Morton codes, radix-sort
 * (morton << 32) | prim keys, then build the binary tree by splitting each
 * sorted range at its highest differing Morton bit (binary search — no
 * binning, no partitioning). Bounds are unioned bottom-up. ~O(N) build with
 * SAH quality typically within ~10-20% of the binned builder.
 */

/* Spread the low 10 bits of v so each lands at every 3rd bit position. */
static inline uint32_t tri_morton_expand10(uint32_t v) {
    v &= 0x3FFu;
    v = (v | (v << 16)) & 0x030000FFu;
    v = (v | (v << 8)) & 0x0300F00Fu;
    v = (v | (v << 4)) & 0x030C30C3u;
    v = (v | (v << 2)) & 0x09249249u;
    return v;
}

/* LSD radix sort of n keys by their high-32 Morton bits (bytes 4..7). The
 * low-32 prim id makes keys unique, so the result is fully deterministic.
 * Returns the array holding the sorted keys (keys or tmp). */
static uint64_t *tri_radix_sort_keys(uint64_t *keys, uint64_t *tmp, size_t n) {
    uint64_t *src = keys, *dst = tmp;
    for (int byte = 4; byte < 8; byte++) {
        uint32_t shift = (uint32_t)byte * 8u;
        size_t count[256];
        memset(count, 0, sizeof(count));
        for (size_t i = 0; i < n; i++) count[(src[i] >> shift) & 0xFFu]++;
        /* skip passes where every key shares the digit (e.g. byte 7 has only
         * 6 used bits, and small scenes leave high bytes constant) */
        int trivial = 0;
        for (int d = 0; d < 256; d++) {
            if (count[d] == n) {
                trivial = 1;
                break;
            }
            if (count[d] != 0) break;
        }
        if (trivial) continue;
        size_t offset[256];
        size_t sum = 0;
        for (int d = 0; d < 256; d++) {
            offset[d] = sum;
            sum += count[d];
        }
        for (size_t i = 0; i < n; i++) {
            dst[offset[(src[i] >> shift) & 0xFFu]++] = src[i];
        }
        uint64_t *t = src;
        src = dst;
        dst = t;
    }
    return src;
}

/* First index in (0, num) where the highest differing Morton bit flips, or
 * num/2 when all codes in the range are equal. */
static uint32_t tri_lbvh_find_split(const uint64_t *keys, uint32_t first,
                                    uint32_t num) {
    uint64_t kf = keys[first] >> 32;
    uint64_t kl = keys[first + num - 1] >> 32;
    uint64_t x = kf ^ kl;
    if (x == 0) return num / 2; /* identical codes: median */
    int bit = 63 - __builtin_clzll(x);
    /* sorted: a prefix has the bit clear, the suffix has it set */
    uint32_t lo = 0, hi = num - 1;
    while (hi - lo > 1) {
        uint32_t m = lo + (hi - lo) / 2;
        if (((keys[first + m] >> 32) >> bit) & 1u) {
            hi = m;
        } else {
            lo = m;
        }
    }
    return hi;
}

/* Build a subtree over the Morton-sorted range [first, first+num); returns
 * the node index and writes the subtree bounds to lo_out/hi_out. */
static uint32_t tri_lbvh_range(tri_build_ctx *c, uint32_t first, uint32_t num,
                               float lo_out[3], float hi_out[3]) {
    if (c->failed) return 0;
    if (c->node_next >= c->node_end) {
        c->failed = 1;
        return 0;
    }
    uint32_t node_idx = c->node_next++;
    tri_bnode *node = &c->bnodes[node_idx];

    if (num <= c->lbvh_leaf) {
        float lo[3], hi[3];
        tri_box_reset(lo, hi);
        for (uint32_t i = 0; i < num; i++) {
            uint32_t p = c->indices[first + i];
            tri_box_expand(lo, hi, &c->plo[(size_t)p * 3], &c->phi[(size_t)p * 3]);
        }
        for (int a = 0; a < 3; a++) {
            node->lo[a] = lo_out[a] = lo[a];
            node->hi[a] = hi_out[a] = hi[a];
        }
        node->a = first;
        node->b = 0;
        node->count = num;
        return node_idx;
    }

    uint32_t mid = tri_lbvh_find_split(c->lbvh_keys, first, num);
    float llo[3], lhi[3], rlo[3], rhi[3];
    uint32_t left = tri_lbvh_range(c, first, mid, llo, lhi);
    uint32_t right = tri_lbvh_range(c, first + mid, num - mid, rlo, rhi);
    if (c->failed) return 0;

    node = &c->bnodes[node_idx];
    for (int a = 0; a < 3; a++) {
        node->lo[a] = lo_out[a] = tri_minf(llo[a], rlo[a]);
        node->hi[a] = hi_out[a] = tri_maxf(lhi[a], rhi[a]);
    }
    node->a = left;
    node->b = right;
    node->count = 0;
    return node_idx;
}

/* Quantize centroids to a 1024^3 grid over the centroid bounds and emit
 * (morton30 << 32) | prim keys. */
typedef struct tri_morton_job {
    const tri_build_ctx *c;
    uint64_t *keys;
    float base[3];
    float scale[3];
} tri_morton_job;

static void tri_morton_chunk_impl(const tri_morton_job *j, uint32_t begin,
                                  uint32_t end) {
    const float *cen = j->c->cen;
    for (uint32_t i = begin; i < end; i++) {
        uint32_t q[3];
        for (int a = 0; a < 3; a++) {
            float v = (cen[(size_t)i * 3 + a] - j->base[a]) * j->scale[a];
            int32_t qi = (int32_t)v;
            if (qi < 0) qi = 0;
            if (qi > 1023) qi = 1023;
            q[a] = (uint32_t)qi;
        }
        uint32_t morton = (tri_morton_expand10(q[0]) << 2) |
                          (tri_morton_expand10(q[1]) << 1) |
                          tri_morton_expand10(q[2]);
        j->keys[i] = ((uint64_t)morton << 32) | (uint64_t)i;
    }
}

#if !defined(__STDC_NO_THREADS__)
static void tri_morton_chunk(void *arg, unsigned chunk, uint32_t begin,
                             uint32_t end) {
    (void)chunk;
    tri_morton_chunk_impl((const tri_morton_job *)arg, begin, end);
}
#endif

static void tri_morton_encode(const tri_build_ctx *c, uint64_t *keys,
                              unsigned threads) {
    tri_morton_job j;
    j.c = c;
    j.keys = keys;
    /* centroid bounds (cheap serial reduction) */
    float clo[3], chi[3];
    tri_box_reset(clo, chi);
    for (size_t i = 0; i < c->ntris; i++) {
        for (int a = 0; a < 3; a++) {
            float v = c->cen[i * 3 + a];
            clo[a] = tri_minf(clo[a], v);
            chi[a] = tri_maxf(chi[a], v);
        }
    }
    for (int a = 0; a < 3; a++) {
        float ext = chi[a] - clo[a];
        j.base[a] = clo[a];
        j.scale[a] = ext > 0.0f ? 1024.0f / ext : 0.0f;
    }
#if !defined(__STDC_NO_THREADS__)
    if (threads > 1 && c->ntris >= TRI_PAR_NODE_MIN) {
        tri_parallel_for((uint32_t)c->ntris, threads, tri_morton_chunk, &j);
        return;
    }
#else
    (void)threads;
#endif
    tri_morton_chunk_impl(&j, 0, (uint32_t)c->ntris);
}

/* ---- Parallel binary build (C11 threads) ---------------------------------
 *
 * A serial frontier expansion splits the root task until there are enough
 * subtree tasks to feed the workers, then each task is built independently:
 * disjoint indices range, private slice of the bnodes arena (a subtree over k
 * prims needs at most 2k-1 nodes), and a unique parent link to store its root
 * into. Workers pull tasks with an atomic cursor.
 */
typedef struct tri_build_task {
    uint32_t first, num, depth;
    uint32_t *parent_slot; /* &bnodes[parent].a or .b (unique per task) */
} tri_build_task;

#if !defined(__STDC_NO_THREADS__)
typedef struct tri_build_pool {
    const tri_build_ctx *proto;
    tri_build_task *tasks;
    uint32_t ntasks;
    atomic_uint next_task;
    /* per-task arena slices, precomputed */
    uint32_t *slice_base;
    atomic_int failed;
    int lbvh; /* tasks run tri_lbvh_range instead of tri_build_recursive */
} tri_build_pool;

static int tri_build_worker(void *arg) {
    tri_build_pool *pool = (tri_build_pool *)arg;
    for (;;) {
        uint32_t t = atomic_fetch_add_explicit(&pool->next_task, 1u,
                                               memory_order_relaxed);
        if (t >= pool->ntasks) break;
        const tri_build_task *task = &pool->tasks[t];
        tri_build_ctx c = *pool->proto;
        c.par_threads = 0; /* subtree tasks are already parallel; no nesting */
        c.node_next = pool->slice_base[t];
        c.node_end = pool->slice_base[t] + 2u * task->num;
        uint32_t root;
        if (pool->lbvh) {
            float lo[3], hi[3];
            root = tri_lbvh_range(&c, task->first, task->num, lo, hi);
        } else {
            root = tri_build_recursive(&c, task->first, task->num, task->depth);
        }
        if (c.failed) {
            atomic_store_explicit(&pool->failed, 1, memory_order_relaxed);
            break;
        }
        *task->parent_slot = root;
    }
    return 0;
}
#endif /* !__STDC_NO_THREADS__ */

/* Build the binary tree over all primitives, using up to num_threads workers.
 * Returns the root node index, or fails via c->failed. */
static uint32_t tri_build_binary(tri_build_ctx *c, unsigned num_threads) {
#if !defined(__STDC_NO_THREADS__)
    if (num_threads > 1 && c->ntris >= 4096) {
        /* Serial frontier expansion: always expand the largest task. */
        enum { MAX_TASKS = 256 };
        tri_build_task tasks[MAX_TASKS];
        uint32_t root_slot = LRT_TRI_NO_HIT; /* root task writes here */
        uint32_t ntasks = 0;
        unsigned target = num_threads * 8u;
        if (target > MAX_TASKS) target = MAX_TASKS;

        tasks[ntasks++] = (tri_build_task){0, (uint32_t)c->ntris, 0, &root_slot};

        while (ntasks > 0 && ntasks < target) {
            /* pick the largest pending task that is splittable */
            uint32_t big = 0;
            for (uint32_t i = 1; i < ntasks; i++) {
                if (tasks[i].num > tasks[big].num) big = i;
            }
            if (tasks[big].num <= c->max_leaf * 4u) break;

            tri_build_task task = tasks[big];
            uint32_t mid;
            uint32_t node_idx =
                tri_build_node(c, task.first, task.num, task.depth, &mid);
            if (c->failed) return 0;
            *task.parent_slot = node_idx;
            if (mid == 0) {
                /* became a leaf: drop the task */
                tasks[big] = tasks[--ntasks];
                continue;
            }
            tri_bnode *node = &c->bnodes[node_idx];
            tasks[big] = (tri_build_task){task.first, mid, task.depth + 1,
                                          &node->a};
            tasks[ntasks++] = (tri_build_task){task.first + mid, task.num - mid,
                                               task.depth + 1, &node->b};
        }

        /* Largest-first order so the biggest subtree never starts last
         * (longest-processing-time schedule). */
        for (uint32_t i = 1; i < ntasks; i++) {
            tri_build_task key = tasks[i];
            uint32_t k = i;
            while (k > 0 && tasks[k - 1].num < key.num) {
                tasks[k] = tasks[k - 1];
                k--;
            }
            tasks[k] = key;
        }

        /* Assign each task a private arena slice of 2*num nodes. */
        uint32_t slice_base[MAX_TASKS];
        uint32_t cursor = c->node_next;
        int fits = 1;
        for (uint32_t i = 0; i < ntasks; i++) {
            slice_base[i] = cursor;
            if (2u * tasks[i].num > c->node_end - cursor) {
                fits = 0;
                break;
            }
            cursor += 2u * tasks[i].num;
        }

        if (fits && ntasks > 1) {
            tri_build_pool pool;
            pool.proto = c;
            pool.tasks = tasks;
            pool.ntasks = ntasks;
            atomic_init(&pool.next_task, 0u);
            pool.slice_base = slice_base;
            atomic_init(&pool.failed, 0);
            pool.lbvh = 0;

            thrd_t tids[64];
            unsigned nthr = num_threads < 64u ? num_threads : 64u;
            if (nthr > ntasks) nthr = ntasks;
            unsigned spawned = 0;
            for (unsigned i = 0; i + 1 < nthr; i++) {
                if (thrd_create(&tids[i], tri_build_worker, &pool) ==
                    thrd_success) {
                    spawned++;
                } else {
                    break;
                }
            }
            tri_build_worker(&pool); /* this thread works too */
            for (unsigned i = 0; i < spawned; i++) thrd_join(tids[i], NULL);

            if (atomic_load(&pool.failed)) {
                c->failed = 1;
                return 0;
            }
            return root_slot;
        }
        /* fall through to serial on slicing failure or a single task */
        if (ntasks >= 1 && root_slot == LRT_TRI_NO_HIT) {
            /* root task never expanded: build it serially below */
        }
        if (root_slot != LRT_TRI_NO_HIT) {
            /* frontier was partially expanded; finish remaining tasks serially */
            for (uint32_t i = 0; i < ntasks; i++) {
                uint32_t r = tri_build_recursive(c, tasks[i].first, tasks[i].num,
                                                 tasks[i].depth);
                if (c->failed) return 0;
                *tasks[i].parent_slot = r;
            }
            return root_slot;
        }
    }
#else
    (void)num_threads;
#endif
    return tri_build_recursive(c, 0, (uint32_t)c->ntris, 0);
}

/* LBVH counterpart of tri_build_binary: indices[] are already Morton-sorted
 * and c->lbvh_keys is set. Frontier expansion is a binary search per split
 * (no O(N) binning/partition), so it parallelizes much better; frontier node
 * bounds are filled in afterwards from their children (reverse creation
 * order: children are always created after their parent). */
static uint32_t tri_build_lbvh(tri_build_ctx *c, unsigned num_threads) {
#if !defined(__STDC_NO_THREADS__)
    if (num_threads > 1 && c->ntris >= 4096) {
        enum { MAX_TASKS = 256 };
        tri_build_task tasks[MAX_TASKS];
        uint32_t fixup[MAX_TASKS];
        uint32_t nfix = 0;
        uint32_t root_slot = LRT_TRI_NO_HIT;
        uint32_t ntasks = 0;
        unsigned target = num_threads * 8u;
        if (target > MAX_TASKS) target = MAX_TASKS;

        tasks[ntasks++] = (tri_build_task){0, (uint32_t)c->ntris, 0, &root_slot};

        while (ntasks > 0 && ntasks < target) {
            uint32_t big = 0;
            for (uint32_t i = 1; i < ntasks; i++) {
                if (tasks[i].num > tasks[big].num) big = i;
            }
            if (tasks[big].num <= c->lbvh_leaf * 4u) break;

            tri_build_task task = tasks[big];
            if (c->node_next >= c->node_end) {
                c->failed = 1;
                return 0;
            }
            uint32_t node_idx = c->node_next++;
            tri_bnode *node = &c->bnodes[node_idx];
            node->count = 0; /* bounds deferred to the fixup pass */
            *task.parent_slot = node_idx;
            fixup[nfix++] = node_idx;

            uint32_t mid = tri_lbvh_find_split(c->lbvh_keys, task.first, task.num);
            tasks[big] = (tri_build_task){task.first, mid, task.depth + 1,
                                          &node->a};
            tasks[ntasks++] = (tri_build_task){task.first + mid, task.num - mid,
                                               task.depth + 1, &node->b};
        }

        for (uint32_t i = 1; i < ntasks; i++) { /* LPT order */
            tri_build_task key = tasks[i];
            uint32_t k = i;
            while (k > 0 && tasks[k - 1].num < key.num) {
                tasks[k] = tasks[k - 1];
                k--;
            }
            tasks[k] = key;
        }

        uint32_t slice_base[MAX_TASKS];
        uint32_t cursor = c->node_next;
        int fits = 1;
        for (uint32_t i = 0; i < ntasks; i++) {
            slice_base[i] = cursor;
            if (2u * tasks[i].num > c->node_end - cursor) {
                fits = 0;
                break;
            }
            cursor += 2u * tasks[i].num;
        }

        if (fits && ntasks > 1) {
            tri_build_pool pool;
            pool.proto = c;
            pool.tasks = tasks;
            pool.ntasks = ntasks;
            atomic_init(&pool.next_task, 0u);
            pool.slice_base = slice_base;
            atomic_init(&pool.failed, 0);
            pool.lbvh = 1;

            thrd_t tids[64];
            unsigned nthr = num_threads < 64u ? num_threads : 64u;
            if (nthr > ntasks) nthr = ntasks;
            unsigned spawned = 0;
            for (unsigned i = 0; i + 1 < nthr; i++) {
                if (thrd_create(&tids[i], tri_build_worker, &pool) ==
                    thrd_success) {
                    spawned++;
                } else {
                    break;
                }
            }
            tri_build_worker(&pool);
            for (unsigned i = 0; i < spawned; i++) thrd_join(tids[i], NULL);

            if (atomic_load(&pool.failed)) {
                c->failed = 1;
                return 0;
            }
            /* Bounds fixup: reverse creation order guarantees children (later
             * frontier nodes or worker-built subtree roots) are final. */
            for (uint32_t i = nfix; i-- > 0;) {
                tri_bnode *n = &c->bnodes[fixup[i]];
                const tri_bnode *l = &c->bnodes[n->a];
                const tri_bnode *r = &c->bnodes[n->b];
                for (int a = 0; a < 3; a++) {
                    n->lo[a] = tri_minf(l->lo[a], r->lo[a]);
                    n->hi[a] = tri_maxf(l->hi[a], r->hi[a]);
                }
            }
            return root_slot;
        }
        if (root_slot != LRT_TRI_NO_HIT) {
            /* slicing failed after partial expansion: finish serially */
            for (uint32_t i = 0; i < ntasks; i++) {
                float lo[3], hi[3];
                uint32_t r = tri_lbvh_range(c, tasks[i].first, tasks[i].num, lo, hi);
                if (c->failed) return 0;
                *tasks[i].parent_slot = r;
            }
            for (uint32_t i = nfix; i-- > 0;) {
                tri_bnode *n = &c->bnodes[fixup[i]];
                const tri_bnode *l = &c->bnodes[n->a];
                const tri_bnode *r = &c->bnodes[n->b];
                for (int a = 0; a < 3; a++) {
                    n->lo[a] = tri_minf(l->lo[a], r->lo[a]);
                    n->hi[a] = tri_maxf(l->hi[a], r->hi[a]);
                }
            }
            return root_slot;
        }
    }
#else
    (void)num_threads;
#endif
    float lo[3], hi[3];
    return tri_lbvh_range(c, 0, (uint32_t)c->ntris, lo, hi);
}

/* ------------------------------------------------------------------------- */
/* Collapse binary -> wide BVH.                                              */
/* ------------------------------------------------------------------------- */

typedef struct tri_collapse_ctx {
    const tri_build_ctx *bc;
    lrt_tri_scene *s;
    uint32_t node_cap;
    uint32_t block_cap;
    float root_area;
    double sah_inner; /* sum SA(node)/SA(root) */
    double sah_leaf;  /* sum SA(leaf)*count/SA(root) */
    uint32_t leaf_count;
    uint32_t max_depth;
    int width;
    int quantized;
    int failed;
} tri_collapse_ctx;

/* Conservative 8-bit quantization of a child bound onto the parent grid:
 * decoded lo never exceeds the true lo, decoded hi never undershoots. */
static inline uint8_t tri_quantize_lo(float v, float org, float scale,
                                      float inv_scale) {
    if (scale <= 0.0f) return 0;
    float f = (v - org) * inv_scale;
    int q = (int)f;
    if (q < 0) q = 0;
    if (q > 255) q = 255;
    while (q > 0 && org + (float)q * scale > v) q--;
    return (uint8_t)q;
}

static inline uint8_t tri_quantize_hi(float v, float org, float scale,
                                      float inv_scale) {
    if (scale <= 0.0f) return 0; /* zero extent: decode == org == v */
    float f = (v - org) * inv_scale;
    int q = (int)f + 1;
    if (q < 0) q = 0;
    if (q > 255) q = 255;
    while (q < 255 && org + (float)q * scale < v) q++;
    return (uint8_t)q;
}

/* Emit the triangles of a binary leaf as SoA blocks of the scene's SIMD
 * width; returns a leaf ref. */
static uint32_t tri_emit_leaf(tri_collapse_ctx *cc, const tri_bnode *bn) {
    const tri_build_ctx *bc = cc->bc;
    lrt_tri_scene *s = cc->s;
    const uint32_t bw = (uint32_t)cc->width;
    uint32_t count = bn->count;
    uint32_t nblocks = (count + bw - 1u) / bw;
    if (s->block_count + nblocks > cc->block_cap || nblocks > 15u) {
        cc->failed = 1;
        return TRI_MAKE_LEAF_REF(0, 0);
    }
    uint32_t first_block = s->block_count;
    for (uint32_t b = 0; b < nblocks; b++) {
        float *f = (float *)(void *)tri_block_floats(s->blocks, s->block_count,
                                                     cc->width);
        uint32_t *ids = (uint32_t *)(f + 9u * bw);
        s->block_count++;
        for (uint32_t lane = 0; lane < bw; lane++) {
            uint32_t k = b * bw + lane;
            if (k < count) {
                uint32_t prim = bc->indices[bn->a + k];
                const float *v = &bc->verts[(size_t)prim * 9];
                f[0 * bw + lane] = v[0];
                f[1 * bw + lane] = v[1];
                f[2 * bw + lane] = v[2];
                f[3 * bw + lane] = v[3] - v[0];
                f[4 * bw + lane] = v[4] - v[1];
                f[5 * bw + lane] = v[5] - v[2];
                f[6 * bw + lane] = v[6] - v[0];
                f[7 * bw + lane] = v[7] - v[1];
                f[8 * bw + lane] = v[8] - v[2];
                ids[lane] = prim;
            } else {
                for (int arr = 0; arr < 9; arr++) f[(uint32_t)arr * bw + lane] = 0.0f;
                ids[lane] = LRT_TRI_NO_HIT;
            }
        }
    }
    cc->leaf_count++;
    cc->sah_leaf += (double)(tri_surface_area(bn->lo, bn->hi) / cc->root_area) *
                    (double)count;
    return TRI_MAKE_LEAF_REF(first_block, nblocks);
}

static uint32_t tri_collapse(tri_collapse_ctx *cc, uint32_t b_idx,
                             uint32_t depth);

/* Fill one wide-node slot from binary node m_idx. */
static void tri_fill_slot(tri_collapse_ctx *cc, uint32_t m_idx, uint32_t depth,
                          float *lo_x, float *lo_y, float *lo_z, float *hi_x,
                          float *hi_y, float *hi_z, uint32_t *child, int slot) {
    const tri_bnode *m = &cc->bc->bnodes[m_idx];
    lo_x[slot] = m->lo[0];
    lo_y[slot] = m->lo[1];
    lo_z[slot] = m->lo[2];
    hi_x[slot] = m->hi[0];
    hi_y[slot] = m->hi[1];
    hi_z[slot] = m->hi[2];
    child[slot] = tri_collapse(cc, m_idx, depth);
}

/* Collapse the binary subtree at b_idx into a wide node (or leaf ref). */
static uint32_t tri_collapse(tri_collapse_ctx *cc, uint32_t b_idx,
                             uint32_t depth) {
    if (cc->failed) return 0;
    const tri_bnode *bn = &cc->bc->bnodes[b_idx];
    if (depth > cc->max_depth) cc->max_depth = depth;

    if (bn->count > 0) return tri_emit_leaf(cc, bn);

    /* Gather up to `width` binary children by repeatedly expanding the inner
     * member with the largest surface area. */
    uint32_t set[8];
    int n = 0;
    set[n++] = bn->a;
    set[n++] = bn->b;
    const int width = cc->width;
    while (n < width) {
        int expand = -1;
        float best_area = -1.0f;
        for (int i = 0; i < n; i++) {
            const tri_bnode *m = &cc->bc->bnodes[set[i]];
            if (m->count > 0) continue; /* leaf: cannot expand */
            float area = tri_surface_area(m->lo, m->hi);
            if (area > best_area) {
                best_area = area;
                expand = i;
            }
        }
        if (expand < 0) break;
        uint32_t inner = set[expand];
        const tri_bnode *m = &cc->bc->bnodes[inner];
        set[expand] = m->a;
        set[n++] = m->b;
    }

    lrt_tri_scene *s = cc->s;
    if (s->node_count >= cc->node_cap) {
        cc->failed = 1;
        return 0;
    }
    uint32_t node_idx = s->node_count++;
    cc->sah_inner += (double)(tri_surface_area(bn->lo, bn->hi) / cc->root_area);

    if (width == 4) {
        lrt_bvh4_node *w = &s->nodes4[node_idx];
        memset(w, 0, sizeof(*w));
        /* Empty slots: a degenerate point box at +INF. SIMD kernels also mask
         * lanes >= nchildren, so these values are only a second line of
         * defense (a min/max slab test would otherwise accept an inverted
         * lo > hi box after its min/max swap). */
        for (int i = 0; i < 4; i++) {
            w->lo_x[i] = w->lo_y[i] = w->lo_z[i] = TRI_INF_F;
            w->hi_x[i] = w->hi_y[i] = w->hi_z[i] = TRI_INF_F;
        }
        w->nchildren = (uint32_t)n;
        for (int i = 0; i < n; i++) {
            /* w may move only if nodes4 reallocated; capacity is fixed. */
            tri_fill_slot(cc, set[i], depth + 1, s->nodes4[node_idx].lo_x,
                          s->nodes4[node_idx].lo_y, s->nodes4[node_idx].lo_z,
                          s->nodes4[node_idx].hi_x, s->nodes4[node_idx].hi_y,
                          s->nodes4[node_idx].hi_z, s->nodes4[node_idx].child,
                          i);
        }
    } else if (cc->quantized) {
        lrt_bvh8q_node *w = &s->nodes8q[node_idx];
        memset(w, 0, sizeof(*w));
        float scale[3], inv_scale[3];
        for (int a = 0; a < 3; a++) {
            w->org[a] = bn->lo[a];
            float ext = bn->hi[a] - bn->lo[a];
            /* small relative inflation guarantees org + 255*scale >= hi
             * despite rounding in the decode arithmetic */
            scale[a] = ext > 0.0f ? (ext / 255.0f) * (1.0f + 4e-7f) : 0.0f;
            inv_scale[a] = scale[a] > 0.0f ? 1.0f / scale[a] : 0.0f;
            w->scale[a] = scale[a];
        }
        for (int i = 0; i < 8; i++) { /* empty slots decode inverted */
            w->qlo_x[i] = w->qlo_y[i] = w->qlo_z[i] = 255;
            w->qhi_x[i] = w->qhi_y[i] = w->qhi_z[i] = 0;
        }
        w->nchildren = (uint32_t)n;
        for (int i = 0; i < n; i++) {
            const tri_bnode *m = &cc->bc->bnodes[set[i]];
            w = &s->nodes8q[node_idx];
            w->qlo_x[i] = tri_quantize_lo(m->lo[0], w->org[0], scale[0], inv_scale[0]);
            w->qlo_y[i] = tri_quantize_lo(m->lo[1], w->org[1], scale[1], inv_scale[1]);
            w->qlo_z[i] = tri_quantize_lo(m->lo[2], w->org[2], scale[2], inv_scale[2]);
            w->qhi_x[i] = tri_quantize_hi(m->hi[0], w->org[0], scale[0], inv_scale[0]);
            w->qhi_y[i] = tri_quantize_hi(m->hi[1], w->org[1], scale[1], inv_scale[1]);
            w->qhi_z[i] = tri_quantize_hi(m->hi[2], w->org[2], scale[2], inv_scale[2]);
            uint32_t ref = tri_collapse(cc, set[i], depth + 1);
            s->nodes8q[node_idx].child[i] = ref;
        }
    } else {
        lrt_bvh8_node *w = &s->nodes8[node_idx];
        memset(w, 0, sizeof(*w));
        for (int i = 0; i < 8; i++) {
            w->lo_x[i] = w->lo_y[i] = w->lo_z[i] = TRI_INF_F;
            w->hi_x[i] = w->hi_y[i] = w->hi_z[i] = TRI_INF_F;
        }
        w->nchildren = (uint32_t)n;
        for (int i = 0; i < n; i++) {
            tri_fill_slot(cc, set[i], depth + 1, s->nodes8[node_idx].lo_x,
                          s->nodes8[node_idx].lo_y, s->nodes8[node_idx].lo_z,
                          s->nodes8[node_idx].hi_x, s->nodes8[node_idx].hi_y,
                          s->nodes8[node_idx].hi_z, s->nodes8[node_idx].child,
                          i);
        }
    }
    return TRI_MAKE_NODE_REF(node_idx);
}

/* ------------------------------------------------------------------------- */
/* Ray setup shared by all kernels.                                          */
/* ------------------------------------------------------------------------- */

typedef struct tri_ray_ctx {
    float org[3];
    float dir[3];
    float invd[3]; /* infinite components replaced by +/-FLT_MAX */
    float tmin;
} tri_ray_ctx;

/* Degenerate direction components get a finite huge inverse instead of inf.
 * 1e18 (not FLT_MAX) so that the quantized-node decode, which multiplies
 * invd by a node-local scale, cannot overflow to inf and produce 0 * inf
 * NaNs; |dir| < 1e-18 is treated as zero. */
#define TRI_INVD_MAX 1e18f

static inline void tri_ray_setup(const lrt_ray *ray, tri_ray_ctx *rc) {
    for (int k = 0; k < 3; k++) {
        rc->org[k] = ray->org[k];
        rc->dir[k] = ray->dir[k];
        float inv = 1.0f / ray->dir[k];
        if (!(inv >= -TRI_INVD_MAX && inv <= TRI_INVD_MAX)) {
            inv = copysignf(TRI_INVD_MAX, ray->dir[k] == 0.0f ? 1.0f : ray->dir[k]);
        }
        rc->invd[k] = inv;
    }
    rc->tmin = ray->tmin;
}

typedef struct tri_stack_entry {
    uint32_t ref;
    float tnear;
} tri_stack_entry;

#if LRT_TRI_HAS_SSE4
/* Prefetch the data a child ref will touch when popped: the bounds planes of
 * an inner node (2 lines for BVH4, 3 for BVH8), or the first triangle block
 * of a leaf. Incoherent rays make these fetches the critical path. */
static inline void tri_prefetch_ref(const lrt_tri_scene *s, uint32_t ref,
                                    int width) {
    if (TRI_REF_IS_LEAF(ref)) {
        const char *b = (const char *)tri_block_floats(s->blocks,
                                                       TRI_REF_BLOCK(ref), width);
        _mm_prefetch(b, _MM_HINT_T0);
        _mm_prefetch(b + 64, _MM_HINT_T0);
        return;
    }
    if (s->quantized) {
        const char *p = (const char *)&s->nodes8q[TRI_REF_NODE(ref)];
        _mm_prefetch(p, _MM_HINT_T0);
        _mm_prefetch(p + 64, _MM_HINT_T0);
        return;
    }
    const char *p = (width == 4) ? (const char *)&s->nodes4[TRI_REF_NODE(ref)]
                                 : (const char *)&s->nodes8[TRI_REF_NODE(ref)];
    _mm_prefetch(p, _MM_HINT_T0);
    _mm_prefetch(p + 64, _MM_HINT_T0);
    if (width == 8) {
        _mm_prefetch(p + 128, _MM_HINT_T0);
        _mm_prefetch(p + 192, _MM_HINT_T0); /* child refs */
    }
}
#endif

/* ------------------------------------------------------------------------- */
/* Scalar kernels (always compiled; fallback + correctness oracle).          */
/* ------------------------------------------------------------------------- */

/* Moller-Trumbore on one lane of a generic-width block (f = 9 float arrays of
 * `bw` lanes). Returns 1 on hit in (tmin, t_best). */
static inline int tri_isect_lane(const float *f, int bw, int lane,
                                 const tri_ray_ctx *rc, float t_best, float *t,
                                 float *u, float *v) {
    float e1x = f[3 * bw + lane], e1y = f[4 * bw + lane], e1z = f[5 * bw + lane];
    float e2x = f[6 * bw + lane], e2y = f[7 * bw + lane], e2z = f[8 * bw + lane];
    float px = rc->dir[1] * e2z - rc->dir[2] * e2y;
    float py = rc->dir[2] * e2x - rc->dir[0] * e2z;
    float pz = rc->dir[0] * e2y - rc->dir[1] * e2x;
    float det = e1x * px + e1y * py + e1z * pz;
    if (det > -1e-12f && det < 1e-12f) return 0;
    float inv_det = 1.0f / det;
    float tvx = rc->org[0] - f[0 * bw + lane];
    float tvy = rc->org[1] - f[1 * bw + lane];
    float tvz = rc->org[2] - f[2 * bw + lane];
    float uu = (tvx * px + tvy * py + tvz * pz) * inv_det;
    if (uu < 0.0f || uu > 1.0f) return 0;
    float qx = tvy * e1z - tvz * e1y;
    float qy = tvz * e1x - tvx * e1z;
    float qz = tvx * e1y - tvy * e1x;
    float vv = (rc->dir[0] * qx + rc->dir[1] * qy + rc->dir[2] * qz) * inv_det;
    if (vv < 0.0f || uu + vv > 1.0f) return 0;
    float tt = (e2x * qx + e2y * qy + e2z * qz) * inv_det;
    if (tt < rc->tmin || tt >= t_best) return 0;
    *t = tt;
    *u = uu;
    *v = vv;
    return 1;
}

/* Decode a quantized node's child bounds to floats (scalar fallback path). */
static inline void tri_bvh8q_decode(const lrt_bvh8q_node *n, float *lo_x,
                                    float *lo_y, float *lo_z, float *hi_x,
                                    float *hi_y, float *hi_z) {
    for (int i = 0; i < 8; i++) {
        lo_x[i] = n->org[0] + (float)n->qlo_x[i] * n->scale[0];
        lo_y[i] = n->org[1] + (float)n->qlo_y[i] * n->scale[1];
        lo_z[i] = n->org[2] + (float)n->qlo_z[i] * n->scale[2];
        hi_x[i] = n->org[0] + (float)n->qhi_x[i] * n->scale[0];
        hi_y[i] = n->org[1] + (float)n->qhi_y[i] * n->scale[1];
        hi_z[i] = n->org[2] + (float)n->qhi_z[i] * n->scale[2];
    }
}

/* Scalar slab test for slot `i` of SoA bounds arrays. */
static inline int tri_slab_scalar(const float *lo_x, const float *lo_y,
                                  const float *lo_z, const float *hi_x,
                                  const float *hi_y, const float *hi_z, int i,
                                  const tri_ray_ctx *rc, float t_best,
                                  float *tnear_out) {
    float tlx = (lo_x[i] - rc->org[0]) * rc->invd[0];
    float thx = (hi_x[i] - rc->org[0]) * rc->invd[0];
    float tly = (lo_y[i] - rc->org[1]) * rc->invd[1];
    float thy = (hi_y[i] - rc->org[1]) * rc->invd[1];
    float tlz = (lo_z[i] - rc->org[2]) * rc->invd[2];
    float thz = (hi_z[i] - rc->org[2]) * rc->invd[2];
    float tnx = tri_minf(tlx, thx), tfx = tri_maxf(tlx, thx);
    float tny = tri_minf(tly, thy), tfy = tri_maxf(tly, thy);
    float tnz = tri_minf(tlz, thz), tfz = tri_maxf(tlz, thz);
    float tnear = tri_maxf(tri_maxf(tnx, tny), tri_maxf(tnz, rc->tmin));
    float tfar = tri_minf(tri_minf(tfx, tfy), tri_minf(tfz, t_best));
    *tnear_out = tnear;
    return tnear <= tfar;
}

/* Generic-width scalar traversal. */
static int tri_intersect_scalar(const lrt_tri_scene *s, const lrt_ray *ray,
                                lrt_hit *hit) {
    tri_ray_ctx rc;
    tri_ray_setup(ray, &rc);
    float best_t = ray->tmax;
    float best_u = 0.0f, best_v = 0.0f;
    uint32_t best_prim = LRT_TRI_NO_HIT;
    const int width = s->layout;

    tri_stack_entry stack[TRI_STACK_SIZE];
    int sp = 0;
    stack[sp].ref = s->root;
    stack[sp].tnear = rc.tmin;
    sp++;

    while (sp > 0) {
        tri_stack_entry e = stack[--sp];
        if (e.tnear >= best_t) continue;
        if (TRI_REF_IS_LEAF(e.ref)) {
            uint32_t blk0 = TRI_REF_BLOCK(e.ref);
            uint32_t nblk = TRI_REF_NBLOCKS(e.ref);
            for (uint32_t b = 0; b < nblk; b++) {
                const float *f = tri_block_floats(s->blocks, blk0 + b, width);
                const uint32_t *ids = (const uint32_t *)(f + 9 * width);
                for (int lane = 0; lane < width; lane++) {
                    if (ids[lane] == LRT_TRI_NO_HIT) continue;
                    float t, u, v;
                    if (tri_isect_lane(f, width, lane, &rc, best_t, &t, &u, &v)) {
                        best_t = t;
                        best_u = u;
                        best_v = v;
                        best_prim = ids[lane];
                    }
                }
            }
            continue;
        }

        const float *lo_x, *lo_y, *lo_z, *hi_x, *hi_y, *hi_z;
        const uint32_t *child;
        int nchildren;
        float dec[48]; /* decode buffer for quantized nodes */
        if (width == 4) {
            const lrt_bvh4_node *n = &s->nodes4[TRI_REF_NODE(e.ref)];
            lo_x = n->lo_x; lo_y = n->lo_y; lo_z = n->lo_z;
            hi_x = n->hi_x; hi_y = n->hi_y; hi_z = n->hi_z;
            child = n->child;
            nchildren = (int)n->nchildren;
        } else if (s->quantized) {
            const lrt_bvh8q_node *n = &s->nodes8q[TRI_REF_NODE(e.ref)];
            tri_bvh8q_decode(n, dec, dec + 8, dec + 16, dec + 24, dec + 32,
                             dec + 40);
            lo_x = dec; lo_y = dec + 8; lo_z = dec + 16;
            hi_x = dec + 24; hi_y = dec + 32; hi_z = dec + 40;
            child = n->child;
            nchildren = (int)n->nchildren;
        } else {
            const lrt_bvh8_node *n = &s->nodes8[TRI_REF_NODE(e.ref)];
            lo_x = n->lo_x; lo_y = n->lo_y; lo_z = n->lo_z;
            hi_x = n->hi_x; hi_y = n->hi_y; hi_z = n->hi_z;
            child = n->child;
            nchildren = (int)n->nchildren;
        }

        /* Test children, then push hits sorted far-to-near so the nearest is
         * popped first. */
        uint32_t hit_ref[8];
        float hit_tnear[8];
        int nhit = 0;
        for (int i = 0; i < nchildren; i++) {
            float tnear;
            if (tri_slab_scalar(lo_x, lo_y, lo_z, hi_x, hi_y, hi_z, i, &rc,
                                best_t, &tnear)) {
                /* insertion: keep ascending tnear */
                int j = nhit++;
                while (j > 0 && hit_tnear[j - 1] > tnear) {
                    hit_tnear[j] = hit_tnear[j - 1];
                    hit_ref[j] = hit_ref[j - 1];
                    j--;
                }
                hit_tnear[j] = tnear;
                hit_ref[j] = child[i];
            }
        }
        if (sp + nhit > TRI_STACK_SIZE) return 0; /* cannot happen: depth-capped */
        for (int i = nhit - 1; i >= 0; i--) {
            stack[sp].ref = hit_ref[i];
            stack[sp].tnear = hit_tnear[i];
            sp++;
        }
    }

    if (hit) {
        hit->t = best_prim != LRT_TRI_NO_HIT ? best_t : 0.0f;
        hit->u = best_u;
        hit->v = best_v;
        hit->prim_id = best_prim;
    }
    return best_prim != LRT_TRI_NO_HIT;
}

static int tri_occluded_scalar(const lrt_tri_scene *s, const lrt_ray *ray) {
    tri_ray_ctx rc;
    tri_ray_setup(ray, &rc);
    const float t_max = ray->tmax;
    const int width = s->layout;

    uint32_t stack[TRI_STACK_SIZE];
    int sp = 0;
    stack[sp++] = s->root;

    while (sp > 0) {
        uint32_t ref = stack[--sp];
        if (TRI_REF_IS_LEAF(ref)) {
            uint32_t blk0 = TRI_REF_BLOCK(ref);
            uint32_t nblk = TRI_REF_NBLOCKS(ref);
            for (uint32_t b = 0; b < nblk; b++) {
                const float *f = tri_block_floats(s->blocks, blk0 + b, width);
                const uint32_t *ids = (const uint32_t *)(f + 9 * width);
                for (int lane = 0; lane < width; lane++) {
                    if (ids[lane] == LRT_TRI_NO_HIT) continue;
                    float t, u, v;
                    if (tri_isect_lane(f, width, lane, &rc, t_max, &t, &u, &v)) {
                        return 1;
                    }
                }
            }
            continue;
        }

        const float *lo_x, *lo_y, *lo_z, *hi_x, *hi_y, *hi_z;
        const uint32_t *child;
        int nchildren;
        float dec[48];
        if (width == 4) {
            const lrt_bvh4_node *n = &s->nodes4[TRI_REF_NODE(ref)];
            lo_x = n->lo_x; lo_y = n->lo_y; lo_z = n->lo_z;
            hi_x = n->hi_x; hi_y = n->hi_y; hi_z = n->hi_z;
            child = n->child;
            nchildren = (int)n->nchildren;
        } else if (s->quantized) {
            const lrt_bvh8q_node *n = &s->nodes8q[TRI_REF_NODE(ref)];
            tri_bvh8q_decode(n, dec, dec + 8, dec + 16, dec + 24, dec + 32,
                             dec + 40);
            lo_x = dec; lo_y = dec + 8; lo_z = dec + 16;
            hi_x = dec + 24; hi_y = dec + 32; hi_z = dec + 40;
            child = n->child;
            nchildren = (int)n->nchildren;
        } else {
            const lrt_bvh8_node *n = &s->nodes8[TRI_REF_NODE(ref)];
            lo_x = n->lo_x; lo_y = n->lo_y; lo_z = n->lo_z;
            hi_x = n->hi_x; hi_y = n->hi_y; hi_z = n->hi_z;
            child = n->child;
            nchildren = (int)n->nchildren;
        }
        if (sp + nchildren > TRI_STACK_SIZE) return 0;
        for (int i = 0; i < nchildren; i++) {
            float tnear;
            if (tri_slab_scalar(lo_x, lo_y, lo_z, hi_x, hi_y, hi_z, i, &rc,
                                t_max, &tnear)) {
                stack[sp++] = child[i];
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------------------- */
/* SSE4 kernels (BVH4).                                                      */
/* ------------------------------------------------------------------------- */
#if LRT_TRI_HAS_SSE4

typedef struct tri_sse_ctx {
    __m128 orgx, orgy, orgz;
    __m128 invdx, invdy, invdz;
    __m128 dirx, diry, dirz;
    __m128 tmin;
} tri_sse_ctx;

static inline void tri_sse_setup(const tri_ray_ctx *rc, tri_sse_ctx *sc) {
    sc->orgx = _mm_set1_ps(rc->org[0]);
    sc->orgy = _mm_set1_ps(rc->org[1]);
    sc->orgz = _mm_set1_ps(rc->org[2]);
    sc->invdx = _mm_set1_ps(rc->invd[0]);
    sc->invdy = _mm_set1_ps(rc->invd[1]);
    sc->invdz = _mm_set1_ps(rc->invd[2]);
    sc->dirx = _mm_set1_ps(rc->dir[0]);
    sc->diry = _mm_set1_ps(rc->dir[1]);
    sc->dirz = _mm_set1_ps(rc->dir[2]);
    sc->tmin = _mm_set1_ps(rc->tmin);
}

/* One ray vs the 4 child boxes of a BVH4 node. Returns hit mask; writes the
 * per-slot entry distances to tnear_out (aligned 16). */
static inline int tri_bvh4_slab_sse(const lrt_bvh4_node *n,
                                    const tri_sse_ctx *sc, __m128 t_best,
                                    float *tnear_out) {
    __m128 tlx = _mm_mul_ps(_mm_sub_ps(_mm_load_ps(n->lo_x), sc->orgx), sc->invdx);
    __m128 thx = _mm_mul_ps(_mm_sub_ps(_mm_load_ps(n->hi_x), sc->orgx), sc->invdx);
    __m128 tly = _mm_mul_ps(_mm_sub_ps(_mm_load_ps(n->lo_y), sc->orgy), sc->invdy);
    __m128 thy = _mm_mul_ps(_mm_sub_ps(_mm_load_ps(n->hi_y), sc->orgy), sc->invdy);
    __m128 tlz = _mm_mul_ps(_mm_sub_ps(_mm_load_ps(n->lo_z), sc->orgz), sc->invdz);
    __m128 thz = _mm_mul_ps(_mm_sub_ps(_mm_load_ps(n->hi_z), sc->orgz), sc->invdz);
    __m128 tnear = _mm_max_ps(
        _mm_max_ps(_mm_min_ps(tlx, thx), _mm_min_ps(tly, thy)),
        _mm_max_ps(_mm_min_ps(tlz, thz), sc->tmin));
    __m128 tfar = _mm_min_ps(
        _mm_min_ps(_mm_max_ps(tlx, thx), _mm_max_ps(tly, thy)),
        _mm_min_ps(_mm_max_ps(tlz, thz), t_best));
    _mm_store_ps(tnear_out, tnear);
    return _mm_movemask_ps(_mm_cmple_ps(tnear, tfar));
}

/* 4-wide SoA Moller-Trumbore over one block. Updates best hit in place. */
static inline void tri_block_isect_sse(const lrt_tri4 *blk,
                                       const tri_sse_ctx *sc, float *best_t,
                                       float *best_u, float *best_v,
                                       uint32_t *best_prim) {
    __m128 e1x = _mm_load_ps(blk->e1x), e1y = _mm_load_ps(blk->e1y),
           e1z = _mm_load_ps(blk->e1z);
    __m128 e2x = _mm_load_ps(blk->e2x), e2y = _mm_load_ps(blk->e2y),
           e2z = _mm_load_ps(blk->e2z);

    /* pvec = dir x e2 */
    __m128 px = _mm_sub_ps(_mm_mul_ps(sc->diry, e2z), _mm_mul_ps(sc->dirz, e2y));
    __m128 py = _mm_sub_ps(_mm_mul_ps(sc->dirz, e2x), _mm_mul_ps(sc->dirx, e2z));
    __m128 pz = _mm_sub_ps(_mm_mul_ps(sc->dirx, e2y), _mm_mul_ps(sc->diry, e2x));

    __m128 det = _mm_add_ps(_mm_add_ps(_mm_mul_ps(e1x, px), _mm_mul_ps(e1y, py)),
                            _mm_mul_ps(e1z, pz));
    const __m128 abs_mask = _mm_castsi128_ps(_mm_set1_epi32(0x7FFFFFFF));
    __m128 valid = _mm_cmpgt_ps(_mm_and_ps(det, abs_mask), _mm_set1_ps(1e-12f));
    if (!_mm_movemask_ps(valid)) return;

    __m128 inv_det = _mm_div_ps(_mm_set1_ps(1.0f), det);

    __m128 tvx = _mm_sub_ps(sc->orgx, _mm_load_ps(blk->v0x));
    __m128 tvy = _mm_sub_ps(sc->orgy, _mm_load_ps(blk->v0y));
    __m128 tvz = _mm_sub_ps(sc->orgz, _mm_load_ps(blk->v0z));

    __m128 u = _mm_mul_ps(
        _mm_add_ps(_mm_add_ps(_mm_mul_ps(tvx, px), _mm_mul_ps(tvy, py)),
                   _mm_mul_ps(tvz, pz)),
        inv_det);
    valid = _mm_and_ps(valid, _mm_cmpge_ps(u, _mm_setzero_ps()));
    valid = _mm_and_ps(valid, _mm_cmple_ps(u, _mm_set1_ps(1.0f)));
    if (!_mm_movemask_ps(valid)) return;

    /* qvec = tvec x e1 */
    __m128 qx = _mm_sub_ps(_mm_mul_ps(tvy, e1z), _mm_mul_ps(tvz, e1y));
    __m128 qy = _mm_sub_ps(_mm_mul_ps(tvz, e1x), _mm_mul_ps(tvx, e1z));
    __m128 qz = _mm_sub_ps(_mm_mul_ps(tvx, e1y), _mm_mul_ps(tvy, e1x));

    __m128 v = _mm_mul_ps(
        _mm_add_ps(_mm_add_ps(_mm_mul_ps(sc->dirx, qx), _mm_mul_ps(sc->diry, qy)),
                   _mm_mul_ps(sc->dirz, qz)),
        inv_det);
    valid = _mm_and_ps(valid, _mm_cmpge_ps(v, _mm_setzero_ps()));
    valid = _mm_and_ps(valid, _mm_cmple_ps(_mm_add_ps(u, v), _mm_set1_ps(1.0f)));
    if (!_mm_movemask_ps(valid)) return;

    __m128 t = _mm_mul_ps(
        _mm_add_ps(_mm_add_ps(_mm_mul_ps(e2x, qx), _mm_mul_ps(e2y, qy)),
                   _mm_mul_ps(e2z, qz)),
        inv_det);
    valid = _mm_and_ps(valid, _mm_cmpge_ps(t, sc->tmin));
    valid = _mm_and_ps(valid, _mm_cmplt_ps(t, _mm_set1_ps(*best_t)));
    int mask = _mm_movemask_ps(valid);
    if (!mask) return;

    float ta[4], ua[4], va[4];
    _mm_storeu_ps(ta, t);
    _mm_storeu_ps(ua, u);
    _mm_storeu_ps(va, v);
    while (mask) {
        int lane = __builtin_ctz((unsigned)mask);
        mask &= mask - 1;
        if (ta[lane] < *best_t) {
            *best_t = ta[lane];
            *best_u = ua[lane];
            *best_v = va[lane];
            *best_prim = blk->prim_id[lane];
        }
    }
}

/* Any-hit variant: returns 1 if any lane hits within (tmin, tmax]. */
static inline int tri_block_occluded_sse(const lrt_tri4 *blk,
                                         const tri_sse_ctx *sc, __m128 tmax) {
    __m128 e1x = _mm_load_ps(blk->e1x), e1y = _mm_load_ps(blk->e1y),
           e1z = _mm_load_ps(blk->e1z);
    __m128 e2x = _mm_load_ps(blk->e2x), e2y = _mm_load_ps(blk->e2y),
           e2z = _mm_load_ps(blk->e2z);
    __m128 px = _mm_sub_ps(_mm_mul_ps(sc->diry, e2z), _mm_mul_ps(sc->dirz, e2y));
    __m128 py = _mm_sub_ps(_mm_mul_ps(sc->dirz, e2x), _mm_mul_ps(sc->dirx, e2z));
    __m128 pz = _mm_sub_ps(_mm_mul_ps(sc->dirx, e2y), _mm_mul_ps(sc->diry, e2x));
    __m128 det = _mm_add_ps(_mm_add_ps(_mm_mul_ps(e1x, px), _mm_mul_ps(e1y, py)),
                            _mm_mul_ps(e1z, pz));
    const __m128 abs_mask = _mm_castsi128_ps(_mm_set1_epi32(0x7FFFFFFF));
    __m128 valid = _mm_cmpgt_ps(_mm_and_ps(det, abs_mask), _mm_set1_ps(1e-12f));
    if (!_mm_movemask_ps(valid)) return 0;
    __m128 inv_det = _mm_div_ps(_mm_set1_ps(1.0f), det);
    __m128 tvx = _mm_sub_ps(sc->orgx, _mm_load_ps(blk->v0x));
    __m128 tvy = _mm_sub_ps(sc->orgy, _mm_load_ps(blk->v0y));
    __m128 tvz = _mm_sub_ps(sc->orgz, _mm_load_ps(blk->v0z));
    __m128 u = _mm_mul_ps(
        _mm_add_ps(_mm_add_ps(_mm_mul_ps(tvx, px), _mm_mul_ps(tvy, py)),
                   _mm_mul_ps(tvz, pz)),
        inv_det);
    valid = _mm_and_ps(valid, _mm_cmpge_ps(u, _mm_setzero_ps()));
    valid = _mm_and_ps(valid, _mm_cmple_ps(u, _mm_set1_ps(1.0f)));
    if (!_mm_movemask_ps(valid)) return 0;
    __m128 qx = _mm_sub_ps(_mm_mul_ps(tvy, e1z), _mm_mul_ps(tvz, e1y));
    __m128 qy = _mm_sub_ps(_mm_mul_ps(tvz, e1x), _mm_mul_ps(tvx, e1z));
    __m128 qz = _mm_sub_ps(_mm_mul_ps(tvx, e1y), _mm_mul_ps(tvy, e1x));
    __m128 v = _mm_mul_ps(
        _mm_add_ps(_mm_add_ps(_mm_mul_ps(sc->dirx, qx), _mm_mul_ps(sc->diry, qy)),
                   _mm_mul_ps(sc->dirz, qz)),
        inv_det);
    valid = _mm_and_ps(valid, _mm_cmpge_ps(v, _mm_setzero_ps()));
    valid = _mm_and_ps(valid, _mm_cmple_ps(_mm_add_ps(u, v), _mm_set1_ps(1.0f)));
    if (!_mm_movemask_ps(valid)) return 0;
    __m128 t = _mm_mul_ps(
        _mm_add_ps(_mm_add_ps(_mm_mul_ps(e2x, qx), _mm_mul_ps(e2y, qy)),
                   _mm_mul_ps(e2z, qz)),
        inv_det);
    valid = _mm_and_ps(valid, _mm_cmpge_ps(t, sc->tmin));
    valid = _mm_and_ps(valid, _mm_cmple_ps(t, tmax));
    return _mm_movemask_ps(valid) != 0;
}

static int tri_intersect_bvh4_sse(const lrt_tri_scene *s, const lrt_ray *ray,
                                  lrt_hit *hit) {
    tri_ray_ctx rc;
    tri_ray_setup(ray, &rc);
    tri_sse_ctx sc;
    tri_sse_setup(&rc, &sc);

    float best_t = ray->tmax;
    float best_u = 0.0f, best_v = 0.0f;
    uint32_t best_prim = LRT_TRI_NO_HIT;

    tri_stack_entry stack[TRI_STACK_SIZE];
    int sp = 0;
    stack[sp].ref = s->root;
    stack[sp].tnear = rc.tmin;
    sp++;

    while (sp > 0) {
        tri_stack_entry e = stack[--sp];
        if (e.tnear >= best_t) continue;
        if (TRI_REF_IS_LEAF(e.ref)) {
            uint32_t blk0 = TRI_REF_BLOCK(e.ref);
            uint32_t nblk = TRI_REF_NBLOCKS(e.ref);
            const lrt_tri4 *blocks = (const lrt_tri4 *)s->blocks;
            for (uint32_t b = 0; b < nblk; b++) {
                tri_block_isect_sse(&blocks[blk0 + b], &sc, &best_t, &best_u,
                                    &best_v, &best_prim);
            }
            continue;
        }

        const lrt_bvh4_node *n = &s->nodes4[TRI_REF_NODE(e.ref)];
        _Alignas(16) float tnear[4];
        int mask = tri_bvh4_slab_sse(n, &sc, _mm_set1_ps(best_t), tnear);
        mask &= (1 << n->nchildren) - 1;
        /* Push hit children sorted far-to-near (insertion over <=4). */
        uint32_t hit_ref[4];
        float hit_tn[4];
        int nhit = 0;
        while (mask) {
            int i = __builtin_ctz((unsigned)mask);
            mask &= mask - 1;
            tri_prefetch_ref(s, n->child[i], 4);
            int j = nhit++;
            while (j > 0 && hit_tn[j - 1] > tnear[i]) {
                hit_tn[j] = hit_tn[j - 1];
                hit_ref[j] = hit_ref[j - 1];
                j--;
            }
            hit_tn[j] = tnear[i];
            hit_ref[j] = n->child[i];
        }
        for (int i = nhit - 1; i >= 0; i--) {
            stack[sp].ref = hit_ref[i];
            stack[sp].tnear = hit_tn[i];
            sp++;
        }
    }

    if (hit) {
        hit->t = best_prim != LRT_TRI_NO_HIT ? best_t : 0.0f;
        hit->u = best_u;
        hit->v = best_v;
        hit->prim_id = best_prim;
    }
    return best_prim != LRT_TRI_NO_HIT;
}

static int tri_occluded_bvh4_sse(const lrt_tri_scene *s, const lrt_ray *ray) {
    tri_ray_ctx rc;
    tri_ray_setup(ray, &rc);
    tri_sse_ctx sc;
    tri_sse_setup(&rc, &sc);
    __m128 tmax4 = _mm_set1_ps(ray->tmax);

    uint32_t stack[TRI_STACK_SIZE];
    int sp = 0;
    stack[sp++] = s->root;

    while (sp > 0) {
        uint32_t ref = stack[--sp];
        if (TRI_REF_IS_LEAF(ref)) {
            uint32_t blk0 = TRI_REF_BLOCK(ref);
            uint32_t nblk = TRI_REF_NBLOCKS(ref);
            const lrt_tri4 *blocks = (const lrt_tri4 *)s->blocks;
            for (uint32_t b = 0; b < nblk; b++) {
                if (tri_block_occluded_sse(&blocks[blk0 + b], &sc, tmax4)) {
                    return 1;
                }
            }
            continue;
        }
        const lrt_bvh4_node *n = &s->nodes4[TRI_REF_NODE(ref)];
        _Alignas(16) float tnear[4];
        int mask = tri_bvh4_slab_sse(n, &sc, tmax4, tnear);
        mask &= (1 << n->nchildren) - 1;
        while (mask) {
            int i = __builtin_ctz((unsigned)mask);
            mask &= mask - 1;
            stack[sp++] = n->child[i];
        }
    }
    return 0;
}

#endif /* LRT_TRI_HAS_SSE4 */

/* ------------------------------------------------------------------------- */
/* AVX2 kernels (BVH8). Leaf blocks remain 4-wide SSE.                       */
/* ------------------------------------------------------------------------- */
#if LRT_TRI_HAS_AVX2

typedef struct tri_avx_ctx {
    __m256 orgx, orgy, orgz;
    __m256 invdx, invdy, invdz;
    __m256 dirx, diry, dirz;
    __m256 tmin;
} tri_avx_ctx;

static inline void tri_avx_setup(const tri_ray_ctx *rc, tri_avx_ctx *ac) {
    ac->orgx = _mm256_set1_ps(rc->org[0]);
    ac->orgy = _mm256_set1_ps(rc->org[1]);
    ac->orgz = _mm256_set1_ps(rc->org[2]);
    ac->invdx = _mm256_set1_ps(rc->invd[0]);
    ac->invdy = _mm256_set1_ps(rc->invd[1]);
    ac->invdz = _mm256_set1_ps(rc->invd[2]);
    ac->dirx = _mm256_set1_ps(rc->dir[0]);
    ac->diry = _mm256_set1_ps(rc->dir[1]);
    ac->dirz = _mm256_set1_ps(rc->dir[2]);
    ac->tmin = _mm256_set1_ps(rc->tmin);
}

/* 8-wide SoA Moller-Trumbore over one lrt_tri8 block. Updates best in place. */
static inline void tri_block_isect_avx(const lrt_tri8 *blk,
                                       const tri_avx_ctx *ac, float *best_t,
                                       float *best_u, float *best_v,
                                       uint32_t *best_prim) {
    __m256 e1x = _mm256_load_ps(blk->e1x), e1y = _mm256_load_ps(blk->e1y),
           e1z = _mm256_load_ps(blk->e1z);
    __m256 e2x = _mm256_load_ps(blk->e2x), e2y = _mm256_load_ps(blk->e2y),
           e2z = _mm256_load_ps(blk->e2z);

    __m256 px = _mm256_fmsub_ps(ac->diry, e2z, _mm256_mul_ps(ac->dirz, e2y));
    __m256 py = _mm256_fmsub_ps(ac->dirz, e2x, _mm256_mul_ps(ac->dirx, e2z));
    __m256 pz = _mm256_fmsub_ps(ac->dirx, e2y, _mm256_mul_ps(ac->diry, e2x));

    __m256 det = _mm256_fmadd_ps(
        e1x, px, _mm256_fmadd_ps(e1y, py, _mm256_mul_ps(e1z, pz)));
    const __m256 abs_mask = _mm256_castsi256_ps(_mm256_set1_epi32(0x7FFFFFFF));
    __m256 valid =
        _mm256_cmp_ps(_mm256_and_ps(det, abs_mask), _mm256_set1_ps(1e-12f),
                      _CMP_GT_OQ);
    if (!_mm256_movemask_ps(valid)) return;

    __m256 inv_det = _mm256_div_ps(_mm256_set1_ps(1.0f), det);

    __m256 tvx = _mm256_sub_ps(ac->orgx, _mm256_load_ps(blk->v0x));
    __m256 tvy = _mm256_sub_ps(ac->orgy, _mm256_load_ps(blk->v0y));
    __m256 tvz = _mm256_sub_ps(ac->orgz, _mm256_load_ps(blk->v0z));

    __m256 u = _mm256_mul_ps(
        _mm256_fmadd_ps(tvx, px, _mm256_fmadd_ps(tvy, py, _mm256_mul_ps(tvz, pz))),
        inv_det);
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(u, _mm256_setzero_ps(), _CMP_GE_OQ));
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(u, _mm256_set1_ps(1.0f), _CMP_LE_OQ));
    if (!_mm256_movemask_ps(valid)) return;

    __m256 qx = _mm256_fmsub_ps(tvy, e1z, _mm256_mul_ps(tvz, e1y));
    __m256 qy = _mm256_fmsub_ps(tvz, e1x, _mm256_mul_ps(tvx, e1z));
    __m256 qz = _mm256_fmsub_ps(tvx, e1y, _mm256_mul_ps(tvy, e1x));

    __m256 v = _mm256_mul_ps(
        _mm256_fmadd_ps(ac->dirx, qx,
                        _mm256_fmadd_ps(ac->diry, qy, _mm256_mul_ps(ac->dirz, qz))),
        inv_det);
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(v, _mm256_setzero_ps(), _CMP_GE_OQ));
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(_mm256_add_ps(u, v),
                                               _mm256_set1_ps(1.0f), _CMP_LE_OQ));
    if (!_mm256_movemask_ps(valid)) return;

    __m256 t = _mm256_mul_ps(
        _mm256_fmadd_ps(e2x, qx, _mm256_fmadd_ps(e2y, qy, _mm256_mul_ps(e2z, qz))),
        inv_det);
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(t, ac->tmin, _CMP_GE_OQ));
    valid = _mm256_and_ps(valid,
                          _mm256_cmp_ps(t, _mm256_set1_ps(*best_t), _CMP_LT_OQ));
    int mask = _mm256_movemask_ps(valid);
    if (!mask) return;

    _Alignas(32) float ta[8], ua[8], va[8];
    _mm256_store_ps(ta, t);
    _mm256_store_ps(ua, u);
    _mm256_store_ps(va, v);
    while (mask) {
        int lane = __builtin_ctz((unsigned)mask);
        mask &= mask - 1;
        if (ta[lane] < *best_t) {
            *best_t = ta[lane];
            *best_u = ua[lane];
            *best_v = va[lane];
            *best_prim = blk->prim_id[lane];
        }
    }
}

/* Any-hit variant. */
static inline int tri_block_occluded_avx(const lrt_tri8 *blk,
                                         const tri_avx_ctx *ac, __m256 tmax) {
    __m256 e1x = _mm256_load_ps(blk->e1x), e1y = _mm256_load_ps(blk->e1y),
           e1z = _mm256_load_ps(blk->e1z);
    __m256 e2x = _mm256_load_ps(blk->e2x), e2y = _mm256_load_ps(blk->e2y),
           e2z = _mm256_load_ps(blk->e2z);
    __m256 px = _mm256_fmsub_ps(ac->diry, e2z, _mm256_mul_ps(ac->dirz, e2y));
    __m256 py = _mm256_fmsub_ps(ac->dirz, e2x, _mm256_mul_ps(ac->dirx, e2z));
    __m256 pz = _mm256_fmsub_ps(ac->dirx, e2y, _mm256_mul_ps(ac->diry, e2x));
    __m256 det = _mm256_fmadd_ps(
        e1x, px, _mm256_fmadd_ps(e1y, py, _mm256_mul_ps(e1z, pz)));
    const __m256 abs_mask = _mm256_castsi256_ps(_mm256_set1_epi32(0x7FFFFFFF));
    __m256 valid =
        _mm256_cmp_ps(_mm256_and_ps(det, abs_mask), _mm256_set1_ps(1e-12f),
                      _CMP_GT_OQ);
    if (!_mm256_movemask_ps(valid)) return 0;
    __m256 inv_det = _mm256_div_ps(_mm256_set1_ps(1.0f), det);
    __m256 tvx = _mm256_sub_ps(ac->orgx, _mm256_load_ps(blk->v0x));
    __m256 tvy = _mm256_sub_ps(ac->orgy, _mm256_load_ps(blk->v0y));
    __m256 tvz = _mm256_sub_ps(ac->orgz, _mm256_load_ps(blk->v0z));
    __m256 u = _mm256_mul_ps(
        _mm256_fmadd_ps(tvx, px, _mm256_fmadd_ps(tvy, py, _mm256_mul_ps(tvz, pz))),
        inv_det);
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(u, _mm256_setzero_ps(), _CMP_GE_OQ));
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(u, _mm256_set1_ps(1.0f), _CMP_LE_OQ));
    if (!_mm256_movemask_ps(valid)) return 0;
    __m256 qx = _mm256_fmsub_ps(tvy, e1z, _mm256_mul_ps(tvz, e1y));
    __m256 qy = _mm256_fmsub_ps(tvz, e1x, _mm256_mul_ps(tvx, e1z));
    __m256 qz = _mm256_fmsub_ps(tvx, e1y, _mm256_mul_ps(tvy, e1x));
    __m256 v = _mm256_mul_ps(
        _mm256_fmadd_ps(ac->dirx, qx,
                        _mm256_fmadd_ps(ac->diry, qy, _mm256_mul_ps(ac->dirz, qz))),
        inv_det);
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(v, _mm256_setzero_ps(), _CMP_GE_OQ));
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(_mm256_add_ps(u, v),
                                               _mm256_set1_ps(1.0f), _CMP_LE_OQ));
    if (!_mm256_movemask_ps(valid)) return 0;
    __m256 t = _mm256_mul_ps(
        _mm256_fmadd_ps(e2x, qx, _mm256_fmadd_ps(e2y, qy, _mm256_mul_ps(e2z, qz))),
        inv_det);
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(t, ac->tmin, _CMP_GE_OQ));
    valid = _mm256_and_ps(valid, _mm256_cmp_ps(t, tmax, _CMP_LE_OQ));
    return _mm256_movemask_ps(valid) != 0;
}

static inline int tri_bvh8_slab_avx(const lrt_bvh8_node *n,
                                    const tri_avx_ctx *ac, __m256 t_best,
                                    float *tnear_out) {
    __m256 tlx = _mm256_mul_ps(_mm256_sub_ps(_mm256_load_ps(n->lo_x), ac->orgx),
                               ac->invdx);
    __m256 thx = _mm256_mul_ps(_mm256_sub_ps(_mm256_load_ps(n->hi_x), ac->orgx),
                               ac->invdx);
    __m256 tly = _mm256_mul_ps(_mm256_sub_ps(_mm256_load_ps(n->lo_y), ac->orgy),
                               ac->invdy);
    __m256 thy = _mm256_mul_ps(_mm256_sub_ps(_mm256_load_ps(n->hi_y), ac->orgy),
                               ac->invdy);
    __m256 tlz = _mm256_mul_ps(_mm256_sub_ps(_mm256_load_ps(n->lo_z), ac->orgz),
                               ac->invdz);
    __m256 thz = _mm256_mul_ps(_mm256_sub_ps(_mm256_load_ps(n->hi_z), ac->orgz),
                               ac->invdz);
    __m256 tnear = _mm256_max_ps(
        _mm256_max_ps(_mm256_min_ps(tlx, thx), _mm256_min_ps(tly, thy)),
        _mm256_max_ps(_mm256_min_ps(tlz, thz), ac->tmin));
    __m256 tfar = _mm256_min_ps(
        _mm256_min_ps(_mm256_max_ps(tlx, thx), _mm256_max_ps(tly, thy)),
        _mm256_min_ps(_mm256_max_ps(tlz, thz), t_best));
    _mm256_store_ps(tnear_out, tnear);
    return _mm256_movemask_ps(_mm256_cmp_ps(tnear, tfar, _CMP_LE_OQ));
}

static int tri_intersect_bvh8_avx2(const lrt_tri_scene *s, const lrt_ray *ray,
                                   lrt_hit *hit) {
    tri_ray_ctx rc;
    tri_ray_setup(ray, &rc);
    tri_avx_ctx ac;
    tri_avx_setup(&rc, &ac);

    float best_t = ray->tmax;
    float best_u = 0.0f, best_v = 0.0f;
    uint32_t best_prim = LRT_TRI_NO_HIT;

    tri_stack_entry stack[TRI_STACK_SIZE];
    int sp = 0;
    stack[sp].ref = s->root;
    stack[sp].tnear = rc.tmin;
    sp++;

    while (sp > 0) {
        tri_stack_entry e = stack[--sp];
        if (e.tnear >= best_t) continue;
        if (TRI_REF_IS_LEAF(e.ref)) {
            uint32_t blk0 = TRI_REF_BLOCK(e.ref);
            uint32_t nblk = TRI_REF_NBLOCKS(e.ref);
            const lrt_tri8 *blocks = (const lrt_tri8 *)s->blocks;
            for (uint32_t b = 0; b < nblk; b++) {
                tri_block_isect_avx(&blocks[blk0 + b], &ac, &best_t, &best_u,
                                    &best_v, &best_prim);
            }
            continue;
        }

        const lrt_bvh8_node *n = &s->nodes8[TRI_REF_NODE(e.ref)];
        _Alignas(32) float tnear[8];
        int mask = tri_bvh8_slab_avx(n, &ac, _mm256_set1_ps(best_t), tnear);
        mask &= (1 << n->nchildren) - 1;
        uint32_t hit_ref[8];
        float hit_tn[8];
        int nhit = 0;
        while (mask) {
            int i = __builtin_ctz((unsigned)mask);
            mask &= mask - 1;
            tri_prefetch_ref(s, n->child[i], 8);
            int j = nhit++;
            while (j > 0 && hit_tn[j - 1] > tnear[i]) {
                hit_tn[j] = hit_tn[j - 1];
                hit_ref[j] = hit_ref[j - 1];
                j--;
            }
            hit_tn[j] = tnear[i];
            hit_ref[j] = n->child[i];
        }
        for (int i = nhit - 1; i >= 0; i--) {
            stack[sp].ref = hit_ref[i];
            stack[sp].tnear = hit_tn[i];
            sp++;
        }
    }

    if (hit) {
        hit->t = best_prim != LRT_TRI_NO_HIT ? best_t : 0.0f;
        hit->u = best_u;
        hit->v = best_v;
        hit->prim_id = best_prim;
    }
    return best_prim != LRT_TRI_NO_HIT;
}

static int tri_occluded_bvh8_avx2(const lrt_tri_scene *s, const lrt_ray *ray) {
    tri_ray_ctx rc;
    tri_ray_setup(ray, &rc);
    tri_avx_ctx ac;
    tri_avx_setup(&rc, &ac);
    __m256 tmax8 = _mm256_set1_ps(ray->tmax);

    uint32_t stack[TRI_STACK_SIZE];
    int sp = 0;
    stack[sp++] = s->root;

    while (sp > 0) {
        uint32_t ref = stack[--sp];
        if (TRI_REF_IS_LEAF(ref)) {
            uint32_t blk0 = TRI_REF_BLOCK(ref);
            uint32_t nblk = TRI_REF_NBLOCKS(ref);
            const lrt_tri8 *blocks = (const lrt_tri8 *)s->blocks;
            for (uint32_t b = 0; b < nblk; b++) {
                if (tri_block_occluded_avx(&blocks[blk0 + b], &ac, tmax8)) {
                    return 1;
                }
            }
            continue;
        }
        const lrt_bvh8_node *n = &s->nodes8[TRI_REF_NODE(ref)];
        _Alignas(32) float tnear[8];
        int mask = tri_bvh8_slab_avx(n, &ac, tmax8, tnear);
        mask &= (1 << n->nchildren) - 1;
        while (mask) {
            int i = __builtin_ctz((unsigned)mask);
            mask &= mask - 1;
            stack[sp++] = n->child[i];
        }
    }
    return 0;
}

/* Quantized-node slab: decode 8-bit child bounds on the fly. With
 * s = scale*invd and b = (org_node - org_ray)*invd per axis, each plane is
 * t = q * s + b (one cvt + fma per plane). invd is clamped to +/-1e18 at ray
 * setup, so s and b stay finite and no 0*inf NaN can appear. */
static inline int tri_bvh8q_slab_avx(const lrt_bvh8q_node *n,
                                     const tri_ray_ctx *rc, __m256 tmin8,
                                     __m256 t_best, float *tnear_out) {
    __m256 sx = _mm256_set1_ps(n->scale[0] * rc->invd[0]);
    __m256 sy = _mm256_set1_ps(n->scale[1] * rc->invd[1]);
    __m256 sz = _mm256_set1_ps(n->scale[2] * rc->invd[2]);
    __m256 bx = _mm256_set1_ps((n->org[0] - rc->org[0]) * rc->invd[0]);
    __m256 by = _mm256_set1_ps((n->org[1] - rc->org[1]) * rc->invd[1]);
    __m256 bz = _mm256_set1_ps((n->org[2] - rc->org[2]) * rc->invd[2]);

#define TRI_Q8_LOAD(arr) \
    _mm256_cvtepi32_ps(_mm256_cvtepu8_epi32( \
        _mm_loadl_epi64((const __m128i *)(const void *)(arr))))
    __m256 tlx = _mm256_fmadd_ps(TRI_Q8_LOAD(n->qlo_x), sx, bx);
    __m256 thx = _mm256_fmadd_ps(TRI_Q8_LOAD(n->qhi_x), sx, bx);
    __m256 tly = _mm256_fmadd_ps(TRI_Q8_LOAD(n->qlo_y), sy, by);
    __m256 thy = _mm256_fmadd_ps(TRI_Q8_LOAD(n->qhi_y), sy, by);
    __m256 tlz = _mm256_fmadd_ps(TRI_Q8_LOAD(n->qlo_z), sz, bz);
    __m256 thz = _mm256_fmadd_ps(TRI_Q8_LOAD(n->qhi_z), sz, bz);
#undef TRI_Q8_LOAD

    __m256 tnear = _mm256_max_ps(
        _mm256_max_ps(_mm256_min_ps(tlx, thx), _mm256_min_ps(tly, thy)),
        _mm256_max_ps(_mm256_min_ps(tlz, thz), tmin8));
    __m256 tfar = _mm256_min_ps(
        _mm256_min_ps(_mm256_max_ps(tlx, thx), _mm256_max_ps(tly, thy)),
        _mm256_min_ps(_mm256_max_ps(tlz, thz), t_best));
    _mm256_store_ps(tnear_out, tnear);
    return _mm256_movemask_ps(_mm256_cmp_ps(tnear, tfar, _CMP_LE_OQ));
}

static int tri_intersect_bvh8q_avx2(const lrt_tri_scene *s, const lrt_ray *ray,
                                    lrt_hit *hit) {
    tri_ray_ctx rc;
    tri_ray_setup(ray, &rc);
    tri_avx_ctx ac;
    tri_avx_setup(&rc, &ac);

    float best_t = ray->tmax;
    float best_u = 0.0f, best_v = 0.0f;
    uint32_t best_prim = LRT_TRI_NO_HIT;

    tri_stack_entry stack[TRI_STACK_SIZE];
    int sp = 0;
    stack[sp].ref = s->root;
    stack[sp].tnear = rc.tmin;
    sp++;

    while (sp > 0) {
        tri_stack_entry e = stack[--sp];
        if (e.tnear >= best_t) continue;
        if (TRI_REF_IS_LEAF(e.ref)) {
            uint32_t blk0 = TRI_REF_BLOCK(e.ref);
            uint32_t nblk = TRI_REF_NBLOCKS(e.ref);
            const lrt_tri8 *blocks = (const lrt_tri8 *)s->blocks;
            for (uint32_t b = 0; b < nblk; b++) {
                tri_block_isect_avx(&blocks[blk0 + b], &ac, &best_t, &best_u,
                                    &best_v, &best_prim);
            }
            continue;
        }

        const lrt_bvh8q_node *n = &s->nodes8q[TRI_REF_NODE(e.ref)];
        _Alignas(32) float tnear[8];
        int mask = tri_bvh8q_slab_avx(n, &rc, ac.tmin, _mm256_set1_ps(best_t),
                                      tnear);
        mask &= (1 << n->nchildren) - 1;
        uint32_t hit_ref[8];
        float hit_tn[8];
        int nhit = 0;
        while (mask) {
            int i = __builtin_ctz((unsigned)mask);
            mask &= mask - 1;
            tri_prefetch_ref(s, n->child[i], 8);
            int j = nhit++;
            while (j > 0 && hit_tn[j - 1] > tnear[i]) {
                hit_tn[j] = hit_tn[j - 1];
                hit_ref[j] = hit_ref[j - 1];
                j--;
            }
            hit_tn[j] = tnear[i];
            hit_ref[j] = n->child[i];
        }
        for (int i = nhit - 1; i >= 0; i--) {
            stack[sp].ref = hit_ref[i];
            stack[sp].tnear = hit_tn[i];
            sp++;
        }
    }

    if (hit) {
        hit->t = best_prim != LRT_TRI_NO_HIT ? best_t : 0.0f;
        hit->u = best_u;
        hit->v = best_v;
        hit->prim_id = best_prim;
    }
    return best_prim != LRT_TRI_NO_HIT;
}

static int tri_occluded_bvh8q_avx2(const lrt_tri_scene *s, const lrt_ray *ray) {
    tri_ray_ctx rc;
    tri_ray_setup(ray, &rc);
    tri_avx_ctx ac;
    tri_avx_setup(&rc, &ac);
    __m256 tmax8 = _mm256_set1_ps(ray->tmax);

    uint32_t stack[TRI_STACK_SIZE];
    int sp = 0;
    stack[sp++] = s->root;

    while (sp > 0) {
        uint32_t ref = stack[--sp];
        if (TRI_REF_IS_LEAF(ref)) {
            uint32_t blk0 = TRI_REF_BLOCK(ref);
            uint32_t nblk = TRI_REF_NBLOCKS(ref);
            const lrt_tri8 *blocks = (const lrt_tri8 *)s->blocks;
            for (uint32_t b = 0; b < nblk; b++) {
                if (tri_block_occluded_avx(&blocks[blk0 + b], &ac, tmax8)) {
                    return 1;
                }
            }
            continue;
        }
        const lrt_bvh8q_node *n = &s->nodes8q[TRI_REF_NODE(ref)];
        _Alignas(32) float tnear[8];
        int mask = tri_bvh8q_slab_avx(n, &rc, ac.tmin, tmax8, tnear);
        mask &= (1 << n->nchildren) - 1;
        while (mask) {
            int i = __builtin_ctz((unsigned)mask);
            mask &= mask - 1;
            stack[sp++] = n->child[i];
        }
    }
    return 0;
}

#endif /* LRT_TRI_HAS_AVX2 */

/* ------------------------------------------------------------------------- */
/* Public API.                                                               */
/* ------------------------------------------------------------------------- */

static void tri_set_err(lrt_result *err, lrt_result v) {
    if (err) *err = v;
}

lrt_tri_scene *lrt_tri_scene_build(const float *vertices, size_t ntris,
                                   const lrt_tri_build_options *opts,
                                   lrt_result *err) {
    tri_set_err(err, LRT_RESULT_OK);
    if (!vertices || ntris == 0 || ntris > 0x07FFFFFFu) {
        /* leaf-ref encoding: block index needs 27 bits -> <= ~134M blocks */
        tri_set_err(err, LRT_RESULT_INVALID_ARGUMENT);
        return NULL;
    }

    lrt_tri_build_options o;
    if (opts) {
        o = *opts;
    } else {
        memset(&o, 0, sizeof(o));
        o.quality = LRT_TRI_BUILD_DEFAULT;
        o.layout = LRT_TRI_LAYOUT_AUTO;
    }

    int layout;
    int quantized = 0;
    if (o.layout == LRT_TRI_LAYOUT_BVH4) {
        layout = 4;
    } else if (o.layout == LRT_TRI_LAYOUT_BVH8) {
        layout = 8;
    } else if (o.layout == LRT_TRI_LAYOUT_BVH8Q) {
        layout = 8;
        quantized = 1;
    } else {
        /* AUTO: BVH4. Measured on Zen 1 (mandelbulb, 128k tris, primary and
         * incoherent rays, 1 and 16 threads), BVH4 matches or beats BVH8:
         * 256-bit ops execute as 2x128-bit there, so the wider node test
         * gains nothing while 256-byte nodes cost more bandwidth. Pass
         * LRT_TRI_LAYOUT_BVH8 explicitly on CPUs with a native 256-bit
         * datapath. */
        layout = 4;
    }

    uint32_t max_leaf = o.max_leaf_size ? o.max_leaf_size : TRI_DEFAULT_LEAF;
    if (max_leaf > TRI_MAX_LEAF) max_leaf = TRI_MAX_LEAF;

    /* --- Precompute pass: per-tri bounds + centroids. --- */
    tri_build_ctx bc;
    memset(&bc, 0, sizeof(bc));
    bc.verts = vertices;
    bc.ntris = ntris;
    bc.max_leaf = max_leaf;
    bc.block_shift = layout == 8 ? 3u : 2u;
    bc.quality = o.quality;

    size_t n3 = ntris * 3;
    bc.plo = (float *)malloc(n3 * sizeof(float));
    bc.phi = (float *)malloc(n3 * sizeof(float));
    bc.cen = (float *)malloc(n3 * sizeof(float));
    bc.indices = (uint32_t *)malloc(ntris * sizeof(uint32_t));
    /* 2*ntris covers any binary tree; +512 absorbs the per-task rounding of
     * the parallel builder's arena slices (2k vs the exact 2k-1). */
    uint32_t bnode_cap = (uint32_t)(2 * ntris) + 512u;
    bc.node_next = 0;
    bc.node_end = bnode_cap;
    bc.bnodes = (tri_bnode *)malloc((size_t)bnode_cap * sizeof(tri_bnode));
    if (!bc.plo || !bc.phi || !bc.cen || !bc.indices || !bc.bnodes) {
        free(bc.plo);
        free(bc.phi);
        free(bc.cen);
        free(bc.indices);
        free(bc.bnodes);
        tri_set_err(err, LRT_RESULT_OUT_OF_MEMORY);
        return NULL;
    }

    unsigned num_threads = o.num_threads ? o.num_threads : 1u;
#if !defined(__STDC_NO_THREADS__)
    if (num_threads > 1 && ntris >= 4096) {
        bc.par_threads = num_threads;
        bc.par_scratch = (uint32_t *)malloc(ntris * sizeof(uint32_t));
        /* scratch failure just disables the parallel partition path */
        if (!bc.par_scratch) bc.par_threads = 0;
    }
#endif

    int bad_input = tri_precompute(&bc, num_threads);
    if (bad_input) {
        free(bc.plo);
        free(bc.phi);
        free(bc.cen);
        free(bc.indices);
        free(bc.bnodes);
        free(bc.par_scratch);
        tri_set_err(err, LRT_RESULT_INVALID_BOUNDS);
        return NULL;
    }

    /* --- LBVH preprocessing (LRT_TRI_BUILD_FAST): Morton sort. --- */
    uint64_t *lbvh_keys = NULL, *lbvh_tmp = NULL;
    if (o.quality == LRT_TRI_BUILD_FAST) {
        lbvh_keys = (uint64_t *)malloc(ntris * sizeof(uint64_t));
        lbvh_tmp = (uint64_t *)malloc(ntris * sizeof(uint64_t));
        if (!lbvh_keys || !lbvh_tmp) {
            free(lbvh_keys);
            free(lbvh_tmp);
            free(bc.plo);
            free(bc.phi);
            free(bc.cen);
            free(bc.indices);
            free(bc.bnodes);
            free(bc.par_scratch);
            tri_set_err(err, LRT_RESULT_OUT_OF_MEMORY);
            return NULL;
        }
        tri_morton_encode(&bc, lbvh_keys, num_threads);
        const uint64_t *sorted = tri_radix_sort_keys(lbvh_keys, lbvh_tmp, ntris);
        for (size_t i = 0; i < ntris; i++) {
            bc.indices[i] = (uint32_t)sorted[i];
        }
        bc.lbvh_keys = sorted;
        uint32_t bw = 1u << bc.block_shift;
        bc.lbvh_leaf = 2u * bw;
        if (bc.lbvh_leaf > max_leaf) bc.lbvh_leaf = max_leaf;
    }

    /* --- Binary build (parallel when num_threads > 1). --- */
    uint32_t b_root = (o.quality == LRT_TRI_BUILD_FAST)
                          ? tri_build_lbvh(&bc, num_threads)
                          : tri_build_binary(&bc, num_threads);

    lrt_tri_scene *s = NULL;
    if (!bc.failed) {
        s = (lrt_tri_scene *)calloc(1, sizeof(lrt_tri_scene));
        if (!s) bc.failed = 1;
    }

    if (!bc.failed) {
        s->layout = layout;
        s->quantized = quantized;
        uint32_t node_cap = (uint32_t)ntris;
        if (node_cap < 1) node_cap = 1;
        uint32_t block_cap = (uint32_t)ntris;
        if (block_cap < 1) block_cap = 1;
        if (layout == 4) {
            s->nodes4 = (lrt_bvh4_node *)tri_aligned_alloc(
                64, (size_t)node_cap * sizeof(lrt_bvh4_node));
        } else if (quantized) {
            s->nodes8q = (lrt_bvh8q_node *)tri_aligned_alloc(
                64, (size_t)node_cap * sizeof(lrt_bvh8q_node));
        } else {
            s->nodes8 = (lrt_bvh8_node *)tri_aligned_alloc(
                64, (size_t)node_cap * sizeof(lrt_bvh8_node));
        }
        s->blocks = tri_aligned_alloc(
            64, (size_t)block_cap * tri_block_size(layout));
        if ((!s->nodes4 && !s->nodes8 && !s->nodes8q) || !s->blocks) {
            bc.failed = 1;
        } else {
            tri_collapse_ctx cc;
            memset(&cc, 0, sizeof(cc));
            cc.bc = &bc;
            cc.s = s;
            cc.node_cap = node_cap;
            cc.block_cap = block_cap;
            cc.width = layout;
            cc.quantized = quantized;
            const tri_bnode *rootn = &bc.bnodes[b_root];
            cc.root_area = tri_surface_area(rootn->lo, rootn->hi);
            if (cc.root_area <= 0.0f) cc.root_area = 1.0f;

            if (rootn->count > 0) {
                s->root = tri_emit_leaf(&cc, rootn);
            } else {
                s->root = tri_collapse(&cc, b_root, 0);
            }
            if (cc.failed) {
                bc.failed = 1;
            } else {
                s->stats.node_count = s->node_count;
                s->stats.leaf_count = cc.leaf_count;
                s->stats.max_depth = cc.max_depth;
                size_t node_size = layout == 4 ? sizeof(lrt_bvh4_node)
                                   : quantized ? sizeof(lrt_bvh8q_node)
                                               : sizeof(lrt_bvh8_node);
                s->stats.memory_bytes =
                    (size_t)s->node_count * node_size +
                    (size_t)s->block_count * tri_block_size(layout);
                s->stats.sah_cost = (float)(TRI_TRAV_COST * cc.sah_inner +
                                            TRI_ISECT_COST * cc.sah_leaf);
            }
        }
    }

    free(bc.plo);
    free(bc.phi);
    free(bc.cen);
    free(bc.indices);
    free(bc.bnodes);
    free(bc.par_scratch);
    free(lbvh_keys);
    free(lbvh_tmp);

    if (bc.failed) {
        lrt_tri_scene_free(s);
        tri_set_err(err, LRT_RESULT_OUT_OF_MEMORY);
        return NULL;
    }

#if LRT_TRI_HAS_AVX2
    s->kernel_name = layout == 4    ? "bvh4/sse4"
                     : quantized    ? "bvh8q/avx2"
                                    : "bvh8/avx2";
#elif LRT_TRI_HAS_SSE4
    s->kernel_name = layout == 4    ? "bvh4/sse4"
                     : quantized    ? "bvh8q/scalar"
                                    : "bvh8/scalar";
#else
    s->kernel_name = layout == 4    ? "bvh4/scalar"
                     : quantized    ? "bvh8q/scalar"
                                    : "bvh8/scalar";
#endif
    return s;
}

void lrt_tri_scene_free(lrt_tri_scene *s) {
    if (!s) return;
    tri_aligned_free(s->nodes4);
    tri_aligned_free(s->nodes8);
    tri_aligned_free(s->nodes8q);
    tri_aligned_free(s->blocks);
    free(s);
}

int lrt_tri_intersect1(const lrt_tri_scene *s, const lrt_ray *ray, lrt_hit *hit) {
    if (!s || !ray) {
        if (hit) hit->prim_id = LRT_TRI_NO_HIT;
        return 0;
    }
#if LRT_TRI_HAS_AVX2
    if (s->layout == 8) {
        return s->quantized ? tri_intersect_bvh8q_avx2(s, ray, hit)
                            : tri_intersect_bvh8_avx2(s, ray, hit);
    }
#endif
#if LRT_TRI_HAS_SSE4
    if (s->layout == 4) return tri_intersect_bvh4_sse(s, ray, hit);
#endif
    return tri_intersect_scalar(s, ray, hit);
}

int lrt_tri_occluded1(const lrt_tri_scene *s, const lrt_ray *ray) {
    if (!s || !ray) return 0;
#if LRT_TRI_HAS_AVX2
    if (s->layout == 8) {
        return s->quantized ? tri_occluded_bvh8q_avx2(s, ray)
                            : tri_occluded_bvh8_avx2(s, ray);
    }
#endif
#if LRT_TRI_HAS_SSE4
    if (s->layout == 4) return tri_occluded_bvh4_sse(s, ray);
#endif
    return tri_occluded_scalar(s, ray);
}

void lrt_tri_intersect1N(const lrt_tri_scene *s, const lrt_ray *rays,
                         lrt_hit *hits, size_t n) {
    if (!s || !rays || !hits) return;
    for (size_t i = 0; i < n; i++) {
#if LRT_TRI_HAS_SSE4
        if (i + 1 < n) _mm_prefetch((const char *)&rays[i + 1], _MM_HINT_T0);
#endif
        lrt_tri_intersect1(s, &rays[i], &hits[i]);
    }
}

void lrt_tri_occluded1N(const lrt_tri_scene *s, const lrt_ray *rays,
                        uint8_t *occluded, size_t n) {
    if (!s || !rays || !occluded) return;
    for (size_t i = 0; i < n; i++) {
#if LRT_TRI_HAS_SSE4
        if (i + 1 < n) _mm_prefetch((const char *)&rays[i + 1], _MM_HINT_T0);
#endif
        occluded[i] = (uint8_t)lrt_tri_occluded1(s, &rays[i]);
    }
}

void lrt_tri_scene_stats(const lrt_tri_scene *s, lrt_tri_stats *out) {
    if (!out) return;
    if (!s) {
        memset(out, 0, sizeof(*out));
        return;
    }
    *out = s->stats;
}

const char *lrt_tri_kernel_name(const lrt_tri_scene *s) {
    return s ? s->kernel_name : "none";
}
