/*
 * backend_lightrt_ext.c — benchmark backends for the production extensions of
 * the fp32 lightrt kernel (lightrt_c_tri.h):
 *
 *   c11-user   custom geometry: each triangle becomes a user primitive
 *              (per-tri AABB + a Moller-Trumbore callback). Same geometry as the
 *              triangle backends, so hit fractions match; measures the cost of
 *              the generic callback path vs the native triangle leaves.
 *   c11-tlas   a single identity instance of the whole soup through the TLAS;
 *              measures the per-leaf ray-transform + indirection overhead.
 *   c11-sphere one analytic sphere per triangle (centroid + circumradius).
 *   c11-sdf    one sphere-SDF blob per triangle, sphere-traced.
 *
 * c11-sphere / c11-sdf reinterpret the geometry (like c11-hair), so their hit
 * fractions intentionally differ from the triangle backends; they are not part
 * of "--backend all".
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <stdlib.h>

#include "backend.h"
#include "timing.h"

/* ---- shared vtable tail for scenes that are a plain lrt_tri_scene --------- */
static void ext_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                            lrt_hit *hits, size_t n, int coherent) {
    (void)thread_idx;
    lrt_tri_intersect1N((const lrt_tri_scene *)scene, rays, hits, n,
                        coherent ? LRT_TRI_BATCH_COHERENT
                                 : LRT_TRI_BATCH_INCOHERENT);
}
static void ext_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                           uint8_t *occluded, size_t n, int coherent) {
    (void)thread_idx;
    lrt_tri_occluded1N((const lrt_tri_scene *)scene, rays, occluded, n,
                       coherent ? LRT_TRI_BATCH_COHERENT
                                : LRT_TRI_BATCH_INCOHERENT);
}
static size_t ext_memory_bytes(void *scene) {
    lrt_tri_stats st;
    lrt_tri_scene_stats((const lrt_tri_scene *)scene, &st);
    return st.memory_bytes;
}
static void ext_destroy(void *scene) {
    lrt_tri_scene_free((lrt_tri_scene *)scene);
}

static void tri_aabb_of(const float *tri, float lo[3], float hi[3]) {
    for (int a = 0; a < 3; a++) {
        lo[a] = hi[a] = tri[a];
        for (int k = 1; k < 3; k++) {
            float c = tri[k * 3 + a];
            if (c < lo[a]) lo[a] = c;
            if (c > hi[a]) hi[a] = c;
        }
    }
}

/* centroid + circumradius-ish bound (max vertex distance), for sphere/sdf. */
static void tri_sphere_of(const float *tri, float c[3], float *r) {
    for (int a = 0; a < 3; a++)
        c[a] = (tri[a] + tri[3 + a] + tri[6 + a]) / 3.0f;
    float rr = 0.0f;
    for (int k = 0; k < 3; k++) {
        float dx = tri[k * 3 + 0] - c[0], dy = tri[k * 3 + 1] - c[1],
              dz = tri[k * 3 + 2] - c[2];
        float d = dx * dx + dy * dy + dz * dz;
        if (d > rr) rr = d;
    }
    rr = sqrtf(rr);
    *r = rr > 1e-7f ? rr : 1e-7f;
}

/* ---- c11-user: custom geometry over the same triangles ------------------- */
static int user_tri_isect(const lrt_ray *ray, uint32_t prim, void *user,
                          float *t, float *u, float *v) {
    const float *tri = &((const float *)user)[(size_t)prim * 9];
    float e1[3] = {tri[3] - tri[0], tri[4] - tri[1], tri[5] - tri[2]};
    float e2[3] = {tri[6] - tri[0], tri[7] - tri[1], tri[8] - tri[2]};
    float px = ray->dir[1] * e2[2] - ray->dir[2] * e2[1];
    float py = ray->dir[2] * e2[0] - ray->dir[0] * e2[2];
    float pz = ray->dir[0] * e2[1] - ray->dir[1] * e2[0];
    float det = e1[0] * px + e1[1] * py + e1[2] * pz;
    if (det > -1e-12f && det < 1e-12f) return 0;
    float inv = 1.0f / det;
    float tvx = ray->org[0] - tri[0], tvy = ray->org[1] - tri[1],
          tvz = ray->org[2] - tri[2];
    float uu = (tvx * px + tvy * py + tvz * pz) * inv;
    if (uu < 0.0f || uu > 1.0f) return 0;
    float qx = tvy * e1[2] - tvz * e1[1];
    float qy = tvz * e1[0] - tvx * e1[2];
    float qz = tvx * e1[1] - tvy * e1[0];
    float vv = (ray->dir[0] * qx + ray->dir[1] * qy + ray->dir[2] * qz) * inv;
    if (vv < 0.0f || uu + vv > 1.0f) return 0;
    float tt = (e2[0] * qx + e2[1] * qy + e2[2] * qz) * inv;
    if (tt < ray->tmin || tt > ray->tmax) return 0;
    *t = tt;
    *u = uu;
    *v = vv;
    return 1;
}

static void *user_build(const float *vertices, size_t ntris, int num_threads,
                        double *build_ms) {
    if (build_ms) *build_ms = 0.0;
    float *aabbs = (float *)malloc(ntris * 6 * sizeof(float));
    if (!aabbs) return NULL;
    for (size_t i = 0; i < ntris; i++) {
        float lo[3], hi[3];
        tri_aabb_of(&vertices[i * 9], lo, hi);
        for (int a = 0; a < 3; a++) {
            aabbs[i * 6 + a] = lo[a];
            aabbs[i * 6 + 3 + a] = hi[a];
        }
    }
    lrt_tri_build_options opts = {
        .quality = LRT_TRI_BUILD_DEFAULT,
        .layout = LRT_TRI_LAYOUT_BVH4,
        .max_leaf_size = 0,
        .num_threads = (unsigned)(num_threads > 0 ? num_threads : 1),
    };
    uint64_t t0 = bench_time_ns();
    lrt_tri_scene *s = lrt_user_scene_build(aabbs, ntris, user_tri_isect, NULL,
                                            (void *)vertices, &opts, NULL);
    uint64_t t1 = bench_time_ns();
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    free(aabbs);
    return s;
}

/* ---- c11-sphere: one analytic sphere per triangle ------------------------ */
static void *sphere_build(const float *vertices, size_t ntris, int num_threads,
                          double *build_ms) {
    if (build_ms) *build_ms = 0.0;
    float *sph = (float *)malloc(ntris * 4 * sizeof(float));
    if (!sph) return NULL;
    for (size_t i = 0; i < ntris; i++) {
        float c[3], r;
        tri_sphere_of(&vertices[i * 9], c, &r);
        sph[i * 4 + 0] = c[0];
        sph[i * 4 + 1] = c[1];
        sph[i * 4 + 2] = c[2];
        sph[i * 4 + 3] = r;
    }
    lrt_tri_build_options opts = {
        .quality = LRT_TRI_BUILD_DEFAULT,
        .layout = LRT_TRI_LAYOUT_BVH4,
        .max_leaf_size = 0,
        .num_threads = (unsigned)(num_threads > 0 ? num_threads : 1),
    };
    uint64_t t0 = bench_time_ns();
    lrt_tri_scene *s = lrt_sphere_scene_build(sph, ntris, &opts, NULL);
    uint64_t t1 = bench_time_ns();
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    free(sph);
    return s;
}

/* ---- c11-tlas: one identity instance of the whole soup ------------------- */
typedef struct {
    lrt_tlas *tlas;
    lrt_tri_scene *blas;
} tlas_wrap;

static void *tlas_build(const float *vertices, size_t ntris, int num_threads,
                        double *build_ms) {
    if (build_ms) *build_ms = 0.0;
    lrt_tri_build_options opts = {
        .quality = LRT_TRI_BUILD_DEFAULT,
        .layout = LRT_TRI_LAYOUT_BVH4,
        .max_leaf_size = 0,
        .num_threads = (unsigned)(num_threads > 0 ? num_threads : 1),
    };
    uint64_t t0 = bench_time_ns();
    lrt_tri_scene *blas = lrt_tri_scene_build(vertices, ntris, &opts, NULL);
    if (!blas) return NULL;
    /* The TLAS keeps the BLAS *array* pointer (not owned), so it must outlive
     * the TLAS — store the BLAS in the wrapper and build over &w->blas, not a
     * local. */
    tlas_wrap *w = (tlas_wrap *)malloc(sizeof(tlas_wrap));
    if (!w) {
        lrt_tri_scene_free(blas);
        return NULL;
    }
    w->blas = blas;
    w->tlas = NULL;
    lrt_instance inst;
    float im[12] = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0};
    for (int k = 0; k < 12; k++) inst.obj2world[k] = im[k];
    inst.blas_id = 0;
    inst.instance_id = 0;
    inst.mask = 0xFFFFFFFFu;
    w->tlas = lrt_tlas_build((lrt_tri_scene *const *)&w->blas, 1, &inst, 1,
                             &opts, NULL);
    uint64_t t1 = bench_time_ns();
    if (!w->tlas) {
        lrt_tri_scene_free(blas);
        free(w);
        return NULL;
    }
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    return w;
}

static void tlas_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                             lrt_hit *hits, size_t n, int coherent) {
    (void)thread_idx;
    (void)coherent;
    const tlas_wrap *w = (const tlas_wrap *)scene;
    for (size_t i = 0; i < n; i++) {
        lrt_tlas_hit th;
        if (lrt_tlas_intersect1(w->tlas, &rays[i], 0xFFFFFFFFu, &th)) {
            hits[i].t = th.t;
            hits[i].u = th.u;
            hits[i].v = th.v;
            hits[i].prim_id = th.prim_id;
        } else {
            hits[i].prim_id = LRT_TRI_NO_HIT;
        }
    }
}
static void tlas_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                            uint8_t *occluded, size_t n, int coherent) {
    (void)thread_idx;
    (void)coherent;
    const tlas_wrap *w = (const tlas_wrap *)scene;
    for (size_t i = 0; i < n; i++)
        occluded[i] = (uint8_t)lrt_tlas_occluded1(w->tlas, &rays[i], 0xFFFFFFFFu);
}
static size_t tlas_memory(void *scene) {
    const tlas_wrap *w = (const tlas_wrap *)scene;
    lrt_tri_stats st;
    lrt_tri_scene_stats(w->blas, &st);
    return st.memory_bytes;
}
static void tlas_destroy(void *scene) {
    tlas_wrap *w = (tlas_wrap *)scene;
    lrt_tlas_free(w->tlas);
    lrt_tri_scene_free(w->blas);
    free(w);
}

/* ---- c11-sdf: one sphere-SDF blob per triangle --------------------------- */
typedef struct {
    float c[3];
    float r;
} sdf_sph_ctx;
typedef struct {
    lrt_tri_scene *scene;
    sdf_sph_ctx *ctx; /* referenced by the blob callbacks; outlives the scene */
} sdf_wrap;

static float sdf_sphere_field(const float p[3], void *user) {
    const sdf_sph_ctx *c = (const sdf_sph_ctx *)user;
    float dx = p[0] - c->c[0], dy = p[1] - c->c[1], dz = p[2] - c->c[2];
    return sqrtf(dx * dx + dy * dy + dz * dz) - c->r;
}

static void *sdf_build(const float *vertices, size_t ntris, int num_threads,
                       double *build_ms) {
    if (build_ms) *build_ms = 0.0;
    sdf_sph_ctx *ctx = (sdf_sph_ctx *)malloc(ntris * sizeof(sdf_sph_ctx));
    lrt_sdf_blob *blobs = (lrt_sdf_blob *)malloc(ntris * sizeof(lrt_sdf_blob));
    if (!ctx || !blobs) {
        free(ctx);
        free(blobs);
        return NULL;
    }
    for (size_t i = 0; i < ntris; i++) {
        float c[3], r;
        tri_sphere_of(&vertices[i * 9], c, &r);
        ctx[i].c[0] = c[0];
        ctx[i].c[1] = c[1];
        ctx[i].c[2] = c[2];
        ctx[i].r = r;
        blobs[i].aabb[0] = c[0] - r;
        blobs[i].aabb[1] = c[1] - r;
        blobs[i].aabb[2] = c[2] - r;
        blobs[i].aabb[3] = c[0] + r;
        blobs[i].aabb[4] = c[1] + r;
        blobs[i].aabb[5] = c[2] + r;
        blobs[i].sdf = sdf_sphere_field;
        blobs[i].user = &ctx[i];
    }
    lrt_sdf_params p;
    p.max_steps = 64;
    p.epsilon = 1e-4f;
    p.over_relax = 0.0f;
    p.t_eps_scale = 0.0f;
    p.normal_eps = 0.0f;
    lrt_tri_build_options opts = {
        .quality = LRT_TRI_BUILD_DEFAULT,
        .layout = LRT_TRI_LAYOUT_BVH4,
        .max_leaf_size = 0,
        .num_threads = (unsigned)(num_threads > 0 ? num_threads : 1),
    };
    uint64_t t0 = bench_time_ns();
    lrt_tri_scene *s = lrt_sdf_scene_build(blobs, ntris, &p, &opts, NULL);
    uint64_t t1 = bench_time_ns();
    free(blobs);
    if (!s) {
        free(ctx);
        return NULL;
    }
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    sdf_wrap *w = (sdf_wrap *)malloc(sizeof(sdf_wrap));
    if (!w) {
        lrt_tri_scene_free(s);
        free(ctx);
        return NULL;
    }
    w->scene = s;
    w->ctx = ctx;
    return w;
}
static void sdf_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                            lrt_hit *hits, size_t n, int coherent) {
    (void)thread_idx;
    (void)coherent;
    const sdf_wrap *w = (const sdf_wrap *)scene;
    lrt_tri_intersect1N(w->scene, rays, hits, n, LRT_TRI_BATCH_INCOHERENT);
}
static void sdf_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                           uint8_t *occluded, size_t n, int coherent) {
    (void)thread_idx;
    (void)coherent;
    const sdf_wrap *w = (const sdf_wrap *)scene;
    lrt_tri_occluded1N(w->scene, rays, occluded, n, LRT_TRI_BATCH_INCOHERENT);
}
static size_t sdf_memory(void *scene) {
    const sdf_wrap *w = (const sdf_wrap *)scene;
    lrt_tri_stats st;
    lrt_tri_scene_stats(w->scene, &st);
    return st.memory_bytes;
}
static void sdf_destroy(void *scene) {
    sdf_wrap *w = (sdf_wrap *)scene;
    lrt_tri_scene_free(w->scene);
    free(w->ctx);
    free(w);
}

static const bench_backend g_user_backend = {
    "c11-user", user_build, ext_intersect1N, ext_occluded1N, ext_memory_bytes,
    ext_destroy,
};
static const bench_backend g_sphere_backend = {
    "c11-sphere", sphere_build, ext_intersect1N, ext_occluded1N,
    ext_memory_bytes, ext_destroy,
};
static const bench_backend g_tlas_backend = {
    "c11-tlas", tlas_build, tlas_intersect1N, tlas_occluded1N, tlas_memory,
    tlas_destroy,
};
static const bench_backend g_sdf_backend = {
    "c11-sdf", sdf_build, sdf_intersect1N, sdf_occluded1N, sdf_memory,
    sdf_destroy,
};

const bench_backend *backend_lightrt_user(void) { return &g_user_backend; }
const bench_backend *backend_lightrt_sphere(void) { return &g_sphere_backend; }
const bench_backend *backend_lightrt_tlas(void) { return &g_tlas_backend; }
const bench_backend *backend_lightrt_sdf(void) { return &g_sdf_backend; }
