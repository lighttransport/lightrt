/*
 * backend_lightrt_cb.c — baseline backend: the existing lightrt_c.h callback
 * API driven by an fp64 Moller-Trumbore triangle callback (the same pairing
 * the X11 viewer's benchmark mode uses). lrt_scene keeps per-query scratch, so
 * one scene is built per worker thread.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stdlib.h>
#include <string.h>

#include "../lightrt_c.h"
#include "backend.h"
#include "timing.h"

typedef struct {
    float *vertices; /* owned copy, 9*ntris */
    size_t ntris;
    int num_threads;
    lrt_scene **scenes; /* one per thread */
} cb_scene;

static lrt_aabb cb_bounds(unsigned prim, void *user) {
    const cb_scene *cs = (const cb_scene *)user;
    const float *v = &cs->vertices[(size_t)prim * 9];
    lrt_aabb bb;
    bb.lo[0] = bb.hi[0] = v[0];
    bb.lo[1] = bb.hi[1] = v[1];
    bb.lo[2] = bb.hi[2] = v[2];
    for (int i = 1; i < 3; i++) {
        const float *p = &v[i * 3];
        for (int k = 0; k < 3; k++) {
            if (p[k] < bb.lo[k]) bb.lo[k] = p[k];
            if (p[k] > bb.hi[k]) bb.hi[k] = p[k];
        }
    }
    return bb;
}

/* fp64 Moller-Trumbore (port of viewer_x11.cc c11_intersect_cb). */
static int cb_intersect(const double org[3], const double dir[3], double tmin,
                        double tmax, unsigned prim, void *user, double *t,
                        double *u, double *v) {
    const cb_scene *cs = (const cb_scene *)user;
    const float *verts = &cs->vertices[(size_t)prim * 9];

    double v0[3] = {verts[0], verts[1], verts[2]};
    double e1[3] = {verts[3] - v0[0], verts[4] - v0[1], verts[5] - v0[2]};
    double e2[3] = {verts[6] - v0[0], verts[7] - v0[1], verts[8] - v0[2]};

    double pvec[3] = {dir[1] * e2[2] - dir[2] * e2[1],
                      dir[2] * e2[0] - dir[0] * e2[2],
                      dir[0] * e2[1] - dir[1] * e2[0]};
    double det = e1[0] * pvec[0] + e1[1] * pvec[1] + e1[2] * pvec[2];
    if (det > -1e-12 && det < 1e-12) return 0;
    double inv_det = 1.0 / det;

    double tvec[3] = {org[0] - v0[0], org[1] - v0[1], org[2] - v0[2]};
    double uu = (tvec[0] * pvec[0] + tvec[1] * pvec[1] + tvec[2] * pvec[2]) * inv_det;
    if (uu < 0.0 || uu > 1.0) return 0;

    double qvec[3] = {tvec[1] * e1[2] - tvec[2] * e1[1],
                      tvec[2] * e1[0] - tvec[0] * e1[2],
                      tvec[0] * e1[1] - tvec[1] * e1[0]};
    double vv = (dir[0] * qvec[0] + dir[1] * qvec[1] + dir[2] * qvec[2]) * inv_det;
    if (vv < 0.0 || uu + vv > 1.0) return 0;

    double tt = (e2[0] * qvec[0] + e2[1] * qvec[1] + e2[2] * qvec[2]) * inv_det;
    if (tt < tmin || tt > tmax) return 0;

    *t = tt;
    *u = uu;
    *v = vv;
    return 1;
}

static void cb_destroy(void *scene) {
    cb_scene *cs = (cb_scene *)scene;
    if (!cs) return;
    if (cs->scenes) {
        for (int i = 0; i < cs->num_threads; i++) lrt_scene_free(cs->scenes[i]);
        free(cs->scenes);
    }
    free(cs->vertices);
    free(cs);
}

static void *cb_build(const float *vertices, size_t ntris, int num_threads,
                      double *build_ms) {
    if (build_ms) *build_ms = 0.0;
    if (!vertices || ntris == 0 || ntris > 0x7FFFFFFFu) return NULL;
    if (num_threads < 1) num_threads = 1;

    cb_scene *cs = (cb_scene *)calloc(1, sizeof(cb_scene));
    if (!cs) return NULL;
    cs->ntris = ntris;
    cs->num_threads = num_threads;
    cs->vertices = (float *)malloc(ntris * 9 * sizeof(float));
    cs->scenes = (lrt_scene **)calloc((size_t)num_threads, sizeof(lrt_scene *));
    if (!cs->vertices || !cs->scenes) {
        cb_destroy(cs);
        return NULL;
    }
    memcpy(cs->vertices, vertices, ntris * 9 * sizeof(float));

    uint64_t t0 = bench_time_ns();
    for (int i = 0; i < num_threads; i++) {
        cs->scenes[i] = lrt_scene_create((unsigned)ntris, cb_bounds, cb_intersect, cs);
        if (!cs->scenes[i] || !lrt_scene_build(cs->scenes[i])) {
            cb_destroy(cs);
            return NULL;
        }
    }
    uint64_t t1 = bench_time_ns();
    /* Report the cost of ONE build: the per-thread replication is an API
     * limitation of the callback backend, not build work the others do. */
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0) / (double)num_threads;
    return cs;
}

static void cb_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                           lrt_hit *hits, size_t n) {
    cb_scene *cs = (cb_scene *)scene;
    lrt_scene *s = cs->scenes[thread_idx % cs->num_threads];
    for (size_t i = 0; i < n; i++) {
        const lrt_ray *r = &rays[i];
        double org[3] = {r->org[0], r->org[1], r->org[2]};
        double dir[3] = {r->dir[0], r->dir[1], r->dir[2]};
        double t = 0.0, u = 0.0, v = 0.0;
        unsigned prim = lrt_scene_intersect(s, org, dir, r->tmin, r->tmax, &t, &u, &v);
        if (prim != LRT_NO_HIT) {
            hits[i].t = (float)t;
            hits[i].u = (float)u;
            hits[i].v = (float)v;
            hits[i].prim_id = prim;
        } else {
            hits[i].t = 0.0f;
            hits[i].u = 0.0f;
            hits[i].v = 0.0f;
            hits[i].prim_id = LRT_TRI_NO_HIT;
        }
    }
}

static void cb_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                          uint8_t *occluded, size_t n) {
    /* The callback API has no any-hit query; closest-hit stands in. */
    cb_scene *cs = (cb_scene *)scene;
    lrt_scene *s = cs->scenes[thread_idx % cs->num_threads];
    for (size_t i = 0; i < n; i++) {
        const lrt_ray *r = &rays[i];
        double org[3] = {r->org[0], r->org[1], r->org[2]};
        double dir[3] = {r->dir[0], r->dir[1], r->dir[2]};
        unsigned prim = lrt_scene_intersect(s, org, dir, r->tmin, r->tmax, NULL, NULL, NULL);
        occluded[i] = (prim != LRT_NO_HIT) ? 1 : 0;
    }
}

static size_t cb_memory_bytes(void *scene) {
    /* lrt_scene internals are opaque; estimate one BVH from its public model:
     * <= 2*ntris nodes of 40 bytes + ntris uint32 prim indices. */
    cb_scene *cs = (cb_scene *)scene;
    return cs->ntris * (2u * 40u + 4u);
}

static const bench_backend g_cb_backend = {
    "c11-cb", cb_build, cb_intersect1N, cb_occluded1N, cb_memory_bytes, cb_destroy,
};

const bench_backend *backend_lightrt_cb(void) { return &g_cb_backend; }
