/*
 * lightrt_c.cc — C11 binding implementation over LightRT's MMapGenericBVH.
 *
 * The fp32 BVH does broad-phase traversal; the user's fp64 intersection
 * callback solves each candidate primitive. The authoritative fp64 ray and the
 * best fp64 hit are kept in the scene's per-query scratch (reached by the
 * trampolines via the BVH's prim_data pointer), so precision is preserved
 * through the callback.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "lightrt_c.h"
#include "lightrt.hh"

#include <cfloat>
#include <cstdlib>
#include <new>

using lightrt::AABB;
using lightrt::MMapGenericBVH;
using lightrt::Ray;
using lightrt::Vec3;

struct lrt_scene {
    MMapGenericBVH   bvh;
    unsigned         nprims;
    lrt_bounds_cb    bounds_cb;
    lrt_intersect_cb isect_cb;
    void            *user;

    /* per-query scratch (authoritative fp64 ray + best fp64 hit) */
    double   org[3], dir[3], tmin, tmax;
    double   best_t, best_u, best_v;
    unsigned best_prim;
};

static AABB bounds_trampoline(const void *prim_data, uint32_t i) noexcept
{
    const lrt_scene *s = static_cast<const lrt_scene *>(prim_data);
    lrt_aabb a = s->bounds_cb(i, s->user);
    return AABB(Vec3((float)a.lo[0], (float)a.lo[1], (float)a.lo[2]),
                Vec3((float)a.hi[0], (float)a.hi[1], (float)a.hi[2]));
}

static bool isect_trampoline(const Ray & /*ray_f32*/, const void *prim_data,
                             uint32_t i, float &t, float &u, float &v) noexcept
{
    /* prim_data is the build-time pointer; we passed the scene itself. The
     * authoritative fp64 ray lives in the scene scratch. */
    lrt_scene *s = const_cast<lrt_scene *>(static_cast<const lrt_scene *>(prim_data));
    double td = 0.0, ud = 0.0, vd = 0.0;
    int hit = s->isect_cb(s->org, s->dir, s->tmin, s->tmax, i, s->user, &td, &ud, &vd);
    if (!hit) return false;
    /* report fp32 t to the BVH for ordering / tmax culling */
    t = (float)td; u = (float)ud; v = (float)vd;
    if (td < s->best_t) {
        s->best_t = td; s->best_u = ud; s->best_v = vd; s->best_prim = i;
    }
    return true;
}

lrt_scene *lrt_scene_create(unsigned nprims, lrt_bounds_cb bounds_cb,
                            lrt_intersect_cb isect_cb, void *user)
{
    if (!bounds_cb || !isect_cb) return nullptr;
    lrt_scene *s = new (std::nothrow) lrt_scene();
    if (!s) return nullptr;
    s->nprims = nprims;
    s->bounds_cb = bounds_cb;
    s->isect_cb = isect_cb;
    s->user = user;
    s->best_prim = LRT_NO_HIT;
    return s;
}

int lrt_scene_build(lrt_scene *s)
{
    if (!s) return 0;
    /* prim_data = the scene itself; the bounds trampoline reads bounds_cb. */
    return s->bvh.build(s, s->nprims, bounds_trampoline) ? 1 : 0;
}

unsigned lrt_scene_intersect(lrt_scene *s, const double org[3], const double dir[3],
                             double tmin, double tmax,
                             double *t, double *u, double *v)
{
    if (!s) return LRT_NO_HIT;
    for (int k = 0; k < 3; k++) { s->org[k] = org[k]; s->dir[k] = dir[k]; }
    s->tmin = tmin; s->tmax = tmax;
    s->best_t = DBL_MAX; s->best_u = 0.0; s->best_v = 0.0; s->best_prim = LRT_NO_HIT;

    float ft = (tmin > 0.0) ? (float)tmin : 0.0f;
    Ray rf(Vec3((float)org[0], (float)org[1], (float)org[2]),
           Vec3((float)dir[0], (float)dir[1], (float)dir[2]),
           ft, (float)tmax);
    float ht = 0.f, hu = 0.f, hv = 0.f;
    s->bvh.traverse(rf, isect_trampoline, ht, hu, hv);

    if (s->best_prim != LRT_NO_HIT) {
        if (t) *t = s->best_t;
        if (u) *u = s->best_u;
        if (v) *v = s->best_v;
    }
    return s->best_prim;
}

void lrt_scene_free(lrt_scene *s) { delete s; }

const char *lrt_backend_name(void) { return "LightRT MMapGenericBVH (fp32 BVH, fp64 callback)"; }
