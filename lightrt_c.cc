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
#include <atomic>
#include <cmath>
#include <cstdlib>
#include <cstring>
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
    int              built = 0;

    lrt_options options;
    std::atomic<int> cancel_requested{0};
    lrt_result last_result = LRT_RESULT_OK;
    char       last_error[128] = "ok";
    size_t     last_progress_done = static_cast<size_t>(-1);
    const char *last_progress_stage = nullptr;
    size_t     bounds_done = 0;
    size_t     intersect_tests_done = 0;

    /* per-query scratch (authoritative fp64 ray + best fp64 hit) */
    double   org[3], dir[3], tmin, tmax;
    double   best_t, best_u, best_v;
    unsigned best_prim;
};

static constexpr size_t kDefaultProgressInterval = 4096u;
static constexpr unsigned kDefaultMaxBuildDepth = 64u;
static constexpr unsigned kDefaultMaxLeafSize = 4u;

static const char *result_string(lrt_result result)
{
    switch (result) {
        case LRT_RESULT_OK: return "ok";
        case LRT_RESULT_INVALID_ARGUMENT: return "invalid argument";
        case LRT_RESULT_OUT_OF_MEMORY: return "out of memory";
        case LRT_RESULT_CANCELED: return "canceled";
        case LRT_RESULT_NOT_BUILT: return "scene is not built";
        case LRT_RESULT_TRAVERSAL_OVERFLOW: return "traversal stack overflow";
        case LRT_RESULT_INVALID_BOUNDS: return "invalid primitive bounds";
        case LRT_RESULT_BUILD_LIMIT: return "BVH build limit reached";
        default: return "unknown error";
    }
}

static void set_result(lrt_scene *s, lrt_result result, const char *message = nullptr)
{
    if (!s) return;
    s->last_result = result;
    if (!message) message = result_string(result);
    std::strncpy(s->last_error, message, sizeof(s->last_error) - 1u);
    s->last_error[sizeof(s->last_error) - 1u] = '\0';
}

static bool finite3(const double v[3])
{
    return v && std::isfinite(v[0]) && std::isfinite(v[1]) && std::isfinite(v[2]);
}

static bool valid_ray(const double org[3], const double dir[3], double tmin, double tmax)
{
    if (!finite3(org) || !finite3(dir)) return false;
    if (!std::isfinite(tmin) || !std::isfinite(tmax) || tmax < tmin) return false;
    return dir[0] != 0.0 || dir[1] != 0.0 || dir[2] != 0.0;
}

static bool valid_aabb(const lrt_aabb& a)
{
    for (int k = 0; k < 3; k++) {
        if (!std::isfinite(a.lo[k]) || !std::isfinite(a.hi[k]) || a.lo[k] > a.hi[k]) {
            return false;
        }
    }
    return true;
}

static bool should_cancel(lrt_scene *s)
{
    if (!s) return true;
    if (s->cancel_requested.load(std::memory_order_relaxed)) {
        if (s->last_result == LRT_RESULT_OK) {
            set_result(s, LRT_RESULT_CANCELED);
        }
        return true;
    }
    if (s->options.cancel_cb && s->options.cancel_cb(s->options.user)) {
        s->cancel_requested.store(1, std::memory_order_relaxed);
        set_result(s, LRT_RESULT_CANCELED);
        return true;
    }
    return false;
}

static void reset_progress(lrt_scene *s)
{
    if (!s) return;
    s->last_progress_done = static_cast<size_t>(-1);
    s->last_progress_stage = nullptr;
}

static void report_progress(lrt_scene *s, const char *stage,
                            size_t done, size_t total, bool force)
{
    if (!s || !s->options.progress_cb) return;
    size_t interval = s->options.progress_interval;
    if (interval == 0) interval = kDefaultProgressInterval;
    if (!force && s->last_progress_stage == stage &&
        s->last_progress_done != static_cast<size_t>(-1) &&
        done < s->last_progress_done + interval) {
        return;
    }

    double fraction = 0.0;
    if (total != 0) {
        fraction = static_cast<double>(done) / static_cast<double>(total);
        if (fraction < 0.0) fraction = 0.0;
        if (fraction > 1.0) fraction = 1.0;
    }
    lrt_progress progress{stage, done, total, fraction};
    s->last_progress_stage = stage;
    s->last_progress_done = done;
    s->options.progress_cb(&progress, s->options.user);
}

static AABB bounds_trampoline(const void *prim_data, uint32_t i) noexcept
{
    lrt_scene *s = const_cast<lrt_scene *>(static_cast<const lrt_scene *>(prim_data));
    if (should_cancel(s)) return AABB(Vec3(0.0f, 0.0f, 0.0f), Vec3(0.0f, 0.0f, 0.0f));
    lrt_aabb a = s->bounds_cb(i, s->user);
    if (!valid_aabb(a)) {
        set_result(s, LRT_RESULT_INVALID_BOUNDS, "bounds callback returned invalid AABB");
        s->cancel_requested.store(1, std::memory_order_relaxed);
        return AABB(Vec3(0.0f, 0.0f, 0.0f), Vec3(0.0f, 0.0f, 0.0f));
    }
    s->bounds_done++;
    report_progress(s, "build", s->bounds_done, s->nprims, false);
    return AABB(Vec3((float)a.lo[0], (float)a.lo[1], (float)a.lo[2]),
                Vec3((float)a.hi[0], (float)a.hi[1], (float)a.hi[2]));
}

static bool isect_trampoline(const Ray & /*ray_f32*/, const void *prim_data,
                             uint32_t i, float &t, float &u, float &v) noexcept
{
    /* prim_data is the build-time pointer; we passed the scene itself. The
     * authoritative fp64 ray lives in the scene scratch. */
    lrt_scene *s = const_cast<lrt_scene *>(static_cast<const lrt_scene *>(prim_data));
    if (should_cancel(s)) return false;
    s->intersect_tests_done++;
    report_progress(s, "intersect", s->intersect_tests_done, 0, false);
    double td = 0.0, ud = 0.0, vd = 0.0;
    double cb_tmax = s->best_t < s->tmax ? s->best_t : s->tmax;
    int hit = s->isect_cb(s->org, s->dir, s->tmin, cb_tmax, i, s->user, &td, &ud, &vd);
    if (!hit) return false;
    if (!std::isfinite(td) || td < s->tmin || td > cb_tmax) return false;
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
    set_result(s, LRT_RESULT_OK);
    return s;
}

int lrt_scene_set_options(lrt_scene *s, const lrt_options *options)
{
    if (!s) return 0;
    if (options) {
        s->options = *options;
    } else {
        std::memset(&s->options, 0, sizeof(s->options));
    }
    set_result(s, LRT_RESULT_OK);
    return 1;
}

int lrt_scene_build(lrt_scene *s)
{
    if (!s || s->nprims == 0) {
        set_result(s, LRT_RESULT_INVALID_ARGUMENT, "scene is null or has no primitives");
        return 0;
    }
    set_result(s, LRT_RESULT_OK);
    reset_progress(s);
    s->bounds_done = 0;
    s->built = 0;
    report_progress(s, "build", 0, s->nprims, true);
    if (should_cancel(s)) return 0;
    /* prim_data = the scene itself; the bounds trampoline reads bounds_cb. */
    lightrt::MMapBVHConfig config;
    config.build.max_depth = s->options.max_build_depth != 0
        ? s->options.max_build_depth
        : kDefaultMaxBuildDepth;
    config.build.max_leaf_size = s->options.max_leaf_size != 0
        ? s->options.max_leaf_size
        : kDefaultMaxLeafSize;
    bool ok = s->bvh.build(s, s->nprims, bounds_trampoline, config);
    if (should_cancel(s)) return 0;
    if (!ok) {
        if (s->last_result == LRT_RESULT_OK) {
            set_result(s, LRT_RESULT_BUILD_LIMIT, "BVH build limit reached");
        }
        return 0;
    }
    report_progress(s, "build", s->nprims, s->nprims, true);
    s->built = 1;
    set_result(s, LRT_RESULT_OK);
    return 1;
}

unsigned lrt_scene_intersect(lrt_scene *s, const double org[3], const double dir[3],
                             double tmin, double tmax,
                             double *t, double *u, double *v)
{
    if (!s) return LRT_NO_HIT;
    set_result(s, LRT_RESULT_OK);
    reset_progress(s);
    if (!valid_ray(org, dir, tmin, tmax)) {
        set_result(s, LRT_RESULT_INVALID_ARGUMENT, "invalid ray or range");
        return LRT_NO_HIT;
    }
    if (!s->built || s->bvh.getPrimitiveCount() == 0) {
        set_result(s, LRT_RESULT_NOT_BUILT);
        return LRT_NO_HIT;
    }
    report_progress(s, "intersect", 0, 0, true);
    if (should_cancel(s)) return LRT_NO_HIT;
    for (int k = 0; k < 3; k++) { s->org[k] = org[k]; s->dir[k] = dir[k]; }
    s->tmin = tmin; s->tmax = tmax;
    s->best_t = DBL_MAX; s->best_u = 0.0; s->best_v = 0.0; s->best_prim = LRT_NO_HIT;
    s->intersect_tests_done = 0;

    float ft = (tmin > 0.0) ? (float)tmin : 0.0f;
    Ray rf(Vec3((float)org[0], (float)org[1], (float)org[2]),
           Vec3((float)dir[0], (float)dir[1], (float)dir[2]),
           ft, (float)tmax);
    float ht = 0.f, hu = 0.f, hv = 0.f;
    s->bvh.traverse(rf, isect_trampoline, ht, hu, hv);
    if (should_cancel(s)) return LRT_NO_HIT;

    if (s->best_prim != LRT_NO_HIT) {
        if (t) *t = s->best_t;
        if (u) *u = s->best_u;
        if (v) *v = s->best_v;
    }
    report_progress(s, "intersect", s->intersect_tests_done, 0, true);
    set_result(s, LRT_RESULT_OK);
    return s->best_prim;
}

void lrt_scene_request_cancel(lrt_scene *s)
{
    if (!s) return;
    s->cancel_requested.store(1, std::memory_order_relaxed);
}

void lrt_scene_clear_cancel(lrt_scene *s)
{
    if (!s) return;
    s->cancel_requested.store(0, std::memory_order_relaxed);
    set_result(s, LRT_RESULT_OK);
}

int lrt_scene_cancel_requested(const lrt_scene *s)
{
    if (!s) return 0;
    return s->cancel_requested.load(std::memory_order_relaxed) ? 1 : 0;
}

lrt_result lrt_scene_last_result(const lrt_scene *s)
{
    if (!s) return LRT_RESULT_INVALID_ARGUMENT;
    return s->last_result;
}

const char *lrt_scene_last_error(const lrt_scene *s)
{
    if (!s) return "invalid argument";
    return s->last_error[0] ? s->last_error : result_string(s->last_result);
}

void lrt_scene_free(lrt_scene *s) { delete s; }

const char *lrt_backend_name(void) { return "LightRT MMapGenericBVH (fp32 BVH, fp64 callback)"; }
