/*
 * raytracer.h - pluggable ray-query backend for the wavefront integrator.
 *
 * The integrator issues ray *batches* (camera, shadow, bounce) and asks a
 * RayTracer to resolve them. Two backends today:
 *   - CPU : lrt_tri_intersect1N / lrt_tri_occluded1N over the local BVH.
 *   - VK  : GPU BVH traversal via lrt_vk_trace_scene (compiled iff MTLX_HAVE_VK).
 * A future CUDA backend implements the same three ops (rt_closest / rt_occluded
 * / rt_destroy) with no integrator change.
 */
#ifndef MTLXRENDER_RAYTRACER_H_
#define MTLXRENDER_RAYTRACER_H_

#include <stdint.h>

#include "gltf_load.h"     /* Scene */
#include "lightrt_c_tri.h" /* lrt_ray, lrt_hit */

typedef struct RayTracer RayTracer;

/* Backends embed this base as their first member (a tiny vtable). Callers treat
 * RayTracer as opaque and use the rt_* dispatchers below. */
struct RayTracer {
    void (*fn_closest)(RayTracer *, const lrt_ray *, lrt_hit *, uint32_t n);
    void (*fn_occluded)(RayTracer *, const lrt_ray *, uint8_t *, uint32_t n);
    void (*fn_destroy)(RayTracer *);
    const char *name;
};

/* CPU backend over the Scene's BVH (lrt_tri_*1N, internally batched). */
RayTracer *rt_cpu_create(const Scene *s);

#ifdef MTLX_HAVE_VK
/* Vulkan backend: GPU BVH traversal of the Scene's BVH. Returns NULL when no
 * Vulkan loader/device is present (the caller should fall back to CPU). */
RayTracer *rt_vk_create(const Scene *s);
#endif

/* Closest hit for n rays. hits[i].prim_id == LRT_TRI_NO_HIT on a miss. */
static inline void rt_closest(RayTracer *rt, const lrt_ray *rays, lrt_hit *hits,
                              uint32_t n) {
    rt->fn_closest(rt, rays, hits, n);
}
/* Any hit for n rays. occ[i] = 1 if something lies within the ray's [tmin,tmax]. */
static inline void rt_occluded(RayTracer *rt, const lrt_ray *rays, uint8_t *occ,
                               uint32_t n) {
    rt->fn_occluded(rt, rays, occ, n);
}
static inline const char *rt_name(const RayTracer *rt) { return rt->name; }
static inline void rt_destroy(RayTracer *rt) {
    if (rt) rt->fn_destroy(rt);
}

#endif /* MTLXRENDER_RAYTRACER_H_ */
