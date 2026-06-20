/*
 * raytracer_vk.c - Vulkan GPU ray-query backend (compiled iff MTLX_HAVE_VK).
 *
 * Closest hit goes straight to lrt_vk_trace_scene (GPU BVH traversal of the
 * CPU-built Scene BVH). Occlusion traces into a reusable hit buffer and reports
 * prim_id != LRT_TRI_NO_HIT (the shadow ray's tmax already bounds the query).
 *
 * NB: this v1 of lrt_vk_trace_scene re-serializes + re-uploads the scene on
 * every batch, so a multi-bounce wavefront pays that per batch. It is correct
 * and demonstrates GPU traversal; a resident-scene fast path is a follow-up.
 */
#ifdef MTLX_HAVE_VK

#include "raytracer.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lightrt_c_vk.h"

typedef struct {
    RayTracer base;
    lrt_vk_engine *engine;
    const Scene *s;
    lrt_hit *hit_tmp; /* reusable buffer for occlusion traces */
    uint32_t hit_cap;
} VkRT;

static void vk_closest(RayTracer *r, const lrt_ray *rays, lrt_hit *hits,
                       uint32_t n) {
    VkRT *v = (VkRT *)r;
    lrt_result err = LRT_RESULT_OK;
    if (lrt_vk_trace_scene(v->engine, v->s->bvh, rays, n, hits, &err) < 0) {
        /* On a GPU error, mark all as misses so the frame still completes. */
        for (uint32_t i = 0; i < n; i++) hits[i].prim_id = LRT_TRI_NO_HIT;
    }
}

static void vk_occluded(RayTracer *r, const lrt_ray *rays, uint8_t *occ,
                        uint32_t n) {
    VkRT *v = (VkRT *)r;
    if (n > v->hit_cap) {
        free(v->hit_tmp);
        v->hit_tmp = (lrt_hit *)malloc((size_t)n * sizeof(lrt_hit));
        v->hit_cap = v->hit_tmp ? n : 0;
    }
    if (!v->hit_tmp) { for (uint32_t i = 0; i < n; i++) occ[i] = 0; return; }
    lrt_result err = LRT_RESULT_OK;
    if (lrt_vk_trace_scene(v->engine, v->s->bvh, rays, n, v->hit_tmp, &err) < 0) {
        for (uint32_t i = 0; i < n; i++) occ[i] = 0;
        return;
    }
    for (uint32_t i = 0; i < n; i++)
        occ[i] = (v->hit_tmp[i].prim_id != LRT_TRI_NO_HIT) ? 1u : 0u;
}

static void vk_destroy(RayTracer *r) {
    VkRT *v = (VkRT *)r;
    free(v->hit_tmp);
    if (v->engine) lrt_vk_engine_destroy(v->engine);
    free(v);
}

RayTracer *rt_vk_create(const Scene *s) {
    lrt_vk_engine_options opt;
    memset(&opt, 0, sizeof(opt));
    opt.device_index = -1;
    opt.prefer_discrete = 1;
    lrt_result err = LRT_RESULT_OK;
    lrt_vk_engine *e = lrt_vk_engine_create(&opt, &err);
    if (!e) return NULL;

    VkRT *v = (VkRT *)calloc(1, sizeof(*v));
    if (!v) { lrt_vk_engine_destroy(e); return NULL; }
    v->base.fn_closest = vk_closest;
    v->base.fn_occluded = vk_occluded;
    v->base.fn_destroy = vk_destroy;
    v->base.name = lrt_vk_engine_device_name(e);
    v->engine = e;
    v->s = s;
    return &v->base;
}

#endif /* MTLX_HAVE_VK */
