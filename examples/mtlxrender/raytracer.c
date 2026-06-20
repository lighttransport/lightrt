#include "raytracer.h"

#include <stdlib.h>

/* ---- CPU backend -------------------------------------------------------- */
typedef struct {
    RayTracer base;
    const Scene *s;
} CpuRT;

static void cpu_closest(RayTracer *r, const lrt_ray *rays, lrt_hit *hits,
                        uint32_t n) {
    CpuRT *c = (CpuRT *)r;
    lrt_tri_intersect1N(c->s->bvh, rays, hits, n, LRT_TRI_BATCH_AUTO);
}
static void cpu_occluded(RayTracer *r, const lrt_ray *rays, uint8_t *occ,
                         uint32_t n) {
    CpuRT *c = (CpuRT *)r;
    lrt_tri_occluded1N(c->s->bvh, rays, occ, n, LRT_TRI_BATCH_AUTO);
}
static void cpu_destroy(RayTracer *r) { free(r); }

RayTracer *rt_cpu_create(const Scene *s) {
    CpuRT *c = (CpuRT *)calloc(1, sizeof(*c));
    if (!c) return NULL;
    c->base.fn_closest = cpu_closest;
    c->base.fn_occluded = cpu_occluded;
    c->base.fn_destroy = cpu_destroy;
    c->base.name = "cpu";
    c->s = s;
    return &c->base;
}
