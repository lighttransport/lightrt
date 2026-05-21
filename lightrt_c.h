/*
 * lightrt_c.h — C11 binding for LightRT's generic BVH + custom-primitive ray
 * intersection.
 *
 * Lets C code drive LightRT's BVH while supplying its own primitive bounds and
 * intersection in *double precision*. A scene is a BVH over `nprims` opaque
 * primitives; the user provides a bounds callback (for building) and an
 * intersection callback (invoked per candidate primitive during traversal).
 *
 * The BVH itself is single precision (broad phase); the intersection callback
 * receives the original fp64 ray, so an analytic surface can be solved at full
 * double precision (e.g. sub-nm OPL for aspheric lens tracing).
 *
 * NOTE: a scene keeps per-query scratch, so a single lrt_scene must not be
 * intersected from multiple threads concurrently. Use one scene per thread (or
 * per surface) for parallel queries.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LIGHTRT_C_H
#define LIGHTRT_C_H

#ifdef __cplusplus
extern "C" {
#endif

/* Returned by lrt_scene_intersect when nothing was hit. */
#define LRT_NO_HIT 0xFFFFFFFFu

typedef struct lrt_scene lrt_scene;

/* Axis-aligned bounding box in world (fp64) coordinates. */
typedef struct { double lo[3]; double hi[3]; } lrt_aabb;

/* Bounds of primitive `prim`. Called during lrt_scene_build. */
typedef lrt_aabb (*lrt_bounds_cb)(unsigned prim, void *user);

/* Intersect the fp64 ray with primitive `prim`. On hit, write the ray parameter
 * to *t (and optional surface params to *u,*v) and return 1; else return 0.
 * Only hits with tmin <= t <= tmax should be reported. */
typedef int (*lrt_intersect_cb)(const double org[3], const double dir[3],
                                double tmin, double tmax, unsigned prim,
                                void *user, double *t, double *u, double *v);

/* Create a scene over `nprims` primitives. Callbacks + user are retained. */
lrt_scene *lrt_scene_create(unsigned nprims, lrt_bounds_cb bounds_cb,
                            lrt_intersect_cb isect_cb, void *user);

/* Build the BVH. Returns 1 on success, 0 on failure. */
int lrt_scene_build(lrt_scene *s);

/* Closest-hit query. Returns the hit primitive id, or LRT_NO_HIT. Writes the
 * fp64 ray parameter / surface params to *t,*u,*v when non-NULL on hit. */
unsigned lrt_scene_intersect(lrt_scene *s, const double org[3], const double dir[3],
                             double tmin, double tmax,
                             double *t, double *u, double *v);

void lrt_scene_free(lrt_scene *s);

/* Human-readable backend description, e.g. "LightRT MMapGenericBVH". */
const char *lrt_backend_name(void);

#ifdef __cplusplus
}
#endif

#endif /* LIGHTRT_C_H */
