/*
 * camera.h - pinhole camera with look-at, generates lightrt rays.
 */
#ifndef MTLXRENDER_CAMERA_H_
#define MTLXRENDER_CAMERA_H_

#include "vecmath.h"
#include "lightrt_c_tri.h"

typedef struct {
    v3 origin;
    v3 forward, right, up; /* orthonormal basis; right/up scaled to image plane */
    float tan_half_fov;
    float aspect;
} Camera;

/* eye/target in world space, fov_y in radians, aspect = width/height. */
static inline Camera camera_lookat(v3 eye, v3 target, v3 world_up, float fov_y, float aspect) {
    Camera c;
    c.origin = eye;
    c.forward = v3_normalize(v3_sub(target, eye));
    c.right = v3_normalize(v3_cross(c.forward, world_up));
    c.up = v3_cross(c.right, c.forward);
    c.tan_half_fov = tanf(0.5f * fov_y);
    c.aspect = aspect;
    return c;
}

/* (px,py) in [0,1] image space (0,0 = top-left). Returns a normalized ray. */
static inline lrt_ray camera_ray(const Camera *c, float px, float py) {
    float sx = (2.0f * px - 1.0f) * c->aspect * c->tan_half_fov;
    float sy = (1.0f - 2.0f * py) * c->tan_half_fov;
    v3 dir = v3_normalize(v3_add(c->forward, v3_add(v3_scale(c->right, sx), v3_scale(c->up, sy))));
    lrt_ray r;
    r.org[0] = c->origin.x; r.org[1] = c->origin.y; r.org[2] = c->origin.z;
    r.dir[0] = dir.x; r.dir[1] = dir.y; r.dir[2] = dir.z;
    r.tmin = 1e-4f;
    r.tmax = 1e30f;
    return r;
}

#endif /* MTLXRENDER_CAMERA_H_ */
