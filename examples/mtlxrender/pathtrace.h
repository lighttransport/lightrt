/*
 * pathtrace.h - the integrator: tiled, multi-threaded unidirectional path
 * tracer with next-event estimation + MIS against the environment.
 */
#ifndef MTLXRENDER_PATHTRACE_H_
#define MTLXRENDER_PATHTRACE_H_

#include <math.h>

#include "gltf_load.h"
#include "mtlx_doc.h"
#include "material_bind.h"
#include "texture.h"
#include "env.h"
#include "camera.h"
#include "framebuffer.h"

typedef struct {
    int   enabled;
    v3    dir;      /* direction TOWARD the sun (unit) */
    v3    radiance; /* color * intensity */
} SunLight;

typedef struct {
    int   width, height;
    int   spp;
    int   max_bounces;
    int   nthreads;
    int   sss_walk;     /* enable random-walk subsurface scattering */
    int   pixel_filter_tent; /* use a tent reconstruction filter for camera rays */
    int   hide_env_bg;  /* primary-ray miss returns black, not the env (env still lights) */
    SunLight sun;       /* optional directional delta light */
    unsigned seed;
} RenderConfig;

/* Match testrender's tent filter, with support of one pixel either side of
 * the pixel center. The default box filter samples the pixel itself. */
static inline float mtlx_pixel_offset(float u, int tent) {
    if (!tent) return u;
    float x = 2.0f * u;
    return 0.5f + (x < 1.0f ? sqrtf(x) - 1.0f : 1.0f - sqrtf(2.0f - x));
}

void render(const Scene *scene, const MtlxDoc *doc, const MaterialBinding *bind,
            TextureCache *tex, const Env *env, const Camera *cam,
            const RenderConfig *cfg, Framebuffer *fb);

#endif /* MTLXRENDER_PATHTRACE_H_ */
