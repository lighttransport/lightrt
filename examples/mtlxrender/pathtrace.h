/*
 * pathtrace.h - the integrator: tiled, multi-threaded unidirectional path
 * tracer with next-event estimation + MIS against the environment.
 */
#ifndef MTLXRENDER_PATHTRACE_H_
#define MTLXRENDER_PATHTRACE_H_

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
    SunLight sun;       /* optional directional delta light */
    unsigned seed;
} RenderConfig;

void render(const Scene *scene, const MtlxDoc *doc, const MaterialBinding *bind,
            TextureCache *tex, const Env *env, const Camera *cam,
            const RenderConfig *cfg, Framebuffer *fb);

#endif /* MTLXRENDER_PATHTRACE_H_ */
