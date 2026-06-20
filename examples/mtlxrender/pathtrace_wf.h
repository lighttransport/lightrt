/*
 * pathtrace_wf.h - wavefront path tracer driven by a RayTracer backend.
 *
 * Unlike the recursive per-pixel tracer in pathtrace.c, this integrator issues
 * ray *batches* (camera, shadow, bounce) and resolves them through a RayTracer
 * (CPU or Vulkan), so the same integrator runs on either backend. Shading stays
 * on the CPU with the full MaterialX node graph; only the ray queries cross to
 * the GPU. Used for the --backend vk path and the --gpu-validate cross-check.
 *
 * (Subsurface random-walk is omitted here; use the default CPU tracer for SSS.)
 */
#ifndef MTLXRENDER_PATHTRACE_WF_H_
#define MTLXRENDER_PATHTRACE_WF_H_

#include "pathtrace.h" /* Scene, MtlxDoc, MaterialBinding, Env, Camera, RenderConfig, Framebuffer */
#include "raytracer.h"

void render_wavefront(const Scene *scene, const MtlxDoc *doc,
                      const MaterialBinding *bind, TextureCache *tex,
                      const Env *env, const Camera *cam, const RenderConfig *cfg,
                      Framebuffer *fb, RayTracer *rt);

#endif /* MTLXRENDER_PATHTRACE_WF_H_ */
