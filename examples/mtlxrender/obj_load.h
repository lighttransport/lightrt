/*
 * obj_load.h - load a Wavefront .obj into the shared Scene.
 *
 * Pure C11, no external dependencies. Produces the same flat Scene as the glTF
 * loader (via mesh_build): one world-space triangle soup with per-triangle
 * uv/normal/material/geom side tables keyed by the BVH's flat prim_id.
 *
 *   usemtl <name>  -> per-triangle material name (Scene.mat_names / tri_mat)
 *   o / g <name>   -> per-triangle geometry name (Scene.geom_names / tri_geom),
 *                     which MaterialX <materialassign geom="..."> binds to
 *
 * Normals are taken from `vn` when present, else synthesized per face.
 */
#ifndef MTLXRENDER_OBJ_LOAD_H_
#define MTLXRENDER_OBJ_LOAD_H_

#include "gltf_load.h" /* Scene */

/* Load `path` (.obj), build the BVH. Returns 0 on success, non-zero on failure
 * (message to stderr). Free with scene_free(). */
int scene_load_obj(const char *path, Scene *out, int build_quality_hq);

#endif /* MTLXRENDER_OBJ_LOAD_H_ */
