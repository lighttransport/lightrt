/*
 * gltf_load.h - load a (binary) glTF into a flat, BVH-ready Scene.
 *
 * All meshes are baked to world space and concatenated into one triangle soup.
 * Per-triangle side tables are keyed by the BVH's flat prim_id (== global
 * triangle index), so the hot shading path needs no pointer chasing.
 */
#ifndef MTLXRENDER_GLTF_LOAD_H_
#define MTLXRENDER_GLTF_LOAD_H_

#include <stddef.h>
#include <stdint.h>
#include "lightrt_c_tri.h"

#define GLTF_MAX_MAT_NAME 128

typedef struct {
    /* BVH-facing geometry: 9 floats (p0,p1,p2) per triangle. */
    float   *verts;
    size_t   ntri;

    /* Per-triangle attributes, indexed by prim_id. */
    float   *tri_uv;   /* 6*ntri: (u,v) per corner */
    float   *tri_n;    /* 9*ntri: world-space normal per corner */
    int32_t *tri_mat;  /* ntri: glTF material index, or -1 */
    int32_t *tri_geom; /* ntri: geometry-name index (node/mesh name) */

    /* glTF material names (for binding to MaterialX shaders). */
    char   (*mat_names)[GLTF_MAX_MAT_NAME];
    int      nmat;

    /* Geometry (node/mesh) names; MaterialX <materialassign geom="..."> binds
     * to these, not to glTF materials. Indexed by tri_geom. */
    char   (*geom_names)[GLTF_MAX_MAT_NAME];
    int      ngeom;

    float    bmin[3], bmax[3]; /* world-space bounds */

    lrt_tri_scene *bvh;
} Scene;

/* Load .glb/.gltf at `path`, build the BVH. Returns 0 on success, non-zero on
 * failure (message printed to stderr). Free with scene_free(). */
int scene_load_gltf(const char *path, Scene *out, int build_quality_hq);
void scene_free(Scene *s);

#endif /* MTLXRENDER_GLTF_LOAD_H_ */
