/*
 * mesh_build.h - shared triangle accumulator + Scene finalize.
 *
 * Both the glTF and the Wavefront-OBJ loaders feed the same growable TriBuf and
 * then call scene_from_tribuf() to move the triangle soup into a Scene, compute
 * bounds, and build the LightRT BVH. Keeping this shared guarantees the two
 * loaders produce an identical Scene layout (prim_id == flat triangle index).
 *
 * Scene and GLTF_MAX_MAT_NAME are declared in gltf_load.h.
 */
#ifndef MTLXRENDER_MESH_BUILD_H_
#define MTLXRENDER_MESH_BUILD_H_

#include <stddef.h>
#include <stdint.h>

#include "gltf_load.h"

#define MESH_MAX_GEOM 256

typedef struct {
    float   *verts;  /* 9 floats/tri */
    float   *uv;     /* 6 floats/tri */
    float   *nrm;    /* 9 floats/tri */
    int32_t *mat;    /* material index per tri, or -1 */
    int32_t *geom;   /* geometry-name index per tri */
    size_t   ntri, cap;
    char     geom_names[MESH_MAX_GEOM][GLTF_MAX_MAT_NAME];
    int      ngeom;
} TriBuf;

/* Intern a geometry name (node/object/group), returning its index. */
int tribuf_geom_intern(TriBuf *tb, const char *name, uint32_t len);

/* Append one triangle (positions/uv/normal already in world space). */
void tribuf_emit_tri(TriBuf *tb, const float P[9], const float UV[6],
                     const float N[9], int32_t mat, int32_t geom);

/* Free the TriBuf working arrays (for error paths before finalize). */
void tribuf_free(TriBuf *tb);

/* Move the triangle soup into `out` (verts/uv/nrm/mat/geom/geom_names), compute
 * out->bmin/bmax, and build out->bvh. Consumes tb's arrays on success. Does NOT
 * touch out->mat_names / out->nmat (each loader fills those). Returns 0 on
 * success; on failure frees tb and returns non-zero. */
int scene_from_tribuf(Scene *out, TriBuf *tb, int build_quality_hq);

#endif /* MTLXRENDER_MESH_BUILD_H_ */
