#include "mesh_build.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int tribuf_geom_intern(TriBuf *tb, const char *name, uint32_t len) {
    char buf[GLTF_MAX_MAT_NAME];
    uint32_t n = len < GLTF_MAX_MAT_NAME - 1 ? len : GLTF_MAX_MAT_NAME - 1;
    if (name && n) memcpy(buf, name, n);
    buf[n] = '\0';
    for (int i = 0; i < tb->ngeom; i++)
        if (strcmp(tb->geom_names[i], buf) == 0) return i;
    if (tb->ngeom >= MESH_MAX_GEOM) return tb->ngeom - 1;
    memcpy(tb->geom_names[tb->ngeom], buf, n + 1);
    return tb->ngeom++;
}

static void tribuf_reserve(TriBuf *tb, size_t need) {
    if (tb->ntri + need <= tb->cap) return;
    size_t cap = tb->cap ? tb->cap * 2 : 65536;
    while (cap < tb->ntri + need) cap *= 2;
    tb->verts = (float *)realloc(tb->verts, cap * 9 * sizeof(float));
    tb->uv = (float *)realloc(tb->uv, cap * 6 * sizeof(float));
    tb->nrm = (float *)realloc(tb->nrm, cap * 9 * sizeof(float));
    tb->mat = (int32_t *)realloc(tb->mat, cap * sizeof(int32_t));
    tb->geom = (int32_t *)realloc(tb->geom, cap * sizeof(int32_t));
    tb->cap = cap;
}

void tribuf_emit_tri(TriBuf *tb, const float P[9], const float UV[6],
                     const float N[9], int32_t mat, int32_t geom) {
    tribuf_reserve(tb, 1);
    memcpy(tb->verts + tb->ntri * 9, P, 9 * sizeof(float));
    memcpy(tb->uv + tb->ntri * 6, UV, 6 * sizeof(float));
    memcpy(tb->nrm + tb->ntri * 9, N, 9 * sizeof(float));
    tb->mat[tb->ntri] = mat;
    tb->geom[tb->ntri] = geom;
    tb->ntri++;
}

void tribuf_free(TriBuf *tb) {
    free(tb->verts); free(tb->uv); free(tb->nrm); free(tb->mat); free(tb->geom);
    memset(tb, 0, sizeof(*tb));
}

int scene_from_tribuf(Scene *out, TriBuf *tb, int build_quality_hq) {
    if (tb->ntri == 0) {
        fprintf(stderr, "mesh: no triangles loaded\n");
        tribuf_free(tb);
        return 1;
    }

    out->verts = tb->verts;
    out->tri_uv = tb->uv;
    out->tri_n = tb->nrm;
    out->tri_mat = tb->mat;
    out->tri_geom = tb->geom;
    out->ntri = tb->ntri;

    out->ngeom = tb->ngeom;
    if (tb->ngeom > 0) {
        out->geom_names = malloc(sizeof(char[GLTF_MAX_MAT_NAME]) * (size_t)tb->ngeom);
        memcpy(out->geom_names, tb->geom_names,
               sizeof(char[GLTF_MAX_MAT_NAME]) * (size_t)tb->ngeom);
    }

    /* bounds */
    out->bmin[0] = out->bmin[1] = out->bmin[2] = 1e30f;
    out->bmax[0] = out->bmax[1] = out->bmax[2] = -1e30f;
    for (size_t i = 0; i < tb->ntri * 3; i++) {
        for (int c = 0; c < 3; c++) {
            float v = out->verts[i * 3 + c];
            if (v < out->bmin[c]) out->bmin[c] = v;
            if (v > out->bmax[c]) out->bmax[c] = v;
        }
    }

    /* build BVH */
    lrt_tri_build_options bopts;
    memset(&bopts, 0, sizeof(bopts));
    bopts.quality = build_quality_hq ? LRT_TRI_BUILD_HQ : LRT_TRI_BUILD_DEFAULT;
    bopts.layout = LRT_TRI_LAYOUT_AUTO;
    lrt_result err = LRT_RESULT_OK;
    out->bvh = lrt_tri_scene_build(out->verts, out->ntri, &bopts, &err);
    if (!out->bvh) {
        fprintf(stderr, "mesh: BVH build failed (%d)\n", (int)err);
        return 1;
    }
    return 0;
}
