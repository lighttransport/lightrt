#include "obj_load.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mesh_build.h"

/* ---- tiny growable float vector ----------------------------------------- */
typedef struct { float *d; size_t n, cap; } Vec;
static void vec_push3(Vec *v, float a, float b, float c) {
    if (v->n + 3 > v->cap) {
        v->cap = v->cap ? v->cap * 2 : 4096;
        v->d = (float *)realloc(v->d, v->cap * sizeof(float));
    }
    v->d[v->n++] = a; v->d[v->n++] = b; v->d[v->n++] = c;
}
static void vec_push2(Vec *v, float a, float b) {
    if (v->n + 2 > v->cap) {
        v->cap = v->cap ? v->cap * 2 : 4096;
        v->d = (float *)realloc(v->d, v->cap * sizeof(float));
    }
    v->d[v->n++] = a; v->d[v->n++] = b;
}

/* ---- material name table ------------------------------------------------ */
typedef struct { char (*names)[GLTF_MAX_MAT_NAME]; int n, cap; } MatTab;
static int mat_intern(MatTab *t, const char *name) {
    char buf[GLTF_MAX_MAT_NAME];
    size_t len = strlen(name);
    if (len >= GLTF_MAX_MAT_NAME) len = GLTF_MAX_MAT_NAME - 1;
    memcpy(buf, name, len); buf[len] = '\0';
    for (int i = 0; i < t->n; i++)
        if (strcmp(t->names[i], buf) == 0) return i;
    if (t->n >= t->cap) {
        t->cap = t->cap ? t->cap * 2 : 16;
        t->names = realloc(t->names, sizeof(char[GLTF_MAX_MAT_NAME]) * (size_t)t->cap);
    }
    memcpy(t->names[t->n], buf, len + 1);
    return t->n++;
}

/* Resolve a 1-based / negative OBJ index against the current element count. */
static int obj_index(long raw, size_t count_elems) {
    if (raw > 0) return (int)(raw - 1);
    if (raw < 0) return (int)((long)count_elems + raw);
    return -1; /* 0 == absent */
}

/* Parse one "v[/vt[/vn]]" face-vertex token into 0-based v/t/n (-1 if absent). */
static void parse_fv(const char *tok, size_t nv, size_t nt, size_t nn,
                     int *vi, int *ti, int *ni) {
    long a = 0, b = 0, c = 0;
    char *p;
    a = strtol(tok, &p, 10);
    *vi = obj_index(a, nv); *ti = -1; *ni = -1;
    if (*p != '/') return;
    p++;
    if (*p != '/') { b = strtol(p, &p, 10); *ti = obj_index(b, nt); }
    if (*p != '/') return;
    p++;
    c = strtol(p, &p, 10); *ni = obj_index(c, nn);
}

int scene_load_obj(const char *path, Scene *out, int build_quality_hq) {
    memset(out, 0, sizeof(*out));

    FILE *f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "obj: cannot open '%s'\n", path); return 1; }
    fseek(f, 0, SEEK_END);
    long fsz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (fsz <= 0) { fclose(f); fprintf(stderr, "obj: empty file\n"); return 1; }
    char *txt = (char *)malloc((size_t)fsz + 1);
    if (!txt || fread(txt, 1, (size_t)fsz, f) != (size_t)fsz) {
        fclose(f); free(txt); fprintf(stderr, "obj: read failed\n"); return 1;
    }
    txt[fsz] = '\0';
    fclose(f);

    Vec vp = {0}, vn = {0}, vt = {0};
    MatTab mtab = {0};
    TriBuf tb;
    memset(&tb, 0, sizeof(tb));

    int cur_mat = -1;
    int cur_geom = -1; /* lazily interned "default" on first face */

    char *save = NULL;
    for (char *line = strtok_r(txt, "\n", &save); line;
         line = strtok_r(NULL, "\n", &save)) {
        /* trim leading whitespace */
        while (*line == ' ' || *line == '\t' || *line == '\r') line++;
        if (line[0] == '#' || line[0] == '\0') continue;

        if (line[0] == 'v' && (line[1] == ' ' || line[1] == '\t')) {
            float x = 0, y = 0, z = 0;
            sscanf(line + 2, "%f %f %f", &x, &y, &z);
            vec_push3(&vp, x, y, z);
        } else if (line[0] == 'v' && line[1] == 'n') {
            float x = 0, y = 0, z = 0;
            sscanf(line + 3, "%f %f %f", &x, &y, &z);
            vec_push3(&vn, x, y, z);
        } else if (line[0] == 'v' && line[1] == 't') {
            float u = 0, v = 0;
            sscanf(line + 3, "%f %f", &u, &v);
            vec_push2(&vt, u, v);
        } else if (line[0] == 'f' && (line[1] == ' ' || line[1] == '\t')) {
            if (cur_geom < 0) cur_geom = tribuf_geom_intern(&tb, "default", 7);
            /* collect polygon vertices, then fan-triangulate */
            int fvi[64], fti[64], fni[64], nf = 0;
            char *tsave = NULL;
            for (char *tok = strtok_r(line + 1, " \t\r", &tsave);
                 tok && nf < 64; tok = strtok_r(NULL, " \t\r", &tsave)) {
                parse_fv(tok, vp.n / 3, vt.n / 2, vn.n / 3,
                         &fvi[nf], &fti[nf], &fni[nf]);
                if (fvi[nf] >= 0 && (size_t)fvi[nf] * 3 < vp.n) nf++;
            }
            for (int t = 2; t < nf; t++) {
                int corner[3] = {0, t - 1, t};
                float P[9], UV[6], N[9];
                int have_n = 1;
                for (int c = 0; c < 3; c++) {
                    int k = corner[c];
                    const float *pp = &vp.d[(size_t)fvi[k] * 3];
                    P[c * 3] = pp[0]; P[c * 3 + 1] = pp[1]; P[c * 3 + 2] = pp[2];
                    if (fti[k] >= 0 && (size_t)fti[k] * 2 < vt.n) {
                        UV[c * 2] = vt.d[(size_t)fti[k] * 2];
                        UV[c * 2 + 1] = vt.d[(size_t)fti[k] * 2 + 1];
                    } else { UV[c * 2] = 0.0f; UV[c * 2 + 1] = 0.0f; }
                    if (fni[k] >= 0 && (size_t)fni[k] * 3 < vn.n) {
                        const float *np = &vn.d[(size_t)fni[k] * 3];
                        N[c * 3] = np[0]; N[c * 3 + 1] = np[1]; N[c * 3 + 2] = np[2];
                    } else { have_n = 0; }
                }
                if (!have_n) { /* synthesize a geometric normal */
                    float e1[3] = {P[3] - P[0], P[4] - P[1], P[5] - P[2]};
                    float e2[3] = {P[6] - P[0], P[7] - P[1], P[8] - P[2]};
                    float gn[3] = {e1[1] * e2[2] - e1[2] * e2[1],
                                   e1[2] * e2[0] - e1[0] * e2[2],
                                   e1[0] * e2[1] - e1[1] * e2[0]};
                    for (int c = 0; c < 3; c++) {
                        N[c * 3] = gn[0]; N[c * 3 + 1] = gn[1]; N[c * 3 + 2] = gn[2];
                    }
                }
                tribuf_emit_tri(&tb, P, UV, N, cur_mat, cur_geom);
            }
        } else if (strncmp(line, "usemtl", 6) == 0) {
            char name[GLTF_MAX_MAT_NAME] = {0};
            if (sscanf(line + 6, "%127s", name) == 1) cur_mat = mat_intern(&mtab, name);
        } else if ((line[0] == 'o' || line[0] == 'g') &&
                   (line[1] == ' ' || line[1] == '\t' || line[1] == '\0' ||
                    line[1] == '\r')) {
            char name[GLTF_MAX_MAT_NAME] = {0};
            if (sscanf(line + 1, "%127s", name) == 1)
                cur_geom = tribuf_geom_intern(&tb, name, (uint32_t)strlen(name));
            else
                cur_geom = tribuf_geom_intern(&tb, "default", 7);
        }
        /* mtllib and everything else: ignored (materials come from the .mtlx) */
    }

    free(vp.d); free(vn.d); free(vt.d); free(txt);

    if (scene_from_tribuf(out, &tb, build_quality_hq)) { free(mtab.names); return 1; }

    out->mat_names = mtab.names; /* hand ownership to the Scene */
    out->nmat = mtab.n;

    fprintf(stderr, "obj: %zu triangles, %d materials, %d geoms, kernel=%s\n",
            out->ntri, out->nmat, out->ngeom, lrt_tri_kernel_name(out->bvh));
    return 0;
}
