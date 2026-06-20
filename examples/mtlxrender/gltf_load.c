#include "gltf_load.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mesh_build.h"
#include "tiny_gltf_v3.h"

/* ---- small double mat4 helpers (column?-agnostic: we use row-major[16]) ---- */
/* glTF node.matrix is column-major; we store as m[col*4+row] and apply as such. */

static void mat4_identity(double m[16]) {
    for (int i = 0; i < 16; i++) m[i] = 0.0;
    m[0] = m[5] = m[10] = m[15] = 1.0;
}

/* column-major multiply: r = a * b */
static void mat4_mul(const double a[16], const double b[16], double r[16]) {
    double t[16];
    for (int c = 0; c < 4; c++) {
        for (int row = 0; row < 4; row++) {
            double s = 0.0;
            for (int k = 0; k < 4; k++) s += a[k * 4 + row] * b[c * 4 + k];
            t[c * 4 + row] = s;
        }
    }
    memcpy(r, t, sizeof(t));
}

static void mat4_from_trs(const double t[3], const double q[4], const double s[3], double m[16]) {
    double x = q[0], y = q[1], z = q[2], w = q[3];
    double xx = x * x, yy = y * y, zz = z * z;
    double xy = x * y, xz = x * z, yz = y * z;
    double wx = w * x, wy = w * y, wz = w * z;
    /* column-major rotation*scale */
    m[0] = (1 - 2 * (yy + zz)) * s[0];
    m[1] = (2 * (xy + wz)) * s[0];
    m[2] = (2 * (xz - wy)) * s[0];
    m[3] = 0;
    m[4] = (2 * (xy - wz)) * s[1];
    m[5] = (1 - 2 * (xx + zz)) * s[1];
    m[6] = (2 * (yz + wx)) * s[1];
    m[7] = 0;
    m[8] = (2 * (xz + wy)) * s[2];
    m[9] = (2 * (yz - wx)) * s[2];
    m[10] = (1 - 2 * (xx + yy)) * s[2];
    m[11] = 0;
    m[12] = t[0];
    m[13] = t[1];
    m[14] = t[2];
    m[15] = 1;
}

static void xform_point(const double m[16], const float p[3], float out[3]) {
    double x = p[0], y = p[1], z = p[2];
    out[0] = (float)(m[0] * x + m[4] * y + m[8] * z + m[12]);
    out[1] = (float)(m[1] * x + m[5] * y + m[9] * z + m[13]);
    out[2] = (float)(m[2] * x + m[6] * y + m[10] * z + m[14]);
}

/* normal matrix = inverse-transpose of upper-left 3x3; apply to a vector. */
static void normal_matrix(const double m[16], double nm[9]) {
    double a = m[0], b = m[4], c = m[8];
    double d = m[1], e = m[5], f = m[9];
    double g = m[2], h = m[6], i = m[10];
    double A = e * i - f * h, B = f * g - d * i, C = d * h - e * g;
    double det = a * A + b * B + c * C;
    if (fabs(det) < 1e-20) { /* fall back to upper 3x3 (no scale) */
        nm[0] = a; nm[1] = b; nm[2] = c;
        nm[3] = d; nm[4] = e; nm[5] = f;
        nm[6] = g; nm[7] = h; nm[8] = i;
        return;
    }
    double inv = 1.0 / det;
    /* inverse */
    double D = c * h - b * i, E = a * i - c * g, F = b * g - a * h;
    double G = b * f - c * e, H = c * d - a * f, I = a * e - b * d;
    /* inverse-transpose */
    nm[0] = A * inv; nm[1] = B * inv; nm[2] = C * inv;
    nm[3] = D * inv; nm[4] = E * inv; nm[5] = F * inv;
    nm[6] = G * inv; nm[7] = H * inv; nm[8] = I * inv;
}

static void xform_normal(const double nm[9], const float n[3], float out[3]) {
    double x = n[0], y = n[1], z = n[2];
    out[0] = (float)(nm[0] * x + nm[3] * y + nm[6] * z);
    out[1] = (float)(nm[1] * x + nm[4] * y + nm[7] * z);
    out[2] = (float)(nm[2] * x + nm[5] * y + nm[8] * z);
}

/* ---- accessor decoding ------------------------------------------------- */

static int comp_size(int ct) {
    switch (ct) {
        case TG3_COMPONENT_TYPE_BYTE:
        case TG3_COMPONENT_TYPE_UNSIGNED_BYTE: return 1;
        case TG3_COMPONENT_TYPE_SHORT:
        case TG3_COMPONENT_TYPE_UNSIGNED_SHORT: return 2;
        case TG3_COMPONENT_TYPE_INT:
        case TG3_COMPONENT_TYPE_UNSIGNED_INT:
        case TG3_COMPONENT_TYPE_FLOAT: return 4;
        case TG3_COMPONENT_TYPE_DOUBLE: return 8;
        default: return 0;
    }
}

static int type_ncomp(int t) {
    switch (t) {
        case TG3_TYPE_SCALAR: return 1;
        case TG3_TYPE_VEC2: return 2;
        case TG3_TYPE_VEC3: return 3;
        case TG3_TYPE_VEC4: return 4;
        default: return 0;
    }
}

static double decode_one(const uint8_t *p, int ct, int normalized) {
    switch (ct) {
        case TG3_COMPONENT_TYPE_FLOAT: { float v; memcpy(&v, p, 4); return v; }
        case TG3_COMPONENT_TYPE_UNSIGNED_BYTE: { uint8_t v = *p; return normalized ? v / 255.0 : v; }
        case TG3_COMPONENT_TYPE_BYTE: { int8_t v; memcpy(&v, p, 1); return normalized ? fmax(v / 127.0, -1.0) : v; }
        case TG3_COMPONENT_TYPE_UNSIGNED_SHORT: { uint16_t v; memcpy(&v, p, 2); return normalized ? v / 65535.0 : v; }
        case TG3_COMPONENT_TYPE_SHORT: { int16_t v; memcpy(&v, p, 2); return normalized ? fmax(v / 32767.0, -1.0) : v; }
        case TG3_COMPONENT_TYPE_UNSIGNED_INT: { uint32_t v; memcpy(&v, p, 4); return v; }
        case TG3_COMPONENT_TYPE_INT: { int32_t v; memcpy(&v, p, 4); return v; }
        case TG3_COMPONENT_TYPE_DOUBLE: { double v; memcpy(&v, p, 8); return v; }
        default: return 0.0;
    }
}

/* Read accessor `ai` into a freshly malloc'd float array of count*want_comp.
 * Missing trailing components are zero-filled. Returns NULL on error/sparse. */
static float *read_accessor_f(const tg3_model *m, int32_t ai, int want_comp, uint64_t *out_count) {
    if (ai < 0 || (uint32_t)ai >= m->accessors_count) return NULL;
    const tg3_accessor *a = &m->accessors[ai];
    if (a->sparse.is_sparse) { fprintf(stderr, "gltf: sparse accessors unsupported\n"); return NULL; }
    if (a->buffer_view < 0 || (uint32_t)a->buffer_view >= m->buffer_views_count) return NULL;
    const tg3_buffer_view *bv = &m->buffer_views[a->buffer_view];
    if (bv->buffer < 0 || (uint32_t)bv->buffer >= m->buffers_count) return NULL;
    const tg3_buffer *buf = &m->buffers[bv->buffer];
    if (!buf->data.data) return NULL;

    int nc = type_ncomp(a->type);
    int cs = comp_size(a->component_type);
    if (nc == 0 || cs == 0) return NULL;
    uint32_t stride = bv->byte_stride ? bv->byte_stride : (uint32_t)(nc * cs);
    uint64_t base = bv->byte_offset + a->byte_offset;

    float *out = (float *)malloc(sizeof(float) * a->count * (uint64_t)want_comp);
    if (!out) return NULL;
    for (uint64_t e = 0; e < a->count; e++) {
        const uint8_t *rec = buf->data.data + base + e * stride;
        for (int c = 0; c < want_comp; c++) {
            out[e * want_comp + c] = (c < nc)
                ? (float)decode_one(rec + c * cs, a->component_type, a->normalized)
                : 0.0f;
        }
    }
    *out_count = a->count;
    return out;
}

/* read indices accessor into uint32 array; NULL if absent. */
static uint32_t *read_indices(const tg3_model *m, int32_t ai, uint64_t *out_count) {
    if (ai < 0 || (uint32_t)ai >= m->accessors_count) return NULL;
    const tg3_accessor *a = &m->accessors[ai];
    if (a->buffer_view < 0) return NULL;
    const tg3_buffer_view *bv = &m->buffer_views[a->buffer_view];
    const tg3_buffer *buf = &m->buffers[bv->buffer];
    int cs = comp_size(a->component_type);
    uint32_t stride = bv->byte_stride ? bv->byte_stride : (uint32_t)cs;
    uint64_t base = bv->byte_offset + a->byte_offset;
    uint32_t *out = (uint32_t *)malloc(sizeof(uint32_t) * a->count);
    if (!out) return NULL;
    for (uint64_t e = 0; e < a->count; e++) {
        const uint8_t *rec = buf->data.data + base + e * stride;
        out[e] = (uint32_t)decode_one(rec, a->component_type, 0);
    }
    *out_count = a->count;
    return out;
}

static void add_primitive(const tg3_model *m, const tg3_primitive *prim,
                          const double world[16], const double nm[9], int32_t geom, TriBuf *tb) {
    int mode = prim->mode < 0 ? TG3_MODE_TRIANGLES : prim->mode;
    if (mode != TG3_MODE_TRIANGLES) return; /* skip non-triangle prims */

    int32_t pos_acc = -1, nrm_acc = -1, uv_acc = -1;
    for (uint32_t i = 0; i < prim->attributes_count; i++) {
        const tg3_str *k = &prim->attributes[i].key;
        if (k->len == 8 && memcmp(k->data, "POSITION", 8) == 0) pos_acc = prim->attributes[i].value;
        else if (k->len == 6 && memcmp(k->data, "NORMAL", 6) == 0) nrm_acc = prim->attributes[i].value;
        else if (k->len == 10 && memcmp(k->data, "TEXCOORD_0", 10) == 0) uv_acc = prim->attributes[i].value;
    }
    if (pos_acc < 0) return;

    uint64_t nv = 0, nn = 0, nu = 0;
    float *pos = read_accessor_f(m, pos_acc, 3, &nv);
    if (!pos) return;
    float *nor = nrm_acc >= 0 ? read_accessor_f(m, nrm_acc, 3, &nn) : NULL;
    float *uvs = uv_acc >= 0 ? read_accessor_f(m, uv_acc, 2, &nu) : NULL;

    uint64_t ni = 0;
    uint32_t *idx = read_indices(m, prim->indices, &ni);
    uint64_t ntri = idx ? ni / 3 : nv / 3;

    for (uint64_t t = 0; t < ntri; t++) {
        uint32_t i0 = idx ? idx[t * 3 + 0] : (uint32_t)(t * 3 + 0);
        uint32_t i1 = idx ? idx[t * 3 + 1] : (uint32_t)(t * 3 + 1);
        uint32_t i2 = idx ? idx[t * 3 + 2] : (uint32_t)(t * 3 + 2);
        if (i0 >= nv || i1 >= nv || i2 >= nv) continue;
        uint32_t ii[3] = {i0, i1, i2};
        float P[9], UV[6], N[9];
        for (int c = 0; c < 3; c++) {
            xform_point(world, &pos[ii[c] * 3], &P[c * 3]);
            if (uvs && ii[c] < nu) { UV[c * 2] = uvs[ii[c] * 2]; UV[c * 2 + 1] = uvs[ii[c] * 2 + 1]; }
            else { UV[c * 2] = 0.0f; UV[c * 2 + 1] = 0.0f; }
            if (nor && ii[c] < nn) {
                xform_normal(nm, &nor[ii[c] * 3], &N[c * 3]);
            } else {
                N[c * 3] = N[c * 3 + 1] = N[c * 3 + 2] = 0.0f; /* fill below */
            }
        }
        if (!nor) { /* geometric normal */
            float e1[3] = {P[3] - P[0], P[4] - P[1], P[5] - P[2]};
            float e2[3] = {P[6] - P[0], P[7] - P[1], P[8] - P[2]};
            float gn[3] = {e1[1] * e2[2] - e1[2] * e2[1], e1[2] * e2[0] - e1[0] * e2[2],
                           e1[0] * e2[1] - e1[1] * e2[0]};
            for (int c = 0; c < 3; c++) { N[c * 3] = gn[0]; N[c * 3 + 1] = gn[1]; N[c * 3 + 2] = gn[2]; }
        }
        tribuf_emit_tri(tb, P, UV, N, prim->material, geom);
    }

    free(pos); free(nor); free(uvs); free(idx);
}

static void visit_node(const tg3_model *m, int32_t ni, const double parent[16], TriBuf *tb) {
    if (ni < 0 || (uint32_t)ni >= m->nodes_count) return;
    const tg3_node *n = &m->nodes[ni];
    double local[16], world[16];
    if (n->has_matrix) memcpy(local, n->matrix, sizeof(local));
    else mat4_from_trs(n->translation, n->rotation, n->scale, local);
    mat4_mul(parent, local, world);

    if (n->mesh >= 0 && (uint32_t)n->mesh < m->meshes_count) {
        double nm[9];
        normal_matrix(world, nm);
        const tg3_mesh *mesh = &m->meshes[n->mesh];
        /* Prefer the node name as the geometry key (matches MaterialX geom),
         * falling back to the mesh name. */
        const tg3_str *gname = (n->name.data && n->name.len) ? &n->name : &mesh->name;
        int32_t geom = tribuf_geom_intern(tb, gname->data, gname->len);
        for (uint32_t p = 0; p < mesh->primitives_count; p++)
            add_primitive(m, &mesh->primitives[p], world, nm, geom, tb);
    }
    for (uint32_t c = 0; c < n->children_count; c++)
        visit_node(m, n->children[c], world, tb);
}

int scene_load_gltf(const char *path, Scene *out, int build_quality_hq) {
    memset(out, 0, sizeof(*out));

    tg3_model model;
    tg3_error_stack errors;
    tg3_error_stack_init(&errors);
    tg3_parse_options opts;
    tg3_parse_options_init(&opts);

    tg3_error_code rc = tg3_parse_file(&model, &errors, path, (uint32_t)strlen(path), &opts);
    if (rc != TG3_OK) {
        fprintf(stderr, "gltf: parse failed for '%s' (code %d)\n", path, (int)rc);
        return 1;
    }

    /* material name table */
    out->nmat = (int)model.materials_count;
    if (out->nmat > 0) {
        out->mat_names = malloc(sizeof(char[GLTF_MAX_MAT_NAME]) * (size_t)out->nmat);
        for (int i = 0; i < out->nmat; i++) {
            const tg3_str *nm = &model.materials[i].name;
            uint32_t len = nm->len < GLTF_MAX_MAT_NAME - 1 ? nm->len : GLTF_MAX_MAT_NAME - 1;
            if (nm->data && len) memcpy(out->mat_names[i], nm->data, len);
            out->mat_names[i][len] = '\0';
        }
    }

    TriBuf tb;
    memset(&tb, 0, sizeof(tb));
    double ident[16];
    mat4_identity(ident);

    /* traverse default scene if present, else all scenes, else all nodes. */
    if (model.default_scene >= 0 && (uint32_t)model.default_scene < model.scenes_count) {
        const tg3_scene *sc = &model.scenes[model.default_scene];
        for (uint32_t i = 0; i < sc->nodes_count; i++) visit_node(&model, sc->nodes[i], ident, &tb);
    } else if (model.scenes_count > 0) {
        for (uint32_t s = 0; s < model.scenes_count; s++)
            for (uint32_t i = 0; i < model.scenes[s].nodes_count; i++)
                visit_node(&model, model.scenes[s].nodes[i], ident, &tb);
    } else {
        for (uint32_t i = 0; i < model.nodes_count; i++) visit_node(&model, (int32_t)i, ident, &tb);
    }

    tg3_model_free(&model);

    /* On failure scene_from_tribuf frees the moved tb arrays; scene_free then
     * releases out->mat_names (allocated above) and zeroes the struct. */
    if (scene_from_tribuf(out, &tb, build_quality_hq)) { scene_free(out); return 1; }

    fprintf(stderr, "gltf: %zu triangles, %d materials, kernel=%s\n",
            out->ntri, out->nmat, lrt_tri_kernel_name(out->bvh));
    return 0;
}

void scene_free(Scene *s) {
    if (!s) return;
    if (s->bvh) lrt_tri_scene_free(s->bvh);
    free(s->verts); free(s->tri_uv); free(s->tri_n); free(s->tri_mat); free(s->tri_geom);
    free(s->mat_names); free(s->geom_names);
    memset(s, 0, sizeof(*s));
}
