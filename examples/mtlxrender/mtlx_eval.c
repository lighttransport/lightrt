#include "mtlx_eval.h"

#include <string.h>

/* ---- MtlxValue helpers ------------------------------------------------- */

static MtlxValue mv_float(float f) { MtlxValue v; memset(&v, 0, sizeof(v)); v.type = MV_FLOAT; v.v[0] = f; return v; }
static MtlxValue mv_color3(v3 c) { MtlxValue v; memset(&v, 0, sizeof(v)); v.type = MV_COLOR3; v.v[0] = c.x; v.v[1] = c.y; v.v[2] = c.z; return v; }
static MtlxValue mv_vec3(v3 c) { MtlxValue v; memset(&v, 0, sizeof(v)); v.type = MV_VEC3; v.v[0] = c.x; v.v[1] = c.y; v.v[2] = c.z; return v; }
static MtlxValue mv_vec2(float x, float y) { MtlxValue v; memset(&v, 0, sizeof(v)); v.type = MV_VEC2; v.v[0] = x; v.v[1] = y; return v; }

static float mv_as_float(const MtlxValue *v) {
    if (v->type == MV_FLOAT || v->type == MV_INT || v->type == MV_BOOL) return v->v[0];
    /* color/vector -> luminance-ish average for scalar coercion */
    return (v->v[0] + v->v[1] + v->v[2]) * (1.0f / 3.0f);
}
static v3 mv_as_v3(const MtlxValue *v) {
    if (v->type == MV_FLOAT) return v3_splat(v->v[0]);
    return v3_make(v->v[0], v->v[1], v->v[2]);
}

/* ---- node category dispatch ------------------------------------------- */
typedef enum {
    OP_UNKNOWN = 0, OP_IMAGE, OP_TILEDIMAGE, OP_NORMALMAP, OP_TEXCOORD,
    OP_CONSTANT, OP_MULTIPLY, OP_ADD, OP_SUBTRACT, OP_MIX, OP_CLAMP, OP_NORMALIZE
} NodeOp;

static NodeOp classify(const char *cat) {
    if (!strcmp(cat, "image")) return OP_IMAGE;
    if (!strcmp(cat, "tiledimage")) return OP_TILEDIMAGE;
    if (!strcmp(cat, "normalmap")) return OP_NORMALMAP;
    if (!strcmp(cat, "texcoord")) return OP_TEXCOORD;
    if (!strcmp(cat, "constant")) return OP_CONSTANT;
    if (!strcmp(cat, "multiply")) return OP_MULTIPLY;
    if (!strcmp(cat, "add")) return OP_ADD;
    if (!strcmp(cat, "subtract")) return OP_SUBTRACT;
    if (!strcmp(cat, "mix")) return OP_MIX;
    if (!strcmp(cat, "clamp")) return OP_CLAMP;
    if (!strcmp(cat, "normalize")) return OP_NORMALIZE;
    return OP_UNKNOWN;
}

static MtlxValue eval_node(ShadeContext *ctx, int node_id);

/* Find an input by name on a node; NULL if absent. */
static const MtlxInput *find_input(const MtlxNode *n, const char *name) {
    for (int i = 0; i < n->ninput; i++)
        if (!strcmp(n->inputs[i].name, name)) return &n->inputs[i];
    return NULL;
}

/* Evaluate an input (connection > literal > zero). */
static MtlxValue eval_input(ShadeContext *ctx, const MtlxInput *in) {
    if (!in) { MtlxValue z; memset(&z, 0, sizeof(z)); return z; }
    if (in->src_node >= 0) return eval_node(ctx, in->src_node);
    if (in->has_value) return in->value;
    MtlxValue z; memset(&z, 0, sizeof(z)); z.type = in->type; return z;
}

/* image / tiledimage: sample the file at the current UV. */
static MtlxValue eval_image(ShadeContext *ctx, const MtlxNode *n) {
    const MtlxInput *file = find_input(n, "file");
    int srgb = file ? file->colorspace_srgb : 0;
    const char *path = (file && file->value.s) ? file->value.s : NULL;
    int id = path ? texcache_get(ctx->tex, path, srgb) : -1;
    float s[4];
    if (id >= 0) {
        texcache_sample(ctx->tex, id, ctx->uv[0], ctx->uv[1], s);
    } else {
        /* fall back to the node's "default" input if present */
        const MtlxInput *def = find_input(n, "default");
        MtlxValue d = eval_input(ctx, def);
        v3 dc = mv_as_v3(&d);
        s[0] = dc.x; s[1] = dc.y; s[2] = dc.z; s[3] = 1.0f;
    }
    switch (n->type) {
        case MV_FLOAT: return mv_float(s[0]);
        case MV_VEC2: return mv_vec2(s[0], s[1]);
        case MV_VEC3: return mv_vec3(v3_make(s[0], s[1], s[2]));
        case MV_COLOR4: { MtlxValue v; memset(&v,0,sizeof(v)); v.type=MV_COLOR4; v.v[0]=s[0];v.v[1]=s[1];v.v[2]=s[2];v.v[3]=s[3]; return v; }
        case MV_COLOR3:
        default: return mv_color3(v3_make(s[0], s[1], s[2]));
    }
}

/* normalmap: decode tangent-space normal -> world space. */
static MtlxValue eval_normalmap(ShadeContext *ctx, const MtlxNode *n) {
    MtlxValue in = eval_input(ctx, find_input(n, "in"));
    v3 t = mv_as_v3(&in);
    /* [0,1] -> [-1,1] */
    v3 ts = v3_make(2.0f * t.x - 1.0f, 2.0f * t.y - 1.0f, 2.0f * t.z - 1.0f);
    const MtlxInput *scin = find_input(n, "scale");
    float scale = scin ? mv_as_float(&scin->value) : 1.0f;
    if (scin && scin->src_node >= 0) { MtlxValue sv = eval_node(ctx, scin->src_node); scale = mv_as_float(&sv); }
    ts.x *= scale; ts.y *= scale;

    v3 N = v3_normalize(ctx->Ns);
    /* Gram-Schmidt orthonormalize the UV tangent against N; fall back to an
     * arbitrary basis if the UV-derived tangent is degenerate. */
    v3 T = v3_sub(ctx->dpdu, v3_scale(N, v3_dot(N, ctx->dpdu)));
    v3 B;
    if (!v3_is_finite(T) || v3_len(T) < 1e-6f) {
        onb(N, &T, &B);
    } else {
        T = v3_normalize(T);
        B = v3_cross(N, T);
    }
    v3 world = v3_add(v3_add(v3_scale(T, ts.x), v3_scale(B, ts.y)), v3_scale(N, ts.z));
    world = v3_normalize(world);
    if (!v3_is_finite(world)) world = N;
    return mv_vec3(world);
}

static MtlxValue eval_node(ShadeContext *ctx, int node_id) {
    if (node_id < 0 || node_id >= ctx->doc->nnode) { MtlxValue z; memset(&z, 0, sizeof(z)); return z; }
    if (ctx->memo_done[node_id]) return ctx->memo[node_id];
    /* cycle guard: mark done with a zero before recursing */
    ctx->memo_done[node_id] = 1;
    MtlxValue z; memset(&z, 0, sizeof(z));
    ctx->memo[node_id] = z;

    const MtlxNode *n = &ctx->doc->nodes[node_id];
    MtlxValue r = z;
    switch (classify(n->category)) {
        case OP_IMAGE:
        case OP_TILEDIMAGE:
            r = eval_image(ctx, n);
            break;
        case OP_NORMALMAP:
            r = eval_normalmap(ctx, n);
            break;
        case OP_TEXCOORD:
            r = (n->type == MV_VEC3) ? mv_vec3(v3_make(ctx->uv[0], ctx->uv[1], 0.0f))
                                     : mv_vec2(ctx->uv[0], ctx->uv[1]);
            break;
        case OP_CONSTANT:
            r = eval_input(ctx, find_input(n, "value"));
            break;
        case OP_MULTIPLY: {
            MtlxValue a = eval_input(ctx, find_input(n, "in1"));
            MtlxValue b = eval_input(ctx, find_input(n, "in2"));
            v3 va = mv_as_v3(&a), vb = mv_as_v3(&b);
            r = (a.type == MV_FLOAT) ? mv_float(a.v[0] * mv_as_float(&b)) : mv_color3(v3_mul(va, vb));
            r.type = (a.type != MV_NONE) ? a.type : b.type;
            break;
        }
        case OP_ADD: {
            MtlxValue a = eval_input(ctx, find_input(n, "in1"));
            MtlxValue b = eval_input(ctx, find_input(n, "in2"));
            r = (a.type == MV_FLOAT) ? mv_float(a.v[0] + mv_as_float(&b)) : mv_color3(v3_add(mv_as_v3(&a), mv_as_v3(&b)));
            r.type = a.type;
            break;
        }
        case OP_SUBTRACT: {
            MtlxValue a = eval_input(ctx, find_input(n, "in1"));
            MtlxValue b = eval_input(ctx, find_input(n, "in2"));
            r = (a.type == MV_FLOAT) ? mv_float(a.v[0] - mv_as_float(&b)) : mv_color3(v3_sub(mv_as_v3(&a), mv_as_v3(&b)));
            r.type = a.type;
            break;
        }
        case OP_MIX: {
            MtlxValue fg = eval_input(ctx, find_input(n, "fg"));
            MtlxValue bg = eval_input(ctx, find_input(n, "bg"));
            MtlxValue mx = eval_input(ctx, find_input(n, "mix"));
            float t = mv_as_float(&mx);
            r = mv_color3(v3_lerp(mv_as_v3(&bg), mv_as_v3(&fg), t));
            r.type = fg.type;
            break;
        }
        case OP_CLAMP: {
            MtlxValue a = eval_input(ctx, find_input(n, "in"));
            v3 va = mv_as_v3(&a);
            r = mv_color3(v3_make(clampf(va.x, 0, 1), clampf(va.y, 0, 1), clampf(va.z, 0, 1)));
            r.type = a.type;
            break;
        }
        case OP_NORMALIZE: {
            MtlxValue a = eval_input(ctx, find_input(n, "in"));
            r = mv_vec3(v3_normalize(mv_as_v3(&a)));
            break;
        }
        case OP_UNKNOWN:
        default:
            /* passthrough first input if any, else zero */
            if (n->ninput > 0) r = eval_input(ctx, &n->inputs[0]);
            break;
    }
    ctx->memo[node_id] = r;
    return r;
}

/* ---- public surface evaluation ---------------------------------------- */

void openpbr_defaults(OpenPBRParams *p) {
    memset(p, 0, sizeof(*p));
    p->base_weight = 1.0f;
    p->base_color = v3_make(0.8f, 0.8f, 0.8f);
    p->metalness = 0.0f;
    p->specular_weight = 1.0f;
    p->specular_color = v3_splat(1.0f);
    p->specular_roughness = 0.3f;
    p->specular_ior = 1.5f;
    p->transmission_color = v3_splat(1.0f);
    p->subsurface_color = v3_splat(0.8f);
    p->subsurface_radius = v3_splat(1.0f);
    p->subsurface_scale = 1.0f;
    p->coat_color = v3_splat(1.0f);
    p->coat_roughness = 0.1f;
    p->coat_ior = 1.5f;
    p->sheen_color = v3_splat(1.0f);
    p->sheen_roughness = 0.3f;
    p->emission_color = v3_splat(1.0f);
    p->opacity = 1.0f;
}

/* helpers to read a named input as float / color, evaluating connections. */
static float in_float(ShadeContext *ctx, const MtlxNode *n, const char *name, float fallback) {
    const MtlxInput *in = find_input(n, name);
    if (!in) return fallback;
    MtlxValue v = eval_input(ctx, in);
    return mv_as_float(&v);
}
static v3 in_color(ShadeContext *ctx, const MtlxNode *n, const char *name, v3 fallback) {
    const MtlxInput *in = find_input(n, name);
    if (!in) return fallback;
    MtlxValue v = eval_input(ctx, in);
    return mv_as_v3(&v);
}

int mtlx_eval_surface(ShadeContext *ctx, int surface_node, OpenPBRParams *out) {
    openpbr_defaults(out);
    out->normal = v3_normalize(ctx->Ns);
    if (surface_node < 0 || surface_node >= ctx->doc->nnode) return 1;

    /* reset memo for this shade point */
    memset(ctx->memo_done, 0, (size_t)ctx->doc->nnode);

    const MtlxNode *n = &ctx->doc->nodes[surface_node];
    int is_openpbr = !strcmp(n->category, "open_pbr_surface");

    if (is_openpbr) {
        out->base_weight = in_float(ctx, n, "base_weight", 1.0f);
        out->base_color = in_color(ctx, n, "base_color", out->base_color);
        out->metalness = in_float(ctx, n, "base_metalness", 0.0f);
        out->diffuse_roughness = in_float(ctx, n, "base_diffuse_roughness", 0.0f);
        out->specular_weight = in_float(ctx, n, "specular_weight", 1.0f);
        out->specular_color = in_color(ctx, n, "specular_color", out->specular_color);
        out->specular_roughness = in_float(ctx, n, "specular_roughness", 0.3f);
        out->specular_ior = in_float(ctx, n, "specular_ior", 1.5f);
        out->transmission = in_float(ctx, n, "transmission_weight", 0.0f);
        out->transmission_color = in_color(ctx, n, "transmission_color", out->transmission_color);
        out->subsurface = in_float(ctx, n, "subsurface_weight", 0.0f);
        out->subsurface_color = in_color(ctx, n, "subsurface_color", out->subsurface_color);
        out->subsurface_radius = v3_splat(in_float(ctx, n, "subsurface_radius", 1.0f));
        out->subsurface_scale = in_float(ctx, n, "subsurface_radius_scale", 1.0f);
        out->coat_weight = in_float(ctx, n, "coat_weight", 0.0f);
        out->coat_color = in_color(ctx, n, "coat_color", out->coat_color);
        out->coat_roughness = in_float(ctx, n, "coat_roughness", 0.0f);
        out->coat_ior = in_float(ctx, n, "coat_ior", 1.6f);
        out->sheen_weight = in_float(ctx, n, "fuzz_weight", 0.0f);
        out->sheen_color = in_color(ctx, n, "fuzz_color", out->sheen_color);
        out->sheen_roughness = in_float(ctx, n, "fuzz_roughness", 0.5f);
        out->emission = in_float(ctx, n, "emission_luminance", 0.0f);
        out->emission_color = in_color(ctx, n, "emission_color", out->emission_color);
        out->opacity = in_float(ctx, n, "geometry_opacity", 1.0f);
    } else { /* standard_surface */
        out->base_weight = in_float(ctx, n, "base", 1.0f);
        out->base_color = in_color(ctx, n, "base_color", out->base_color);
        out->metalness = in_float(ctx, n, "metalness", 0.0f);
        out->diffuse_roughness = in_float(ctx, n, "diffuse_roughness", 0.0f);
        out->specular_weight = in_float(ctx, n, "specular", 1.0f);
        out->specular_color = in_color(ctx, n, "specular_color", out->specular_color);
        out->specular_roughness = in_float(ctx, n, "specular_roughness", 0.2f);
        out->specular_ior = in_float(ctx, n, "specular_IOR", 1.5f);
        out->transmission = in_float(ctx, n, "transmission", 0.0f);
        out->transmission_color = in_color(ctx, n, "transmission_color", out->transmission_color);
        out->subsurface = in_float(ctx, n, "subsurface", 0.0f);
        out->subsurface_color = in_color(ctx, n, "subsurface_color", out->subsurface_color);
        out->subsurface_radius = in_color(ctx, n, "subsurface_radius", v3_splat(1.0f));
        out->subsurface_scale = in_float(ctx, n, "subsurface_scale", 1.0f);
        out->coat_weight = in_float(ctx, n, "coat", 0.0f);
        out->coat_color = in_color(ctx, n, "coat_color", out->coat_color);
        out->coat_roughness = in_float(ctx, n, "coat_roughness", 0.1f);
        out->coat_ior = in_float(ctx, n, "coat_IOR", 1.5f);
        out->sheen_weight = in_float(ctx, n, "sheen", 0.0f);
        out->sheen_color = in_color(ctx, n, "sheen_color", out->sheen_color);
        out->sheen_roughness = in_float(ctx, n, "sheen_roughness", 0.3f);
        out->emission = in_float(ctx, n, "emission", 0.0f);
        out->emission_color = in_color(ctx, n, "emission_color", out->emission_color);
        out->opacity = 1.0f;
    }

    /* normal input (already world-space via normalmap kernel) */
    const MtlxInput *nin = find_input(n, is_openpbr ? "geometry_normal" : "normal");
    if (nin && nin->src_node >= 0) {
        MtlxValue nv = eval_node(ctx, nin->src_node);
        v3 wn = mv_as_v3(&nv);
        if (v3_is_finite(wn) && v3_len(wn) > 0.1f) out->normal = v3_normalize(wn);
    }

    /* sanitize */
    out->specular_roughness = clampf(out->specular_roughness, 0.01f, 1.0f);
    out->coat_roughness = clampf(out->coat_roughness, 0.01f, 1.0f);
    out->metalness = clampf(out->metalness, 0.0f, 1.0f);
    return 0;
}
