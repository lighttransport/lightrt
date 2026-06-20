/*
 * mtlxvk.c — MaterialX -> GPU shading bridge.
 *
 * Loads a .mtlx document, evaluates every <surfacematerial> with the CPU
 * MaterialX node-graph interpreter at a single representative shade point to
 * bake constant OpenPBR parameters, maps those onto the analytic-shading
 * primitive (lrt_vk_shade_prim), and renders one sphere per material on the GPU
 * via lrt_vk_shade_analytic / the resident lrt_vk_shade_scene API.
 *
 * This is the GPU counterpart of the CPU path tracer: the node graph stays on
 * the CPU (evaluated once per material), and only the resulting constant
 * material parameters are shaded en masse on the GPU. Spatially varying inputs
 * (textures) are therefore collapsed to a single baked colour per sphere; the
 * GPU BSDF is the OpenPBR core (diffuse + metallic/dielectric GGX), so coat /
 * sheen / transmission / subsurface lobes are not shown.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lightrt_c_vk.h"
#include "mtlx_doc.h"
#include "mtlx_eval.h"
#include "texture.h"
#include "vecmath.h"

/* ---- baked material -> primitive ----------------------------------------- */
static void map_params(const OpenPBRParams *p, lrt_vk_shade_prim *prim) {
    v3 base = v3_scale(p->base_color, p->base_weight);
    prim->base_color[0] = base.x;
    prim->base_color[1] = base.y;
    prim->base_color[2] = base.z;
    prim->metalness = p->metalness;
    prim->roughness = p->specular_roughness;
    prim->specular_ior = p->specular_ior > 1.0f ? p->specular_ior : 1.5f;
    /* The core GPU BSDF has no emission_color; tint emission by the base. */
    prim->emission = p->emission * (luminance(p->emission_color) > 0.0f ? 1.0f : 0.0f);
    prim->opacity = p->opacity;
}

/* ---- tonemapped PPM (P6, zero deps) -------------------------------------- */
static int write_ppm(const char *path, const float *rgba, uint32_t w, uint32_t h) {
    FILE *f = fopen(path, "wb");
    if (!f) return 0;
    fprintf(f, "P6\n%u %u\n255\n", w, h);
    for (uint32_t i = 0; i < w * h; i++) {
        for (int c = 0; c < 3; c++) {
            float v = rgba[i * 4 + c];
            v = v / (1.0f + v);                       /* Reinhard */
            v = powf(v < 0 ? 0 : (v > 1 ? 1 : v), 1.0f / 2.2f);
            fputc((unsigned char)(v * 255.0f + 0.5f), f);
        }
    }
    fclose(f);
    return 1;
}

/* dir part of a path (into buf); "." when there is no slash. */
static void path_dir(const char *path, char *buf, size_t n) {
    const char *slash = strrchr(path, '/');
    if (!slash) { snprintf(buf, n, "."); return; }
    size_t len = (size_t)(slash - path);
    if (len >= n) len = n - 1;
    memcpy(buf, path, len);
    buf[len] = 0;
}

int main(int argc, char **argv) {
    const char *mtlx_path = NULL, *out_path = "mtlxvk.ppm";
    uint32_t w = 800, h = 600, spp = 4;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--mtlx") && i + 1 < argc) mtlx_path = argv[++i];
        else if (!strcmp(argv[i], "--out") && i + 1 < argc) out_path = argv[++i];
        else if (!strcmp(argv[i], "--w") && i + 1 < argc) w = (uint32_t)atoi(argv[++i]);
        else if (!strcmp(argv[i], "--h") && i + 1 < argc) h = (uint32_t)atoi(argv[++i]);
        else if (!strcmp(argv[i], "--spp") && i + 1 < argc) spp = (uint32_t)atoi(argv[++i]);
    }
    if (!mtlx_path) {
        fprintf(stderr,
                "usage: mtlxvk --mtlx FILE.mtlx [--out img.ppm] [--w N --h N --spp N]\n");
        return 2;
    }

    MtlxDoc *doc = mtlx_load(mtlx_path);
    if (!doc) { fprintf(stderr, "failed to load %s\n", mtlx_path); return 1; }
    if (doc->nmat <= 0) {
        fprintf(stderr, "%s defines no <surfacematerial> nodes\n", mtlx_path);
        mtlx_free(doc);
        return 1;
    }

    char base_dir[1024];
    path_dir(mtlx_path, base_dir, sizeof(base_dir));
    TextureCache *tc = texcache_create(base_dir);
    if (tc) texcache_preload(tc, doc);

    /* Evaluate every material at one representative shade point. */
    MtlxValue *memo = (MtlxValue *)calloc((size_t)doc->nnode, sizeof(MtlxValue));
    char *memo_done = (char *)calloc((size_t)doc->nnode, 1);
    lrt_vk_shade_prim *prims =
        (lrt_vk_shade_prim *)calloc((size_t)doc->nmat, sizeof(lrt_vk_shade_prim));
    if (!memo || !memo_done || !prims) { fprintf(stderr, "OOM\n"); return 1; }

    uint32_t n = 0;
    printf("baking %d MaterialX material(s) from %s\n", doc->nmat, mtlx_path);
    for (int m = 0; m < doc->nmat; m++) {
        const MtlxMaterial *mat = &doc->mats[m];
        lrt_vk_shade_prim *prim = &prims[n];
        memset(prim, 0, sizeof(*prim));
        prim->type = 0.0f;          /* sphere */
        prim->radius = 0.46f;
        prim->base_color[0] = prim->base_color[1] = prim->base_color[2] = 0.6f;
        prim->roughness = 0.5f;
        prim->specular_ior = 1.5f;

        if (mat->surface_node >= 0) {
            ShadeContext ctx;
            memset(&ctx, 0, sizeof(ctx));
            ctx.doc = doc;
            ctx.tex = tc;
            ctx.uv[0] = 0.5f; ctx.uv[1] = 0.5f;
            ctx.P = v3_make(0, 0, 0);
            ctx.Ns = v3_make(0, 0, 1);
            ctx.Ng = v3_make(0, 0, 1);
            ctx.dpdu = v3_make(1, 0, 0);
            ctx.dpdv = v3_make(0, 1, 0);
            memset(memo_done, 0, (size_t)doc->nnode);
            ctx.memo = memo;
            ctx.memo_done = memo_done;
            OpenPBRParams p;
            openpbr_defaults(&p);
            if (mtlx_eval_surface(&ctx, mat->surface_node, &p) == 0)
                map_params(&p, prim);
            printf("  [%2u] %-28s base=(%.3f %.3f %.3f) metal=%.2f rough=%.2f ior=%.2f%s\n",
                   n, mat->name, prim->base_color[0], prim->base_color[1],
                   prim->base_color[2], prim->metalness, prim->roughness,
                   prim->specular_ior, prim->emission > 0 ? " [emissive]" : "");
        } else {
            printf("  [%2u] %-28s (no surface shader; default gray)\n", n, mat->name);
        }
        n++;
    }

    /* Lay the spheres out on a centred grid in the z=0 plane. */
    uint32_t cols = (uint32_t)ceilf(sqrtf((float)n));
    uint32_t rows = (n + cols - 1) / cols;
    const float spacing = 1.15f;
    for (uint32_t i = 0; i < n; i++) {
        uint32_t col = i % cols, row = i / cols;
        prims[i].center[0] = ((float)col - (float)(cols - 1) * 0.5f) * spacing;
        prims[i].center[1] = ((float)(rows - 1) * 0.5f - (float)row) * spacing;
        prims[i].center[2] = 0.0f;
    }

    /* Camera framing the whole grid. */
    lrt_vk_shade_desc desc;
    memset(&desc, 0, sizeof(desc));
    desc.width = w; desc.height = h; desc.spp = spp;
    float aspect = (float)w / (float)h;
    desc.aspect = aspect;
    float tan_half = tanf(0.5f * 45.0f * 3.14159265358979323846f / 180.0f);
    desc.tan_half_fov = tan_half;
    float half_w = (float)cols * spacing * 0.5f + 0.6f;
    float half_h = (float)rows * spacing * 0.5f + 0.6f;
    float dist = half_h / tan_half;
    float dist_w = half_w / (tan_half * aspect);
    if (dist_w > dist) dist = dist_w;
    dist *= 1.1f;
    desc.cam_origin[0] = 0; desc.cam_origin[1] = 0; desc.cam_origin[2] = dist;
    desc.cam_forward[0] = 0; desc.cam_forward[1] = 0; desc.cam_forward[2] = -1;
    desc.cam_right[0] = 1; desc.cam_right[1] = 0; desc.cam_right[2] = 0;
    desc.cam_up[0] = 0; desc.cam_up[1] = 1; desc.cam_up[2] = 0;
    /* sun + sky */
    float sl = sqrtf(0.3f * 0.3f + 0.7f * 0.7f + 0.5f * 0.5f);
    desc.sun_dir[0] = -0.3f / sl; desc.sun_dir[1] = 0.7f / sl; desc.sun_dir[2] = 0.5f / sl;
    desc.sun_radiance[0] = 3.0f; desc.sun_radiance[1] = 2.9f; desc.sun_radiance[2] = 2.7f;
    desc.env_top[0] = 0.5f; desc.env_top[1] = 0.7f; desc.env_top[2] = 1.0f;
    desc.env_bottom[0] = 0.3f; desc.env_bottom[1] = 0.3f; desc.env_bottom[2] = 0.32f;

    float *img = (float *)malloc((size_t)w * h * 4 * sizeof(float));
    if (!img) { fprintf(stderr, "OOM\n"); return 1; }

    lrt_result err = LRT_RESULT_OK;
    lrt_vk_engine_options opt;
    memset(&opt, 0, sizeof(opt));
    opt.device_index = -1;
    opt.prefer_discrete = 1;
    lrt_vk_engine *e = lrt_vk_engine_create(&opt, &err);
    if (!e) {
        printf("no Vulkan device available (err=%d); cannot render on GPU.\n", (int)err);
        free(img); free(prims); free(memo); free(memo_done);
        if (tc) texcache_free(tc);
        mtlx_free(doc);
        return 0; /* keep GPU-less CI green */
    }
    printf("GPU: %s\n", lrt_vk_engine_device_name(e));

    lrt_vk_shade_scene *scene = lrt_vk_shade_scene_build(e, prims, n, &err);
    if (!scene || lrt_vk_shade_scene_render(e, scene, &desc, img, &err) != 0) {
        fprintf(stderr, "GPU render failed: %s\n", lrt_vk_engine_last_error(e));
        if (scene) lrt_vk_shade_scene_free(e, scene);
        lrt_vk_engine_destroy(e);
        return 1;
    }
    lrt_vk_shade_scene_free(e, scene);
    lrt_vk_engine_destroy(e);

    if (!write_ppm(out_path, img, w, h)) {
        fprintf(stderr, "failed to write %s\n", out_path);
        return 1;
    }
    printf("wrote %s (%ux%u, %u spheres, spp=%u)\n", out_path, w, h, n, spp);

    free(img); free(prims); free(memo); free(memo_done);
    if (tc) texcache_free(tc);
    mtlx_free(doc);
    return 0;
}
