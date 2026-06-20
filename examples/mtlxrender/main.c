/*
 * mtlxrender - a tiny C11 MaterialX path tracer.
 *
 * Loads a (binary) glTF mesh + a MaterialX document, binds materials to
 * geometry by name, and path-traces with an OpenPBR-style BSDF, writing an
 * HDR EXR (and an optional tonemapped PNG preview).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "gltf_load.h"
#include "mtlx_doc.h"
#include "mtlx_eval.h"
#include "material_bind.h"
#include "texture.h"
#include "env.h"
#include "camera.h"
#include "framebuffer.h"
#include "pathtrace.h"
#include "vecmath.h"

static void dirname_of(const char *path, char *out, size_t cap) {
    const char *slash = strrchr(path, '/');
    if (!slash) { snprintf(out, cap, "."); return; }
    size_t n = (size_t)(slash - path);
    if (n >= cap) n = cap - 1;
    memcpy(out, path, n);
    out[n] = '\0';
}

static long cpu_count(void) {
#ifdef _SC_NPROCESSORS_ONLN
    long n = sysconf(_SC_NPROCESSORS_ONLN);
    return n > 0 ? n : 4;
#else
    return 4;
#endif
}

static void usage(const char *prog) {
    fprintf(stderr,
        "Usage: %s --gltf <file.glb> --mtlx <file.mtlx> [options]\n"
        "  --out <file.exr>       output EXR (default chess.exr)\n"
        "  --png <file.png>       also write a tonemapped sRGB PNG\n"
        "  --w <int> --h <int>    image size (default 800x600)\n"
        "  --spp <int>            samples per pixel (default 64)\n"
        "  --bounces <int>        max path length (default 8)\n"
        "  --threads <int>        worker threads (default: all cores)\n"
        "  --env <file.exr>       lat-long HDRI environment\n"
        "  --env-intensity <f>    env scale (default 1)\n"
        "  --env-rotation <deg>   HDRI azimuth rotation (default 0)\n"
        "  --sky                  procedural sky gradient (default: gray dome)\n"
        "  --exposure <f>         PNG tonemap exposure (default 1)\n"
        "  --sss-walk             enable random-walk subsurface scattering\n"
        "  --hq                   high-quality SBVH build\n"
        "  --cam-yaw <deg> --cam-pitch <deg> --cam-dist <f>   orbit camera\n",
        prog);
}

int main(int argc, char **argv) {
    const char *gltf_path = NULL, *mtlx_path = NULL;
    const char *out_path = "chess.exr", *png_path = NULL, *env_path = NULL;
    int W = 800, H = 600, spp = 64, bounces = 8, threads = 0, hq = 0, sss_walk = 0, sky = 0;
    float exposure = 1.0f, env_intensity = 1.0f, env_rot = 0.0f;
    float cam_yaw = 35.0f, cam_pitch = 25.0f, cam_dist = 1.6f;

    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        #define NEXT (i + 1 < argc ? argv[++i] : "")
        if (!strcmp(a, "--gltf")) gltf_path = NEXT;
        else if (!strcmp(a, "--mtlx")) mtlx_path = NEXT;
        else if (!strcmp(a, "--out")) out_path = NEXT;
        else if (!strcmp(a, "--png")) png_path = NEXT;
        else if (!strcmp(a, "--w")) W = atoi(NEXT);
        else if (!strcmp(a, "--h")) H = atoi(NEXT);
        else if (!strcmp(a, "--spp")) spp = atoi(NEXT);
        else if (!strcmp(a, "--bounces")) bounces = atoi(NEXT);
        else if (!strcmp(a, "--threads")) threads = atoi(NEXT);
        else if (!strcmp(a, "--env")) env_path = NEXT;
        else if (!strcmp(a, "--env-intensity")) env_intensity = (float)atof(NEXT);
        else if (!strcmp(a, "--env-rotation")) env_rot = (float)atof(NEXT);
        else if (!strcmp(a, "--sky")) sky = 1;
        else if (!strcmp(a, "--exposure")) exposure = (float)atof(NEXT);
        else if (!strcmp(a, "--sss-walk")) sss_walk = 1;
        else if (!strcmp(a, "--hq")) hq = 1;
        else if (!strcmp(a, "--cam-yaw")) cam_yaw = (float)atof(NEXT);
        else if (!strcmp(a, "--cam-pitch")) cam_pitch = (float)atof(NEXT);
        else if (!strcmp(a, "--cam-dist")) cam_dist = (float)atof(NEXT);
        else if (!strcmp(a, "-h") || !strcmp(a, "--help")) { usage(argv[0]); return 0; }
        else { fprintf(stderr, "unknown option '%s'\n", a); usage(argv[0]); return 1; }
        #undef NEXT
    }
    if (!gltf_path || !mtlx_path) { usage(argv[0]); return 1; }

    /* ---- load geometry ---- */
    Scene scene;
    if (scene_load_gltf(gltf_path, &scene, hq)) return 1;

    /* ---- load + bind materials ---- */
    MtlxDoc *doc = mtlx_load(mtlx_path);
    if (!doc) { fprintf(stderr, "failed to load mtlx\n"); scene_free(&scene); return 1; }
    MaterialBinding bind = material_bind(&scene, doc);

    char base_dir[1024];
    dirname_of(mtlx_path, base_dir, sizeof(base_dir));
    TextureCache *tex = texcache_create(base_dir);
    texcache_preload(tex, doc); /* load + freeze: render-time access is read-only */

    /* ---- environment ---- */
    Env *env = NULL;
    if (env_path) env = env_hdri(env_path, env_intensity, env_rot);
    if (!env) {
        if (sky) env = env_gradient(v3_make(0.18f, 0.16f, 0.14f), v3_make(0.5f, 0.7f, 1.0f), env_intensity);
        else env = env_constant(v3_scale(v3_splat(1.0f), env_intensity));
    }

    /* ---- camera: orbit around scene center ---- */
    v3 center = v3_make(0.5f * (scene.bmin[0] + scene.bmax[0]),
                        0.5f * (scene.bmin[1] + scene.bmax[1]),
                        0.5f * (scene.bmin[2] + scene.bmax[2]));
    float radius = 0.5f * v3_len(v3_make(scene.bmax[0] - scene.bmin[0],
                                         scene.bmax[1] - scene.bmin[1],
                                         scene.bmax[2] - scene.bmin[2]));
    float yaw = cam_yaw * (MTLX_PI / 180.0f), pitch = cam_pitch * (MTLX_PI / 180.0f);
    float d = radius * 2.0f * cam_dist;
    v3 eye = v3_add(center, v3_make(d * cosf(pitch) * sinf(yaw),
                                    d * sinf(pitch),
                                    d * cosf(pitch) * cosf(yaw)));
    Camera cam = camera_lookat(eye, center, v3_make(0, 1, 0),
                               45.0f * (MTLX_PI / 180.0f), (float)W / (float)H);

    /* ---- render ---- */
    RenderConfig cfg;
    memset(&cfg, 0, sizeof(cfg));
    cfg.width = W; cfg.height = H; cfg.spp = spp; cfg.max_bounces = bounces;
    cfg.nthreads = threads > 0 ? threads : (int)cpu_count();
    cfg.sss_walk = sss_walk; cfg.seed = 12345u;

    fprintf(stderr, "render %dx%d spp=%d bounces=%d threads=%d\n",
            W, H, spp, bounces, cfg.nthreads);

    Framebuffer fb;
    fb_init(&fb, W, H);
    render(&scene, doc, &bind, tex, env, &cam, &cfg, &fb);

    fb_write_exr(&fb, out_path);
    if (png_path) fb_write_png(&fb, png_path, TONEMAP_ACES, exposure);

    fb_free(&fb);
    env_free(env);
    texcache_free(tex);
    material_binding_free(&bind);
    mtlx_free(doc);
    scene_free(&scene);
    return 0;
}
