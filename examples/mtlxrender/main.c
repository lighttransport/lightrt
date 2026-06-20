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
#include "obj_load.h"
#include "mtlx_doc.h"
#include "mtlx_eval.h"
#include "material_bind.h"
#include "texture.h"
#include "env.h"
#include "camera.h"
#include "framebuffer.h"
#include "pathtrace.h"
#include "pathtrace_wf.h"
#include "raytracer.h"
#include "vecmath.h"
#include "exr.h"
#include "stb_image.h"

static int ends_with(const char *s, const char *suf) {
    size_t ls = strlen(s), lf = strlen(suf);
    return ls >= lf && strcmp(s + ls - lf, suf) == 0;
}

/* Load an EXR's R/G/B planes into an interleaved float buffer (malloc'd). */
static float *load_exr_rgb(const char *path, int *W, int *H) {
    exr_image img; memset(&img, 0, sizeof(img));
    if (!EXR_OK(exr_load_from_file(path, NULL, &img)) || img.num_parts < 1) return NULL;
    exr_part *p = &img.parts[0];
    int w = p->width, h = p->height, ci[3] = {-1, -1, -1};
    for (int c = 0; c < p->header.num_channels; c++) {
        const char *nm = p->header.channels[c].name;
        if (!strcmp(nm, "R")) ci[0] = c; else if (!strcmp(nm, "G")) ci[1] = c; else if (!strcmp(nm, "B")) ci[2] = c;
    }
    if (ci[0] < 0) ci[0] = 0;
    if (ci[1] < 0) ci[1] = ci[0];
    if (ci[2] < 0) ci[2] = ci[0];
    size_t npx = (size_t)w * h;
    float *rgb = (float *)malloc(sizeof(float) * npx * 3), *tmp = (float *)malloc(sizeof(float) * npx);
    for (int k = 0; k < 3; k++) {
        exr_convert_pixels(tmp, EXR_PIXEL_FLOAT, p->images[ci[k]], p->header.channels[ci[k]].pixel_type, npx, EXR_CONVERT_RAW);
        for (size_t i = 0; i < npx; i++) rgb[i * 3 + k] = tmp[i];
    }
    free(tmp); exr_image_free(&img);
    *W = w; *H = h;
    return rgb;
}

/* Load an image (EXR or anything stb reads) as interleaved float RGB. */
static float *load_image_rgb(const char *path, int *W, int *H) {
    if (ends_with(path, ".exr")) return load_exr_rgb(path, W, H);
    int comp;
    unsigned char *p = stbi_load(path, W, H, &comp, 3);
    if (!p) return NULL;
    size_t n = (size_t)(*W) * (*H) * 3;
    float *f = (float *)malloc(sizeof(float) * n);
    for (size_t i = 0; i < n; i++) f[i] = p[i] / 255.0f;
    stbi_image_free(p);
    return f;
}

/* Compare two images (EXR or PNG); print RMSE/max, return 0 if within tol. */
static int diff_exr(const char *a_path, const char *b_path, float tol) {
    int aw, ah, bw, bh;
    float *a = load_image_rgb(a_path, &aw, &ah), *b = load_image_rgb(b_path, &bw, &bh);
    if (!a || !b) { fprintf(stderr, "diff: failed to load EXRs\n"); free(a); free(b); return 2; }
    if (aw != bw || ah != bh) { fprintf(stderr, "diff: size mismatch %dx%d vs %dx%d\n", aw, ah, bw, bh); free(a); free(b); return 2; }
    double se = 0.0; float mx = 0.0f;
    size_t n = (size_t)aw * ah * 3;
    for (size_t i = 0; i < n; i++) { float d = a[i] - b[i]; se += (double)d * d; float ad = fabsf(d); if (ad > mx) mx = ad; }
    float rmse = (float)sqrt(se / n);
    free(a); free(b);
    int ok = rmse <= tol;
    fprintf(stderr, "diff: rmse=%.6f max=%.6f tol=%.6f -> %s\n", rmse, mx, tol, ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

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
        "Usage: %s (--gltf <file.glb> | --obj <file.obj>) --mtlx <file.mtlx> [options]\n"
        "  --obj <file.obj>       load a Wavefront OBJ instead of glTF\n"
        "  --out <file.exr>       output EXR (default chess.exr)\n"
        "  --png <file.png>       also write a tonemapped (ACES) sRGB PNG\n"
        "  --srgb <file.png>      also write a plain linear->sRGB PNG, no tonemap\n"
        "                         (for the verify/ harness; --exposure scales it)\n"
        "  --w <int> --h <int>    image size (default 800x600)\n"
        "  --spp <int>            samples per pixel (default 64)\n"
        "  --bounces <int>        max path length (default 8)\n"
        "  --threads <int>        worker threads (default: all cores)\n"
        "  --env <file.exr>       lat-long HDRI environment\n"
        "  --env-intensity <f>    env scale (default 1)\n"
        "  --env-rotation <deg>   HDRI azimuth rotation (default 0)\n"
        "  --sky                  procedural sky gradient (default: gray dome)\n"
        "  --sun                  add a directional sun (crisp shadows)\n"
        "  --sun-az <deg>         sun azimuth (default 130)\n"
        "  --sun-el <deg>         sun elevation (default 45)\n"
        "  --sun-intensity <f>    sun radiance scale (default 3)\n"
        "  --exposure <f>         PNG tonemap exposure (default 1)\n"
        "  --sss-walk             enable random-walk subsurface scattering\n"
        "  --hq                   high-quality SBVH build\n"
        "  --cam-yaw <deg> --cam-pitch <deg> --cam-dist <f>   orbit camera\n"
        "  --cam-eye x,y,z --cam-target x,y,z --cam-fov <deg>  explicit look-at\n"
        "                         camera (overrides orbit; for the verify harness)\n"
        "  --hide-env             black background; env still lights the scene\n"
        "  --backend <cpu|vk>     cpu = tiled tracer (default); vk = GPU-traced\n"
        "                         wavefront (needs a VK build + device)\n"
        "  --gpu-validate         render the wavefront on CPU and GPU, report RMSE\n",
        prog);
}

int main(int argc, char **argv) {
    /* diff mode: mtlxrender --diff a.exr b.exr [tol] */
    if (argc >= 4 && !strcmp(argv[1], "--diff"))
        return diff_exr(argv[2], argv[3], argc >= 5 ? (float)atof(argv[4]) : 1e-3f);

    const char *gltf_path = NULL, *obj_path = NULL, *mtlx_path = NULL;
    const char *out_path = "chess.exr", *png_path = NULL, *env_path = NULL;
    const char *srgb_path = NULL; /* plain linear->sRGB PNG (no ACES) for verify harness */
    int W = 800, H = 600, spp = 64, bounces = 8, threads = 0, hq = 0, sss_walk = 0, sky = 0;
    int hide_env_bg = 0; /* black background, env still lights (for verify harness) */
    float exposure = 1.0f, env_intensity = 1.0f, env_rot = 0.0f;
    float cam_yaw = 35.0f, cam_pitch = 25.0f, cam_dist = 1.6f;
    /* Explicit look-at camera (overrides the orbit camera when --cam-eye is given). */
    int cam_explicit = 0;
    v3 cam_eye = {0, 0, 5}, cam_target = {0, 0, 0};
    float cam_fov = 45.0f;
    int sun_on = 0;
    float sun_az = 130.0f, sun_el = 45.0f, sun_intensity = 3.0f;
    v3 sun_color = {1.0f, 0.95f, 0.85f};
    const char *backend = "cpu"; /* cpu (tiled) | vk (GPU-traced wavefront) */
    int gpu_validate = 0;

    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        #define NEXT (i + 1 < argc ? argv[++i] : "")
        if (!strcmp(a, "--gltf")) gltf_path = NEXT;
        else if (!strcmp(a, "--obj")) obj_path = NEXT;
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
        else if (!strcmp(a, "--sun")) sun_on = 1;
        else if (!strcmp(a, "--sun-az")) sun_az = (float)atof(NEXT);
        else if (!strcmp(a, "--sun-el")) sun_el = (float)atof(NEXT);
        else if (!strcmp(a, "--sun-intensity")) sun_intensity = (float)atof(NEXT);
        else if (!strcmp(a, "--exposure")) exposure = (float)atof(NEXT);
        else if (!strcmp(a, "--sss-walk")) sss_walk = 1;
        else if (!strcmp(a, "--hq")) hq = 1;
        else if (!strcmp(a, "--cam-yaw")) cam_yaw = (float)atof(NEXT);
        else if (!strcmp(a, "--cam-pitch")) cam_pitch = (float)atof(NEXT);
        else if (!strcmp(a, "--cam-dist")) cam_dist = (float)atof(NEXT);
        else if (!strcmp(a, "--cam-eye")) {
            sscanf(NEXT, "%f,%f,%f", &cam_eye.x, &cam_eye.y, &cam_eye.z); cam_explicit = 1;
        }
        else if (!strcmp(a, "--cam-target")) {
            sscanf(NEXT, "%f,%f,%f", &cam_target.x, &cam_target.y, &cam_target.z);
        }
        else if (!strcmp(a, "--cam-fov")) cam_fov = (float)atof(NEXT);
        else if (!strcmp(a, "--srgb")) srgb_path = NEXT;
        else if (!strcmp(a, "--hide-env")) hide_env_bg = 1;
        else if (!strcmp(a, "--backend")) backend = NEXT;
        else if (!strcmp(a, "--gpu-validate")) gpu_validate = 1;
        else if (!strcmp(a, "-h") || !strcmp(a, "--help")) { usage(argv[0]); return 0; }
        else { fprintf(stderr, "unknown option '%s'\n", a); usage(argv[0]); return 1; }
        #undef NEXT
    }
    if ((!gltf_path && !obj_path) || !mtlx_path) { usage(argv[0]); return 1; }

    /* ---- load geometry (glTF or Wavefront OBJ) ---- */
    Scene scene;
    if (obj_path) {
        if (scene_load_obj(obj_path, &scene, hq)) return 1;
    } else {
        if (scene_load_gltf(gltf_path, &scene, hq)) return 1;
    }

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

    /* ---- camera: explicit look-at (--cam-eye) or orbit around scene center ---- */
    Camera cam;
    if (cam_explicit) {
        cam = camera_lookat(cam_eye, cam_target, v3_make(0, 1, 0),
                            cam_fov * (MTLX_PI / 180.0f), (float)W / (float)H);
    } else {
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
        cam = camera_lookat(eye, center, v3_make(0, 1, 0),
                            cam_fov * (MTLX_PI / 180.0f), (float)W / (float)H);
    }

    /* ---- render ---- */
    RenderConfig cfg;
    memset(&cfg, 0, sizeof(cfg));
    cfg.width = W; cfg.height = H; cfg.spp = spp; cfg.max_bounces = bounces;
    cfg.nthreads = threads > 0 ? threads : (int)cpu_count();
    cfg.sss_walk = sss_walk; cfg.seed = 12345u;
    cfg.hide_env_bg = hide_env_bg;

    /* directional sun from azimuth/elevation (degrees) */
    cfg.sun.enabled = sun_on;
    if (sun_on) {
        float az = sun_az * (MTLX_PI / 180.0f), el = sun_el * (MTLX_PI / 180.0f);
        cfg.sun.dir = v3_normalize(v3_make(cosf(el) * sinf(az), sinf(el), cosf(el) * cosf(az)));
        cfg.sun.radiance = v3_scale(sun_color, sun_intensity);
    }

    fprintf(stderr, "render %dx%d spp=%d bounces=%d threads=%d backend=%s\n",
            W, H, spp, bounces, cfg.nthreads, gpu_validate ? "gpu-validate" : backend);

    Framebuffer fb;
    fb_init(&fb, W, H);

    if (gpu_validate) {
        /* Same wavefront integrator, CPU vs GPU ray backend -> compare RMSE. */
#ifdef MTLX_HAVE_VK
        RayTracer *rt_vk = rt_vk_create(&scene);
        if (!rt_vk) {
            fprintf(stderr, "gpu-validate: no Vulkan device available\n");
            fb_free(&fb); goto teardown;
        }
        fprintf(stderr, "gpu-validate: GPU = %s\n", rt_name(rt_vk));
        Framebuffer fb_cpu; fb_init(&fb_cpu, W, H);
        RayTracer *rt_cpu = rt_cpu_create(&scene);
        render_wavefront(&scene, doc, &bind, tex, env, &cam, &cfg, &fb_cpu, rt_cpu);
        render_wavefront(&scene, doc, &bind, tex, env, &cam, &cfg, &fb, rt_vk);
        rt_destroy(rt_cpu); rt_destroy(rt_vk);
        double se = 0.0, maxd = 0.0; size_t np = (size_t)W * H;
        for (size_t i = 0; i < np; i++) {
            v3 a = v3_scale(fb_cpu.accum[i], 1.0f / (float)spp);
            v3 b = v3_scale(fb.accum[i], 1.0f / (float)spp);
            float d[3] = {a.x - b.x, a.y - b.y, a.z - b.z};
            for (int c = 0; c < 3; c++) { se += (double)d[c] * d[c]; if (fabs(d[c]) > maxd) maxd = fabs(d[c]); }
        }
        double rmse = sqrt(se / (double)(np * 3));
        fprintf(stderr, "gpu-validate: CPU vs GPU wavefront RMSE=%.6f maxdiff=%.6f\n", rmse, maxd);
        fb_free(&fb_cpu);
#else
        fprintf(stderr, "gpu-validate: this binary was built without Vulkan (use VK=1)\n");
        fb_free(&fb); goto teardown;
#endif
    } else if (!strcmp(backend, "vk")) {
#ifdef MTLX_HAVE_VK
        RayTracer *rt = rt_vk_create(&scene);
        if (rt) {
            fprintf(stderr, "backend vk: GPU = %s\n", rt_name(rt));
            render_wavefront(&scene, doc, &bind, tex, env, &cam, &cfg, &fb, rt);
            rt_destroy(rt);
        } else {
            fprintf(stderr, "backend vk: no Vulkan device; falling back to CPU\n");
            render(&scene, doc, &bind, tex, env, &cam, &cfg, &fb);
        }
#else
        fprintf(stderr, "backend vk: built without Vulkan (use VK=1); using CPU\n");
        render(&scene, doc, &bind, tex, env, &cam, &cfg, &fb);
#endif
    } else {
        render(&scene, doc, &bind, tex, env, &cam, &cfg, &fb);
    }

    fb_write_exr(&fb, out_path);
    if (png_path) fb_write_png(&fb, png_path, TONEMAP_ACES, exposure);
    if (srgb_path) fb_write_png_srgb(&fb, srgb_path, exposure);
    fb_free(&fb);

teardown:
    env_free(env);
    texcache_free(tex);
    material_binding_free(&bind);
    mtlx_free(doc);
    scene_free(&scene);
    return 0;
}
