/*
 * vk_shade.c — Vulkan compute *shading* demo for analytic spheres & boxes.
 *
 * Builds a tiny scene of analytic spheres and axis-aligned boxes, each carrying
 * a constant OpenPBR-style material (base colour / metalness / roughness — the
 * kind of parameters you would bake per-object from a MaterialX node graph on
 * the CPU), and forward-shades it on the GPU via lrt_vk_shade_analytic().
 *
 * To prove the GPU shading is correct, the SAME shading math is reimplemented
 * here on the CPU (shade_cpu) and the two images are compared (RMSE). The CPU
 * reference and the GLSL shader (vk/shaders/shade_analytic.comp) are kept in
 * lock-step. A tonemapped PPM (P6, zero dependencies) is written for eyeballing.
 *
 * If no Vulkan device/loader is present, the program prints a notice and exits
 * 0 (so GPU-less CI stays green), after still writing the CPU reference image.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "lightrt_c_vk.h"

/* Portable wall-clock seconds (C11 timespec_get; no feature macros needed). */
static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

/* ---- tiny vec3 ----------------------------------------------------------- */
typedef struct { float x, y, z; } v3;
static v3 V(float x, float y, float z) { v3 r = {x, y, z}; return r; }
static v3 add(v3 a, v3 b) { return V(a.x + b.x, a.y + b.y, a.z + b.z); }
static v3 sub(v3 a, v3 b) { return V(a.x - b.x, a.y - b.y, a.z - b.z); }
static v3 mul(v3 a, v3 b) { return V(a.x * b.x, a.y * b.y, a.z * b.z); }
static v3 scl(v3 a, float s) { return V(a.x * s, a.y * s, a.z * s); }
static float dot(v3 a, v3 b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
static v3 nrm(v3 a) { float l = sqrtf(dot(a, a)); return l > 0 ? scl(a, 1.0f / l) : a; }
static v3 neg(v3 a) { return V(-a.x, -a.y, -a.z); }
static v3 lerp3(v3 a, v3 b, float t) { return add(scl(a, 1.0f - t), scl(b, t)); }
static float clampf(float x, float a, float b) { return x < a ? a : (x > b ? b : x); }

#define MPI 3.14159265358979323846f
#define INV_PI 0.31830988618379067154f

/* ---- CPU reference: byte-for-byte mirror of shade_analytic.comp ---------- */
static float hit_sphere(v3 c, float r, v3 o, v3 d, float tmax) {
    v3 oc = sub(o, c);
    float b = dot(oc, d);
    float cc = dot(oc, oc) - r * r;
    float disc = b * b - cc;
    if (disc < 0.0f) return -1.0f;
    float s = sqrtf(disc);
    float t = -b - s;
    if (t < 1e-4f) t = -b + s;
    if (t < 1e-4f || t >= tmax) return -1.0f;
    return t;
}
static float hit_box(v3 c, v3 h, v3 o, v3 d, float tmax, v3 *n) {
    v3 lo = sub(c, h), hi = add(c, h);
    float dd[3] = {d.x, d.y, d.z};
    float tsm[3], tbg[3];
    float oo[3] = {o.x, o.y, o.z}, ll[3] = {lo.x, lo.y, lo.z}, hh[3] = {hi.x, hi.y, hi.z};
    for (int k = 0; k < 3; k++) {
        float invd = 1.0f / dd[k];
        float t0 = (ll[k] - oo[k]) * invd, t1 = (hh[k] - oo[k]) * invd;
        tsm[k] = fminf(t0, t1); tbg[k] = fmaxf(t0, t1);
    }
    int axis = 0; float tnear = tsm[0];
    if (tsm[1] > tnear) { tnear = tsm[1]; axis = 1; }
    if (tsm[2] > tnear) { tnear = tsm[2]; axis = 2; }
    int faxis = 0; float tfar = tbg[0];
    if (tbg[1] < tfar) { tfar = tbg[1]; faxis = 1; }
    if (tbg[2] < tfar) { tfar = tbg[2]; faxis = 2; }
    *n = V(0, 0, 0);
    if (tnear > tfar || tfar < 1e-4f) return -1.0f;
    int use_far = !(tnear > 1e-4f);
    float t = use_far ? tfar : tnear;
    if (t >= tmax) return -1.0f;
    int a = use_far ? faxis : axis;
    float nn[3] = {0, 0, 0};
    nn[a] = dd[a] > 0.0f ? -1.0f : 1.0f;
    *n = V(nn[0], nn[1], nn[2]);
    return t;
}
static int trace_cpu(const lrt_vk_shade_prim *p, uint32_t n, v3 o, v3 d,
                     float tmax, float *bt, v3 *nrm_out) {
    int best = -1;
    *bt = tmax;
    *nrm_out = V(0, 0, 0);
    for (uint32_t i = 0; i < n; i++) {
        v3 c = V(p[i].center[0], p[i].center[1], p[i].center[2]);
        v3 h = V(p[i].half_extent[0], p[i].half_extent[1], p[i].half_extent[2]);
        if (p[i].type < 0.5f) {
            float t = hit_sphere(c, p[i].radius, o, d, *bt);
            if (t > 0.0f) { *bt = t; best = (int)i; *nrm_out = nrm(sub(add(o, scl(d, t)), c)); }
        } else {
            v3 nn;
            float t = hit_box(c, h, o, d, *bt, &nn);
            if (t > 0.0f) { *bt = t; best = (int)i; *nrm_out = nn; }
        }
    }
    return best;
}
static int occluded_cpu(const lrt_vk_shade_prim *p, uint32_t n, v3 o, v3 d, float tmax) {
    for (uint32_t i = 0; i < n; i++) {
        v3 c = V(p[i].center[0], p[i].center[1], p[i].center[2]);
        v3 h = V(p[i].half_extent[0], p[i].half_extent[1], p[i].half_extent[2]);
        if (p[i].type < 0.5f) { if (hit_sphere(c, p[i].radius, o, d, tmax) > 0.0f) return 1; }
        else { v3 nn; if (hit_box(c, h, o, d, tmax, &nn) > 0.0f) return 1; }
    }
    return 0;
}
static v3 fresnel(float ct, v3 f0) {
    float m = clampf(1.0f - ct, 0.0f, 1.0f), m5 = m * m * m * m * m;
    return add(f0, scl(sub(V(1, 1, 1), f0), m5));
}
static float ggx_D(float NoH, float a) {
    if (NoH <= 0.0f) return 0.0f;
    float a2 = a * a, dd = NoH * NoH * (a2 - 1.0f) + 1.0f;
    return a2 / (MPI * dd * dd);
}
static float ggx_G1(float NoX, float a) {
    if (NoX <= 0.0f) return 0.0f;
    float a2 = a * a, t = NoX * NoX;
    return 2.0f * NoX / (NoX + sqrtf(a2 + (1.0f - a2) * t));
}
static v3 bsdf_eval(const lrt_vk_shade_prim *m, v3 N, v3 wo, v3 wi) {
    float NoL = dot(N, wi), NoV = dot(N, wo);
    if (NoL <= 0.0f || NoV <= 0.0f) return V(0, 0, 0);
    v3 base = V(m->base_color[0], m->base_color[1], m->base_color[2]);
    float metal = m->metalness, rough = clampf(m->roughness, 0.02f, 1.0f), a = rough * rough;
    v3 H = nrm(add(wo, wi));
    float NoH = dot(N, H), VoH = dot(wo, H);
    v3 diff = scl(base, (1.0f - metal) * INV_PI);
    float f0d = (m->specular_ior - 1.0f) / (m->specular_ior + 1.0f);
    f0d = f0d * f0d;
    v3 F0 = lerp3(V(f0d, f0d, f0d), base, metal);
    float D = ggx_D(NoH, a), G = ggx_G1(NoV, a) * ggx_G1(NoL, a);
    v3 F = fresnel(VoH, F0);
    v3 spec = scl(F, D * G / (4.0f * NoV * NoL));
    return add(diff, spec);
}
static v3 env_eval(const lrt_vk_shade_desc *d, v3 dir) {
    v3 top = V(d->env_top[0], d->env_top[1], d->env_top[2]);
    v3 bot = V(d->env_bottom[0], d->env_bottom[1], d->env_bottom[2]);
    return lerp3(bot, top, clampf(dir.y * 0.5f + 0.5f, 0.0f, 1.0f));
}
static v3 reflect3(v3 i, v3 n) { return sub(i, scl(n, 2.0f * dot(i, n))); }
static v3 spec_f0(const lrt_vk_shade_prim *m) {
    v3 base = V(m->base_color[0], m->base_color[1], m->base_color[2]);
    float f0d = (m->specular_ior - 1.0f) / (m->specular_ior + 1.0f);
    f0d = f0d * f0d;
    return lerp3(V(f0d, f0d, f0d), base, m->metalness);
}
/* Ambient env: (1-F)-weighted diffuse irradiance + Fresnel specular reflection
 * of the env in the roughness-blurred mirror direction. rd = view ray dir. */
static v3 ambient_env(const lrt_vk_shade_desc *d, const lrt_vk_shade_prim *m,
                      v3 N, v3 wo, v3 rd) {
    float rough = clampf(m->roughness, 0.02f, 1.0f);
    v3 F0 = spec_f0(m);
    v3 Fr = fresnel(fmaxf(dot(N, wo), 0.0f), F0);
    v3 R = reflect3(rd, N);
    v3 Rb = nrm(lerp3(R, N, rough));
    v3 albedo = scl(V(m->base_color[0], m->base_color[1], m->base_color[2]), 1.0f - m->metalness);
    v3 diff = mul(mul(albedo, env_eval(d, N)), sub(V(1, 1, 1), Fr));
    v3 spec = mul(Fr, env_eval(d, Rb));
    return add(diff, spec);
}
static void shade_cpu(const lrt_vk_shade_prim *p, uint32_t n,
                      const lrt_vk_shade_desc *d, float *out) {
    v3 ro = V(d->cam_origin[0], d->cam_origin[1], d->cam_origin[2]);
    v3 fwd = V(d->cam_forward[0], d->cam_forward[1], d->cam_forward[2]);
    v3 rgt = V(d->cam_right[0], d->cam_right[1], d->cam_right[2]);
    v3 up = V(d->cam_up[0], d->cam_up[1], d->cam_up[2]);
    v3 sun = V(d->sun_dir[0], d->sun_dir[1], d->sun_dir[2]);
    v3 srad = V(d->sun_radiance[0], d->sun_radiance[1], d->sun_radiance[2]);
    float th = d->tan_half_fov;
    float asp = d->aspect != 0.0f ? d->aspect : (float)d->width / (float)d->height;
    uint32_t spp = d->spp ? d->spp : 1;
    for (uint32_t py = 0; py < d->height; py++) {
        for (uint32_t px = 0; px < d->width; px++) {
            v3 accum = V(0, 0, 0);
            for (uint32_t s = 0; s < spp; s++) {
                float jx = (spp == 1) ? 0.5f : ((float)s + 0.5f) / (float)spp;
                float jyf = (float)s * 0.61803398875f + 0.5f;
                float jy = (spp == 1) ? 0.5f : (jyf - floorf(jyf));
                float sx = (2.0f * ((float)px + jx) / (float)d->width - 1.0f) * th * asp;
                float sy = (1.0f - 2.0f * ((float)py + jy) / (float)d->height) * th;
                v3 rd = nrm(add(fwd, add(scl(rgt, sx), scl(up, sy))));
                float t;
                v3 N;
                int hit = trace_cpu(p, n, ro, rd, 1e30f, &t, &N);
                if (hit < 0) { accum = add(accum, env_eval(d, rd)); continue; }
                const lrt_vk_shade_prim *m = &p[hit];
                v3 P = add(ro, scl(rd, t));
                v3 wo = neg(rd);
                if (dot(N, wo) < 0.0f) N = neg(N);
                v3 col = V(0, 0, 0);
                if (m->emission > 0.0f)
                    col = add(col, scl(V(m->base_color[0], m->base_color[1], m->base_color[2]), m->emission));
                if (dot(srad, srad) > 0.0f) {
                    float NoL = dot(N, sun);
                    if (NoL > 0.0f && !occluded_cpu(p, n, add(P, scl(N, 1e-3f)), sun, 1e30f)) {
                        v3 f = bsdf_eval(m, N, wo, sun);
                        col = add(col, scl(mul(f, srad), NoL));
                    }
                }
                col = add(col, ambient_env(d, m, N, wo, rd));
                accum = add(accum, col);
            }
            accum = scl(accum, 1.0f / (float)spp);
            size_t o = ((size_t)py * d->width + px) * 4;
            out[o + 0] = accum.x; out[o + 1] = accum.y; out[o + 2] = accum.z; out[o + 3] = 1.0f;
        }
    }
}

/* ---- output ------------------------------------------------------------- */
static int write_ppm(const char *path, const float *rgba, uint32_t w, uint32_t h) {
    FILE *f = fopen(path, "wb");
    if (!f) return 0;
    fprintf(f, "P6\n%u %u\n255\n", w, h);
    for (uint32_t i = 0; i < w * h; i++) {
        for (int c = 0; c < 3; c++) {
            float v = rgba[i * 4 + c];
            v = v / (1.0f + v);                 /* Reinhard tonemap          */
            v = powf(clampf(v, 0.0f, 1.0f), 1.0f / 2.2f); /* gamma           */
            unsigned char b = (unsigned char)(v * 255.0f + 0.5f);
            fputc(b, f);
        }
    }
    fclose(f);
    return 1;
}

/* ---- scene -------------------------------------------------------------- */
static void build_scene(lrt_vk_shade_prim *p, uint32_t *np) {
    uint32_t n = 0;
    /* ground box */
    lrt_vk_shade_prim g; memset(&g, 0, sizeof(g));
    g.type = 1.0f; g.center[0] = 0; g.center[1] = -1.0f; g.center[2] = 0;
    g.half_extent[0] = 6; g.half_extent[1] = 1; g.half_extent[2] = 6;
    g.base_color[0] = 0.6f; g.base_color[1] = 0.6f; g.base_color[2] = 0.62f;
    g.roughness = 0.9f; g.specular_ior = 1.5f; p[n++] = g;

    /* dielectric red sphere */
    lrt_vk_shade_prim s1; memset(&s1, 0, sizeof(s1));
    s1.type = 0.0f; s1.center[0] = -1.4f; s1.center[1] = 0.2f; s1.center[2] = 0; s1.radius = 0.8f;
    s1.base_color[0] = 0.85f; s1.base_color[1] = 0.12f; s1.base_color[2] = 0.1f;
    s1.roughness = 0.35f; s1.specular_ior = 1.5f; p[n++] = s1;

    /* polished gold metal sphere */
    lrt_vk_shade_prim s2; memset(&s2, 0, sizeof(s2));
    s2.type = 0.0f; s2.center[0] = 0.3f; s2.center[1] = 0.3f; s2.center[2] = -0.4f; s2.radius = 0.9f;
    s2.base_color[0] = 1.0f; s2.base_color[1] = 0.78f; s2.base_color[2] = 0.34f;
    s2.metalness = 1.0f; s2.roughness = 0.15f; s2.specular_ior = 1.5f; p[n++] = s2;

    /* rough blue box */
    lrt_vk_shade_prim b1; memset(&b1, 0, sizeof(b1));
    b1.type = 1.0f; b1.center[0] = 1.7f; b1.center[1] = 0.1f; b1.center[2] = 0.3f;
    b1.half_extent[0] = 0.6f; b1.half_extent[1] = 0.7f; b1.half_extent[2] = 0.6f;
    b1.base_color[0] = 0.15f; b1.base_color[1] = 0.3f; b1.base_color[2] = 0.85f;
    b1.roughness = 0.6f; b1.specular_ior = 1.5f; p[n++] = b1;

    /* small emissive sphere */
    lrt_vk_shade_prim e1; memset(&e1, 0, sizeof(e1));
    e1.type = 0.0f; e1.center[0] = -0.2f; e1.center[1] = 1.3f; e1.center[2] = 1.2f; e1.radius = 0.3f;
    e1.base_color[0] = 1.0f; e1.base_color[1] = 0.9f; e1.base_color[2] = 0.6f;
    e1.emission = 6.0f; e1.roughness = 0.5f; e1.specular_ior = 1.5f; p[n++] = e1;

    *np = n;
}

static void build_desc(lrt_vk_shade_desc *d, uint32_t w, uint32_t h, uint32_t spp) {
    memset(d, 0, sizeof(*d));
    d->width = w; d->height = h; d->spp = spp;
    /* camera */
    v3 eye = V(0.0f, 1.6f, 5.0f), target = V(0.0f, 0.2f, 0.0f), up = V(0, 1, 0);
    v3 fwd = nrm(sub(target, eye));
    v3 rgt = nrm(V(fwd.z, 0, -fwd.x)); /* right = normalize(cross(fwd, up)) */
    rgt = nrm(V(fwd.y * up.z - fwd.z * up.y, fwd.z * up.x - fwd.x * up.z, fwd.x * up.y - fwd.y * up.x));
    v3 cup = V(rgt.y * fwd.z - rgt.z * fwd.y, rgt.z * fwd.x - rgt.x * fwd.z, rgt.x * fwd.y - rgt.y * fwd.x);
    d->cam_origin[0] = eye.x; d->cam_origin[1] = eye.y; d->cam_origin[2] = eye.z;
    d->cam_forward[0] = fwd.x; d->cam_forward[1] = fwd.y; d->cam_forward[2] = fwd.z;
    d->cam_right[0] = rgt.x; d->cam_right[1] = rgt.y; d->cam_right[2] = rgt.z;
    d->cam_up[0] = cup.x; d->cam_up[1] = cup.y; d->cam_up[2] = cup.z;
    d->tan_half_fov = tanf(0.5f * 40.0f * MPI / 180.0f);
    d->aspect = (float)w / (float)h;
    /* sun */
    v3 sun = nrm(V(-0.4f, 0.8f, 0.45f));
    d->sun_dir[0] = sun.x; d->sun_dir[1] = sun.y; d->sun_dir[2] = sun.z;
    d->sun_radiance[0] = 3.0f; d->sun_radiance[1] = 2.85f; d->sun_radiance[2] = 2.6f;
    /* env */
    d->env_top[0] = 0.5f; d->env_top[1] = 0.7f; d->env_top[2] = 1.0f;
    d->env_bottom[0] = 0.25f; d->env_bottom[1] = 0.22f; d->env_bottom[2] = 0.2f;
}

int main(int argc, char **argv) {
    uint32_t w = 512, h = 384, spp = 4;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--w") && i + 1 < argc) w = (uint32_t)atoi(argv[++i]);
        else if (!strcmp(argv[i], "--h") && i + 1 < argc) h = (uint32_t)atoi(argv[++i]);
        else if (!strcmp(argv[i], "--spp") && i + 1 < argc) spp = (uint32_t)atoi(argv[++i]);
    }

    lrt_vk_shade_prim prims[8];
    uint32_t nprims = 0;
    build_scene(prims, &nprims);
    lrt_vk_shade_desc desc;
    build_desc(&desc, w, h, spp);

    size_t npix = (size_t)w * h;
    float *cpu = (float *)malloc(npix * 4 * sizeof(float));
    float *gpu = (float *)malloc(npix * 4 * sizeof(float));
    if (!cpu || !gpu) { fprintf(stderr, "OOM\n"); return 1; }

    printf("vk_shade: %ux%u, spp=%u, %u analytic prims\n", w, h, spp, nprims);

    double mpix = (double)npix * 1e-6;

    /* CPU reference (always). */
    double t0 = now_sec();
    shade_cpu(prims, nprims, &desc, cpu);
    double cpu_ms = (now_sec() - t0) * 1e3;
    write_ppm("vk_shade_cpu.ppm", cpu, w, h);
    printf("wrote vk_shade_cpu.ppm (CPU reference, single-threaded)\n");
    printf("CPU shade: %8.2f ms   %6.1f Mpix/s\n", cpu_ms, mpix / (cpu_ms * 1e-3));

    /* GPU shading. */
    lrt_result err = LRT_RESULT_OK;
    lrt_vk_engine_options opt;
    memset(&opt, 0, sizeof(opt));
    opt.device_index = -1;
    opt.prefer_discrete = 1;
    lrt_vk_engine *e = lrt_vk_engine_create(&opt, &err);
    if (!e) {
        printf("no Vulkan device available (err=%d); CPU-only run.\n", (int)err);
        free(cpu); free(gpu);
        return 0; /* keep GPU-less CI green */
    }
    printf("GPU: %s  caps=0x%x\n", lrt_vk_engine_device_name(e), lrt_vk_engine_caps(e));

    /* Warm-up run builds the pipeline + descriptor pool; the timed run then
     * reflects dispatch + buffer upload/readback (this v1 backend re-uploads
     * the scene per call). */
    if (lrt_vk_shade_analytic(e, prims, nprims, &desc, gpu, &err) != 0) {
        fprintf(stderr, "lrt_vk_shade_analytic failed: %s\n", lrt_vk_engine_last_error(e));
        lrt_vk_engine_destroy(e);
        free(cpu); free(gpu);
        return 1;
    }
    t0 = now_sec();
    lrt_vk_shade_analytic(e, prims, nprims, &desc, gpu, &err);
    double gpu_ms = (now_sec() - t0) * 1e3;
    write_ppm("vk_shade_gpu.ppm", gpu, w, h);
    printf("wrote vk_shade_gpu.ppm (GPU)\n");
    printf("GPU shade: %8.2f ms   %6.1f Mpix/s   (%.1fx vs CPU)\n",
           gpu_ms, mpix / (gpu_ms * 1e-3), cpu_ms / gpu_ms);

    /* Compare. Interior pixels must match closely; a small fraction of
     * silhouette/shadow-edge pixels legitimately differ because a sub-sample
     * flips hit/miss between the GLSL and C float paths (sub-ULP divergence in
     * sqrt/normalize). So the pass criterion is: low overall RMSE AND a high
     * fraction of pixels agreeing within a per-channel tolerance. */
    const double PIX_TOL = 0.02;
    double se = 0.0, maxd = 0.0;
    size_t agree = 0;
    for (size_t i = 0; i < npix; i++) {
        double pe = 0.0;
        for (int c = 0; c < 4; c++) {
            double dd = (double)gpu[i * 4 + c] - (double)cpu[i * 4 + c];
            se += dd * dd;
            if (fabs(dd) > maxd) maxd = fabs(dd);
            if (fabs(dd) > pe) pe = fabs(dd);
        }
        if (pe <= PIX_TOL) agree++;
    }
    double rmse = sqrt(se / (double)(npix * 4));
    double frac = (double)agree / (double)npix;
    printf("GPU vs CPU:  RMSE = %.6f   max abs diff = %.6f\n", rmse, maxd);
    printf("             pixels within %.2f: %.3f%% (%zu/%zu)\n",
           PIX_TOL, frac * 100.0, agree, npix);

    int pass = (rmse < 1e-2) && (frac > 0.99);
    printf("%s\n", pass ? "PASS (GPU shading matches CPU reference)"
                        : "FAIL (GPU/CPU mismatch beyond tolerance)");

    lrt_vk_engine_destroy(e);
    free(cpu); free(gpu);
    return pass ? 0 : 1;
}
