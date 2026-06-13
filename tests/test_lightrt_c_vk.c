/*
 * test_lightrt_c_vk.c — correctness test for the Vulkan GPU interop.
 *
 * Path A (CPU build -> GPU trace): GPU hits must agree with the CPU kernel
 *   lrt_tri_intersect1 (itself validated against brute force in
 *   test_lightrt_c_tri.c) — hit/miss must match, and on a mutual hit the ray
 *   parameter t must match within 1e-3 relative (prim_id is NOT compared, to
 *   tolerate ties between (near-)equidistant triangles).
 *
 * Path B (GPU build -> CPU trace): a GPU-built scene must agree with a CPU FAST
 *   build under CPU traversal, same tolerance rule.
 *
 * Both BVH4 and BVH8 are exercised. The test SKIPS (exit 0) when no Vulkan
 * device is available, so GPU-less CI stays green.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lightrt_c_tri.h"
#include "lightrt_c_vk.h"

static uint64_t g_rng = 0x9e3779b97f4a7c15ULL;
static uint32_t rnd_u32(void) {
    g_rng ^= g_rng << 13;
    g_rng ^= g_rng >> 7;
    g_rng ^= g_rng << 17;
    return (uint32_t)(g_rng >> 16);
}
static float rnd_f(float lo, float hi) {
    return lo + (hi - lo) * ((float)(rnd_u32() & 0xFFFFFF) / (float)0x1000000);
}

static int g_fail = 0;
#define CHECK(cond, ...)                       \
    do {                                       \
        if (!(cond)) {                         \
            printf("FAIL: ");                  \
            printf(__VA_ARGS__);               \
            printf("\n");                      \
            g_fail = 1;                        \
        }                                      \
    } while (0)

/* Random triangle soup: small triangles scattered in a cube. */
static float *make_random_soup(size_t ntris) {
    float *v = (float *)malloc(ntris * 9 * sizeof(float));
    for (size_t i = 0; i < ntris; i++) {
        float c[3] = {rnd_f(-3, 3), rnd_f(-3, 3), rnd_f(-3, 3)};
        for (int j = 0; j < 9; j++) v[i * 9 + j] = c[j % 3] + rnd_f(-0.25f, 0.25f);
    }
    return v;
}

static void make_random_ray(lrt_ray *r) {
    r->org[0] = rnd_f(-4, 4);
    r->org[1] = rnd_f(-4, 4);
    r->org[2] = -6.0f;
    r->dir[0] = rnd_f(-0.5f, 0.5f);
    r->dir[1] = rnd_f(-0.5f, 0.5f);
    r->dir[2] = 1.0f;
    /* Occasionally zero a direction component to exercise the invd clamp. */
    if ((rnd_u32() & 7u) == 0u) r->dir[rnd_u32() % 3u] = 0.0f;
    r->tmin = 0.0f;
    r->tmax = 1e30f;
}

/* Compare two hits with the test_lightrt_c_tri tolerance rule. Returns 1 on a
 * tolerated match, 0 on a real mismatch. */
static int hit_matches(int a_hit, const lrt_hit *a, int b_hit, const lrt_hit *b) {
    if (a_hit != b_hit) return 0;
    if (!a_hit) return 1;
    float dt = fabsf(a->t - b->t);
    return dt <= 1e-3f * (1.0f + fabsf(b->t));
}

/* Path A: trace `nrays` rays through a CPU-built scene of layout `layout` on the
 * GPU, compare to lrt_tri_intersect1. */
static void test_path_a(lrt_vk_engine *e, const float *v, size_t ntris,
                        lrt_tri_layout layout, size_t nrays, const char *label) {
    lrt_result err;
    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.quality = LRT_TRI_BUILD_DEFAULT;
    o.layout = layout;
    lrt_tri_scene *s = lrt_tri_scene_build(v, ntris, &o, &err);
    CHECK(s != NULL, "[%s] CPU build failed", label);
    if (!s) return;

    lrt_ray *rays = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_hit *gh = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    for (size_t i = 0; i < nrays; i++) make_random_ray(&rays[i]);

    int hits = lrt_vk_trace_scene(e, s, rays, (uint32_t)nrays, gh, &err);
    CHECK(hits >= 0, "[%s] GPU trace failed: %s", label,
          lrt_vk_engine_last_error(e));
    if (hits < 0) {
        free(rays);
        free(gh);
        lrt_tri_scene_free(s);
        return;
    }

    int mism = 0;
    for (size_t i = 0; i < nrays; i++) {
        lrt_hit ch;
        int ch_hit = lrt_tri_intersect1(s, &rays[i], &ch);
        int gh_hit = gh[i].prim_id != LRT_TRI_NO_HIT;
        if (!hit_matches(gh_hit, &gh[i], ch_hit, &ch)) mism++;
    }
    CHECK(mism == 0, "[%s] Path A: %d/%zu rays mismatch GPU vs CPU", label, mism,
          nrays);
    printf("  [%s] Path A ok: %d mismatches over %zu rays (%d GPU hits)\n",
           label, mism, nrays, hits);

    free(rays);
    free(gh);
    lrt_tri_scene_free(s);
}

/* Path B: build on GPU, trace on CPU, compare to a CPU FAST build. */
static void test_path_b(lrt_vk_engine *e, const float *v, size_t ntris,
                        lrt_tri_layout layout, size_t nrays, const char *label) {
    lrt_result err;
    lrt_tri_scene *gpu = NULL;
    int br = lrt_vk_build_scene(e, v, (uint32_t)ntris, layout, &gpu, &err);
    CHECK(br == 0 && gpu != NULL, "[%s] Path B build failed: %s", label,
          lrt_vk_engine_last_error(e));
    if (br != 0 || !gpu) return;

    lrt_tri_build_options o;
    memset(&o, 0, sizeof(o));
    o.quality = LRT_TRI_BUILD_FAST;
    o.layout = layout;
    lrt_tri_scene *cpu = lrt_tri_scene_build(v, ntris, &o, &err);
    CHECK(cpu != NULL, "[%s] CPU FAST build failed", label);

    int mism = 0;
    if (cpu) {
        for (size_t i = 0; i < nrays; i++) {
            lrt_ray r;
            make_random_ray(&r);
            lrt_hit a, b;
            int ah = lrt_tri_intersect1(gpu, &r, &a);
            int bh = lrt_tri_intersect1(cpu, &r, &b);
            if (!hit_matches(ah, &a, bh, &b)) mism++;
        }
        CHECK(mism == 0, "[%s] Path B: %d/%zu rays mismatch GPU-built vs CPU-FAST",
              label, mism, nrays);
        printf("  [%s] Path B ok: %d mismatches over %zu rays\n", label, mism,
               nrays);
        lrt_tri_scene_free(cpu);
    }
    lrt_tri_scene_free(gpu);
}

int main(void) {
    lrt_result err;
    lrt_vk_engine_options eo;
    memset(&eo, 0, sizeof(eo));
    eo.device_index = -1;
    eo.prefer_discrete = 1;
    eo.want_ray_tracing = 1;

    lrt_vk_engine *e = lrt_vk_engine_create(&eo, &err);
    if (!e) {
        printf("SKIP: no Vulkan device (libvulkan/loader/device unavailable)\n");
        return 0; /* keep GPU-less CI green */
    }
    printf("Vulkan device: %s (caps=0x%x)\n", lrt_vk_engine_device_name(e),
           lrt_vk_engine_caps(e));

    const size_t ntris = 4000, nrays = 8000;
    float *v = make_random_soup(ntris);

    test_path_a(e, v, ntris, LRT_TRI_LAYOUT_BVH8, nrays, "BVH8");
    test_path_a(e, v, ntris, LRT_TRI_LAYOUT_BVH4, nrays, "BVH4");
    test_path_b(e, v, ntris, LRT_TRI_LAYOUT_BVH8, nrays, "BVH8");
    test_path_b(e, v, ntris, LRT_TRI_LAYOUT_BVH4, nrays, "BVH4");

    free(v);
    lrt_vk_engine_destroy(e);

    if (g_fail) {
        printf("FAILED\n");
        return 1;
    }
    printf("PASSED\n");
    return 0;
}
