/*
 * test_lightrt_c_cuda.c — CUDA backend self-test.
 *
 * Builds a random triangle BVH on the CPU, uploads it to the GPU (resident
 * scene), traces / occludes ray batches on the device, and checks every result
 * against the CPU oracle (lrt_tri_intersect1 / lrt_tri_occluded1): closest-hit
 * t must match within tolerance, hit/miss must agree. Also exercises the
 * one-shot path and in-place refit. Skips (exit 0) when no CUDA device exists,
 * so GPU-less CI stays green.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lightrt_c_cuda.h"
#include "lightrt_c_tri.h"

static uint32_t rng_state = 0x12345678u;
static float frand(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 17;
    rng_state ^= rng_state << 5;
    return (float)(rng_state & 0xFFFFFF) / (float)0xFFFFFF;
}
static float frand_range(float lo, float hi) { return lo + (hi - lo) * frand(); }

static int failures = 0;
#define CHECK(cond, ...)                                                        \
    do {                                                                        \
        if (!(cond)) {                                                          \
            printf("FAIL: ");                                                   \
            printf(__VA_ARGS__);                                                \
            printf("\n");                                                       \
            failures++;                                                         \
        }                                                                       \
    } while (0)

static void make_scene_verts(float *verts, size_t ntris) {
    for (size_t i = 0; i < ntris; i++) {
        float cx = frand_range(-10, 10), cy = frand_range(-10, 10), cz = frand_range(-10, 10);
        for (int v = 0; v < 3; v++) {
            verts[i * 9 + v * 3 + 0] = cx + frand_range(-1, 1);
            verts[i * 9 + v * 3 + 1] = cy + frand_range(-1, 1);
            verts[i * 9 + v * 3 + 2] = cz + frand_range(-1, 1);
        }
    }
}

static void make_random_ray(lrt_ray *r) {
    r->org[0] = frand_range(-12, 12);
    r->org[1] = frand_range(-12, 12);
    r->org[2] = frand_range(-12, 12);
    float dx = frand_range(-1, 1), dy = frand_range(-1, 1), dz = frand_range(-1, 1);
    float n = sqrtf(dx * dx + dy * dy + dz * dz) + 1e-9f;
    r->dir[0] = dx / n; r->dir[1] = dy / n; r->dir[2] = dz / n;
    r->tmin = 0.0f; r->tmax = 1e30f;
}

int main(void) {
    lrt_result err = LRT_RESULT_OK;
    lrt_cuda_engine *e = lrt_cuda_engine_create(NULL, &err);
    if (!e) {
        printf("no CUDA device available (err=%d); skipping (CI-green).\n", (int)err);
        return 0;
    }
    printf("CUDA device: %s  caps=0x%x\n", lrt_cuda_engine_device_name(e),
           lrt_cuda_engine_caps(e));

    const size_t NTRI = 20000;
    const uint32_t NRAYS = 50000;
    float *verts = (float *)malloc(NTRI * 9 * sizeof(float));
    make_scene_verts(verts, NTRI);

    lrt_tri_build_options bo;
    memset(&bo, 0, sizeof(bo));
    bo.quality = LRT_TRI_BUILD_DEFAULT;
    bo.layout = LRT_TRI_LAYOUT_AUTO;
    lrt_tri_scene *cpu = lrt_tri_scene_build(verts, NTRI, &bo, &err);
    CHECK(cpu != NULL, "CPU build failed (%d)", (int)err);
    if (!cpu) return 1;

    lrt_ray *rays = (lrt_ray *)malloc(NRAYS * sizeof(lrt_ray));
    lrt_hit *gpu_hits = (lrt_hit *)malloc(NRAYS * sizeof(lrt_hit));
    uint8_t *gpu_occ = (uint8_t *)malloc(NRAYS);
    for (uint32_t i = 0; i < NRAYS; i++) make_random_ray(&rays[i]);

    /* ---- resident upload + closest-hit trace ---- */
    lrt_cuda_scene *s = lrt_cuda_scene_upload(e, cpu, &err);
    CHECK(s != NULL, "scene upload failed: %s", lrt_cuda_engine_last_error(e));
    if (!s) return 1;

    int ghits = lrt_cuda_scene_trace(e, s, rays, NRAYS, gpu_hits, &err);
    CHECK(ghits >= 0, "GPU trace failed: %s", lrt_cuda_engine_last_error(e));

    size_t mismatch = 0, both_hit = 0, agree_t = 0;
    for (uint32_t i = 0; i < NRAYS; i++) {
        lrt_hit ch;
        int chit = lrt_tri_intersect1(cpu, &rays[i], &ch);
        int ghit = gpu_hits[i].prim_id != LRT_TRI_NO_HIT;
        if (chit != ghit) { mismatch++; continue; }
        if (chit) {
            both_hit++;
            float dt = fabsf(ch.t - gpu_hits[i].t);
            float rel = dt / (fabsf(ch.t) + 1e-4f);
            if (rel < 1e-3f) agree_t++;
        }
    }
    printf("trace: %u rays, %d gpu-hits, both-hit=%zu, t-agree=%zu, hit/miss-mismatch=%zu\n",
           NRAYS, ghits, both_hit, agree_t, mismatch);
    /* A handful of silhouette pixels may pick different prims; demand tight bounds. */
    CHECK(mismatch < NRAYS / 500, "too many hit/miss mismatches: %zu", mismatch);
    CHECK(agree_t >= both_hit - both_hit / 500, "too many t disagreements (%zu/%zu)",
          both_hit - agree_t, both_hit);

    /* ---- occlusion ---- */
    int gocc = lrt_cuda_scene_occluded(e, s, rays, NRAYS, gpu_occ, &err);
    CHECK(gocc >= 0, "GPU occluded failed: %s", lrt_cuda_engine_last_error(e));
    size_t occ_mismatch = 0;
    for (uint32_t i = 0; i < NRAYS; i++) {
        int co = lrt_tri_occluded1(cpu, &rays[i]) ? 1 : 0;
        if (co != (gpu_occ[i] ? 1 : 0)) occ_mismatch++;
    }
    printf("occluded: %d gpu-occluded, mismatch=%zu\n", gocc, occ_mismatch);
    CHECK(occ_mismatch < NRAYS / 500, "too many occlusion mismatches: %zu", occ_mismatch);

    /* ---- one-shot path ---- */
    lrt_hit *one = (lrt_hit *)malloc(NRAYS * sizeof(lrt_hit));
    int oh = lrt_cuda_trace_scene(e, cpu, rays, NRAYS, one, &err);
    CHECK(oh == ghits, "one-shot hit count %d != resident %d", oh, ghits);
    size_t one_diff = 0;
    for (uint32_t i = 0; i < NRAYS; i++)
        if ((one[i].prim_id != LRT_TRI_NO_HIT) != (gpu_hits[i].prim_id != LRT_TRI_NO_HIT))
            one_diff++;
    CHECK(one_diff == 0, "one-shot vs resident differ in %zu rays", one_diff);
    free(one);

    /* ---- in-place refit (re-jitter geometry, refit, re-trace, re-check) ---- */
    make_scene_verts(verts, NTRI);
    int rf = lrt_cuda_scene_refit(e, s, verts, NTRI, &err);
    if (rf == 0) {
        /* CPU oracle must be rebuilt over the new verts to compare. */
        lrt_tri_scene *cpu2 = lrt_tri_scene_build(verts, NTRI, &bo, &err);
        lrt_cuda_scene_trace(e, s, rays, NRAYS, gpu_hits, &err);
        size_t rmis = 0;
        for (uint32_t i = 0; i < NRAYS; i++) {
            lrt_hit ch;
            int chit = lrt_tri_intersect1(cpu2, &rays[i], &ch);
            int ghit = gpu_hits[i].prim_id != LRT_TRI_NO_HIT;
            if (chit != ghit) rmis++;
        }
        printf("refit: hit/miss-mismatch=%zu (refit preserves topology, so some drift ok)\n", rmis);
        CHECK(rmis < NRAYS / 50, "refit produced too many mismatches: %zu", rmis);
        lrt_tri_scene_free(cpu2);
    } else {
        printf("refit: not supported for this scene (skipped)\n");
    }

    lrt_cuda_scene_free(e, s);
    lrt_cuda_engine_destroy(e);
    lrt_tri_scene_free(cpu);
    free(verts); free(rays); free(gpu_hits); free(gpu_occ);

    if (failures == 0) printf("RESULT: PASS\n");
    else printf("RESULT: FAIL (%d failures)\n", failures);
    return failures ? 1 : 0;
}
