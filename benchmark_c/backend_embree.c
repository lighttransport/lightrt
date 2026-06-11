/*
 * backend_embree.c — Embree 4 backend (rtcIntersect1 / rtcOccluded1 per ray).
 * Compiled in only when the build finds an Embree SDK and defines
 * LRTBENCH_HAVE_EMBREE; otherwise backend_embree() returns NULL and the
 * harness reports the backend as unavailable.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stddef.h>

#include "backend.h"

#ifdef LRTBENCH_HAVE_EMBREE

#include <embree4/rtcore.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "timing.h"

typedef struct {
    RTCDevice device;
    RTCScene scene;
} em_scene;

static void em_error_cb(void *user, enum RTCError code, const char *str) {
    (void)user;
    fprintf(stderr, "embree error %d: %s\n", (int)code, str ? str : "");
}

static void em_destroy(void *scene) {
    em_scene *es = (em_scene *)scene;
    if (!es) return;
    if (es->scene) rtcReleaseScene(es->scene);
    if (es->device) rtcReleaseDevice(es->device);
    free(es);
}

static void *em_build(const float *vertices, size_t ntris, int num_threads,
                      double *build_ms) {
    if (build_ms) *build_ms = 0.0;
    em_scene *es = (em_scene *)calloc(1, sizeof(em_scene));
    if (!es) return NULL;

    char cfg[64];
    snprintf(cfg, sizeof(cfg), "threads=%d", num_threads > 0 ? num_threads : 1);
    es->device = rtcNewDevice(cfg);
    if (!es->device) {
        free(es);
        return NULL;
    }
    rtcSetDeviceErrorFunction(es->device, em_error_cb, NULL);

    uint64_t t0 = bench_time_ns();
    es->scene = rtcNewScene(es->device);
    RTCGeometry geom = rtcNewGeometry(es->device, RTC_GEOMETRY_TYPE_TRIANGLE);

    /* Vertex buffer: 3 vertices per triangle (soup), index buffer 0..3N. */
    float *vb = (float *)rtcSetNewGeometryBuffer(
        geom, RTC_BUFFER_TYPE_VERTEX, 0, RTC_FORMAT_FLOAT3, 3 * sizeof(float),
        ntris * 3);
    uint32_t *ib = (uint32_t *)rtcSetNewGeometryBuffer(
        geom, RTC_BUFFER_TYPE_INDEX, 0, RTC_FORMAT_UINT3, 3 * sizeof(uint32_t),
        ntris);
    if (!vb || !ib) {
        rtcReleaseGeometry(geom);
        em_destroy(es);
        return NULL;
    }
    memcpy(vb, vertices, ntris * 9 * sizeof(float));
    for (size_t i = 0; i < ntris * 3; i++) ib[i] = (uint32_t)i;

    rtcCommitGeometry(geom);
    rtcAttachGeometry(es->scene, geom);
    rtcReleaseGeometry(geom);
    rtcCommitScene(es->scene);
    uint64_t t1 = bench_time_ns();
    if (build_ms) *build_ms = bench_ns_to_ms(t1 - t0);
    return es;
}

static void em_intersect1N(void *scene, int thread_idx, const lrt_ray *rays,
                           lrt_hit *hits, size_t n, int coherent) {
    (void)coherent;
    (void)thread_idx;
    em_scene *es = (em_scene *)scene;
    for (size_t i = 0; i < n; i++) {
        const lrt_ray *r = &rays[i];
        struct RTCRayHit rh;
        rh.ray.org_x = r->org[0];
        rh.ray.org_y = r->org[1];
        rh.ray.org_z = r->org[2];
        rh.ray.dir_x = r->dir[0];
        rh.ray.dir_y = r->dir[1];
        rh.ray.dir_z = r->dir[2];
        rh.ray.tnear = r->tmin;
        rh.ray.tfar = r->tmax;
        rh.ray.time = 0.0f;
        rh.ray.mask = 0xFFFFFFFFu;
        rh.ray.id = 0;
        rh.ray.flags = 0;
        rh.hit.geomID = RTC_INVALID_GEOMETRY_ID;
        rh.hit.primID = RTC_INVALID_GEOMETRY_ID;
        rtcIntersect1(es->scene, &rh, NULL);
        if (rh.hit.geomID != RTC_INVALID_GEOMETRY_ID) {
            hits[i].t = rh.ray.tfar;
            hits[i].u = rh.hit.u;
            hits[i].v = rh.hit.v;
            hits[i].prim_id = rh.hit.primID;
        } else {
            hits[i].t = 0.0f;
            hits[i].u = 0.0f;
            hits[i].v = 0.0f;
            hits[i].prim_id = LRT_TRI_NO_HIT;
        }
    }
}

static void em_occluded1N(void *scene, int thread_idx, const lrt_ray *rays,
                          uint8_t *occluded, size_t n, int coherent) {
    (void)coherent;
    (void)thread_idx;
    em_scene *es = (em_scene *)scene;
    for (size_t i = 0; i < n; i++) {
        const lrt_ray *r = &rays[i];
        struct RTCRay ray;
        ray.org_x = r->org[0];
        ray.org_y = r->org[1];
        ray.org_z = r->org[2];
        ray.dir_x = r->dir[0];
        ray.dir_y = r->dir[1];
        ray.dir_z = r->dir[2];
        ray.tnear = r->tmin;
        ray.tfar = r->tmax;
        ray.time = 0.0f;
        ray.mask = 0xFFFFFFFFu;
        ray.id = 0;
        ray.flags = 0;
        rtcOccluded1(es->scene, &ray, NULL);
        occluded[i] = (ray.tfar < 0.0f) ? 1 : 0; /* -inf tfar marks occlusion */
    }
}

static size_t em_memory_bytes(void *scene) {
    (void)scene; /* Embree exposes no per-scene byte count via the C API */
    return 0;
}

static const bench_backend g_embree_backend = {
    "embree", em_build, em_intersect1N, em_occluded1N, em_memory_bytes,
    em_destroy,
};

const bench_backend *backend_embree(void) { return &g_embree_backend; }

#else /* !LRTBENCH_HAVE_EMBREE */

const bench_backend *backend_embree(void) { return NULL; }

#endif
