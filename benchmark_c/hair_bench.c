/*
 * hair_bench.c — CyHair (.hair) loader + round-linear ray-curve benchmark.
 *
 * Loads a CyHair model (default data/wCurly.hair), builds it as Embree-style
 * round-linear curves with the lightrt C11 kernel (lrt_roundcurve_scene_build)
 * and, when available, with Embree 4 (RTC_GEOMETRY_TYPE_ROUND_LINEAR_CURVE with
 * matching neighbor flags). It reports build time, memory, and ray throughput
 * (coherent camera rays + incoherent rays) for each backend, cross-checks
 * lightrt vs Embree hit agreement, and writes a shaded PPM of the model so the
 * loader + intersector can be verified visually.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <math.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../lightrt_c_tri.h"
#include "cyhair.h"
#include "furball.h"
#include "timing.h"

#ifdef LRTBENCH_HAVE_EMBREE
#include <embree4/rtcore.h>
#endif

#define MAX_THREADS 256

/* Primitive families this tool can build (lightrt + Embree, cross-checked). */
enum prim_mode {
    PRIM_ROUND = 0, /* round-linear curves */
    PRIM_FLAT,      /* flat (ribbon) linear curves */
    PRIM_BEZIER,    /* round cubic Bezier curves (Catmull-Rom through points) */
    PRIM_SPHERE,    /* sphere points */
    PRIM_DISC,      /* ray-facing disc points */
    PRIM_ODISC      /* oriented (fixed-normal) disc points */
};
static int parse_prim(const char *s) {
    if (!strcmp(s, "round")) return PRIM_ROUND;
    if (!strcmp(s, "flat")) return PRIM_FLAT;
    if (!strcmp(s, "bezier")) return PRIM_BEZIER;
    if (!strcmp(s, "sphere")) return PRIM_SPHERE;
    if (!strcmp(s, "disc")) return PRIM_DISC;
    if (!strcmp(s, "odisc")) return PRIM_ODISC;
    return -1;
}
static int prim_is_curve(int p) {
    return p == PRIM_ROUND || p == PRIM_FLAT || p == PRIM_BEZIER;
}

/* Catmull-Rom -> cubic-Bezier control points for every strand segment (16
 * floats/seg: 4 CPs of xyz+radius), in the same global segment order as seg_i0.
 * The curve interpolates the strand points; the same CPs feed lightrt and
 * Embree's ROUND_BEZIER_CURVE so the geometry is identical. */
static float *build_bezier_cps(const cyhair_t *h, size_t nstrands, size_t nseg) {
    float *bez = (float *)malloc(nseg * 16 * sizeof(float));
    if (!bez) return NULL;
    size_t w = 0;
    for (size_t i = 0; i < nstrands; i++) {
        uint32_t first = h->strand_first[i], cnt = h->strand_count[i];
        if (cnt < 2) continue;
        for (uint32_t j = 0; j + 1u < cnt; j++, w++) {
            uint32_t i0 = first + j, i1 = first + j + 1u;
            uint32_t im1 = j > 0u ? first + j - 1u : i0;
            uint32_t ip2 = (j + 2u < cnt) ? first + j + 2u : i1;
            float *b = &bez[w * 16];
            for (int a = 0; a < 3; a++) {
                float p0 = h->points[(size_t)i0 * 3 + a];
                float p1 = h->points[(size_t)i1 * 3 + a];
                float pm = h->points[(size_t)im1 * 3 + a];
                float pp = h->points[(size_t)ip2 * 3 + a];
                b[0 * 4 + a] = p0;
                b[1 * 4 + a] = p0 + (p1 - pm) * (1.0f / 6.0f);
                b[2 * 4 + a] = p1 - (pp - p0) * (1.0f / 6.0f);
                b[3 * 4 + a] = p1;
            }
            float r0 = h->radius[i0], r1 = h->radius[i1], rm = h->radius[im1],
                  rp = h->radius[ip2];
            b[0 * 4 + 3] = r0;
            b[1 * 4 + 3] = r0 + (r1 - rm) * (1.0f / 6.0f);
            b[2 * 4 + 3] = r1 - (rp - r0) * (1.0f / 6.0f);
            b[3 * 4 + 3] = r1;
        }
    }
    return bez;
}

/* ------------------------------------------------------------------------- */
/* Small vec / RNG helpers.                                                  */
/* ------------------------------------------------------------------------- */

static inline void v3sub(const float a[3], const float b[3], float o[3]) {
    o[0] = a[0] - b[0]; o[1] = a[1] - b[1]; o[2] = a[2] - b[2];
}
static inline float v3dot(const float a[3], const float b[3]) {
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
}
static inline void v3cross(const float a[3], const float b[3], float o[3]) {
    o[0] = a[1] * b[2] - a[2] * b[1];
    o[1] = a[2] * b[0] - a[0] * b[2];
    o[2] = a[0] * b[1] - a[1] * b[0];
}
static inline void v3norm(float v[3]) {
    float l = sqrtf(v3dot(v, v));
    if (l > 0.0f) { v[0] /= l; v[1] /= l; v[2] /= l; }
}

static inline uint32_t pcg_hash(uint32_t x) {
    uint32_t state = x * 747796405u + 2891336453u;
    uint32_t word = ((state >> ((state >> 28u) + 4u)) ^ state) * 277803737u;
    return (word >> 22u) ^ word;
}
static inline float pcg_unit(uint32_t *s) { /* [0,1) */
    *s = pcg_hash(*s);
    return (float)(*s) * (1.0f / 4294967296.0f);
}

/* ------------------------------------------------------------------------- */
/* Threaded ray dispatch.                                                    */
/* ------------------------------------------------------------------------- */

typedef void (*trace_fn)(void *scene, const lrt_ray *rays, lrt_hit *hits,
                         size_t n);

typedef struct {
    trace_fn fn;
    void *scene;
    const lrt_ray *rays;
    lrt_hit *hits;
    size_t n;
} worker_args;

static void *worker_main(void *p) {
    worker_args *w = (worker_args *)p;
    if (w->n) w->fn(w->scene, w->rays, w->hits, w->n);
    return NULL;
}

static double run_trace(trace_fn fn, void *scene, int threads,
                        const lrt_ray *rays, lrt_hit *hits, size_t n) {
    uint64_t t0 = bench_time_ns();
    if (threads <= 1) {
        worker_args w = {fn, scene, rays, hits, n};
        worker_main(&w);
    } else {
        pthread_t tid[MAX_THREADS];
        worker_args wa[MAX_THREADS];
        size_t chunk = (n + (size_t)threads - 1) / (size_t)threads;
        int spawned = 0;
        for (int t = 0; t < threads; t++) {
            size_t lo = (size_t)t * chunk;
            if (lo >= n) break;
            size_t cnt = chunk < n - lo ? chunk : n - lo;
            wa[t] = (worker_args){fn, scene, rays + lo, hits + lo, cnt};
            pthread_create(&tid[t], NULL, worker_main, &wa[t]);
            spawned++;
        }
        for (int t = 0; t < spawned; t++) pthread_join(tid[t], NULL);
    }
    return bench_ns_to_s(bench_time_ns() - t0);
}

static void lrt_trace_coherent(void *scene, const lrt_ray *rays, lrt_hit *hits,
                               size_t n) {
    lrt_tri_intersect1N((const lrt_tri_scene *)scene, rays, hits, n,
                        LRT_TRI_BATCH_COHERENT);
}
static void lrt_trace_incoherent(void *scene, const lrt_ray *rays,
                                 lrt_hit *hits, size_t n) {
    lrt_tri_intersect1N((const lrt_tri_scene *)scene, rays, hits, n,
                        LRT_TRI_BATCH_INCOHERENT);
}

static int cmp_double(const void *a, const void *b) {
    double da = *(const double *)a, db = *(const double *)b;
    return (da > db) - (da < db);
}

/* Median Mrays/s over `repeat` timed runs of fn. */
static double measure_mrays(trace_fn fn, void *scene, int threads,
                            const lrt_ray *rays, lrt_hit *hits, size_t n,
                            int repeat) {
    run_trace(fn, scene, threads, rays, hits, n); /* warm-up */
    double samp[64];
    int reps = repeat < 64 ? repeat : 64;
    if (reps < 1) reps = 1;
    for (int r = 0; r < reps; r++) {
        double s = run_trace(fn, scene, threads, rays, hits, n);
        samp[r] = s > 0.0 ? (double)n / s / 1e6 : 0.0;
    }
    qsort(samp, (size_t)reps, sizeof(double), cmp_double);
    return samp[reps / 2];
}

/* ------------------------------------------------------------------------- */
/* Embree round-linear curve backend (optional).                            */
/* ------------------------------------------------------------------------- */

#ifdef LRTBENCH_HAVE_EMBREE
typedef struct {
    RTCDevice device;
    RTCScene scene;
} em_scene;

static void em_error_cb(void *u, enum RTCError code, const char *str) {
    (void)u;
    fprintf(stderr, "embree error %d: %s\n", (int)code, str ? str : "");
}
static void em_destroy(em_scene *es); /* fwd */

static em_scene *em_new(int threads) {
    em_scene *es = (em_scene *)calloc(1, sizeof(em_scene));
    if (!es) return NULL;
    char cfg[64];
    snprintf(cfg, sizeof(cfg), "threads=%d", threads > 0 ? threads : 1);
    es->device = rtcNewDevice(cfg);
    if (!es->device) { free(es); return NULL; }
    rtcSetDeviceErrorFunction(es->device, em_error_cb, NULL);
    es->scene = rtcNewScene(es->device);
    return es;
}

/* Build a linear-curve scene (round or flat). gtype selects the curve type;
 * seg_i0[i] is the first vertex index of segment i; flags (or NULL) carries the
 * NEIGHBOR_LEFT/RIGHT bits used by round curves at the joints. */
static em_scene *em_build_curve(const cyhair_t *h, size_t npts_used,
                                const uint32_t *seg_i0, const uint8_t *flags,
                                size_t nseg, enum RTCGeometryType gtype, int threads,
                                double *build_ms) {
    em_scene *es = em_new(threads);
    if (!es) return NULL;
    uint64_t t0 = bench_time_ns();
    RTCGeometry g = rtcNewGeometry(es->device, gtype);
    float *vb = (float *)rtcSetNewGeometryBuffer(
        g, RTC_BUFFER_TYPE_VERTEX, 0, RTC_FORMAT_FLOAT4, 4 * sizeof(float),
        npts_used);
    unsigned *ib = (unsigned *)rtcSetNewGeometryBuffer(
        g, RTC_BUFFER_TYPE_INDEX, 0, RTC_FORMAT_UINT, sizeof(unsigned), nseg);
    unsigned char *fb = NULL;
    if (flags)
        fb = (unsigned char *)rtcSetNewGeometryBuffer(
            g, RTC_BUFFER_TYPE_FLAGS, 0, RTC_FORMAT_UCHAR, sizeof(unsigned char),
            nseg);
    if (!vb || !ib || (flags && !fb)) {
        rtcReleaseGeometry(g);
        em_destroy(es);
        return NULL;
    }
    for (size_t i = 0; i < npts_used; i++) {
        vb[i * 4 + 0] = h->points[i * 3 + 0];
        vb[i * 4 + 1] = h->points[i * 3 + 1];
        vb[i * 4 + 2] = h->points[i * 3 + 2];
        vb[i * 4 + 3] = h->radius[i];
    }
    for (size_t i = 0; i < nseg; i++) {
        ib[i] = seg_i0[i];
        if (fb) fb[i] = flags[i];
    }
    rtcCommitGeometry(g);
    rtcAttachGeometry(es->scene, g);
    rtcReleaseGeometry(g);
    rtcCommitScene(es->scene);
    if (build_ms) *build_ms = bench_ns_to_ms(bench_time_ns() - t0);
    return es;
}

/* Build a point-cloud scene (sphere / disc / oriented-disc). centers is the
 * float4 (xyz+radius) vertex source; normals (or NULL) feeds oriented discs. */
static em_scene *em_build_points(const float *centers4, const float *normals,
                                 size_t npts, enum RTCGeometryType gtype, int threads,
                                 double *build_ms) {
    em_scene *es = em_new(threads);
    if (!es) return NULL;
    uint64_t t0 = bench_time_ns();
    RTCGeometry g = rtcNewGeometry(es->device, gtype);
    float *vb = (float *)rtcSetNewGeometryBuffer(
        g, RTC_BUFFER_TYPE_VERTEX, 0, RTC_FORMAT_FLOAT4, 4 * sizeof(float), npts);
    float *nb = NULL;
    if (normals)
        nb = (float *)rtcSetNewGeometryBuffer(g, RTC_BUFFER_TYPE_NORMAL, 0,
                                              RTC_FORMAT_FLOAT3, 3 * sizeof(float),
                                              npts);
    if (!vb || (normals && !nb)) {
        rtcReleaseGeometry(g);
        em_destroy(es);
        return NULL;
    }
    memcpy(vb, centers4, npts * 4 * sizeof(float));
    if (nb) memcpy(nb, normals, npts * 3 * sizeof(float));
    rtcCommitGeometry(g);
    rtcAttachGeometry(es->scene, g);
    rtcReleaseGeometry(g);
    rtcCommitScene(es->scene);
    if (build_ms) *build_ms = bench_ns_to_ms(bench_time_ns() - t0);
    return es;
}

/* Round cubic-Bezier scene from explicit control points (16 floats/seg). Each
 * segment is 4 distinct vertices (index buffer steps by 4), identical to the
 * CPs handed to lrt_bezcurve_scene_build. */
static em_scene *em_build_bezier(const float *bez_cps, size_t nseg, int threads,
                                 double *build_ms) {
    em_scene *es = em_new(threads);
    if (!es) return NULL;
    uint64_t t0 = bench_time_ns();
    RTCGeometry g =
        rtcNewGeometry(es->device, RTC_GEOMETRY_TYPE_ROUND_BEZIER_CURVE);
    size_t nvtx = nseg * 4;
    float *vb = (float *)rtcSetNewGeometryBuffer(
        g, RTC_BUFFER_TYPE_VERTEX, 0, RTC_FORMAT_FLOAT4, 4 * sizeof(float), nvtx);
    unsigned *ib = (unsigned *)rtcSetNewGeometryBuffer(
        g, RTC_BUFFER_TYPE_INDEX, 0, RTC_FORMAT_UINT, sizeof(unsigned), nseg);
    if (!vb || !ib) {
        rtcReleaseGeometry(g);
        em_destroy(es);
        return NULL;
    }
    memcpy(vb, bez_cps, nvtx * 4 * sizeof(float));
    for (size_t i = 0; i < nseg; i++) ib[i] = (unsigned)(i * 4);
    rtcCommitGeometry(g);
    rtcAttachGeometry(es->scene, g);
    rtcReleaseGeometry(g);
    rtcCommitScene(es->scene);
    if (build_ms) *build_ms = bench_ns_to_ms(bench_time_ns() - t0);
    return es;
}

static void em_trace(void *scene, const lrt_ray *rays, lrt_hit *hits, size_t n) {
    em_scene *es = (em_scene *)scene;
    for (size_t i = 0; i < n; i++) {
        const lrt_ray *r = &rays[i];
        struct RTCRayHit rh;
        rh.ray.org_x = r->org[0]; rh.ray.org_y = r->org[1]; rh.ray.org_z = r->org[2];
        rh.ray.dir_x = r->dir[0]; rh.ray.dir_y = r->dir[1]; rh.ray.dir_z = r->dir[2];
        rh.ray.tnear = r->tmin; rh.ray.tfar = r->tmax;
        rh.ray.time = 0.0f; rh.ray.mask = 0xFFFFFFFFu; rh.ray.id = 0; rh.ray.flags = 0;
        rh.hit.geomID = RTC_INVALID_GEOMETRY_ID;
        rh.hit.primID = RTC_INVALID_GEOMETRY_ID;
        rtcIntersect1(es->scene, &rh, NULL);
        if (rh.hit.geomID != RTC_INVALID_GEOMETRY_ID) {
            hits[i].t = rh.ray.tfar;
            hits[i].u = rh.hit.u;
            hits[i].v = rh.hit.v;
            hits[i].prim_id = rh.hit.primID;
        } else {
            hits[i].prim_id = LRT_TRI_NO_HIT;
            hits[i].t = 0.0f;
        }
    }
}

static void em_destroy(em_scene *es) {
    if (!es) return;
    if (es->scene) rtcReleaseScene(es->scene);
    if (es->device) rtcReleaseDevice(es->device);
    free(es);
}
#endif /* LRTBENCH_HAVE_EMBREE */

/* ------------------------------------------------------------------------- */
/* Camera + ray generation.                                                  */
/* ------------------------------------------------------------------------- */

typedef struct {
    float pos[3], forward[3], right[3], up[3];
    float tan_half, aspect;
    float tmax;
} camera;

static void camera_frame(const cyhair_t *h, int w, int hgt, camera *cam) {
    float center[3], ext[3];
    for (int a = 0; a < 3; a++) {
        center[a] = 0.5f * (h->bbox_min[a] + h->bbox_max[a]);
        ext[a] = 0.5f * (h->bbox_max[a] - h->bbox_min[a]);
        if (ext[a] < 1e-6f) ext[a] = 1e-6f;
    }
    float radius = sqrtf(ext[0] * ext[0] + ext[1] * ext[1] + ext[2] * ext[2]);
    /* look along the smallest-extent axis to show the broadest silhouette */
    int va = 0;
    if (ext[1] < ext[va]) va = 1;
    if (ext[2] < ext[va]) va = 2;
    float n[3] = {0, 0, 0};
    n[va] = 1.0f;
    float up[3] = {0, 1, 0};
    if (va == 1) { up[0] = 0; up[1] = 0; up[2] = 1; }

    const float fov_y = 40.0f * 3.14159265358979f / 180.0f;
    cam->tan_half = tanf(0.5f * fov_y);
    cam->aspect = (float)w / (float)hgt;
    float dist = radius / cam->tan_half * 1.3f;
    for (int a = 0; a < 3; a++) {
        cam->pos[a] = center[a] + n[a] * dist;
        cam->forward[a] = -n[a];
    }
    v3cross(cam->forward, up, cam->right);
    v3norm(cam->right);
    v3cross(cam->right, cam->forward, cam->up);
    v3norm(cam->up);
    cam->tmax = dist + 3.0f * radius;
}

static void gen_primary(const camera *cam, int w, int hgt, lrt_ray *rays) {
    for (int y = 0; y < hgt; y++) {
        for (int x = 0; x < w; x++) {
            float sx = (2.0f * ((float)x + 0.5f) / (float)w - 1.0f) * cam->aspect *
                       cam->tan_half;
            float sy = (1.0f - 2.0f * ((float)y + 0.5f) / (float)hgt) * cam->tan_half;
            float d[3];
            for (int a = 0; a < 3; a++)
                d[a] = cam->forward[a] + sx * cam->right[a] + sy * cam->up[a];
            v3norm(d);
            lrt_ray *r = &rays[(size_t)y * w + x];
            for (int a = 0; a < 3; a++) { r->org[a] = cam->pos[a]; r->dir[a] = d[a]; }
            r->tmin = 1e-4f;
            r->tmax = cam->tmax;
        }
    }
}

static void gen_incoherent(const cyhair_t *h, lrt_ray *rays, size_t n,
                           uint32_t seed) {
    float center[3], ext[3];
    for (int a = 0; a < 3; a++) {
        center[a] = 0.5f * (h->bbox_min[a] + h->bbox_max[a]);
        ext[a] = 0.5f * (h->bbox_max[a] - h->bbox_min[a]);
    }
    float radius = sqrtf(ext[0] * ext[0] + ext[1] * ext[1] + ext[2] * ext[2]);
    if (radius < 1e-6f) radius = 1.0f;
    for (size_t i = 0; i < n; i++) {
        uint32_t s = seed + (uint32_t)i * 9781u + 1u;
        float z = 2.0f * pcg_unit(&s) - 1.0f;
        float phi = 6.2831853f * pcg_unit(&s);
        float rr = sqrtf(1.0f - z * z);
        float o[3] = {rr * cosf(phi), z, rr * sinf(phi)};
        float tgt[3];
        for (int a = 0; a < 3; a++)
            tgt[a] = center[a] + (2.0f * pcg_unit(&s) - 1.0f) * ext[a] * 0.8f;
        lrt_ray *r = &rays[i];
        for (int a = 0; a < 3; a++) r->org[a] = center[a] + o[a] * radius * 2.0f;
        float d[3];
        v3sub(tgt, r->org, d);
        v3norm(d);
        for (int a = 0; a < 3; a++) r->dir[a] = d[a];
        r->tmin = 1e-4f;
        r->tmax = radius * 8.0f;
    }
}

/* ------------------------------------------------------------------------- */
/* Shaded PPM output.                                                        */
/* ------------------------------------------------------------------------- */

static int write_ppm(const char *path, const unsigned char *rgb, int w, int h) {
    FILE *f = fopen(path, "wb");
    if (!f) return -1;
    fprintf(f, "P6\n%d %d\n255\n", w, h);
    size_t nbytes = (size_t)w * h * 3;
    int ok = fwrite(rgb, 1, nbytes, f) == nbytes;
    fclose(f);
    return ok ? 0 : -1;
}

/* Shade primary hits with a headlight using the reconstructed cone normal. */
static void shade_image(const cyhair_t *h, const uint32_t *seg_i0,
                        const lrt_ray *rays, const lrt_hit *hits, int w,
                        int hgt, unsigned char *rgb) {
    for (int i = 0; i < w * hgt; i++) {
        float r = 0.04f, g = 0.05f, b = 0.07f; /* background */
        const lrt_hit *hit = &hits[i];
        if (hit->prim_id != LRT_TRI_NO_HIT) {
            const lrt_ray *ray = &rays[i];
            uint32_t i0 = seg_i0[hit->prim_id];
            const float *p0 = &h->points[(size_t)i0 * 3];
            const float *p1 = &h->points[(size_t)(i0 + 1) * 3];
            float hp[3];
            for (int a = 0; a < 3; a++) hp[a] = ray->org[a] + hit->t * ray->dir[a];
            float axis[3];
            v3sub(p1, p0, axis);
            float al2 = v3dot(axis, axis);
            float s = hit->u;
            if (s < 0.0f) s = 0.0f; else if (s > 1.0f) s = 1.0f;
            float ap[3], nrm[3];
            for (int a = 0; a < 3; a++) ap[a] = p0[a] + (al2 > 0.0f ? s : 0.0f) * axis[a];
            v3sub(hp, ap, nrm);
            v3norm(nrm);
            float ndotv = -v3dot(nrm, ray->dir); /* dir points away from camera */
            if (ndotv < 0.0f) ndotv = -ndotv;
            float shade = 0.15f + 0.85f * ndotv;
            /* warm hair tint */
            r = shade * 0.80f;
            g = shade * 0.58f;
            b = shade * 0.40f;
        }
        rgb[i * 3 + 0] = (unsigned char)(255.0f * (r > 1 ? 1 : r));
        rgb[i * 3 + 1] = (unsigned char)(255.0f * (g > 1 ? 1 : g));
        rgb[i * 3 + 2] = (unsigned char)(255.0f * (b > 1 ? 1 : b));
    }
}

/* Shade point-primitive hits (prim_id = point index) by the radial normal. */
static void shade_image_points(const cyhair_t *h, const lrt_ray *rays,
                               const lrt_hit *hits, int w, int hgt,
                               unsigned char *rgb) {
    for (int i = 0; i < w * hgt; i++) {
        float r = 0.04f, g = 0.05f, b = 0.07f;
        const lrt_hit *hit = &hits[i];
        if (hit->prim_id != LRT_TRI_NO_HIT) {
            const lrt_ray *ray = &rays[i];
            const float *c = &h->points[(size_t)hit->prim_id * 3];
            float nrm[3];
            for (int a = 0; a < 3; a++)
                nrm[a] = ray->org[a] + hit->t * ray->dir[a] - c[a];
            v3norm(nrm);
            float ndotv = -v3dot(nrm, ray->dir);
            if (ndotv < 0.0f) ndotv = -ndotv;
            float shade = 0.15f + 0.85f * ndotv;
            r = shade * 0.80f;
            g = shade * 0.58f;
            b = shade * 0.40f;
        }
        rgb[i * 3 + 0] = (unsigned char)(255.0f * (r > 1 ? 1 : r));
        rgb[i * 3 + 1] = (unsigned char)(255.0f * (g > 1 ? 1 : g));
        rgb[i * 3 + 2] = (unsigned char)(255.0f * (b > 1 ? 1 : b));
    }
}

/* ------------------------------------------------------------------------- */

static void usage(const char *a0) {
    fprintf(stderr,
            "usage: %s [options]\n"
            "  --hair FILE        CyHair model (default data/wCurly.hair)\n"
            "  --gen furball      generate procedural fur instead of loading a file\n"
            "  --strands N        furball strand count (default 200000)\n"
            "  --segments N       furball segments per strand (default 8)\n"
            "  --prim KIND        round (default) | flat | bezier | sphere | disc | odisc\n"
            "                     (round/flat/bezier = curves; sphere/disc/odisc = points)\n"
            "  --width N          image width (default 1024)\n"
            "  --height N         image height (default 1024)\n"
            "  --radius-scale F   multiply hair radius (default 1.0)\n"
            "  --max-strands N    use only the first N strands (0 = all)\n"
            "  --out FILE         output PPM (default hair.ppm)\n"
            "  --nrays N          incoherent rays (default 4000000)\n"
            "  --threads N        worker threads (default 1)\n"
            "  --repeat N         timed reps, median reported (default 5)\n"
            "  --seed N           incoherent RNG seed (default 1234)\n",
            a0);
}

int main(int argc, char **argv) {
    const char *hair_path = "data/wCurly.hair";
    const char *out_path = "hair.ppm";
    int width = 1024, height = 1024;
    float radius_scale = 1.0f;
    size_t max_strands = 0;
    size_t nrays = 4000000;
    int threads = 1, repeat = 5;
    uint32_t seed = 1234;
    int prim = PRIM_ROUND;
    int gen_furball = 0;
    size_t fb_strands = 200000;
    int fb_segs = 8;

    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        const char *nx = (i + 1 < argc) ? argv[i + 1] : NULL;
        if (!strcmp(a, "--hair") && nx) hair_path = argv[++i];
        else if (!strcmp(a, "--gen") && nx) {
            gen_furball = !strcmp(argv[++i], "furball");
        }
        else if (!strcmp(a, "--strands") && nx) fb_strands = (size_t)atoll(argv[++i]);
        else if (!strcmp(a, "--segments") && nx) fb_segs = atoi(argv[++i]);
        else if (!strcmp(a, "--prim") && nx) {
            prim = parse_prim(argv[++i]);
            if (prim < 0) { fprintf(stderr, "bad --prim\n"); usage(argv[0]); return 1; }
        }
        else if (!strcmp(a, "--out") && nx) out_path = argv[++i];
        else if (!strcmp(a, "--width") && nx) width = atoi(argv[++i]);
        else if (!strcmp(a, "--height") && nx) height = atoi(argv[++i]);
        else if (!strcmp(a, "--radius-scale") && nx) radius_scale = (float)atof(argv[++i]);
        else if (!strcmp(a, "--max-strands") && nx) max_strands = (size_t)atoll(argv[++i]);
        else if (!strcmp(a, "--nrays") && nx) nrays = (size_t)atoll(argv[++i]);
        else if (!strcmp(a, "--threads") && nx) threads = atoi(argv[++i]);
        else if (!strcmp(a, "--repeat") && nx) repeat = atoi(argv[++i]);
        else if (!strcmp(a, "--seed") && nx) seed = (uint32_t)strtoul(argv[++i], NULL, 10);
        else if (!strcmp(a, "--help") || !strcmp(a, "-h")) { usage(argv[0]); return 0; }
        else { fprintf(stderr, "unknown option: %s\n", a); usage(argv[0]); return 1; }
    }
    if (width < 1) width = 1;
    if (height < 1) height = 1;
    if (threads < 1) threads = 1;
    if (threads > MAX_THREADS) threads = MAX_THREADS;

    /* --- Load or generate --- */
    cyhair_t hair;
    uint64_t l0 = bench_time_ns();
    int lr = gen_furball
                 ? furball_generate(fb_strands, fb_segs, 0.006f, radius_scale,
                                    seed, &hair)
                 : cyhair_load(hair_path, radius_scale, &hair);
    uint64_t l1 = bench_time_ns();
    if (lr != 0) {
        if (gen_furball)
            fprintf(stderr, "furball_generate failed (error %d)\n", lr);
        else
            fprintf(stderr, "failed to load %s (error %d)\n", hair_path, lr);
        return 1;
    }
    size_t nstrands = hair.nstrands;
    if (max_strands && max_strands < nstrands) nstrands = max_strands;
    /* points actually referenced by the (possibly subset) strands */
    size_t npts_used = (size_t)hair.strand_first[nstrands - 1] +
                       hair.strand_count[nstrands - 1];
    size_t nseg = 0;
    for (size_t i = 0; i < nstrands; i++)
        nseg += hair.strand_count[i] >= 2 ? hair.strand_count[i] - 1 : 0;

    printf("%s %s: %zu strands, %zu points, %zu segments (%.1f ms)\n",
           gen_furball ? "generated" : "loaded",
           gen_furball ? "furball" : hair_path, nstrands, npts_used, nseg,
           bench_ns_to_ms(l1 - l0));
    printf("bbox: [%.3f %.3f %.3f] .. [%.3f %.3f %.3f]\n", hair.bbox_min[0],
           hair.bbox_min[1], hair.bbox_min[2], hair.bbox_max[0], hair.bbox_max[1],
           hair.bbox_max[2]);

    /* --- Flat segment->first-point map + Embree neighbor flags --- */
    uint32_t *seg_i0 = (uint32_t *)malloc(nseg * sizeof(uint32_t));
    uint8_t *seg_flags = (uint8_t *)malloc(nseg * sizeof(uint8_t));
    if (!seg_i0 || !seg_flags) { fprintf(stderr, "oom\n"); return 1; }
    {
        size_t w = 0;
        for (size_t i = 0; i < nstrands; i++) {
            uint32_t first = hair.strand_first[i], cnt = hair.strand_count[i];
            if (cnt < 2) continue;
            for (uint32_t j = 0; j + 1u < cnt; j++, w++) {
                seg_i0[w] = first + j;
                uint8_t fl = 0;
#ifdef LRTBENCH_HAVE_EMBREE
                if (j > 0u) fl |= RTC_CURVE_FLAG_NEIGHBOR_LEFT;
                if (j + 2u < cnt) fl |= RTC_CURVE_FLAG_NEIGHBOR_RIGHT;
#endif
                seg_flags[w] = fl;
            }
        }
    }

    const char *prim_name[] = {"round-curve",  "flat-curve", "bezier-curve",
                               "sphere-point", "disc-point", "odisc-point"};
    size_t nprim = prim_is_curve(prim) ? nseg : npts_used;

    /* Point clouds: float4 (xyz+r) vertices for Embree + per-point normals
     * (oriented disc only), normal = radial direction from the bbox center. */
    float *centers4 = NULL, *pnormals = NULL;
    if (!prim_is_curve(prim)) {
        centers4 = (float *)malloc(npts_used * 4 * sizeof(float));
        if (!centers4) { fprintf(stderr, "oom\n"); return 1; }
        for (size_t i = 0; i < npts_used; i++) {
            centers4[i * 4 + 0] = hair.points[i * 3 + 0];
            centers4[i * 4 + 1] = hair.points[i * 3 + 1];
            centers4[i * 4 + 2] = hair.points[i * 3 + 2];
            centers4[i * 4 + 3] = hair.radius[i];
        }
        if (prim == PRIM_ODISC) {
            float ctr[3];
            for (int a = 0; a < 3; a++)
                ctr[a] = 0.5f * (hair.bbox_min[a] + hair.bbox_max[a]);
            pnormals = (float *)malloc(npts_used * 3 * sizeof(float));
            if (!pnormals) { fprintf(stderr, "oom\n"); return 1; }
            for (size_t i = 0; i < npts_used; i++) {
                float n[3] = {hair.points[i * 3 + 0] - ctr[0],
                              hair.points[i * 3 + 1] - ctr[1],
                              hair.points[i * 3 + 2] - ctr[2]};
                v3norm(n);
                if (n[0] == 0.0f && n[1] == 0.0f && n[2] == 0.0f) n[2] = 1.0f;
                pnormals[i * 3 + 0] = n[0];
                pnormals[i * 3 + 1] = n[1];
                pnormals[i * 3 + 2] = n[2];
            }
        }
    }

    /* --- Build lightrt scene --- */
    lrt_hair_strands strands = {0};
    strands.points = hair.points;
    strands.radius = hair.radius;
    strands.constant_radius = 0.0f;
    strands.strand_first = hair.strand_first;
    strands.strand_count = hair.strand_count;
    strands.nstrands = nstrands;
    strands.npoints = npts_used;

    /* Catmull-Rom -> Bezier control points (shared with Embree) */
    float *bez_cps = NULL;
    if (prim == PRIM_BEZIER) {
        bez_cps = build_bezier_cps(&hair, nstrands, nseg);
        if (!bez_cps) { fprintf(stderr, "oom\n"); return 1; }
    }

    lrt_tri_build_options opts = {0};
    opts.num_threads = (unsigned)threads;
    lrt_result err = LRT_RESULT_OK;
    uint64_t b0 = bench_time_ns();
    lrt_tri_scene *scene = NULL;
    switch (prim) {
        case PRIM_ROUND: scene = lrt_roundcurve_scene_build(&strands, &opts, &err); break;
        case PRIM_FLAT:  scene = lrt_flatcurve_scene_build(&strands, &opts, &err); break;
        case PRIM_BEZIER: scene = lrt_bezcurve_scene_build(bez_cps, nseg, &opts, &err); break;
        case PRIM_SPHERE: scene = lrt_points_scene_build(hair.points, hair.radius, NULL, LRT_POINT_SPHERE, npts_used, &opts, &err); break;
        case PRIM_DISC:   scene = lrt_points_scene_build(hair.points, hair.radius, NULL, LRT_POINT_DISC, npts_used, &opts, &err); break;
        case PRIM_ODISC:  scene = lrt_points_scene_build(hair.points, hair.radius, pnormals, LRT_POINT_ORIENTED_DISC, npts_used, &opts, &err); break;
    }
    uint64_t b1 = bench_time_ns();
    if (!scene) {
        fprintf(stderr, "lightrt scene build failed (err %d)\n", (int)err);
        return 1;
    }
    lrt_tri_stats st;
    lrt_tri_scene_stats(scene, &st);
    double lrt_build_ms = bench_ns_to_ms(b1 - b0);
    printf("\nprim: %s  (%zu primitives)\n", prim_name[prim], nprim);
    printf("lightrt  build %8.1f ms (%6.2f Mprim/s)  mem %7.2f MB  [%s]\n",
           lrt_build_ms, (double)nprim / lrt_build_ms / 1e3,
           (double)st.memory_bytes / (1024.0 * 1024.0),
           lrt_tri_kernel_name(scene));

    /* --- Build Embree scene --- */
    void *embree = NULL;
    double em_build_ms = 0.0;
#ifdef LRTBENCH_HAVE_EMBREE
    if (prim == PRIM_BEZIER) {
        embree = em_build_bezier(bez_cps, nseg, threads, &em_build_ms);
    } else if (prim_is_curve(prim)) {
        enum RTCGeometryType gt = prim == PRIM_ROUND
                                 ? RTC_GEOMETRY_TYPE_ROUND_LINEAR_CURVE
                                 : RTC_GEOMETRY_TYPE_FLAT_LINEAR_CURVE;
        const uint8_t *fl = prim == PRIM_ROUND ? seg_flags : NULL;
        embree = em_build_curve(&hair, npts_used, seg_i0, fl, nseg, gt, threads,
                                &em_build_ms);
    } else {
        enum RTCGeometryType gt = prim == PRIM_SPHERE
                                 ? RTC_GEOMETRY_TYPE_SPHERE_POINT
                                 : prim == PRIM_DISC
                                       ? RTC_GEOMETRY_TYPE_DISC_POINT
                                       : RTC_GEOMETRY_TYPE_ORIENTED_DISC_POINT;
        embree = em_build_points(centers4, prim == PRIM_ODISC ? pnormals : NULL,
                                 npts_used, gt, threads, &em_build_ms);
    }
    if (embree)
        printf("embree   build %8.1f ms (%6.2f Mprim/s)\n", em_build_ms,
               (double)nprim / em_build_ms / 1e3);
    else
        fprintf(stderr, "embree scene build failed (continuing lightrt-only)\n");
#else
    printf("embree   (not built; configure with Embree to compare)\n");
#endif

    /* --- Camera primary rays --- */
    size_t npix = (size_t)width * height;
    lrt_ray *primary = (lrt_ray *)malloc(npix * sizeof(lrt_ray));
    lrt_hit *hits = (lrt_hit *)malloc(npix * sizeof(lrt_hit));
    lrt_ray *incoh = (lrt_ray *)malloc(nrays * sizeof(lrt_ray));
    lrt_hit *ihits = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
    if (!primary || !hits || !incoh || !ihits) { fprintf(stderr, "oom\n"); return 1; }
    camera cam;
    camera_frame(&hair, width, height, &cam);
    gen_primary(&cam, width, height, primary);
    gen_incoherent(&hair, incoh, nrays, seed);

    /* --- Throughput --- */
    printf("\n%-9s %-11s %12s %10s\n", "backend", "workload", "Mrays/s", "hit");
    double mr;
    run_trace(lrt_trace_coherent, scene, threads, primary, hits, npix); /* for image + hit */
    size_t nhit = 0;
    for (size_t i = 0; i < npix; i++) nhit += hits[i].prim_id != LRT_TRI_NO_HIT;
    mr = measure_mrays(lrt_trace_coherent, scene, threads, primary, hits, npix, repeat);
    printf("%-9s %-11s %12.3f %10.4f\n", "lightrt", "primary", mr,
           (double)nhit / (double)npix);
    mr = measure_mrays(lrt_trace_incoherent, scene, threads, incoh, ihits, nrays, repeat);
    size_t nhit_i = 0;
    for (size_t i = 0; i < nrays; i++) nhit_i += ihits[i].prim_id != LRT_TRI_NO_HIT;
    printf("%-9s %-11s %12.3f %10.4f\n", "lightrt", "incoherent", mr,
           (double)nhit_i / (double)nrays);

#ifdef LRTBENCH_HAVE_EMBREE
    lrt_hit *ehits = NULL;
    if (embree) {
        ehits = (lrt_hit *)malloc(npix * sizeof(lrt_hit));
        lrt_hit *eihits = (lrt_hit *)malloc(nrays * sizeof(lrt_hit));
        if (ehits && eihits) {
            run_trace(em_trace, embree, threads, primary, ehits, npix);
            size_t en = 0;
            for (size_t i = 0; i < npix; i++) en += ehits[i].prim_id != LRT_TRI_NO_HIT;
            mr = measure_mrays(em_trace, embree, threads, primary, ehits, npix, repeat);
            printf("%-9s %-11s %12.3f %10.4f\n", "embree", "primary", mr,
                   (double)en / (double)npix);
            mr = measure_mrays(em_trace, embree, threads, incoh, eihits, nrays, repeat);
            size_t eni = 0;
            for (size_t i = 0; i < nrays; i++) eni += eihits[i].prim_id != LRT_TRI_NO_HIT;
            printf("%-9s %-11s %12.3f %10.4f\n", "embree", "incoherent", mr,
                   (double)eni / (double)nrays);

            /* --- Cross-check lightrt vs embree on primary rays --- */
            size_t mism = 0;
            double max_rel = 0.0;
            for (size_t i = 0; i < npix; i++) {
                int ha = hits[i].prim_id != LRT_TRI_NO_HIT;
                int hb = ehits[i].prim_id != LRT_TRI_NO_HIT;
                if (ha != hb) { mism++; continue; }
                if (ha) {
                    double denom = fabs((double)ehits[i].t) > 1e-9 ? fabs((double)ehits[i].t) : 1e-9;
                    double rel = fabs((double)hits[i].t - (double)ehits[i].t) / denom;
                    if (rel > max_rel) max_rel = rel;
                    if (rel > 1e-3) mism++;
                }
            }
            double agree = 1.0 - (double)mism / (double)npix;
            printf("\nverify lightrt vs embree (primary): agreement %.4f%% "
                   "max_rel_t %.3e %s\n",
                   agree * 100.0, max_rel, agree >= 0.99 ? "PASS" : "CHECK");
        }
        free(eihits);
    }
#endif

    /* --- Shaded image (from lightrt hits) --- */
    unsigned char *rgb = (unsigned char *)malloc(npix * 3);
    if (rgb) {
        if (prim_is_curve(prim))
            shade_image(&hair, seg_i0, primary, hits, width, height, rgb);
        else
            shade_image_points(&hair, primary, hits, width, height, rgb);
        if (write_ppm(out_path, rgb, width, height) == 0)
            printf("\nwrote %s (%dx%d)\n", out_path, width, height);
        else
            fprintf(stderr, "failed to write %s\n", out_path);
        free(rgb);
    }

#ifdef LRTBENCH_HAVE_EMBREE
    free(ehits);
    em_destroy((em_scene *)embree);
#endif
    lrt_tri_scene_free(scene);
    free(primary);
    free(hits);
    free(incoh);
    free(ihits);
    free(seg_i0);
    free(seg_flags);
    free(centers4);
    free(pnormals);
    free(bez_cps);
    cyhair_free(&hair);
    return 0;
}
