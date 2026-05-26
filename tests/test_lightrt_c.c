/*
 * test_lightrt_c.c — correctness test for the pure-C11 lightrt_c.c port.
 *
 * Builds a scene of analytic spheres, intersects many random rays through the
 * BVH, and compares each closest-hit against an O(N) brute-force search.
 * Validates hit primitive id and the fp64 ray parameter t.
 *
 * Build (pure C, no C++):
 *   cc -std=c11 -O2 -Wall -Wextra lightrt_c.c tests/test_lightrt_c.c -o test_lightrt_c -lm
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "../lightrt_c.h"

#include <math.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

/* --- scene: a set of spheres, intersected analytically in fp64 --- */
typedef struct { double c[3]; double r; } sphere;

typedef struct { const sphere *sph; unsigned n; } scene_data;

typedef struct {
    unsigned progress_calls;
    int cancel_now;
} api_events;

typedef enum {
    SYNTH_POINT_LEAF,
    SYNTH_POINT_LINE,
    SYNTH_SAME_POINT,
    SYNTH_SAME_BOX,
    SYNTH_COPLANAR_GRID,
    SYNTH_NAN_BOUNDS,
    SYNTH_INF_BOUNDS,
    SYNTH_INVERTED_BOUNDS
} synthetic_kind;

typedef struct {
    synthetic_kind kind;
} synthetic_data;

typedef enum {
    ISECT_NORMAL,
    ISECT_NEVER,
    ISECT_NAN_T,
    ISECT_AFTER_TMAX,
    ISECT_BEFORE_TMIN
} isect_mode;

typedef struct {
    const sphere *sph;
    unsigned n;
    isect_mode mode;
    unsigned calls;
} callback_scene_data;

static lrt_aabb sphere_bounds(unsigned i, void *user) {
    const scene_data *sd = (const scene_data *)user;
    const sphere *s = &sd->sph[i];
    lrt_aabb b;
    for (int k = 0; k < 3; k++) {
        b.lo[k] = s->c[k] - s->r;
        b.hi[k] = s->c[k] + s->r;
    }
    return b;
}

static lrt_aabb callback_bounds(unsigned i, void *user) {
    const callback_scene_data *sd = (const callback_scene_data *)user;
    const sphere *s = &sd->sph[i];
    lrt_aabb b;
    for (int k = 0; k < 3; k++) {
        b.lo[k] = s->c[k] - s->r;
        b.hi[k] = s->c[k] + s->r;
    }
    return b;
}

static lrt_aabb inverted_bounds(unsigned i, void *user) {
    (void)i;
    (void)user;
    lrt_aabb b;
    b.lo[0] = 1.0; b.lo[1] = 1.0; b.lo[2] = 1.0;
    b.hi[0] = 0.0; b.hi[1] = 0.0; b.hi[2] = 0.0;
    return b;
}

static lrt_aabb synthetic_bounds(unsigned i, void *user) {
    const synthetic_data *sd = (const synthetic_data *)user;
    lrt_aabb b;
    for (int k = 0; k < 3; k++) {
        b.lo[k] = 0.0;
        b.hi[k] = 0.0;
    }

    switch (sd->kind) {
        case SYNTH_POINT_LEAF:
            b.lo[0] = b.hi[0] = (double)i;
            b.lo[1] = b.hi[1] = 0.0;
            b.lo[2] = b.hi[2] = 0.0;
            break;
        case SYNTH_POINT_LINE:
            b.lo[0] = b.hi[0] = (double)i;
            b.lo[1] = b.hi[1] = 0.0;
            b.lo[2] = b.hi[2] = 0.0;
            break;
        case SYNTH_SAME_POINT:
            break;
        case SYNTH_SAME_BOX:
            b.lo[0] = b.lo[1] = b.lo[2] = -1.0;
            b.hi[0] = b.hi[1] = b.hi[2] = 1.0;
            break;
        case SYNTH_COPLANAR_GRID: {
            double x = (double)(i % 4u);
            double y = (double)(i / 4u);
            b.lo[0] = x - 0.2; b.hi[0] = x + 0.2;
            b.lo[1] = y - 0.2; b.hi[1] = y + 0.2;
            b.lo[2] = 0.0;     b.hi[2] = 0.0;
            break;
        }
        case SYNTH_NAN_BOUNDS:
            b.lo[0] = NAN;
            b.hi[0] = 1.0;
            break;
        case SYNTH_INF_BOUNDS:
            b.lo[0] = -INFINITY;
            b.hi[0] = 1.0;
            break;
        case SYNTH_INVERTED_BOUNDS:
            b.lo[0] = 1.0;
            b.hi[0] = 0.0;
            break;
    }
    return b;
}

/* Nearest ray-sphere root in [tmin, tmax], full fp64. */
static int sphere_intersect(const double org[3], const double dir[3],
                            double tmin, double tmax, unsigned i, void *user,
                            double *t, double *u, double *v) {
    const scene_data *sd = (const scene_data *)user;
    const sphere *s = &sd->sph[i];
    double oc[3] = { org[0] - s->c[0], org[1] - s->c[1], org[2] - s->c[2] };
    double a = dir[0] * dir[0] + dir[1] * dir[1] + dir[2] * dir[2];
    double b = 2.0 * (oc[0] * dir[0] + oc[1] * dir[1] + oc[2] * dir[2]);
    double c = oc[0] * oc[0] + oc[1] * oc[1] + oc[2] * oc[2] - s->r * s->r;
    double disc = b * b - 4.0 * a * c;
    if (disc < 0.0) return 0;
    double sq = sqrt(disc);
    double t0 = (-b - sq) / (2.0 * a);
    double t1 = (-b + sq) / (2.0 * a);
    double hit = (t0 >= tmin && t0 <= tmax) ? t0
               : (t1 >= tmin && t1 <= tmax) ? t1
               : -1.0;
    if (hit < 0.0) return 0;
    *t = hit;
    *u = 0.0;
    *v = 0.0;
    return 1;
}

static int callback_intersect(const double org[3], const double dir[3],
                              double tmin, double tmax, unsigned i, void *user,
                              double *t, double *u, double *v) {
    callback_scene_data *sd = (callback_scene_data *)user;
    sd->calls++;
    switch (sd->mode) {
        case ISECT_NORMAL: {
            scene_data base = { sd->sph, sd->n };
            return sphere_intersect(org, dir, tmin, tmax, i, &base, t, u, v);
        }
        case ISECT_NEVER:
            return 0;
        case ISECT_NAN_T:
            *t = NAN; *u = 1.0; *v = 1.0;
            return 1;
        case ISECT_AFTER_TMAX:
            *t = tmax + 1.0; *u = 1.0; *v = 1.0;
            return 1;
        case ISECT_BEFORE_TMIN:
            *t = tmin - 1.0; *u = 1.0; *v = 1.0;
            return 1;
    }
    return 0;
}

/* Brute-force closest hit for cross-checking the BVH. */
static unsigned brute_force(const scene_data *sd, const double org[3],
                            const double dir[3], double tmin, double tmax,
                            double *out_t) {
    unsigned best = LRT_NO_HIT;
    double best_t = tmax;
    for (unsigned i = 0; i < sd->n; i++) {
        double t, u, v;
        if (sphere_intersect(org, dir, tmin, best_t, i, (void *)sd, &t, &u, &v) &&
            t < best_t) {
            best_t = t;
            best = i;
        }
    }
    if (best != LRT_NO_HIT) *out_t = best_t;
    return best;
}

static int never_intersect(const double org[3], const double dir[3],
                           double tmin, double tmax, unsigned i, void *user,
                           double *t, double *u, double *v) {
    (void)org; (void)dir; (void)tmin; (void)tmax; (void)i; (void)user;
    (void)t; (void)u; (void)v;
    return 0;
}

/* Deterministic LCG so the test is reproducible across platforms. */
static uint64_t g_seed = UINT64_C(0x12345678);
static double frand(void) {
    g_seed = g_seed * UINT64_C(6364136223846793005) +
             UINT64_C(1442695040888963407);
    return (double)((g_seed >> 33) & 0x7fffffff) / (double)0x7fffffff;
}
static double frange(double lo, double hi) { return lo + (hi - lo) * frand(); }

static int cancel_cb(void *user) {
    api_events *events = (api_events *)user;
    return events->cancel_now;
}

static void progress_cb(const lrt_progress *progress, void *user) {
    api_events *events = (api_events *)user;
    if (!progress || !progress->stage) return;
    if (progress->total != 0 &&
        (progress->fraction < -1e-12 || progress->fraction > 1.0 + 1e-12)) {
        fprintf(stderr, "invalid progress fraction for %s: %.17g\n",
                progress->stage, progress->fraction);
        exit(1);
    }
    events->progress_calls++;
}

static int run_synthetic_case(const char *label, unsigned nprims,
                              synthetic_kind kind, const lrt_options *options,
                              int expect_success, lrt_result expect_result) {
    synthetic_data sd = { kind };
    lrt_scene *scene = lrt_scene_create(nprims, synthetic_bounds,
                                        never_intersect, &sd);
    if (!scene) {
        fprintf(stderr, "%s: create failed\n", label);
        return 0;
    }
    if (!lrt_scene_set_options(scene, options)) {
        fprintf(stderr, "%s: set_options failed\n", label);
        lrt_scene_free(scene);
        return 0;
    }

    int ok = lrt_scene_build(scene);
    lrt_result got = lrt_scene_last_result(scene);
    if ((ok != 0) != (expect_success != 0) || got != expect_result) {
        fprintf(stderr, "%s: build=%d result=%d error=%s, expected build=%d result=%d\n",
                label, ok, (int)got, lrt_scene_last_error(scene),
                expect_success, (int)expect_result);
        lrt_scene_free(scene);
        return 0;
    }
    lrt_scene_free(scene);
    return 1;
}

static int run_invalid_intersect_case(const char *label, isect_mode mode) {
    sphere one = { { 0.0, 0.0, 0.0 }, 1.0 };
    callback_scene_data csd = { &one, 1, mode, 0 };
    lrt_scene *scene = lrt_scene_create(1, callback_bounds, callback_intersect, &csd);
    if (!scene) {
        fprintf(stderr, "%s: create failed\n", label);
        return 0;
    }
    if (!lrt_scene_build(scene)) {
        fprintf(stderr, "%s: build failed: %s\n", label, lrt_scene_last_error(scene));
        lrt_scene_free(scene);
        return 0;
    }

    double org[3] = { 0.0, 0.0, -4.0 };
    double dir[3] = { 0.0, 0.0, 1.0 };
    double t = 123.0, u = 456.0, v = 789.0;
    unsigned got = lrt_scene_intersect(scene, org, dir, 0.0, 100.0, &t, &u, &v);
    if (got != LRT_NO_HIT || lrt_scene_last_result(scene) != LRT_RESULT_OK ||
        t != 123.0 || u != 456.0 || v != 789.0 || csd.calls == 0) {
        fprintf(stderr, "%s: invalid callback hit was not ignored, got=%u result=%d error=%s\n",
                label, got, (int)lrt_scene_last_result(scene),
                lrt_scene_last_error(scene));
        lrt_scene_free(scene);
        return 0;
    }
    lrt_scene_free(scene);
    return 1;
}

int main(void) {
    const unsigned N = 2000;   /* spheres */
    const unsigned R = 20000;  /* rays */
    const double WORLD = 50.0;

    sphere *spheres = (sphere *)malloc(N * sizeof(sphere));
    for (unsigned i = 0; i < N; i++) {
        spheres[i].c[0] = frange(-WORLD, WORLD);
        spheres[i].c[1] = frange(-WORLD, WORLD);
        spheres[i].c[2] = frange(-WORLD, WORLD);
        spheres[i].r = frange(0.3, 2.0);
    }
    scene_data sd = { spheres, N };

    lrt_scene *scene = lrt_scene_create(N, sphere_bounds, sphere_intersect, &sd);
    if (!scene) { fprintf(stderr, "create failed\n"); return 1; }
    api_events events = { 0, 0 };
    lrt_options options;
    options.cancel_cb = cancel_cb;
    options.progress_cb = progress_cb;
    options.user = &events;
    options.progress_interval = 512;
    options.max_build_depth = 0;
    options.max_leaf_size = 0;

    if (lrt_scene_create(1, NULL, sphere_intersect, &sd) != NULL ||
        lrt_scene_create(1, sphere_bounds, NULL, &sd) != NULL) {
        fprintf(stderr, "create accepted NULL callbacks\n");
        return 1;
    }
    if (lrt_scene_set_options(NULL, &options) != 0 ||
        lrt_scene_last_result(NULL) != LRT_RESULT_INVALID_ARGUMENT ||
        lrt_scene_cancel_requested(NULL) != 0) {
        fprintf(stderr, "NULL scene API handling failed\n");
        return 1;
    }

    {
        lrt_scene *zero_scene = lrt_scene_create(0, sphere_bounds, sphere_intersect, &sd);
        if (!zero_scene) { fprintf(stderr, "zero scene create failed\n"); return 1; }
        if (lrt_scene_build(zero_scene) ||
            lrt_scene_last_result(zero_scene) != LRT_RESULT_INVALID_ARGUMENT) {
            fprintf(stderr, "zero-primitive build was not rejected: %s\n",
                    lrt_scene_last_error(zero_scene));
            return 1;
        }
        lrt_scene_free(zero_scene);
    }

    {
        lrt_scene *unbuilt_scene = lrt_scene_create(1, sphere_bounds, sphere_intersect, &sd);
        double org[3] = { 0.0, 0.0, -2.0 };
        double dir[3] = { 0.0, 0.0, 1.0 };
        if (!unbuilt_scene) { fprintf(stderr, "unbuilt scene create failed\n"); return 1; }
        if (lrt_scene_intersect(unbuilt_scene, org, dir, 0.0, 10.0, NULL, NULL, NULL) !=
                LRT_NO_HIT ||
            lrt_scene_last_result(unbuilt_scene) != LRT_RESULT_NOT_BUILT) {
            fprintf(stderr, "unbuilt query status mismatch: %s\n",
                    lrt_scene_last_error(unbuilt_scene));
            return 1;
        }
        lrt_scene_free(unbuilt_scene);
    }

    {
        lrt_scene *clear_scene = lrt_scene_create(1, sphere_bounds, sphere_intersect, &sd);
        if (!clear_scene) { fprintf(stderr, "clear scene create failed\n"); return 1; }
        events.cancel_now = 1;
        if (!lrt_scene_set_options(clear_scene, &options) ||
            !lrt_scene_set_options(clear_scene, NULL) ||
            !lrt_scene_build(clear_scene)) {
            fprintf(stderr, "clearing options did not disable cancel callback: %s\n",
                    lrt_scene_last_error(clear_scene));
            return 1;
        }
        lrt_scene_free(clear_scene);
        events.cancel_now = 0;
    }

    if (!lrt_scene_set_options(scene, &options)) {
        fprintf(stderr, "set_options failed\n");
        return 1;
    }
    if (!lrt_scene_build(scene)) { fprintf(stderr, "build failed\n"); return 1; }
    if (lrt_scene_last_result(scene) != LRT_RESULT_OK) {
        fprintf(stderr, "unexpected build status: %s\n", lrt_scene_last_error(scene));
        return 1;
    }
    if (events.progress_calls == 0) {
        fprintf(stderr, "progress callback was not called during build\n");
        return 1;
    }

    {
        lrt_options shallow_options = options;
        double org[3] = { 0.0, 0.0, -200.0 };
        double dir[3] = { 0.0, 0.0, 1.0 };
        shallow_options.max_build_depth = 1;
        if (!lrt_scene_set_options(scene, &shallow_options) ||
            lrt_scene_build(scene) ||
            lrt_scene_last_result(scene) != LRT_RESULT_BUILD_LIMIT) {
            fprintf(stderr, "rebuild failure did not report build limit: %s\n",
                    lrt_scene_last_error(scene));
            return 1;
        }
        if (lrt_scene_intersect(scene, org, dir, 0.0, 1e30, NULL, NULL, NULL) !=
                LRT_NO_HIT ||
            lrt_scene_last_result(scene) != LRT_RESULT_NOT_BUILT) {
            fprintf(stderr, "failed rebuild left scene queryable: %s\n",
                    lrt_scene_last_error(scene));
            return 1;
        }
        if (!lrt_scene_set_options(scene, &options) || !lrt_scene_build(scene)) {
            fprintf(stderr, "rebuild recovery failed: %s\n", lrt_scene_last_error(scene));
            return 1;
        }
    }

    events.cancel_now = 1;
    lrt_scene *cancel_scene = lrt_scene_create(N, sphere_bounds, sphere_intersect, &sd);
    if (!cancel_scene) { fprintf(stderr, "cancel scene create failed\n"); return 1; }
    if (!lrt_scene_set_options(cancel_scene, &options)) {
        fprintf(stderr, "cancel scene set_options failed\n");
        return 1;
    }
    if (lrt_scene_build(cancel_scene)) {
        fprintf(stderr, "cancelled build unexpectedly succeeded\n");
        return 1;
    }
    if (lrt_scene_last_result(cancel_scene) != LRT_RESULT_CANCELED ||
        !lrt_scene_cancel_requested(cancel_scene)) {
        fprintf(stderr, "cancelled build status mismatch: %s\n",
                lrt_scene_last_error(cancel_scene));
        return 1;
    }
    lrt_scene_free(cancel_scene);
    events.cancel_now = 0;

    {
        lrt_options shallow_options = options;
        shallow_options.max_build_depth = 1;
        lrt_scene *shallow_scene = lrt_scene_create(N, sphere_bounds, sphere_intersect, &sd);
        if (!shallow_scene) { fprintf(stderr, "shallow scene create failed\n"); return 1; }
        if (!lrt_scene_set_options(shallow_scene, &shallow_options)) {
            fprintf(stderr, "shallow scene set_options failed\n");
            return 1;
        }
        if (lrt_scene_build(shallow_scene) ||
            lrt_scene_last_result(shallow_scene) != LRT_RESULT_BUILD_LIMIT) {
            fprintf(stderr, "max-depth build limit was not reported: %s\n",
                    lrt_scene_last_error(shallow_scene));
            return 1;
        }
        lrt_scene_free(shallow_scene);
    }

    {
        sphere bad_spheres[8];
        for (unsigned i = 0; i < 8; i++) {
            bad_spheres[i].c[0] = 0.0;
            bad_spheres[i].c[1] = 0.0;
            bad_spheres[i].c[2] = 0.0;
            bad_spheres[i].r = 1.0;
        }
        scene_data bad_sd = { bad_spheres, 8 };
        lrt_scene *bad_scene = lrt_scene_create(8, sphere_bounds, sphere_intersect, &bad_sd);
        if (!bad_scene) { fprintf(stderr, "bad scene create failed\n"); return 1; }
        if (!lrt_scene_set_options(bad_scene, &options)) {
            fprintf(stderr, "bad scene set_options failed\n");
            return 1;
        }
        if (lrt_scene_build(bad_scene) ||
            lrt_scene_last_result(bad_scene) != LRT_RESULT_BUILD_LIMIT) {
            fprintf(stderr, "oversized leaf build limit was not reported: %s\n",
                    lrt_scene_last_error(bad_scene));
            return 1;
        }
        lrt_scene_free(bad_scene);
    }

    {
        lrt_scene *invalid_scene = lrt_scene_create(1, inverted_bounds,
                                                    sphere_intersect, &sd);
        if (!invalid_scene) { fprintf(stderr, "invalid scene create failed\n"); return 1; }
        if (!lrt_scene_set_options(invalid_scene, &options)) {
            fprintf(stderr, "invalid scene set_options failed\n");
            return 1;
        }
        if (lrt_scene_build(invalid_scene) ||
            lrt_scene_last_result(invalid_scene) != LRT_RESULT_INVALID_BOUNDS) {
            fprintf(stderr, "invalid bounds were not reported: %s\n",
                    lrt_scene_last_error(invalid_scene));
            return 1;
        }
        lrt_scene_free(invalid_scene);
    }

    if (!run_synthetic_case("degenerate point leaf accepted", 4,
                            SYNTH_POINT_LEAF, &options, 1, LRT_RESULT_OK)) {
        return 1;
    }
    if (!run_synthetic_case("degenerate point line reports build limit", 8,
                            SYNTH_POINT_LINE, &options, 0, LRT_RESULT_BUILD_LIMIT)) {
        return 1;
    }
    if (!run_synthetic_case("all vertices same position reports build limit", 8,
                            SYNTH_SAME_POINT, &options, 0, LRT_RESULT_BUILD_LIMIT)) {
        return 1;
    }
    if (!run_synthetic_case("duplicate-index equivalent reports build limit", 8,
                            SYNTH_SAME_BOX, &options, 0, LRT_RESULT_BUILD_LIMIT)) {
        return 1;
    }
    if (!run_synthetic_case("coplanar finite grid accepted", 16,
                            SYNTH_COPLANAR_GRID, &options, 1, LRT_RESULT_OK)) {
        return 1;
    }
    if (!run_synthetic_case("nan bounds rejected", 1,
                            SYNTH_NAN_BOUNDS, &options, 0, LRT_RESULT_INVALID_BOUNDS)) {
        return 1;
    }
    if (!run_synthetic_case("inf bounds rejected", 1,
                            SYNTH_INF_BOUNDS, &options, 0, LRT_RESULT_INVALID_BOUNDS)) {
        return 1;
    }
    if (!run_synthetic_case("inverted bounds rejected", 1,
                            SYNTH_INVERTED_BOUNDS, &options, 0, LRT_RESULT_INVALID_BOUNDS)) {
        return 1;
    }

    if (!run_invalid_intersect_case("nan callback t ignored", ISECT_NAN_T) ||
        !run_invalid_intersect_case("after-tmax callback t ignored", ISECT_AFTER_TMAX) ||
        !run_invalid_intersect_case("before-tmin callback t ignored", ISECT_BEFORE_TMIN)) {
        return 1;
    }

    {
        sphere one = { { 0.0, 0.0, 0.0 }, 1.0 };
        scene_data one_sd = { &one, 1 };
        lrt_scene *one_scene = lrt_scene_create(1, sphere_bounds, sphere_intersect, &one_sd);
        double org[3] = { 0.0, 0.0, -4.0 };
        double dir[3] = { 0.0, 0.0, 1.0 };
        double bad_org[3] = { NAN, 0.0, -4.0 };
        if (!one_scene) { fprintf(stderr, "one scene create failed\n"); return 1; }
        if (!lrt_scene_build(one_scene)) {
            fprintf(stderr, "one scene build failed: %s\n", lrt_scene_last_error(one_scene));
            return 1;
        }
        if (lrt_scene_intersect(one_scene, org, dir, 0.0, 100.0,
                                NULL, NULL, NULL) != 0 ||
            lrt_scene_last_result(one_scene) != LRT_RESULT_OK) {
            fprintf(stderr, "null output closest-hit query failed: %s\n",
                    lrt_scene_last_error(one_scene));
            return 1;
        }
        if (lrt_scene_intersect(one_scene, org, dir, 10.0, 1.0,
                                NULL, NULL, NULL) != LRT_NO_HIT ||
            lrt_scene_last_result(one_scene) != LRT_RESULT_INVALID_ARGUMENT) {
            fprintf(stderr, "invalid t range was not rejected\n");
            return 1;
        }
        if (lrt_scene_intersect(one_scene, bad_org, dir, 0.0, 100.0,
                                NULL, NULL, NULL) != LRT_NO_HIT ||
            lrt_scene_last_result(one_scene) != LRT_RESULT_INVALID_ARGUMENT) {
            fprintf(stderr, "NaN ray origin was not rejected\n");
            return 1;
        }
        lrt_scene_free(one_scene);
    }

    {
        double org[3] = { 0.0, 0.0, -200.0 };
        double dir[3] = { 0.0, 0.0, 1.0 };
        double t = 0.0, u = 0.0, v = 0.0;
        unsigned before_progress = events.progress_calls;
        lrt_scene_request_cancel(scene);
        if (lrt_scene_intersect(scene, org, dir, 1e-4, 1e30, &t, &u, &v) != LRT_NO_HIT ||
            lrt_scene_last_result(scene) != LRT_RESULT_CANCELED) {
            fprintf(stderr, "requested-cancel intersect failed: %s\n",
                    lrt_scene_last_error(scene));
            return 1;
        }
        lrt_scene_clear_cancel(scene);
        if (lrt_scene_cancel_requested(scene)) {
            fprintf(stderr, "clear_cancel failed\n");
            return 1;
        }
        if (lrt_scene_intersect(scene, org, dir, 1e-4, 1e30, &t, &u, &v) == LRT_NO_HIT &&
            lrt_scene_last_result(scene) != LRT_RESULT_OK) {
            fprintf(stderr, "post-cancel intersect failed: %s\n",
                    lrt_scene_last_error(scene));
            return 1;
        }
        if (events.progress_calls == before_progress) {
            fprintf(stderr, "progress callback was not called during intersect\n");
            return 1;
        }
        dir[2] = 0.0;
        if (lrt_scene_intersect(scene, org, dir, 1e-4, 1e30, &t, &u, &v) != LRT_NO_HIT ||
            lrt_scene_last_result(scene) != LRT_RESULT_INVALID_ARGUMENT) {
            fprintf(stderr, "invalid ray was not rejected\n");
            return 1;
        }
    }

    printf("backend: %s\n", lrt_backend_name());
    printf("scene:   %u spheres, %u rays\n", N, R);

    unsigned mismatches = 0, hits = 0;
    double max_t_err = 0.0;
    for (unsigned r = 0; r < R; r++) {
        double org[3] = { frange(-WORLD, WORLD), frange(-WORLD, WORLD),
                          frange(-WORLD, WORLD) };
        double dir[3] = { frange(-1, 1), frange(-1, 1), frange(-1, 1) };
        double len = sqrt(dir[0] * dir[0] + dir[1] * dir[1] + dir[2] * dir[2]);
        if (len < 1e-9) continue;
        dir[0] /= len; dir[1] /= len; dir[2] /= len;
        double tmin = 1e-4, tmax = 1e30;

        double bt = 0.0;
        unsigned bf = brute_force(&sd, org, dir, tmin, tmax, &bt);

        double t = 0.0, u = 0.0, v = 0.0;
        unsigned got = lrt_scene_intersect(scene, org, dir, tmin, tmax, &t, &u, &v);

        if (got != bf) {
            /* Tie / fp32-broadphase edge: accept if the t values agree. */
            if (got != LRT_NO_HIT && bf != LRT_NO_HIT &&
                fabs(t - bt) <= 1e-4 * (1.0 + fabs(bt))) {
                /* acceptable: two surfaces at (near) identical distance */
            } else {
                if (mismatches < 10) {
                    fprintf(stderr,
                            "MISMATCH ray %u: bvh=%u (t=%.9g) bf=%u (t=%.9g)\n",
                            r, got, t, bf, bt);
                }
                mismatches++;
            }
        } else if (got != LRT_NO_HIT) {
            hits++;
            double e = fabs(t - bt);
            if (e > max_t_err) max_t_err = e;
        }
    }

    printf("hits:    %u / %u rays\n", hits, R);
    printf("max |t_bvh - t_bf| on agreeing hits: %.3e\n", max_t_err);
    printf("mismatches: %u\n", mismatches);

    lrt_scene_free(scene);
    free(spheres);

    if (mismatches != 0) { printf("RESULT: FAIL\n"); return 1; }
    printf("RESULT: PASS\n");
    return 0;
}
