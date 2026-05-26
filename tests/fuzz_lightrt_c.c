/*
 * fuzz_lightrt_c.c - libFuzzer harness for the pure-C11 lightrt_c.c API.
 *
 * Build manually:
 *   clang -std=c11 -O1 -g -fsanitize=fuzzer,address,undefined \
 *     lightrt_c.c tests/fuzz_lightrt_c.c -I. -lm -o fuzz_lightrt_c
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "../lightrt_c.h"

#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define FUZZ_MAX_PRIMS 64u
#define FUZZ_MAX_RAYS 16u

typedef struct {
    lrt_aabb bounds[FUZZ_MAX_PRIMS];
    unsigned nprims;
    unsigned callback_mode;
    unsigned cancel_after;
    unsigned cancel_checks;
    unsigned progress_calls;
} fuzz_scene;

static uint8_t fuzz_u8(const uint8_t **data, size_t *size) {
    if (*size == 0) return 0;
    uint8_t v = **data;
    (*data)++;
    (*size)--;
    return v;
}

static uint32_t fuzz_u32(const uint8_t **data, size_t *size) {
    uint32_t v = 0;
    for (int i = 0; i < 4; i++) {
        v |= (uint32_t)fuzz_u8(data, size) << (8 * i);
    }
    return v;
}

static double fuzz_coord(const uint8_t **data, size_t *size) {
    int32_t raw = (int32_t)(fuzz_u32(data, size) & 0xffffu) - 32768;
    return (double)raw / 256.0;
}

static lrt_aabb make_bounds(const uint8_t **data, size_t *size,
                            unsigned kind, unsigned prim) {
    lrt_aabb b;
    for (int k = 0; k < 3; k++) {
        b.lo[k] = 0.0;
        b.hi[k] = 0.0;
    }

    switch (kind % 10u) {
        case 0: { /* ordinary finite box */
            double x = fuzz_coord(data, size);
            double y = fuzz_coord(data, size);
            double z = fuzz_coord(data, size);
            double ex = (double)(fuzz_u8(data, size) & 31u) / 16.0;
            double ey = (double)(fuzz_u8(data, size) & 31u) / 16.0;
            double ez = (double)(fuzz_u8(data, size) & 31u) / 16.0;
            b.lo[0] = x;      b.hi[0] = x + ex;
            b.lo[1] = y;      b.hi[1] = y + ey;
            b.lo[2] = z;      b.hi[2] = z + ez;
            break;
        }
        case 1: /* degenerate point, distinct x */
            b.lo[0] = b.hi[0] = (double)prim;
            break;
        case 2: /* all primitives share one vertex position */
            break;
        case 3: /* all primitive indices effectively refer to same bounds */
            b.lo[0] = b.lo[1] = b.lo[2] = -1.0;
            b.hi[0] = b.hi[1] = b.hi[2] = 1.0;
            break;
        case 4: { /* coplanar finite box grid */
            double x = (double)(prim % 8u);
            double y = (double)(prim / 8u);
            b.lo[0] = x - 0.25; b.hi[0] = x + 0.25;
            b.lo[1] = y - 0.25; b.hi[1] = y + 0.25;
            b.lo[2] = 0.0;      b.hi[2] = 0.0;
            break;
        }
        case 5: /* line-like boxes */
            b.lo[0] = (double)prim;
            b.hi[0] = (double)prim + 0.125;
            break;
        case 6: /* inverted */
            b.lo[0] = 1.0; b.hi[0] = 0.0;
            break;
        case 7: /* NaN */
            b.lo[0] = NAN; b.hi[0] = 1.0;
            break;
        case 8: /* infinity */
            b.lo[0] = -INFINITY; b.hi[0] = 1.0;
            break;
        case 9: /* very thin but finite */
            b.lo[0] = fuzz_coord(data, size);
            b.hi[0] = b.lo[0] + 1e-12;
            b.lo[1] = fuzz_coord(data, size);
            b.hi[1] = b.lo[1] + 1e-12;
            b.lo[2] = fuzz_coord(data, size);
            b.hi[2] = b.lo[2] + 1e-12;
            break;
    }
    return b;
}

static lrt_aabb fuzz_bounds(unsigned prim, void *user) {
    fuzz_scene *scene = (fuzz_scene *)user;
    if (prim >= scene->nprims) {
        lrt_aabb empty = {{1.0, 1.0, 1.0}, {0.0, 0.0, 0.0}};
        return empty;
    }
    return scene->bounds[prim];
}

static int aabb_hit(const lrt_aabb *b, const double org[3], const double dir[3],
                    double tmin, double tmax, double *out_t) {
    double near_t = tmin;
    double far_t = tmax;
    for (int k = 0; k < 3; k++) {
        if (dir[k] == 0.0) {
            if (org[k] < b->lo[k] || org[k] > b->hi[k]) return 0;
            continue;
        }
        double inv = 1.0 / dir[k];
        double t0 = (b->lo[k] - org[k]) * inv;
        double t1 = (b->hi[k] - org[k]) * inv;
        if (t0 > t1) {
            double tmp = t0;
            t0 = t1;
            t1 = tmp;
        }
        if (t0 > near_t) near_t = t0;
        if (t1 < far_t) far_t = t1;
        if (far_t < near_t) return 0;
    }
    *out_t = near_t;
    return 1;
}

static int fuzz_intersect(const double org[3], const double dir[3],
                          double tmin, double tmax, unsigned prim, void *user,
                          double *t, double *u, double *v) {
    fuzz_scene *scene = (fuzz_scene *)user;
    if (prim >= scene->nprims) return 0;
    if (scene->callback_mode == 1u) return 0;
    if (scene->callback_mode == 2u) {
        *t = NAN; *u = 0.0; *v = 0.0;
        return 1;
    }
    if (scene->callback_mode == 3u) {
        *t = tmax + 1.0; *u = 0.0; *v = 0.0;
        return 1;
    }

    if (!aabb_hit(&scene->bounds[prim], org, dir, tmin, tmax, t)) return 0;
    *u = 0.0;
    *v = 0.0;
    return 1;
}

static int fuzz_cancel(void *user) {
    fuzz_scene *scene = (fuzz_scene *)user;
    scene->cancel_checks++;
    return scene->cancel_after != 0 && scene->cancel_checks >= scene->cancel_after;
}

static void fuzz_progress(const lrt_progress *progress, void *user) {
    fuzz_scene *scene = (fuzz_scene *)user;
    if (!progress || !progress->stage) abort();
    if (progress->total != 0 &&
        (progress->fraction < -1e-12 || progress->fraction > 1.0 + 1e-12)) {
        abort();
    }
    scene->progress_calls++;
}

static unsigned brute_force(const fuzz_scene *scene, const double org[3],
                            const double dir[3], double tmin, double tmax,
                            double *out_t) {
    unsigned best = LRT_NO_HIT;
    double best_t = tmax;
    for (unsigned i = 0; i < scene->nprims; i++) {
        double t = 0.0;
        if (aabb_hit(&scene->bounds[i], org, dir, tmin, best_t, &t) && t < best_t) {
            best_t = t;
            best = i;
        }
    }
    if (best != LRT_NO_HIT) *out_t = best_t;
    return best;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < 4) return 0;

    fuzz_scene scene;
    memset(&scene, 0, sizeof(scene));
    scene.nprims = (unsigned)(fuzz_u8(&data, &size) % FUZZ_MAX_PRIMS) + 1u;
    unsigned kind = fuzz_u8(&data, &size);
    scene.callback_mode = fuzz_u8(&data, &size) % 4u;
    scene.cancel_after = (fuzz_u8(&data, &size) & 7u) == 0u
        ? (unsigned)(fuzz_u8(&data, &size) % 8u)
        : 0u;

    for (unsigned i = 0; i < scene.nprims; i++) {
        scene.bounds[i] = make_bounds(&data, &size, kind, i);
    }

    lrt_scene *lrt = lrt_scene_create(scene.nprims, fuzz_bounds,
                                      fuzz_intersect, &scene);
    if (!lrt) abort();

    lrt_options options;
    memset(&options, 0, sizeof(options));
    options.cancel_cb = fuzz_cancel;
    options.progress_cb = fuzz_progress;
    options.user = &scene;
    options.progress_interval = (size_t)(fuzz_u8(&data, &size) % 8u);
    options.max_build_depth = (unsigned)(fuzz_u8(&data, &size) % 16u);
    options.max_leaf_size = (unsigned)(fuzz_u8(&data, &size) % 9u);
    if (!lrt_scene_set_options(lrt, &options)) abort();

    int built = lrt_scene_build(lrt);
    lrt_result build_result = lrt_scene_last_result(lrt);
    if (!built) {
        if (build_result == LRT_RESULT_OK) abort();
        lrt_scene_free(lrt);
        return 0;
    }
    if (build_result != LRT_RESULT_OK) abort();

    unsigned nrays = (unsigned)(fuzz_u8(&data, &size) % FUZZ_MAX_RAYS) + 1u;
    for (unsigned r = 0; r < nrays; r++) {
        double org[3] = {
            fuzz_coord(&data, &size),
            fuzz_coord(&data, &size),
            fuzz_coord(&data, &size)
        };
        double dir[3] = {
            fuzz_coord(&data, &size),
            fuzz_coord(&data, &size),
            fuzz_coord(&data, &size)
        };
        if (dir[0] == 0.0 && dir[1] == 0.0 && dir[2] == 0.0) {
            dir[0] = 1.0;
        }
        double tmin = 0.0;
        double tmax = 1024.0;
        double t = 0.0, u = 0.0, v = 0.0;
        unsigned got = lrt_scene_intersect(lrt, org, dir, tmin, tmax, &t, &u, &v);
        lrt_result query_result = lrt_scene_last_result(lrt);
        if (query_result == LRT_RESULT_CANCELED) break;
        if (query_result != LRT_RESULT_OK) abort();
        if (got != LRT_NO_HIT && (!isfinite(t) || t < tmin || t > tmax)) abort();

        if (scene.callback_mode == 0u) {
            double brute_t = 0.0;
            unsigned brute = brute_force(&scene, org, dir, tmin, tmax, &brute_t);
            if (brute != LRT_NO_HIT &&
                (brute_t <= tmin + 1e-5 || brute_t >= tmax - 1e-5)) {
                continue;
            }
            if (got == LRT_NO_HIT && brute != LRT_NO_HIT) abort();
            if (got != LRT_NO_HIT && brute == LRT_NO_HIT) abort();
            if (got != LRT_NO_HIT && fabs(t - brute_t) > 1e-5 * (1.0 + fabs(brute_t))) {
                abort();
            }
        }
    }

    lrt_scene_free(lrt);
    return 0;
}
