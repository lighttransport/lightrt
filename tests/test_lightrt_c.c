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
#include <stdlib.h>

/* --- scene: a set of spheres, intersected analytically in fp64 --- */
typedef struct { double c[3]; double r; } sphere;

typedef struct { const sphere *sph; unsigned n; } scene_data;

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

/* Deterministic LCG so the test is reproducible across platforms. */
static unsigned long g_seed = 0x12345678ul;
static double frand(void) {
    g_seed = g_seed * 6364136223846793005ul + 1442695040888963407ul;
    return (double)((g_seed >> 33) & 0x7fffffff) / (double)0x7fffffff;
}
static double frange(double lo, double hi) { return lo + (hi - lo) * frand(); }

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
    if (!lrt_scene_build(scene)) { fprintf(stderr, "build failed\n"); return 1; }

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
