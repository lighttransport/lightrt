/*
 * cyhair.h — zero-dependency loader for Cem Yuksel's CyHair (.hair) binary
 * format (https://www.cemyuksel.com/research/hairmodels/).
 *
 * Each hair strand is a polyline of points with an optional per-point thickness.
 * The loader returns the points, a per-point radius (= 0.5 * thickness *
 * radius_scale), and per-strand offsets so the geometry can be turned into
 * round-linear curve segments (see lrt_roundcurve_scene_build).
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LRTBENCH_CYHAIR_H
#define LRTBENCH_CYHAIR_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct cyhair_t {
    float *points;          /* 3*npoints xyz */
    float *radius;          /* npoints */
    uint32_t *strand_first; /* nstrands: first point index of each strand */
    uint32_t *strand_count; /* nstrands: points per strand (>= 2) */
    size_t nstrands;
    size_t npoints;
    size_t nsegments;       /* sum of (strand_count - 1) */
    float bbox_min[3];
    float bbox_max[3];
} cyhair_t;

/* Load a CyHair file. radius_scale (>0; <=0 treated as 1) multiplies the
 * per-point radius. Returns 0 on success (caller owns *out -> cyhair_free), or a
 * negative error code:
 *   -1 open/arg error, -2 short read, -3 bad "HAIR" signature,
 *   -4 empty, -5 no points array, -6 point-count mismatch, -10 out of memory. */
int cyhair_load(const char *path, float radius_scale, cyhair_t *out);

void cyhair_free(cyhair_t *h);

#ifdef __cplusplus
}
#endif

#endif /* LRTBENCH_CYHAIR_H */
