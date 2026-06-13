/*
 * furball.h — procedural fur/hair generator (no data file needed).
 *
 * Grows curly strands outward from a sphere, à la Embree's curve/hair tutorials,
 * and fills a cyhair_t (the same struct the CyHair loader produces) so the
 * generated fur feeds every curve/point builder in hair_bench.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LRTBENCH_FURBALL_H
#define LRTBENCH_FURBALL_H

#include <stddef.h>
#include <stdint.h>

#include "cyhair.h" /* cyhair_t */

#ifdef __cplusplus
extern "C" {
#endif

/* Generate `nstrands` curly strands, each with `segs` segments (segs+1 points),
 * rooted on a unit sphere and tapering from root_radius to ~0 at the tip.
 * radius_scale multiplies the radius (matches the loader's knob). Returns 0 on
 * success (caller owns *out -> cyhair_free), negative on error. */
int furball_generate(size_t nstrands, int segs, float root_radius,
                     float radius_scale, uint32_t seed, cyhair_t *out);

#ifdef __cplusplus
}
#endif

#endif /* LRTBENCH_FURBALL_H */
