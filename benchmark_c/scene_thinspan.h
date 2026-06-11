/*
 * scene_thinspan.h — synthetic pathological scene: long, thin triangles
 * spanning the scene diagonally. The worst case for object-split BVHs (every
 * primitive's AABB covers a large diagonal slab of the scene, so child boxes
 * overlap massively) and the showcase for spatial splits (SBVH), which chop
 * the references into short segments.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LRTBENCH_SCENE_THINSPAN_H
#define LRTBENCH_SCENE_THINSPAN_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Generate ntris hair-like triangles inside the [-1.6, 1.6]^3 cube: each is a
 * thin sliver of width `thickness` (default 0.002 when <= 0) along a random
 * diagonal direction, of length `span` * cube diagonal (default 0.25 when
 * <= 0; span >= 1 approaches full corner-to-corner hairs). Deterministic from
 * `seed`. Returns ntris and stores a malloc'd 9*ntris float array in
 * *out_verts (caller frees); 0 on failure. */
size_t scene_thinspan_generate(size_t ntris, float thickness, float span,
                               uint32_t seed, float **out_verts);

#define THINSPAN_BOUND 1.6f

#ifdef __cplusplus
}
#endif

#endif /* LRTBENCH_SCENE_THINSPAN_H */
