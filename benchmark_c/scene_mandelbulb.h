/*
 * scene_mandelbulb.h — procedural mandelbulb triangle-soup generation (C11).
 *
 * Marching-cubes mesh of the power-N mandelbulb distance estimator, ported
 * from viewer_x11/viewer_x11.cc so offline benchmarks reproduce the viewer's
 * benchmark-mode geometry exactly (same DE, same bounds, same tables).
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LRTBENCH_SCENE_MANDELBULB_H
#define LRTBENCH_SCENE_MANDELBULB_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Generate the mandelbulb mesh. fineness = marching-cubes grid resolution
 * (viewer uses 16..256), power = mandelbulb exponent (viewer uses 8).
 * On success returns the triangle count and stores a malloc'd array of
 * 9*ntris floats (v0 v1 v2 per triangle) in *out_verts; caller frees.
 * Returns 0 with *out_verts = NULL on failure. */
size_t scene_mandelbulb_generate(int fineness, int power, float **out_verts);

/* Scene bounds used for generation: [-1.6, 1.6]^3 (matches the viewer). */
#define MANDELBULB_BOUND 1.6f

#ifdef __cplusplus
}
#endif

#endif /* LRTBENCH_SCENE_MANDELBULB_H */
