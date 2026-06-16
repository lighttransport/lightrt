/*
 * rays.h — deterministic ray-workload generators for the C benchmark harness.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LRTBENCH_RAYS_H
#define LRTBENCH_RAYS_H

#include <stddef.h>
#include <stdint.h>

#include "../lightrt_c_tri.h" /* lrt_ray / lrt_hit */

#ifdef __cplusplus
extern "C" {
#endif

/* Coherent primary rays: pinhole camera at (2.5,2.5,2.5) looking at the
 * origin, 60-degree vertical FOV, emitted in Morton (Z-curve) pixel order over
 * a side x side image where side = ceil(sqrt(n)). */
void rays_gen_primary(lrt_ray *rays, size_t n, uint32_t seed);

/* Incoherent rays: port of the viewer benchmark's runBenchmarkMeasurement —
 * pcg-hash origins on a radius-5 sphere, directions toward the center with
 * spread, tmin = 1e-6, tmax = 1e10. seed offsets the hash stream. */
void rays_gen_incoherent(lrt_ray *rays, size_t n, uint32_t seed);

/* Shadow rays derived from primary-hit surface points: for each primary ray i
 * with hits[i].prim_id != LRT_TRI_NO_HIT, a ray from the hit point (offset by
 * eps along the geometric normal facing the light) toward the point light at
 * (4, 6, 4), with tmax just short of the light. Misses are replaced by rays
 * re-aimed from the light into the scene so every slot stays a useful ray.
 * vertices = the scene triangle soup (for normals). Returns the count written
 * (== n). */
size_t rays_gen_shadow(lrt_ray *rays, size_t n, const lrt_ray *primary,
                       const lrt_hit *hits, const float *vertices,
                       size_t ntris, uint32_t seed);

#ifdef __cplusplus
}
#endif

#endif /* LRTBENCH_RAYS_H */
