# lightrt-c Edge-Case Testing

## Overview

The test file `tests/test_lightrt_c_tri.c` (5444 lines) has comprehensive
correctness tests with brute-force oracles, plus extensive edge-case coverage.
All 26 sections from the original test plan have been implemented.

### Coverage Summary

| Section | Test function | Status |
|---------|--------------|--------|
| §1 Quantized Triangle | `test_qtri()` | ✓ |
| §2 Quantized Nodes | `test_qnodes()` | ✓ |
| §3 TLAS | `test_tlas()` | ✓ |
| §4 Refit | `test_refit()` | ✓ |
| §5 Serialization | `test_serialization()` | ✓ |
| §6 SDF | `test_sdf_standalone()`, `test_sdf_scene()` | ✓ |
| §7 Batched Queries | `test_batch_matches_single()` | ✓ |
| §8 Packets | `test_packets()` | ✓ |
| §9 Any-hit Filter | `test_anyhit_filter()` | ✓ |
| §10 Scene Stats | `test_stats()` | ✓ |
| §11 Kernel Name | `test_kernel_name()` | ✓ |
| §12 Curve Edge Cases | `test_hair_edge_cases()`, `test_curve_edge_cases()` | ✓ |
| §13 Points Edge Cases | `test_curve_point_edge_cases()`, `test_point_edge_cases()` | ✓ |
| §14 User Geometry | `test_user_geometry()`, `test_user_geometry_edge_cases()` | ✓ |
| §15 Sphere Scene | `test_sphere_scene()`, `test_sphere_edge_cases()` | ✓ |
| §16 Triangle Edge Cases | `test_tri_edge_cases()` | ✓ |
| §17 Multi-hit | `test_multihit()` | ✓ |
| §18 KNN | `test_closest_point_knn()` | ✓ |
| §19 Closest Point | `test_closest_point_knn()` | ✓ |
| §20 Region Query | `test_region_queries()`, `test_region_query_edge_cases()` | ✓ |
| §21 Parallel Build | `test_parallel_build()` | ✓ |
| §22 Build Options | `test_build_options()` | ✓ |
| §23 NULL/Empty | `test_null_inputs()` | ✓ |
| §24 FP Precision | `test_fp_precision()` | ✓ |
| §25 Thread Safety | `test_thread_safety()` | ✓ |
| §26 TLAS Edge Cases | `test_tlas_edge_cases()` | ✓ |

### New Tests Added (2026-06)

**Round 1** (13 new functions, ~1024 lines):
- `test_null_inputs()` — §23: NULL vertices, ntris=0, overflow guard, NULL scene/ray/hit, NULL free/save/load/mmap, truncated buffer
- `test_batch_edge_cases()` — §7: n=0 batch, NULL hit/ray buffers, tmin>tmax, identical rays
- `test_stats()` — §10: 1-triangle stats, 2-triangle stats, BVH4/BVH8 consistency
- `test_kernel_name()` — §11: BVH4/BVH8/BVH8Q kernel name strings
- `test_user_geometry_edge_cases()` — §14: NULL callback, NaN AABB, inverted AABB, always-hit/miss
- `test_sphere_scene_edge_cases()` — §15: NaN/Inf center, mixed valid/invalid radii
- `test_triangle_intersection_edge_cases()` — §16: vertex at origin, INF vertex, degenerate edge
- `test_multihit_edge_cases()` — §17: max_hits=0/1/>, capped at scene size
- `test_closest_point_edge_cases()` — §19: centroid query, edge query, far query
- `test_region_query_edge_cases()` — §20: zero-volume AABB, zero/Inf radius sphere, NaN center
- `test_build_options()` — §22: max_leaf_size=0/1/INT_MAX, num_threads=0/1
- `test_fp_precision()` — §24: tmin/tmax=1e38/1e-38, denormalized coords, subnormal origin
- `test_tlas_edge_cases()` — §26: 1 BLAS/1 instance, 2 BLASes closest, refit zero transforms

**Round 2** (4 new functions, ~500 lines):
- `test_parallel_build()` — §21: 100-tri/4t, 4096-tri/4t, 100k-tri/8t, FAST LBVH, HQ SBVH
- `test_curve_edge_cases()` — §12: extreme-length capsule, Inf/NaN radius, zero-length segment, large roundcurve radius, zero-width ribbon
- `test_point_edge_cases()` — §13: Inf/NaN sphere radius, zero/Inf disc radius, zero-length normal
- `test_thread_safety()` — §25: 4 threads × 1000 intersect1, 4 threads × 100× intersect1N(4)

---

## 1. Quantized Triangle (`lrt_qtri_scene_build`)

### 1.1 All-zero / degenerate quantized triangles
- Build a scene of 10 all-zero triangles (all vertices at origin).
- **Q16 (near-lossless)**: should build, never hit.
- **Q8/FP8/FP4**: may build or reject — at least no crash.

### 1.2 Quantized triangle with NaN/Inf vertices
- Build with one NaN vertex → should reject with `INVALID_BOUNDS`.
- Build with one Inf vertex → should reject with `INVALID_BOUNDS`.

### 1.3 Quantized triangle with extremely large extents
- Build 1 triangle spanning [-1e5, 1e5]^3 with Q16 → should build and hit.
- Same with Q4 → may have precision loss but should not crash.

### 1.4 Quantized triangle with extremely small extents
- Build 1 triangle with 1e-7 extent → may build or reject.
- Same with CONSERVATIVE flag → should not miss a transverse ray.

### 1.5 Quantized scene refit rejection
- Build a Q16 scene, attempt refit → should return `INVALID_ARGUMENT`
  (quantized scenes don't support refit).

### 1.6 Quantized scene serialization rejection
- Build a Q8 scene, attempt save → should return `INVALID_ARGUMENT`
  (quantized scenes don't serialize).

### 1.7 Quantized triangle single-triangle traversal
- Build 1 triangle with each format (Q16/Q8/FP8/FP4) × LOSSY/CONSERVATIVE.
- Ray through center → should hit.
- Ray far away → should miss.

---

## 2. Quantized Nodes (BVH8_Q4 / BVH8_QF8)

### 2.1 Single-triangle BVH8_Q4 / BVH8_QF8
- Build 1 triangle with BVH8_Q4 → ray through center should hit.
- Build 1 triangle with BVH8_QF8 → ray through center should hit.
- Verify t within tolerance (quantization adds ~0.1% error).

### 2.2 Quantized node bounds with extreme aspect ratio
- Build 1 very thin triangle (100 units long, 0.001 wide) with BVH8_Q4.
- Ray through the thin dimension → should hit (quantized bounds still cull well).

### 2.3 Quantized node bounds with extreme bounding box
- Build 1 triangle spanning [-1e5, 1e5]^3 with BVH8_Q4.
- Ray through center → should hit (quantized bounds may be loose but correct).

---

## 3. TLAS (Top-Level Acceleration Structure)

### 3.1 Empty TLAS (zero instances)
- Build TLAS with 0 instances → should succeed.
- Any ray query → should miss (no geometry).

### 3.2 TLAS with zero BLAS count
- Build TLAS with `nblas=0` → should return NULL with INVALID_ARGUMENT.

### 3.3 TLAS with BLAS NULL
- Pass a NULL pointer in `blas[]` array → should reject.

### 3.4 TLAS with invalid blas_id (out of range)
- Build TLAS with 2 BLASes, then reference blas_id=5 → should reject.

### 3.5 TLAS with near-singular transform
- Build instance with near-singular transform (determinant ≈ 0) → should be
  skipped silently, not crash.

### 3.6 TLAS with mask=0 (fully hidden instance)
- Build 1 instance with mask=0 → ray should miss (instance invisible).

### 3.7 TLAS with mask=0x00000001 (selective visibility)
- Build 2 instances, ray_mask=0x00000001 → only instance 0 visible.
- Ray should hit instance 0's geometry, not instance 1's.

### 3.8 TLAS refit with invalid instance count
- Build TLAS with 2 instances, then refit with 3 → should reject.

### 3.9 TLAS with identity transform
- Build instance with identity transform → ray should hit same as untransformed.

### 3.10 TLAS with negative scale transform
- Build instance with -1 scale on x → ray should hit mirrored geometry.

---

## 4. Refit Edge Cases

### 4.1 Refit with all-zero vertices
- Build scene with 100 triangles, refit with all-zero → should succeed
  (degenerate triangles are valid).

### 4.2 Refit with swapped vertices (same points, different order)
- Build scene, refit with same vertices but permuted → should succeed.
- Hit results may differ (BVH structure preserved, triangle data same).

### 4.3 Refit that collapses scene to single plane
- Build 100 triangles, refit all to z=0 → should succeed.
- Ray from below → should hit (degenerate but still intersects).

### 4.4 Refit with very large deformation
- Build 100 triangles in [-1,1]^3, refit to [-1e5, 1e5]^3 → should succeed.
- Tree topology preserved, bounds updated.

### 4.5 Refit with vertices that have +0/-0
- Build scene, refit with +0 and -0 → should succeed.

### 4.6 Refit with vertices that have denormalized floats
- Build scene, refit with very small values (1e-38) → should succeed.

---

## 5. Serialization / MMAP

### 5.1 Serialization with zero triangles (edge case)
- Build 1 triangle, serialize → should produce valid blob.
- Load blob → should traverse correctly.

### 5.2 Serialization of single-triangle scene
- Build 1 triangle with BVH4 → serialize → load → hit.
- Build 1 triangle with BVH8 → serialize → load → hit.

### 5.3 MMAP with truncated file
- Build scene, save to file, truncate file to half size → open_mmap should
  fail (or mmap fails, then load_from_memory rejects).

### 5.4 MMAP with corrupted child reference
- Build scene, save, corrupt a child reference → open_mmap should reject
  (validation step catches it).

### 5.5 Load from empty buffer
- Load from_memory with buf=NULL, n=0 → should return NULL.

### 5.6 Load from_memory with too-small buffer
- Load from_memory with buffer smaller than magic header (4 bytes) → should
  return NULL.

### 5.7 User scene serialization rejection
- Build user scene, attempt save → should return INVALID_ARGUMENT.

### 5.8 Sphere scene serialization rejection
- Build sphere scene, attempt save → should return INVALID_ARGUMENT.

### 5.9 SDF scene serialization rejection
- Build SDF scene, attempt save → should return INVALID_ARGUMENT.

---

## 6. SDF (Signed Distance Fields)

### 6.1 SDF sphere trace with NaN field value
- SDF callback that returns NaN → should not crash, likely miss.

### 6.2 SDF sphere trace with Inf field value
- SDF callback that returns Inf → should not crash, likely miss.

### 6.3 SDF sphere trace with non-Lipschitz field
- SDF callback that returns `dist * 2` (Lipschitz=2, not unit) → may tunnel
  through thin features. Should not crash.

### 6.4 SDF sphere trace with constant field
- SDF callback that returns `1.0` (flat field) → sphere tracing advances by
  1.0 each step, may miss surface. Should not crash.

### 6.5 SDF sphere trace with max_steps=0 (default)
- Use params with max_steps=0 → should use default 128.

### 6.6 SDF sphere trace with max_steps=1 (minimum)
- Use params with max_steps=1 → should advance once, likely miss.

### 6.7 SDF sphere trace with tmax very small
- Ray with tmax=1e-6 → sphere trace should not find surface (too short).

### 6.8 SDF sphere trace with tmin > tmax
- Ray with tmin=10, tmax=5 → should not crash, likely miss.

### 6.9 SDF sphere trace with zero-length direction
- Ray with dir=[0,0,0] → should not crash, likely miss.

### 6.10 SDF sphere trace with over-relaxation omega=2.0
- Use params with over_relax=2.0 (max) → should converge faster but not crash.

### 6.11 SDF sphere trace with epsilon=0 (default)
- Use params with epsilon=0 → should use default 1e-4.

### 6.12 SDF sphere trace with very large epsilon
- Use params with epsilon=1.0 → surface hit threshold is very loose.

### 6.13 SDF scene with NaN blob AABB
- Build SDF scene with one NaN AABB → should reject with INVALID_BOUNDS.

### 6.14 SDF scene with zero-width blob (lo==hi)
- Build SDF scene with one degenerate AABB → should build, no crash.

### 6.15 SDF scene with overlapping blobs
- Build SDF scene with 2 overlapping sphere blobs (union field).
- Ray through overlap → should find nearest surface across both blobs.

---

## 7. Batched Queries (intersect1N / occluded1N)

### 7.1 Batched query with zero rays
- Call intersect1N with n=0 → should not crash.

### 7.2 Batched query with NULL hit buffer
- Call intersect1N with hits=NULL → should not crash.

### 7.3 Batched query with NULL ray buffer
- Call intersect1N with rays=NULL → should not crash.

### 7.4 Batched query with tmin > tmax per ray
- Build scene, batch of 4 rays each with tmin > tmax → all should miss.

### 7.5 Batched query with mixed hit/miss rays
- Build scene, batch of 2 hit rays + 2 miss rays → results should match
  per-ray calls exactly.

### 7.6 Batched occluded with tmax clipping
- Build scene, batch of 4 rays with tmax before surface → all occluded=0.

### 7.7 Batched query with same ray repeated 4 times
- Build scene, Ray4 with identical rays → all 4 lanes should produce same hit.

---

## 8. Packet Queries (Ray4 / Ray8)

### 8.1 Ray4 with identical lanes
- Build scene, Ray4 with all 4 lanes identical → all 4 hits should match.

### 8.2 Ray8 with identical lanes
- Build scene, Ray8 with all 8 lanes identical → all 8 hits should match.

### 8.3 Ray4 with one hit + three misses
- Build scene, Ray4 with 1 hit ray + 3 miss rays → only 1 lane should hit.

### 8.4 Ray8 with one hit + seven misses
- Build scene, Ray8 with 1 hit ray + 7 miss rays → only 1 lane should hit.

### 8.5 Ray4 occluded with mixed results
- Build scene, Ray4 occluded4 with 2 hit + 2 miss → bitmask should match.

### 8.6 Ray8 occluded with mixed results
- Build scene, Ray8 occluded8 with 3 hit + 5 miss → bitmask should match.

---

## 9. Any-Hit Filter (`lrt_tri_occluded1_filtered`)

### 9.1 Filter that rejects all hits
- Build scene, any-hit filter that always returns 0 → should never occlude.

### 9.2 Filter that accepts all hits
- Build scene, any-hit filter that always returns 1 → same as occluded1.

### 9.3 Filter based on prim_id
- Build scene, filter that rejects prim_id < 5 → should skip first 5 triangles.

### 9.4 Filter based on t value
- Build scene, filter that rejects hits with t < 3 → should skip near hits.

### 9.5 Filter based on u/v barycentrics
- Build scene, filter that rejects hits with u > 0.5 → should skip mid-triangle hits.

### 9.6 Filter with NULL user pointer
- Build scene, filter with user=NULL → filter callback should handle NULL user.

---

## 10. Scene Stats (`lrt_tri_scene_stats`)

### 10.1 Single-triangle scene stats
- Build 1 triangle → stats should show 1 leaf, 0 interior nodes (or 1 node).

### 10.2 Two-triangle scene stats
- Build 2 triangles → stats should show 2 leaves, at least 1 interior node.

### 10.3 Stats consistency across layouts
- Build same scene with BVH4 and BVH8 → node_count/leaf_count may differ
  but memory_bytes should be comparable.

### 10.4 Stats for quantized node scene
- Build scene with BVH8_Q4 → stats should show correct node/leaf counts.

---

## 11. Kernel Name (`lrt_tri_kernel_name`)

### 11.1 Scalar fallback detection
- On a system without AVX2, BVH8 should fall back to scalar.
- `lrt_tri_kernel_name` should return "bvh8/scalar" or similar.

### 11.2 BVH8_Q4 kernel name
- Build scene with BVH8_Q4 → kernel name should indicate quantized.

### 11.3 BVH8_QF8 kernel name
- Build scene with BVH8_QF8 → kernel name should indicate fp8 quantized.

---

## 12. Curve/Hair Edge Cases (Additional)

### 12.1 Capsule with extremely long segment
- Build capsule from (0,0,0) to (0,0,1e5) with r=0.5 → should build and hit.

### 12.2 Capsule with extremely short segment
- Build capsule from (0,0,0) to (0,0,1e-7) with r=0.5 → may build or reject.

### 12.3 Capsule with Inf radius
- Build capsule with constant_radius=INFINITY → should reject with INVALID_BOUNDS.

### 12.4 Capsule with NaN radius
- Build capsule with constant_radius=NAN → should reject.

### 12.5 Capsule with zero-length segment and non-zero radius
- Build capsule from (0,0,0) to (0,0,0) with r=0.5 → sphere at origin.
- Ray through sphere → should hit.

### 12.6 Roundcurve with very large radius
- Build roundcurve with r0=1e5, r1=1e5 → should build and hit.

### 12.7 Flatcurve with zero-width ribbon (r=0)
- Build flatcurve with radii=[0, 0] → should reject or build (no crash).

### 12.8 Flatcurve with Inf radius
- Build flatcurve with constant_radius=INFINITY → should reject.

---

## 13. Points Edge Cases (Additional)

### 13.1 Point sphere with Inf radius
- Build sphere point with r=INFINITY → should reject.

### 13.2 Point sphere with NaN center
- Build sphere point with center=NAN → should reject.

### 13.3 Point disc with zero radius
- Build disc point with r=0 → should never hit.

### 13.4 Point disc with Inf radius
- Build disc point with r=INFINITY → should reject.

### 13.5 Oriented disc with zero-length normal
- Build oriented disc with normal=[0,0,0] → should reject or handle gracefully.

---

## 14. User Geometry Edge Cases

### 14.1 User geometry with NULL isect callback
- Build user scene with isect=NULL → should reject with INVALID_ARGUMENT.

### 14.2 User geometry with NaN AABB
- Build user scene with NaN in AABB → should reject.

### 14.3 User geometry with inverted AABB (lo > hi)
- Build user scene with inverted AABB → should build (user owns AABB validity).

### 14.4 User geometry callback that always returns hit
- Build user scene with callback that always hits → all rays should hit.

### 14.5 User geometry callback that always returns miss
- Build user scene with callback that always misses → all rays should miss.

### 14.6 User geometry with occ callback returning different result than isect
- Build user scene with isect/occ returning different results → occluded1
  should agree with occ callback, not isect.

---

## 15. Sphere Scene Edge Cases (Additional)

### 15.1 Sphere scene with NaN center
- Build sphere scene with one NaN sphere → should reject.

### 15.2 Sphere scene with Inf center
- Build sphere scene with one Inf sphere → should reject.

### 15.3 Sphere scene with mixed valid/invalid radii
- Build sphere scene with some r<=0 (never-hit spheres) → should build.
- Ray through valid sphere → should hit. Ray through invalid → should miss.

### 15.4 Sphere scene with all r<=0
- Build sphere scene with all r=0 → should build, never hit.

---

## 16. Triangle Intersection Edge Cases (Additional)

### 16.1 Ray with unnormalized direction
- Build scene, ray with dir=[1,1,0] (not normalized) → should hit at t
  scaled by |dir|.

### 16.2 Ray with negative tmax
- Build scene, ray with tmax=-1 → should never hit (empty interval).

### 16.3 Ray with tmin=tmax (non-empty, single point)
- Build scene, ray with tmin=5, tmax=5 → should never hit (zero-length).

### 16.4 Ray with tmin > tmax
- Build scene, ray with tmin=10, tmax=5 → should never hit (invalid interval).

### 16.5 Triangle with one vertex at origin
- Build triangle with v0=[0,0,0] → ray through origin should hit.

### 16.6 Triangle with one vertex at infinity
- Build triangle with v0=[INF,0,0] → should reject with INVALID_BOUNDS.

### 16.7 Triangle with two identical vertices (degenerate edge)
- Build triangle with v0=v1 → degenerate edge, should build but never hit
  (or hit only on edge, depending on MT behavior).

---

## 17. Multi-Hit Edge Cases (Additional)

### 17.1 Multi-hit with max_hits=1
- Build scene, intersect_n with max_hits=1 → should return same as intersect1.

### 17.2 Multi-hit with max_hits=0
- Build scene, intersect_n with max_hits=0 → should return 0 hits.

### 17.3 Multi-hit with max_hits > scene size
- Build scene with 5 triangles, intersect_n with max_hits=100 → should return
  at most 5 hits.

### 17.4 Multi-hit on single-triangle scene
- Build 1 triangle, intersect_n with max_hits=10 → should return 1 hit.

### 17.5 Multi-hit on empty scene (after refit to zero)
- Build scene, refit to all-zero triangles, intersect_n → should return 0.

---

## 18. KNN Edge Cases (Additional)

### 18.1 KNN with k=0
- Build scene, knn with k=0 → should return 0 results.

### 18.2 KNN with k=1 (same as closest_point)
- Build scene, knn with k=1 → should return same prim_id and dist_sq as
  closest_point.

### 18.3 KNN with k > scene size
- Build scene with 10 triangles, k=100 → should return at most 10 results.

### 18.4 KNN with query point at triangle vertex
- Build scene, query point exactly at a vertex → should find that triangle
  as nearest (dist_sq=0).

### 18.5 KNN with query point on triangle edge
- Build scene, query point on triangle edge → should find that triangle.

### 18.6 KNN with query point very far from scene
- Build scene in [-1,1]^3, query at [1e5, 1e5, 1e5] → should find nearest
  triangle (farthest from query).

---

## 19. Closest Point Edge Cases (Additional)

### 19.1 Closest point with query at triangle centroid
- Build scene, query point at triangle centroid → should find that triangle
  with dist_sq≈0.

### 19.2 Closest point with query on triangle edge
- Build scene, query point on triangle edge → should find that triangle.

### 19.3 Closest point with query outside all triangles
- Build scene, query point far away → should find nearest triangle.

---

## 20. Region Query Edge Cases (Additional)

### 20.1 Query AABB with zero volume (lo==hi)
- Build scene, query AABB with lo==hi → should return 0 or primitives at that
  point.

### 20.2 Query AABB with NaN bounds
- Build scene, query AABB with NaN → should not crash, return 0.

### 20.3 Query sphere with zero radius
- Build scene, query_sphere with radius=0 → should return 0.

### 20.4 Query sphere with Inf radius
- Build scene, query_sphere with radius=INFINITY → should return all primitives.

### 20.5 Query sphere with NaN center
- Build scene, query_sphere with NaN center → should not crash, return 0.

### 20.6 Query frustum with zero-area frustum
- Build scene, frustum from degenerate matrix → should not crash, return 0.

### 20.7 Query frustum with inverted near/far
- Build scene, frustum with near > far → should not crash, return 0.

### 20.8 Query frustum with NaN plane coefficients
- Build scene, frustum with NaN plane → should not crash, return 0.

---

## 21. Parallel Build Edge Cases

### 21.1 Parallel build with ntris < 4096 (below parallel threshold)
- Build 100 triangles with 4 threads → should use serial path (below 4096).

### 21.2 Parallel build with ntris = 4096 (at threshold)
- Build 4096 triangles with 4 threads → should use parallel path.

### 21.3 Parallel build with ntris = 100000 (large scene)
- Build 100k triangles with 8 threads → should use parallel path.

### 21.4 Parallel LBVH build with large scene
- Build 100k triangles with FAST quality and 8 threads → should use parallel
  Morton sort + radix sort.

### 21.5 Parallel SBVH (HQ) build (serial only)
- Build 100k triangles with HQ quality and 4 threads → should use serial
  path (SBVH is serial regardless of thread count).

---

## 22. Build Options Edge Cases

### 22.1 max_leaf_size = 0 (default)
- Build with max_leaf_size=0 → should use default (8).

### 22.2 max_leaf_size = 1 (minimum)
- Build with max_leaf_size=1 → each triangle is its own leaf.

### 22.3 max_leaf_size > TRI_MAX_LEAF
- Build with max_leaf_size=0x7FFFFFFF → should clamp to TRI_MAX_LEAF.

### 22.4 num_threads = 0 (default)
- Build with num_threads=0 → should use default (1, serial).

### 22.5 num_threads = 1 (explicit serial)
- Build with num_threads=1 → should use serial path.

### 22.6 num_threads > 1 with small scene
- Build 100 triangles with 16 threads → should use serial path (below 4096).

---

## 23. NULL / Empty Input Edge Cases

### 23.1 Build with NULL vertices
- lrt_tri_scene_build(NULL, 10, NULL, &err) → should return NULL.

### 23.2 Build with ntris = 0
- lrt_tri_scene_build(verts, 0, NULL, &err) → should return NULL.

### 23.3 Build with ntris > 0x07FFFFFF (overflow guard)
- lrt_tri_scene_build(verts, 0x07FFFFFF + 1, NULL, &err) → should return NULL.

### 23.4 Intersect with NULL scene
- lrt_tri_intersect1(NULL, &ray, &hit) → should return 0, not crash.

### 23.5 Intersect with NULL ray
- lrt_tri_intersect1(scene, NULL, &hit) → should return 0, not crash.

### 23.6 Intersect with NULL hit
- lrt_tri_intersect1(scene, &ray, NULL) → should return hit/miss, not crash.

### 23.7 Free with NULL scene
- lrt_tri_scene_free(NULL) → should not crash.

### 23.8 Save with NULL scene
- lrt_tri_scene_save(NULL, "path") → should return INVALID_ARGUMENT.

### 23.9 Load with non-existent path
- lrt_tri_scene_load("/tmp/nonexistent.lrts", &err) → should return NULL.

### 23.10 Open mmap with non-existent path
- lrt_tri_scene_open_mmap("/tmp/nonexistent.lrts", &err) → should return NULL.

---

## 24. FP Precision Edge Cases

### 24.1 Ray with very large tmin/tmax
- Build scene, ray with tmin=1e38, tmax=1e38 → should not crash.

### 24.2 Ray with very small tmin/tmax (denormalized)
- Build scene, ray with tmin=1e-38, tmax=1e-38 → should not crash.

### 24.3 Triangle with denormalized vertex coordinates
- Build scene with vertices at 1e-38 → should build and hit.

### 24.4 Triangle with very large vertex coordinates
- Build scene with vertices at 1e38 → should build (within float range).

### 24.5 Ray origin at subnormal float
- Build scene, ray with origin at 1e-38 → should not crash.

---

## 25. Thread Safety

### 25.1 Concurrent intersect1 from multiple threads
- Build scene, 4 threads each calling intersect1 with different rays →
  should not crash, results should be correct.

### 25.2 Concurrent intersect1N from multiple threads
- Build scene, 4 threads each calling intersect1N with different ray batches →
  should not crash, results should be correct.

---

## 26. TLAS Edge Cases (Detailed)

### 26.1 TLAS with 1 BLAS, 1 instance, ray through it
- Build 1 triangle BLAS, 1 instance, ray → should hit.

### 26.2 TLAS with 2 BLASes, 2 instances, ray through both
- Build 2 triangle BLASes, 2 instances, ray → should hit closest instance.

### 26.3 TLAS refit with same transform
- Build TLAS, refit with same transforms → should succeed.

### 26.4 TLAS refit with all-zero transforms
- Build TLAS, refit with all-zero obj2world → should succeed (instances at origin).

---

## Priority Recommendations for Coding Agent

**High priority** (most likely to catch real bugs):
1. **NULL/empty input** (#23) — easy to miss, common crash vector
2. **Serialization corruption** (#5) — already partially tested, extend
3. **TLAS edge cases** (#3, #26) — complex code path, easy to miss
4. **SDF edge cases** (#6) — numerical stability, many parameter combos
5. **Batched/packet queries** (#7, #8) — SIMD edge cases

**Medium priority** (good coverage gaps):
6. **Quantized triangles** (#1) — format-specific edge cases
7. **Quantized nodes** (#2) — precision edge cases
8. **Refit edge cases** (#4) — deformation scenarios
9. **Any-hit filter** (#9) — filter callback variations
10. **User geometry** (#14) — callback edge cases

**Low priority** (nice-to-have):
11. **KNN/closest_point** (#18, #19) — boundary queries
12. **Region queries** (#20) — degenerate volumes
13. **Stats/kernel_name** (#10, #11) — verification only
14. **Parallel build** (#21) — thread edge cases
15. **Thread safety** (#25) — concurrent access
