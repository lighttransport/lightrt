# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

### Makefile (recommended for development)
```bash
make                  # Build library and example
make DEBUG=1          # Build with debug symbols
make run              # Build and run example
make benchmark        # Build and run benchmarks (default: 100k triangles, 100k rays)
make benchmark TRIANGLES=50000 RAYS=200000  # Custom benchmark params
make clean            # Remove build artifacts
make info             # Show build configuration
```

Disable SIMD features:
```bash
make NO_AVX=1         # Disable AVX
make NO_AVX2=1        # Disable AVX2
make NO_F16C=1        # Disable FP16 hardware conversion
make NO_SVE=1         # Disable ARM SVE
```

### CMake
```bash
mkdir build && cd build
cmake ..
make
./lightrt_example
```

## Architecture

LightRT is a two-file BVH (Bounding Volume Hierarchy) library: `lightrt.hh` (header) and `lightrt.cc` (implementation).

### Two-Level BVH Structure
- **BLAS** (Bottom-Level Acceleration Structure): Contains geometry primitives (AABBs) for a single mesh/object
- **TLAS** (Top-Level Acceleration Structure): Contains instances of BLAS with transformations, enabling instancing
- **BVH**: Core single-level BVH used by both BLAS and TLAS

### Key Classes (all in `lightrt` namespace)
- `BVH`: Single-level BVH with SAH-based construction, SIMD traversal, and spatial queries (AABB primitives)
- `TriangleBVH`: BVH over triangles with Moller-Trumbore ray-triangle intersection and spatial queries
- `BLAS`: Wraps BVH for bottom-level geometry
- `TLAS`: Manages instanced scene with `BLASInstance` transforms
- `BVHNode`: Interior/leaf node using union for child indices or primitive offset/count
- `MMapTriangleBVH`: Zero-copy BVH over external triangle data with compact nodes
- `MMapGenericBVH`: Zero-copy BVH for custom primitives via callbacks
- `CompactBVHNode`: 24-byte node with 16-bit quantized bounds (vs 56-byte BVHNode)
- `TraversalProfile`: Profiling data (nodes visited, prims tested, depth)
- `NoProfiler` / `WithProfiler`: Template policies for zero-overhead profiling
- `HeatmapWriter`: Image writer for BVH visualization (BMP, TGA, PPM, PNG)
- `HitRecord` / `MultiHitResult`: Multi-hit traversal results for transparency
- `Ray4` / `Ray8`: SoA ray packets for SIMD traversal
- `HitResult4` / `HitResult8`: Packet hit results

### Primitive Types
- `Triangle`: 3 vertices (36 bytes), Moller-Trumbore intersection
- `QuantizedTriangle`: 16-bit quantized vertices (18 bytes), requires global bounding box for dequantization
- `Quad`: 4 vertices (bilinear patch), split into 2 triangles
- `NGon`: N vertices (convex polygon), Newell normal + crossing number test
- `Sphere`: Center + radius, analytic quadratic intersection
- `Disk`: Center + normal + radius, ray-plane + distance check
- `OrientedDisk`: Billboard/screen-oriented disk that faces ray origin
- `Curve`: Hair/fiber with varying radius, supports:
  - `CurveType::Linear`: Fast capsule-based segments
  - `CurveType::Bezier`: Phantom Ray-Hair algorithm (Reshetov & Luebke, HPG 2018)
  - `CurveType::CatmullRom`: Catmull-Rom spline evaluation
- `CustomGeometry`: AABB + callback functions for user-defined intersection
- `GaussianSplat`: 3D Gaussian for neural radiance fields (~220 bytes)
  - Position, scale, quaternion rotation, opacity
  - Spherical harmonics coefficients (up to degree 3)
  - Ray-ellipsoid intersection using 3-sigma confidence ellipsoid
  - View-dependent color via SH evaluation
- `QuantizedGaussianSplat`: Compressed Gaussian (~32 bytes)
  - 16-bit quantized position, log-scale
  - 8-bit quantized quaternion, opacity, DC color

### SBVH (Split BVH)
- `SBVH`: Triangle BVH with spatial splits (Stich et al., HPG 2009)
- `SBVHGeneric`: Generic AABB-based SBVH
- Allows primitives to be split/duplicated across nodes
- Benefits scenes with large triangles spanning multiple spatial regions
- Uses `PrimRef` (primitive reference) with clipped bounds
- Configuration via `SBVHBuildConfig`:
  - `num_spatial_bins`: Bins for spatial split evaluation (default: 256)
  - `num_object_bins`: Bins for object split evaluation (default: 32)
  - `alpha`: Overlap threshold for considering spatial splits (default: 1e-5)
  - `max_split_factor`: Maximum reference count increase (default: 1.5 = 50% more)

### Traversal Configuration
`TraversalConfig` controls traversal behavior:
- `max_prim_tests`: Limit primitive tests to avoid O(N) worst case (0 = unlimited)
- `exclude_prim_id`: Primitive to skip (for self-intersection avoidance)
- `use_mailboxing`: Avoid duplicate tests in SBVH (important when split_ratio > 1)
- `early_termination`: Stop on first hit (for shadow rays)

Presets:
- `TraversalConfig::fast(K)`: Limit to K tests with mailboxing
- `TraversalConfig::anyHit()`: Stop on first hit (shadow rays)
- `TraversalConfig::shadowRay(exclude_prim)`: Any-hit + self-intersection avoidance
- `TraversalConfig::secondaryRay(exclude_prim)`: Self-intersection avoidance for reflection/refraction

### Packet Traversal (Path Tracing)
Ray packets enable SIMD-parallel traversal for coherent rays:

- `Ray4` / `Ray8`: SoA (Structure of Arrays) ray packets
- `HitResult4` / `HitResult8`: Packet hit results with prim_id, t, u, v per ray

Methods on `TriangleBVH` and `SBVH`:
```cpp
// Single-ray any-hit (shadow rays)
bool traverseAnyHit(const Ray& ray, uint32_t exclude_prim_id = kInvalidIndex);

// 4-ray packet traversal
void traverse4(const Ray4& rays, HitResult4& results);
uint32_t traverse4AnyHit(const Ray4& rays, uint32_t exclude_prim_id = kInvalidIndex);

// 8-ray packet traversal (AVX optimized)
void traverse8(const Ray8& rays, HitResult8& results);
uint32_t traverse8AnyHit(const Ray8& rays, uint32_t exclude_prim_id = kInvalidIndex);
```

Usage:
```cpp
// Shadow ray from surface
Ray shadow_ray(hit_pos + to_light * 0.001f, to_light, kEpsilon, light_dist);
bool occluded = bvh.traverseAnyHit(shadow_ray, hit_prim_id);

// Packet traversal for coherent rays
Ray4 packet = Ray4::fromRays(rays, 4);
HitResult4 results;
bvh.traverse4(packet, results);

// Packet any-hit returns bit mask
uint32_t hit_mask = bvh.traverse4AnyHit(packet);
```

`TraversalStats` returns traversal statistics:
- `nodes_visited`, `prims_tested`, `prims_hit`, `terminated_early`

### Multi-Hit Traversal (Transparency)
For rendering transparent surfaces, volumetrics, or CSG operations:

```cpp
MultiHitResult result;
uint32_t count = bvh.traverseMultiHit(ray, result, max_hits, exclude_prim_id);

// Iterate hits front-to-back (sorted by distance)
for (const auto& hit : result.hits) {
  // hit.prim_id, hit.t, hit.u, hit.v
  float alpha = getAlpha(hit.prim_id, hit.u, hit.v);
  if (alpha > 0.99f) break;  // Opaque - stop
}
```

### BVH Refitting (Animation)
For animated scenes, refit BVH bounds without rebuilding:

```cpp
// Modify triangle vertices
auto& triangles = bvh.getMutableTriangles();
for (auto& tri : triangles) {
  tri.v0 = animate(tri.v0, time);
  // ...
}

// Update BVH bounds (fast, preserves tree structure)
bvh.refit();
```

### BVH Serialization
Save/load BVH to disk for caching:

```cpp
// Save BVH to file
bvh.save("scene.bvh");

// Load BVH from file
TriangleBVH loaded_bvh;
loaded_bvh.load("scene.bvh");

// Memory buffer serialization
std::vector<uint8_t> buffer;
bvh.saveToMemory(buffer);
bvh.loadFromMemory(buffer.data(), buffer.size());
```

### Build Configuration
`BVHBuildConfig` controls construction:
- `use_sah`: Surface Area Heuristic for optimal splits (default: true)
- `use_binning`: Binned SAH for large datasets (default: true)
- `max_leaf_size`: Maximum primitives per leaf (default: 4)
- `force_max_leaf_size`: Always enforce max_leaf_size, ignore SAH cost (default: false)
- `use_lbvh`: Use Linear BVH (Morton code-based, fast O(N log N) build) (default: false)

Presets:
```cpp
BVHBuildConfig::fast()     // LBVH: ~5x faster build, good traversal
BVHBuildConfig::quality()  // SAH with binning: slower build, best traversal
```

### LBVH (Linear BVH)
Fast BVH construction using Morton codes (Z-order curve):
- **Build time**: O(N log N) vs O(N log² N) for SAH
- **Quality**: ~7-10% higher SAH cost than binned SAH
- **Use case**: Dynamic scenes, fast preview, streaming

Benchmark (100k triangles):
| Method | Build Time | SAH Cost | Speedup |
|--------|------------|----------|---------|
| SAH    | 190ms      | 434,493  | 1x      |
| LBVH   | 37ms       | 467,303  | 5x      |

Implementation uses:
- 30-bit Morton codes (10 bits per axis)
- Radix sort for O(N) ordering
- Bit-level tree construction

## Spatial Queries

BVH provides efficient spatial indexing for broad-phase collision detection and frustum culling.

### AABB Query

Collect all primitives whose AABBs intersect a query AABB:

```cpp
// Query all triangles within a bounding box
AABB query_box(Vec3(0, 0, 0), Vec3(10, 10, 10));
std::vector<uint32_t> results;
bvh.queryAABB(query_box, results);

// Results contains indices of intersecting triangles
for (uint32_t tri_idx : results) {
  // Process triangle tri_idx
}
```

### Sphere Query

Collect all primitives within a sphere radius:

```cpp
// Query all triangles within sphere
Vec3 center(5.0f, 5.0f, 5.0f);
float radius = 3.0f;
std::vector<uint32_t> results;
bvh.querySphere(center, radius, results);
```

### Use Cases

- **Frustum culling**: Use AABB query with view frustum bounds
- **Broad-phase collision**: Find potential collision candidates
- **Area-of-effect**: Find entities within explosion/effect radius
- **Spatial indexing**: Range queries for nearest neighbor search

### Frustum Culling

Collect primitives visible within a view frustum:

```cpp
// Create frustum from view-projection matrix (column-major)
float mvp[16] = { ... };  // projection * view
Frustum frustum = Frustum::fromMatrix(mvp);

// Or construct planes manually
Frustum frustum;
frustum.planes[0] = Frustum::Plane(nx, ny, nz, d);  // Left
frustum.planes[1] = Frustum::Plane(...);            // Right
// ... near, far, top, bottom

// Query visible primitives
std::vector<uint32_t> visible;
bvh.queryFrustum(frustum, visible);
```

### K-Nearest Neighbor (KNN)

Find K closest primitives to a query point:

```cpp
// Find 10 nearest triangles to a point
Vec3 query_point(5.0f, 0.0f, 5.0f);
std::vector<KNNResult> results;
bvh.queryKNN(query_point, 10, results);

// Results sorted by distance (nearest first)
for (const auto& r : results) {
  uint32_t tri_idx = r.prim_id;
  float dist_sq = r.distance_sq;
}

// For single nearest neighbor
float dist_sq;
uint32_t nearest = bvh.queryNearest(query_point, dist_sq);
```

### Performance

Spatial queries traverse the BVH tree, testing nodes against the query volume:
- **Time complexity**: O(log N + K) where K is the result count
- **Stack-based traversal**: No recursion overhead
- **Early culling**: Skips entire subtrees when bounds don't intersect
- **KNN uses priority queue**: Visits nodes in distance order for optimal pruning

## Collision Detection

BVH provides efficient collision detection between objects using simultaneous tree traversal.

### BVH-BVH Collision

Find all colliding primitive pairs between two BVHs:

```cpp
// Check if any collision exists (fast early-out)
if (bvh_a.hasCollision(bvh_b)) {
  // Find all colliding pairs
  std::vector<CollisionPair> pairs;
  bvh_a.findCollisions(bvh_b, pairs);

  for (const auto& p : pairs) {
    // p.prim_a from bvh_a, p.prim_b from bvh_b
    handleCollision(p.prim_a, p.prim_b);
  }
}

// Near-collision with distance threshold
std::vector<CollisionPair> near_pairs;
bvh_a.findCollisions(bvh_b, 0.5f, near_pairs);  // Within 0.5 units
```

### Self-Collision

Detect collisions within a single BVH (e.g., cloth simulation):

```cpp
// Check if any self-collision exists
if (bvh.hasSelfCollision()) {
  std::vector<CollisionPair> self_pairs;
  bvh.findSelfCollisions(self_pairs);
  // Pairs are deduplicated: only (a, b) where a < b
}
```

### Swept Collision (Continuous Collision Detection)

Find collisions as an object moves along a velocity vector:

```cpp
Vec3 velocity(10.0f, 0.0f, 0.0f);  // Movement for this frame

// Find first collision
SweptCollisionResult result;
if (moving_bvh.findSweptCollision(static_bvh, velocity, result)) {
  // result.t_first: time of first contact [0, 1]
  // result.t_last: time of last contact
  // result.normal: collision normal
  Vec3 safe_pos = original_pos + velocity * result.t_first;
}

// Find all collisions along path
std::vector<SweptCollisionResult> all_results;
moving_bvh.findAllSweptCollisions(static_bvh, velocity, all_results);
// Results sorted by t_first (earliest first)
```

### AABB Utilities

Additional AABB methods for collision detection:

```cpp
// Swept AABB intersection
float t_first, t_last;
if (aabb_a.intersectSwept(aabb_b, velocity, t_first, t_last)) {
  // Collision during interval [t_first, t_last]
}

// Penetration depth and normal for overlapping AABBs
Vec3 normal;
float depth;
if (aabb_a.computePenetration(aabb_b, normal, depth)) {
  // Resolve by pushing aabb_a along normal by depth
  position += normal * depth;
}

// Minkowski operations
AABB sum = aabb_a.minkowskiSum(aabb_b);       // For configuration space
AABB diff = aabb_a.minkowskiDifference(aabb_b);  // For GJK-style tests

// Point containment
if (aabb.contains(point)) { ... }
```

## Benchmark (`benchmark/benchmark.cc`)

Tests BVH performance with different scenarios:
1. **Random triangles + random rays**: General performance
2. **Uniform grid triangles + random rays**: Spatially coherent geometry
3. **Random triangles + coherent rays**: Camera-like ray patterns
4. **Overlapping triangles**: Degenerate case where all primitives share same centroid
5. **SBVH vs TriangleBVH**: Comparison with large and random triangles
6. **Pathological scenes**: Thin spanning, diagonal, hair-like triangles
7. **Co-planar triangles**: Single layer, tessellated plane, overlapping, multiple layers
8. **Auto-tuning**: Tests AutoTuner with random, hair-like, and co-planar scenes

Co-planar and pathological tests demonstrate:
- `max_prim_tests` limit caps O(N) to O(K) with configurable accuracy trade-off
- Mailboxing reduces duplicate tests in SBVH (split_ratio > 1)
- K=64-128 typically provides good speed/accuracy balance

Auto-tuning tests demonstrate:
- Scene analysis detects thin triangles, co-planar regions, clustering
- Quick vs full tuning trade-off (with/without SBVH testing)
- Traversal config tuning for existing BVH

## Auto-Tuning

`AutoTuner` automatically selects optimal BVH construction and traversal parameters by sampling primitives and measuring performance.

### Usage

```cpp
// Auto-tune and get best configuration
auto result = AutoTuner::tune(triangles);

// Build with tuned config
if (result.best_method == BVHBuildMethod::TriangleBVH) {
  bvh.build(triangles, result.best_bvh_config);
} else {
  sbvh.build(triangles, result.best_sbvh_config);
}

// Or use convenience function
TriangleBVH bvh;
AutoTuner::buildOptimal(triangles, bvh);

// Tune traversal config for existing BVH
auto trav_config = AutoTuner::tuneTraversal(bvh, scene_bounds);
```

### Configuration Presets

`AutoTuneConfig` presets for different use cases:
- `AutoTuneConfig()`: Default balanced tuning
- `AutoTuneConfig::throughput()`: Optimize for ray throughput (90% traversal weight)
- `AutoTuneConfig::interactive()`: Balance build/traversal for frequent rebuilds
- `AutoTuneConfig::memory()`: Optimize for memory-constrained scenes
- `AutoTuneConfig::quick()`: Fast tuning with fewer samples (no SBVH testing)

### Tuning Process

1. **Sample primitives**: Stratified sampling of M primitives from N input (default: sqrt(N), clamped to 100-5000)
2. **Analyze scene**: Detect thin triangles, co-planar regions, clustering, overlap ratio
3. **Test configurations**: Build and traverse with different settings
4. **Select best**: Weighted cost function: `build_weight * build_time + traversal_weight * trav_time + memory_weight * memory`

### AutoTuneResult

Returns:
- `best_method`: `BVHBuildMethod::TriangleBVH` or `BVHBuildMethod::SBVH`
- `best_bvh_config` / `best_sbvh_config`: Optimal build parameters
- `best_traversal_config`: Optimal traversal settings (max_prim_tests, mailboxing)
- `scene_info`: Scene characteristics (avg_triangle_area, overlap_ratio, has_thin_triangles, etc.)
- `all_metrics`: Detailed metrics for all tested configurations

### Scene Analysis

`AutoTuner::analyzeScene()` provides scene characteristics:
- `avg_triangle_area`: Average triangle surface area
- `triangle_density`: Triangles per unit volume
- `overlap_ratio`: Estimated spatial overlap between primitives
- `has_thin_triangles`: Long thin triangles detected (aspect ratio > 10)
- `has_clustered_distribution`: Spatial clustering detected
- `has_coplanar_regions`: Co-planar triangles detected

## Memory-Mapped BVH (Zero-Copy)

`MMapTriangleBVH` and `MMapGenericBVH` provide zero-copy BVH construction over external primitive data, optimized for low memory and bandwidth.

### Usage

```cpp
// Triangle data from memory-mapped file or external source
const Triangle* triangles = reinterpret_cast<const Triangle*>(mmap_data);
uint32_t count = file_size / sizeof(Triangle);

// Build BVH over external data (zero-copy)
MMapTriangleBVH bvh;
bvh.build(triangles, count);

// Traverse
float hit_t = std::numeric_limits<float>::max();
float hit_u, hit_v;
uint32_t hit_idx = bvh.traverse(ray, hit_t, hit_u, hit_v);

// For custom primitives, use callbacks
MMapGenericBVH generic_bvh;
generic_bvh.build(aabbs, count, intersect_callback, user_data);
```

### Memory Optimization

**CompactBVHNode** (24 bytes vs 56 bytes for standard BVHNode):
- 16-bit quantized bounds (6 × uint16_t = 12 bytes)
- Dequantized on-the-fly during traversal using scene bounding box
- ~57% memory savings for BVH structure

**Variable Precision Indices**:
- `uint8_t` for ≤255 primitives (1 byte per index)
- `uint16_t` for ≤65535 primitives (2 bytes per index)
- `uint32_t` for >65535 primitives (4 bytes per index)
- Automatic selection based on primitive count

### Configuration

`MMapBVHConfig` presets:
- `MMapBVHConfig()`: Default balanced settings
- `MMapBVHConfig::minMemory()`: Compact nodes (16-bit bounds)
- `MMapBVHConfig::maxSpeed()`: Full precision nodes (32-bit bounds)

```cpp
// Minimum memory mode
MMapBVHConfig config = MMapBVHConfig::minMemory();
config.max_leaf_size = 8;  // More primitives per leaf
bvh.build(triangles, count, config);

// Get BVH memory usage (excludes external primitive data)
size_t bvh_memory = bvh.getBVHMemoryUsage();
```

### Performance

Benchmark results (100k triangles):
| Configuration | Memory | vs Standard |
|---------------|--------|-------------|
| Standard TriangleBVH | 780 KB | baseline |
| MMap Compact (16-bit) | 129 KB | -83.5% |
| MMap Full (32-bit) | 331 KB | -57.6% |

Benefits:
- **Zero-copy**: Primitive data stays in place (memory-mapped files, GPU buffers)
- **Cache-friendly**: Smaller BVH fits in CPU cache
- **Ordered traversal**: Traversal ordered by split axis for better memory access patterns

### Limitations

- Quantized bounds have ~0.0015% precision loss (16-bit = 65536 levels)
- External primitive data must remain valid during BVH lifetime
- Slightly slower dequantization overhead for compact nodes

## Traversal Profiling (Zero-Overhead Template)

Template-based profiling system with zero overhead when disabled.

### Usage

```cpp
// Non-profiled (zero overhead - NoProfiler calls are optimized away)
float t, u, v;
uint32_t hit = traverseProfiled<NoProfiler>(bvh, ray, t, u, v, nullptr);

// Profiled (collects statistics)
TraversalProfile profile;
uint32_t hit = traverseProfiled<WithProfiler>(bvh, ray, t, u, v, &profile);

// Access statistics
std::cout << "Nodes visited: " << profile.nodes_visited << "\n";
std::cout << "Prims tested: " << profile.prims_tested << "\n";
std::cout << "Max depth: " << profile.max_depth << "\n";
```

### Profile Data

`TraversalProfile` contains:
- `nodes_visited`: Total BVH nodes visited
- `leaf_visits`: Leaf nodes visited
- `prims_tested`: Primitive intersection tests
- `max_depth`: Maximum traversal depth reached

### Supported BVH Types

- `TriangleBVH`: Full profiling support
- `SBVH`: Full profiling support
- `MMapTriangleBVH`: Estimated profile based on BVH stats

### Performance

Benchmark results (10000 rays, 10000 triangles):
- Non-profiled: ~29ms
- Profiled: ~34ms
- Overhead: ~16%

## Heatmap / Pseudocolor Image Writer

Zero-dependency image writer for BVH traversal visualization.

### Supported Formats

- **BMP**: Windows Bitmap (24-bit RGB, uncompressed)
- **TGA**: Truevision TGA (24-bit RGB, uncompressed)
- **PPM**: Portable Pixmap (binary P6)
- **PNG**: PNG (24-bit RGB, DEFLATE compressed, no zlib dependency)

### Colormaps

- `Grayscale`: Black to white
- `Heat`: Black → Red → Yellow → White
- `Jet`: Blue → Cyan → Green → Yellow → Red
- `Viridis`: Perceptually uniform (purple → blue → green → yellow)
- `Turbo`: Google's improved rainbow
- `Plasma`: Perceptually uniform (purple → pink → orange → yellow)
- `Inferno`: Perceptually uniform (black → purple → red → yellow)
- `Cool`: Cyan to Magenta
- `Hot`: Black → Red → Yellow → White (classic)

### Usage

```cpp
// Render image with profiling
TraversalProfile* profiles = renderImageProfiled(
    bvh, width, height,
    camera_pos, camera_dir, camera_up, fov_y);

// Write heatmap
HeatmapWriter::writeHeatmap("nodes.bmp", profiles, width, height,
                             HeatmapWriter::Metric::NodesVisited,
                             Colormap::Viridis, ImageFormat::BMP);

// Available metrics
HeatmapWriter::Metric::NodesVisited  // Nodes visited per ray
HeatmapWriter::Metric::LeafVisits    // Leaf nodes visited
HeatmapWriter::Metric::PrimsTested   // Primitive tests per ray
HeatmapWriter::Metric::MaxDepth      // Traversal depth

// Direct colormap API
HeatmapWriter::writeImage("out.bmp", float_data, w, h, Colormap::Plasma);
HeatmapWriter::writeImage("out.bmp", uint_data, w, h, max_val, Colormap::Hot);

delete[] profiles;  // Caller owns memory
```

### PNG Implementation Notes

The PNG writer uses a dependency-free DEFLATE implementation:
- Fixed Huffman codes (RFC 1951 compliant)
- Literals-only encoding (no LZ77 dictionary matching)
- Valid PNG output readable by all standard tools
- Simple implementation (~300 lines) with no external dependencies

## Memory Usage

Quantized primitives trade precision for memory savings:

| Primitive | Full Size | Quantized Size | Compression |
|-----------|-----------|----------------|-------------|
| Triangle | 36 bytes | 18 bytes | 2x |
| GaussianSplat | ~220 bytes | ~32 bytes | 7x |

Quantized types require a global bounding box for coordinate reconstruction. Use `quantize()` to compress and `dequantize()` to restore full precision before intersection testing.

## C11 Production Ray-Tracing Kernel (`lightrt_c_tri.h`)

A standalone, dependency-free C11 fp32 wide-BVH kernel (separate from the C++
`lightrt` library and from the fp64 generic callback API in `lightrt_c.h`).
Build a scene once, then query it from any number of threads concurrently
(stateless, lock-free). Compiled scalar + SSE4 (BVH4) + AVX2 (BVH8) with
compile-time dispatch; `lrt_tri_kernel_name()` reports the selection. Tests:
`tests/test_lightrt_c_tri.c` (brute-force oracles across BVH4/BVH8/BVH8Q ×
FAST/DEFAULT/HQ, plus scalar + ASan/UBSan).

### Scene types (all share the `lrt_tri_scene` handle and the `lrt_tri_*` queries)
- `lrt_tri_scene_build` — triangles (BVH4/BVH8/BVH8Q; LBVH/SAH/SBVH).
- `lrt_curve_scene_build` — hair/curve capsules (constant radius per
  sub-segment; cylinder + 2 end spheres).
- `lrt_roundcurve_scene_build` — **Embree-style round-linear curves**: one
  tapered cone (varying radius r0→r1) per strand segment, tangent to its two end
  spheres, CSG-clipped at the joints against the strand neighbors (a port of
  Embree's `roundline_intersector.h`, scalar `tri_rlc_isect_one` + a 4-wide SSE
  leaf `tri_rlc4_isect_sse` over the SoA `lrt_rlc4` block; matches Embree's
  `RTC_GEOMETRY_TYPE_ROUND_LINEAR_CURVE` to fp precision — see the wCurly.hair
  cross-check in `benchmark_c/hair_bench.c`). Strand-structured input
  (`lrt_hair_strands`: points + per-point radius + strand offsets); `prim_kind ==
  TRI_PRIM_RLCURVE`, `lrt_rlc4` leaf (own 272-byte `block_stride`, stores
  v0/v1/vL/vR), BVH4 only, no serialization/refit/mmap. The CyHair (.hair) loader
  is `benchmark_c/cyhair.{h,c}`; `hair_bench` loads `data/wCurly.hair`, builds it
  with both lightrt and Embree, reports build/throughput, cross-checks hits, and
  writes a shaded PPM. `hair_bench --prim {round,flat,sphere,disc,odisc}` exercises
  all the curve/point types below against the matching Embree geometry, and
  `hair_bench --gen furball [--strands N --segments M]` generates procedural fur
  (`benchmark_c/furball.{h,c}`, à la Embree's hair tutorial) instead of a file.
- `lrt_flatcurve_scene_build` — **flat (ribbon) linear curves**: each strand
  segment is a ray-facing ribbon quad of width 2r (Embree
  `RTC_GEOMETRY_TYPE_FLAT_LINEAR_CURVE`; world-space `b = normalize(cross(p1-p0,
  dir))` quad, two-triangle MT). `TRI_PRIM_FLATCURVE`, `lrt_flat4` leaf, scalar +
  4-wide SSE leaf `tri_flat4_isect_sse`. Matches Embree ~99.96% (the ribbon's
  ray-space-vs-world orientation differs at grazing edges).
- `lrt_bezcurve_scene_build` — **true higher-order round cubic-Bézier curves**
  (not tessellation): a port of Embree's sweep intersector
  (`curve_intersector_sweep.h`, `RTC_GEOMETRY_TYPE_ROUND_BEZIER_CURVE`). Each
  sub-interval seeds a 2D Newton/Jacobian iteration (`tri_bez_newton`: `f =
  dot(R,T)` foot, `g = dist−radius` surface) that converges to the exact tube;
  the seed comes from a round-linear cone, with a cone fallback when Newton is
  ill-conditioned (grazing). Build-time de Casteljau **pre-subdivision**
  (`TRI_BEZ_BUILD_SPLIT=4`) gives tight AABBs so the BVH culls well; the sub-arcs
  are computed on the fly (no materialized temp array — low build memory), and
  the leaf keeps the original segment id (`seg = sub/K`). `TRI_PRIM_BEZCURVE`,
  `lrt_bez4` leaf (4 CPs xyz+r). The SSE leaf (`tri_bez4_isect_sse`) is a 4-wide
  **ray-to-segment closest-distance cull** over the block's 4 curves (a tight
  capsule that is robust for *all* ray orientations, including exactly parallel —
  a cylinder-based capsule cull silently under-fired there, and a sphere cull was
  correct but too loose) that gates the exact scalar sweep on the survivors
  (bit-identical to scalar). The scalar sweep seeds Newton from a lean tapered
  cone (`tri_cone_seed`, no neighbor CSG). Net: **beats Embree** on the trace
  (~1.3–1.5× on primary and incoherent) at ~99.5% agreement. Input is explicit
  cubic CPs (`16*nseg`); B-spline/Catmull-Rom convert to Bézier first (hair_bench
  does Catmull-Rom→Bézier). Memory/build trade off against `TRI_BEZ_BUILD_SPLIT`
  (K). The sweep is **adaptive and SIMD** (`tri_bez_sweep_sse`): it recursively
  4-ary-subdivides each fired curve, evaluating/bounding/rejecting 4 sub-intervals
  at a time (4-wide), pruning those whose bounding capsule the ray misses and
  refining only the surviving leaves with cone+Newton — far regions cost a cheap
  4-wide reject, and accuracy rises to ~99.9%. This lifts the whole speed/memory
  Pareto: default `TRI_BEZ_BUILD_SPLIT=2` ≈Embree speed (and beats it on
  incoherent) at ~94 MB; `K=4` ~13 Mrays/s at 191 MB; `K=1` matches Embree's
  memory (~46 MB) and build (store-once) at ~half Embree's trace speed (looser
  K=1 BVH boxes fire more curves). The scalar `tri_bez_isect_one` (also adaptive)
  is the non-SSE fallback.
- `lrt_points_scene_build(centers, radii, normals, point_type, n)` — **point
  primitives** mirroring Embree's point types (`lrt_tri_point_type`):
  `LRT_POINT_SPHERE` (ray-sphere), `LRT_POINT_DISC` (ray-facing disc),
  `LRT_POINT_ORIENTED_DISC` (fixed-normal disc; normals required). `TRI_PRIM_POINT`,
  `lrt_point4` leaf (160 B, reuses the default block path), scalar + 4-wide SSE
  leaf `tri_point4_isect_sse`. Direct port of Embree's
  `sphere_intersector.h`/`disc_intersector.h`; matches Embree ≥99.99% and beats it
  on point throughput. (Sphere points overlap the older `lrt_sphere_scene_build`
  path but add disc/oriented-disc + a normal buffer.)
- `lrt_sphere_scene_build` — built-in fully-SIMD analytic spheres (`cx cy cz r`).
- `lrt_user_scene_build` — **efficient custom geometry**: an fp32 BVH broad
  phase over caller AABBs, with a per-candidate intersect/occluded callback
  invoked only after a 4-wide AABB pretest. Far faster than the fp64
  `lightrt_c.h` path. Callbacks must be re-entrant for concurrent queries.
- `lrt_quad_scene_build` / `lrt_tetra_scene_build` — **planar quad** (4-vertex
  face, two-triangle MT) and **solid tetrahedron** (nearest of 4 faces); shared
  208-byte `lrt_quad4` 4-point leaf, `TRI_PRIM_QUAD` / `_TETRA`. Input 12*n
  floats (v0 v1 v2 v3). Serialize + GPU-trace.
- `lrt_sdfprim_scene_build` — **built-in implicit/SDF primitives** (sphere/box/
  torus via `lrt_sdf_shape`), sphere-traced analytically on both CPU and GPU —
  a device-friendly custom-geometry path that needs no host callbacks (so it
  serializes and GPU-traces, unlike `lrt_user_scene_build`). `TRI_PRIM_SDF`,
  144-byte `lrt_sdf4` leaf (center, bounding radius, type, 3 params).
- **Parametric surfaces (direct ray-patch intersection, no tessellation — a
  superset of Embree, which has no native NURBS/Bézier-surface/trim types):**
  - `lrt_bilinear_scene_build` — true **bilinear patch** (Embree GRID cell),
    exact closed-form quadratic solve (Reshetov "Cool Patches"). `TRI_PRIM_
    BILINEAR`, reuses the 208-byte `lrt_quad4` leaf.
  - `lrt_bezpatch_scene_build` — **bicubic Bézier surface** (4×4 CPs), adaptive
    (u,v) quadtree subdivision + Newton on (u,v,t). `TRI_PRIM_BEZPATCH`,
    784-byte `lrt_bezpatch4` leaf (4 patches/block SoA).
  - `lrt_nurbs_scene_build` — **NURBS surface** (control net + 2 knot vectors +
    weights, any bidegree ≤8): build-time knot-insertion Bézier extraction
    (NURBS Book A5.6) + degree-elevation to rational bicubic, intersected
    directly (homogeneous eval + perspective divide). `TRI_PRIM_RBEZPATCH`,
    1104-byte `lrt_rbezpatch4` leaf (16 homogeneous CPs + per-patch domain).
  - `lrt_trimnurbs_scene_build` — **trimmed NURBS**: the above + (u,v) trim loops
    (polylines; outer + holes, even-odd rule). A patch hit is kept only if its
    global (u,v) is visible; trimmed hits are rejected and the search continues
    for the nearest untrimmed hit. `TRI_PRIM_TRIMNURBS`, scene-owned trim side
    buffers. Verified by residual (surface point on the ray) + the trim
    invariant (every hit inside the trim region). Serializes via the **LRTS v2
    aux region** (trim loops ride after the blocks; v1 files still load — their
    zero padding reads as aux_size 0). `lrt_trimnurbs_bezier_scene_build` takes
    **cubic-Bézier trim loops** (4 (u,v) CPs/segment, C0-closed) and flattens
    them to a polyline at build time (adaptive de Casteljau to a `tol`), then
    builds the same scene — so the trim test, serialization, and GPU trace are
    unchanged (the GPU never sees curves; zero parity risk).
  - **Post-hit shading** (`lrt_tri_surface_normal`): given a hit's `prim_id` +
    `(u,v)`, re-evaluates the surface for the point `P`, geometric normal `Ng =
    cross(dP/du, dP/dv)`, and the two parametric tangents (any output NULL-able)
    — the partials the intersectors already compute but discard. Works for all
    four surface kinds; NURBS `(u,v)` is global and is remapped to the per-patch
    local domain internally (tangents reported w.r.t. the global params). The
    per-prim control data is reconstructed from the leaf blocks
    (`tri_build_shade_data`), so the query works on freshly built and
    serialized/mmapped scenes alike; non-surface scenes return
    `INVALID_ARGUMENT`. CPU-side by design (normals are consumed at shade time
    on the host), so it is **not** mirrored on the HIP device — the `prim_kind`
    trace-dispatch parity is unaffected. Curves use `lrt_tri_curve_frame`
    instead (a tube's radial normal needs the ray-dependent hit point).

### Implicit surfaces / SDF (`lrt_sdf_*`)
- `lrt_sdf_sphere_trace` — standalone enhanced sphere tracing (over-relaxation
  with safe fallback, relative epsilon, tetrahedron-difference normal). The SDF
  must be a Lipschitz≤1 distance bound.
- `lrt_sdf_scene_build` — BVH-accelerated field of SDF blobs (built on the
  custom-geometry path; for overlaps, each blob's callback evaluates the global
  union field).

### Queries (triangle scenes)
- Closest hit `lrt_tri_intersect1`, any-hit `lrt_tri_occluded1`, batched
  `*1N` (with `lrt_tri_batch_hint` for coherent vs incoherent).
- Nearest-N multi-hit `lrt_tri_intersect_n` (transparency / CSG / volumes).
- Point query `lrt_tri_closest_point`, kNN `lrt_tri_knn`.
- Region queries `lrt_tri_query_aabb` / `_sphere` / `_frustum`
  (+ `lrt_frustum_from_matrix`).
- Coherent ray packets `lrt_tri_intersect4/8`, `lrt_tri_occluded4/8`.
- Filtered any-hit `lrt_tri_occluded1_filtered` (alpha-tested shadows).

### Post-hit shading data (CPU; geometry-aware)
- `lrt_tri_surface_normal` — parametric SURFACE point / geometric normal (`Ng =
  cross(dP/du, dP/dv)`) / tangents from a hit's `(prim_id, u, v)`. See the
  parametric-surfaces section.
- `lrt_tri_curve_frame` — LINEAR curve (round-linear / flat) centerline point
  `C(u)`, tangent `T = dC/du`, and radius `r(u)` from a hit's `(prim_id, u)`; the
  caller forms the shading normal by removing the tangential part of `P - C`.
  Cubic-Bezier curves are *not* served — the build pre-subdivides each cubic and
  the reported `u` is local to the unrecorded sub-arc, so a global segment
  parameter can't be reconstructed (`INVALID_ARGUMENT`).
- Both queries are CPU-side. The per-prim control data is **reconstructed from
  the leaf blocks** (`tri_build_shade_data`) — the leaves are the intersector's
  own source of truth — so the queries work on freshly built *and*
  serialized/mmapped scenes alike, with no extra on-disk data (a deserialized
  scene rebuilds the arrays on load). `LRT_RESULT_UNSUPPORTED` only on an
  allocation failure.
- `lrt_tri_surface_tessellate[_bound]` — dice a parametric SURFACE scene into a
  triangle mesh (positions + geometric normals + (u,v), 2·segu·segv tris/patch)
  for rasterization preview / OBJ export / collision proxy. Samples each patch
  over its parameter domain (per-patch (u,v) span for NURBS, [0,1]² otherwise)
  via `lrt_tri_surface_normal`; trimmed-NURBS cells whose centroid is outside
  the trim region are dropped (actual count ≤ the bound). Size buffers with
  `_bound`, then fill; `*ntris_out` reports the full count.
  `lrt_tri_surface_tessellate_indexed[_bound]` is the welded variant: a shared
  (segu+1)×(segv+1) vertex grid per patch + a triangle index buffer (~what GPU
  vertex buffers / OBJ exporters want, far less vertex data); trimmed cells just
  omit their index triples.
- `lrt_tri_surface_project` — closest-point projection (inverse of evaluation):
  the (u,v) on a patch nearest a query point Q, via multi-start Gauss-Newton on
  |S(u,v)-Q|² clamped to the patch domain. For collision response / decal
  projection / snapping. Per-patch (caller picks prim_id; call over all patches
  for a whole-surface nearest point).
- `lrt_tri_curve_tessellate[_bound]` — tessellate a ROUND-LINEAR (hair) scene
  into a tube mesh: each segment a tapered cone frustum with `nsides` radial
  faces (2·nsides tris, no caps), vertices on the cone surface at r(t), outward
  cone-surface normals. Round-linear only (flat is a view-dependent ribbon;
  Bézier u is sub-arc-local) → others return `INVALID_ARGUMENT`.
- `lrt_tri_surface_refit` — in-place refit for animation (deforming patches):
  replace control points and recompute node bounds without rebuilding the tree
  (mirrors `lrt_tri_scene_refit` for triangles; shared `tri_refit_propagate`
  tail + a `prim_kind`-dispatched `tri_leaf_box`). Bilinear (12 floats/patch) and
  bicubic Bézier (48) only — the direct-control-point kinds; NURBS leaves are
  extracted rational patches with no 1:1 map to the input net, so they are
  rejected. Refreshes the shade cache, so the normal/tessellate queries reflect
  the new geometry. Traces identically to a fresh build of the new CPs.
- `lrt_curve_refit` — in-place refit for animated hair: re-derive the segments
  (incl. round-linear CSG-neighbor data) from a new strand set and recompute node
  bounds without a rebuild. Round-linear + flat curves; the strand topology must
  match the original (same segment count). Refreshes the shade cache. Traces
  identically to a fresh build (round joints included).

### Production
- Serialization: `lrt_tri_scene_save[_to_memory]` / `load[_from_memory]`, plus
  zero-copy `lrt_tri_scene_open_mmap` (validates every child ref on load).
  Triangle/curve scenes only.
- Refit: `lrt_tri_scene_refit` updates vertices + node bounds in place (no
  rebuild), for animation.
- Instancing/TLAS: `lrt_tlas_build` / `lrt_tlas_intersect1` / `lrt_tlas_occluded1`
  / `lrt_tlas_refit` — two-level BVH with per-instance 3×4 affine transforms,
  `instance_id`, and a visibility `mask`.

## Vulkan GPU Interop (`lightrt_c_vk.h`)

Optional Vulkan-compute GPU interop for the C11 triangle kernel, in **both
directions**. The Vulkan loader (`lightrt_vkew.{h,c}`) is a C11 port of vkew that
`dlopen`s libvulkan at runtime: **no Vulkan SDK headers, no link-time `-lvulkan`,
no `find_package(Vulkan)`**. Build is opt-in and the test skips (exit 0) when no
device is present.

### Directions
- **Path A — CPU build → GPU trace**: `lrt_vk_trace_scene(engine, scene, rays, n,
  out, err)`. Uploads a scene built by `lrt_tri_scene_build` and traverses it with
  a compute shader that mirrors the scalar CPU kernel (identical hits within fp
  tolerance). Plain triangle scenes, BVH4/BVH8 only.
- **Path B — GPU build → CPU trace**: `lrt_vk_build_scene(engine, verts, ntris,
  layout, &scene, err)`. Computes centroids + 30-bit Morton codes on the GPU,
  finishes the LBVH (radix sort + collapse + leaf packing) on the CPU, and returns
  a heap `lrt_tri_scene` usable with the normal `lrt_tri_*` queries. Matches a FAST
  CPU build.
- **Path C — hardware ray tracing**: `lrt_vk_trace_scene_rtx(engine, verts, ntris,
  rays, n, out, err)`. Builds a real `VkAccelerationStructure` (BLAS + identity
  TLAS) on the GPU and traces it with a `GL_EXT_ray_query` compute shader. Takes
  raw triangles (the AS is vendor-opaque, so trace-only — it cannot feed Path B).
  Requires `lrt_vk_engine_caps() & LRT_VK_CAP_RAY_QUERY` (engine created with
  `want_ray_tracing=1` on an RT-capable device); hits match a Moller-Trumbore CPU
  trace within fp tolerance. For repeated tracing, build the AS once with the
  resident API — `lrt_vk_rtx_scene_build` / `lrt_vk_rtx_scene_trace` /
  `lrt_vk_rtx_scene_free` — which keeps the BLAS+TLAS device-resident and traces
  via device-local ray/hit buffers (the one-shot call above is build+trace+free).

### Engine
`lrt_vk_engine_create` (NULL → caller falls back to CPU), `_destroy`, `_caps`
(`LRT_VK_CAP_COMPUTE/BUFFER_ADDRESS/ACCEL_STRUCT/RAY_QUERY`), `_device_name`,
`_last_error`. A single engine is reusable but not thread-safe (one queue).

### How it works
- Both directions bridge through the existing LRTS serialization blob
  (`lrt_tri_scene_save_to_memory` / `load_from_memory`); the latter bounds-checks
  every child ref, so GPU-built trees are validated for free. `block_stride` must
  equal `tri_block_size(layout)`.
- `vk/shaders/trace_bvh.comp` mirrors `tri_intersect_scalar` exactly over **raw
  `uint[]` SSBOs with manual offset math** (not std430 structs), so the GPU sees
  byte-identical `lrt_bvh{4,8}_node` / `lrt_tri{4,8}` data. Spec constant `W` (4/8)
  + `STACK`; node stride = `8*W` words, block stride = `10*W` words, prim_id at
  word `9*W`. Parity constants replicated: invd clamp `1e18`, MT det `±1e-12`,
  slab `(bound-org)*invd`, deferred tnear culling.
- Path B uses the internal hook `lrt_tri_scene_build_lbvh_morton` in
  `lightrt_c_tri.c` (a refactor of the builder taking optional precomputed Morton
  codes; not a public-ABI entry).
- Path C builds the AS via the soft-loaded `VK_KHR_acceleration_structure` /
  `ray_query` entry points (AS-input and scratch buffers use device addresses;
  the `trace_ray_query.comp` descriptor set binds the TLAS + ray/hit SSBOs).
- Shaders are **pre-compiled to checked-in SPIR-V** (`vk/shaders/*.spv.h`), so a
  normal build needs no shader toolchain. Regenerate after editing a `.comp` with
  `scripts/compile_shaders.sh` — note `trace_ray_query.comp` needs a glslang with
  `GL_EXT_ray_query` (Vulkan SDK ≥1.2 / glslang ≥11; the checked-in set was built
  with one).

### Build / test / benchmark
```bash
cmake -S . -B build_vk -DLIGHTRT_BUILD_VK=ON -DBUILD_TESTING=ON
cmake --build build_vk && ctest --test-dir build_vk -R lightrt_c_vk_test
make vk_test && ./lightrt_c_vk_test          # Makefile path (opt-in)
make shaders                                  # optional SPIR-V regen
cmake -S benchmark_c -B build_bench_c -DLRTBENCH_VK=ON
./build_bench_c/bench_c --backend vk-trace,vk-rtx --verify  # GPU trace + HW RT
```

### Notes / current limits
- `vk-rtx` uses the resident AS (built once) + device-local trace buffers, so its
  benchmark number reflects traversal + per-batch ray/hit PCIe transfer (it beats
  embree on incoherent rays on an RTX 3070). `vk-trace` still re-uploads the BVH
  per call (a resident compute-trace mode and a GPU any-hit/occlusion path are
  follow-ups).
- Path B v1 is hybrid (GPU front end, CPU hierarchy); full-GPU LBVH (radix sort /
  Karras tree / collapse on GPU) is a planned v2/v3.

## HIP GPU Backend (`lightrt_c_hip.h`)

Optional HIP (ROCm/AMD) GPU backend for the C11 triangle kernel, parallel to the
Vulkan path but with a **device-resident scene** (upload the BVH once, trace many
batches) and Phase-2 hooks for WMMA / int-quantized low-precision tracing.
Targets RDNA4 (gfx1201, wave32) but runs on any HIP device. Implementation is
`lightrt_c_hip.hip` (compiled by `hipcc` as C++, all symbols `extern "C"`); the
header is pure C11 so the C library/benchmark include it cleanly. Build is opt-in
and the test skips (exit 0) when no device is present.

### Phase 1 (implemented): fp32 build + trace
- **Resident trace**: `lrt_hip_scene_upload` (CPU-built BVH4/BVH8 → device via the
  LRTS serialization blob, byte-identical to the Vulkan path) then
  `lrt_hip_scene_trace` / `lrt_hip_scene_occluded` (reused/grown device ray/hit
  scratch). The `k_trace<W,STACK>` / `k_occluded<W,STACK>` kernels are a
  byte-for-byte port of `vk/shaders/trace_bvh.comp` over raw `uint32_t*` node/leaf
  buffers (node stride `8*W` words, block stride `10*W`, prim at `9*W`; parity
  constants `INVD_MAX=1e18`, MT det `±1e-12`, deferred tnear cull, far-to-near
  push). Compiled `-ffp-contract=off` to stay bit-faithful to the scalar C kernel
  → matches `lrt_tri_intersect1` to ~99.999% (`max_rel_t < 1e-6`).
- **Hybrid GPU build (Path B)**: `lrt_hip_build_scene` runs `k_centroids` +
  `k_morton` on the GPU (port of `build_morton.comp`), finishes the LBVH on the
  CPU via `lrt_tri_scene_build_lbvh_morton`; matches a FAST CPU build (~50 ms).
- **Full-GPU LBVH (`lrt_hip_scene_build_gpu`, `lightrt_hip_lbvh.hip`)**: builds
  the whole BVH on the GPU with NO CPU hierarchy work — centroids + Morton, a
  hipCUB radix sort of unique 64-bit `(morton<<32|index)` keys, a Karras (2012)
  binary radix tree, bottom-up bounds via the atomic-flag walk-up, and emission
  directly into the trace kernel's BVH4 wide-node format as a binary (2-wide)
  tree (one triangle per leaf block). Returns a resident scene traceable
  immediately. hipCUB-gated (`lrt_hip_have_gpu_build()`). On the 220k-tri
  mandelbulb: **~2.2 ms build** (vs ~143 ms CPU SAH, ~50 ms hybrid) at
  essentially the same primary trace throughput (~218 Mray/s) and 99.999% oracle
  agreement — the fast-rebuild path for topology-changing dynamic scenes. The
  un-collapsed 2-wide tree costs a little on incoherent rays; a GPU collapse to
  4/8-wide is a possible future refinement.
- **GPU refit (dynamic / motion-blur)**: `lrt_hip_scene_refit` updates leaf
  vertices + node bounds in place without rebuilding (multi-pass bottom-up;
  parent index < child index by construction). Matches a CPU refit 100%. On the
  220k-tri mandelbulb it is ~1 ms vs ~136 ms for a full build (~140× faster) —
  the realtime animation path.
- **Fully GPU-resident dynamic pipeline (no per-frame PCIe)**: for animation /
  motion blur the whole loop stays on-device. `lrt_hip_dbuffer` holds resident
  vertex/ray/hit buffers; `lrt_hip_raygen_camera` generates pinhole primary rays
  on the GPU; `lrt_hip_scene_trace_device` / `_occluded_device` trace
  device→device; `lrt_hip_scene_refit_device` / `lrt_hip_scene_build_gpu_device`
  refit/rebuild from a device vertex buffer. The full-GPU build derives Morton
  base/scale on-device (`kl_init6`+`kl_basescale`) — no D2H readback at all.
  Only one-time vertex upload and a final present/debug download cross PCIe.
  `bench_hip --dynamic` runs an orbiting-camera frame loop (1280×720, 220k tris,
  zero per-frame PCIe): ~1500 fps raygen+trace, ~975 fps refit+raygen+trace
  (deforming mesh), ~430 fps full-GPU-rebuild+raygen+trace (topology change).
  Note refit suits the shallow collapsed BVH8 (depth ~20); the GPU binary tree
  is depth ~64, for which a full rebuild is the better dynamic path.
- **One-shot**: `lrt_hip_trace_scene` (upload+trace+free).
- Engine: `lrt_hip_engine_create`/`_destroy`/`_caps`/`_device_name`/`_last_error`.
  Caps report `WMMA`/`FP8`/`INT8`/`INT4` (inferred from gfx11xx/gfx12xx arch).
- `lrt_hip_scene_trace_ex(mode, ...)` selects precision; Phase-2 modes
  (`WMMA_BF16`/`WMMA_FP8`/`WMMA_F32SEED`/`INT8`/`INT4`) currently fall back to fp32.

### Build / test / benchmark
```bash
cmake -S . -B build_hip -DLIGHTRT_BUILD_HIP=ON -DLIGHTRT_BUILD_BENCHMARK_HIP=ON -DBUILD_TESTING=ON
cmake --build build_hip && ctest --test-dir build_hip -R lightrt_c_hip_test
./build_hip/benchmark_hip/bench_hip --scene mandelbulb --tris 200000 --rays 2000000
make hip_test && ./lightrt_c_hip_test           # Makefile path (opt-in, needs hipcc)
make benchmark_hip && ./bench_hip               # benchmark
```
The benchmark (`benchmark_hip/`) reports build_ms + primary/incoherent/shadow
Mray/s + agreement vs the CPU oracle, for `cpu-bvh8` / `hip-fp32` / `hip-build`.
On an RX 9070 XT (gfx1201) hip-fp32 traces a 220k-tri mandelbulb at ~210 Mray/s
primary / ~135 Mray/s incoherent (vs ~19 / ~2 for 1-thread CPU); the GPU build is
~2.7× faster than the CPU SAH build. Override the arch with `-DCMAKE_HIP_ARCHITECTURES=...`
or `make HIP_ARCH=...`.

### Non-triangle primitives on GPU (implemented)
The HIP trace path is primitive-aware: alongside triangles (BVH4/BVH8) it traces
all the BVH4 geometric primitives — **sphere, point (sphere/disc/oriented-disc),
quad, tetra, round-linear & flat curves, cubic Bézier, built-in SDF
(sphere/box/torus), and the parametric surfaces (bilinear / bicubic Bézier /
NURBS / trimmed NURBS)** — by carrying `prim_kind`/`point_type` through the LRTS
header and dispatching `k_trace_prim`/`k_occluded_prim` (BVH4, runtime kind) to
device intersectors ported byte-for-byte from the CPU scalars (`hp_*` in
`lightrt_c_hip.hip`). CPU build → GPU trace; serialization opened up per kind
(USER/SDF-callback and QTRI still refuse). Agreement vs the CPU oracle: analytic
prims, quad/tetra, round/flat curves, and SDF are 100% (max_rel_t 0); cubic
Bézier ~99.96% (GPU scalar adaptive-sweep vs CPU SSE adaptive-sweep). Host
function-pointer custom geometry (`lrt_user_scene_build`) cannot run on the GPU
by construction; `lrt_sdfprim_scene_build` is the GPU-resident replacement.

**On-device shading normals** (`lrt_hip_scene_trace_normals[_device]`): a
post-pass `k_shade_normals` kernel computes the per-hit geometric normal for
parametric surfaces (bilinear/bezpatch/NURBS/trimmed-NURBS — `Ng =
cross(dP/du, dP/dv)` via the same `hp_bezpatch_eval`/`hp_rbez_eval` the
intersector uses) and the radial normal for round-linear curves, mirroring the
CPU `lrt_tri_surface_normal`/`lrt_tri_curve_frame`. Upload copies the CPU scene's
per-prim shade control points to `d_shade_cps`/`d_shade_dom` (via the
`lrt_tri_surface_shade_data` accessor); the kernel indexes them by the hit's
`prim_id`. Verified on an RX 9070 XT (host D2H *and* the device-resident
`_device` path, bit-identical): 100% normal agreement (min cos 1.00000) vs the
CPU oracle across all four surface kinds + round-linear. Triangle/other scenes
carry no shade data → `LRT_RESULT_UNSUPPORTED`. `bench_hip --normals` reports the
post-pass cost: on a 20k-patch bezpatch scene the `k_shade_normals` pass adds
only ~5% on primary rays and <1% on incoherent (traversal-bound) over trace-only.

### Phase 2 (implemented): WMMA + int-quantized leaf kernels
`lightrt_hip_wmma.hip` (compiled into `lightrt_hip` when rocWMMA is present;
`lrt_hip_have_wmma()` reports it). RDNA4 WMMA does `D=A·B+C` — fits batched dense
math, NOT divergent traversal — so the leaf intersection of a coherent 16-ray
tile vs <=16 triangles is cast as the **Plücker edge-side GEMM**: ray Plücker
`A=[dir, cross(org,dir)]` (M=16, K=6) times per-edge Plücker `B_k=[moment;dir]`
(3 edges -> 3 16x16x16 mma ops), fp32/int32 accumulate; the sign of the three
edge functions classifies in/out and `t` is recovered in fp32. Methods
(`lrt_hip_leaf_bench`, `lrt_hip_isect_method`): `SCALAR` (fp32 Moller-Trumbore
baseline), `WMMA_BF16`, `WMMA_FP16`, `WMMA_FP8` (e4m3, leaf-local normalized),
`WMMA_INT8` (leaf-local quantized iu8). `lrt_hip_transform_bench` is the batched
ray transform / motion-blur keyframe-lerp kernel (instancing path).

**Honest verdict (RX 9070 XT, `bench_hip --leaf`, 16 rays/leaf, full-wave
scalar baseline):** scalar fp32 FMA **beats** WMMA for leaf intersection — WMMA
tops out at ~0.5x scalar (fp16) in both coherent and incoherent regimes. The
K=6 tiles waste 10/16 of the WMMA K dimension and the shared-memory staging +
3 GEMMs/leaf cost more than the lean scalar Moller-Trumbore. This is the
expected result for tiny one-tile-per-leaf ops and matches the design's
prediction; the benchmark reports it rather than hiding it. Classification
accuracy vs scalar: fp16 ~98–99.6%, int8 ~94–98%, fp8 ~94–97%, bf16 ~88–97%
(fp16 best; coherent rays graze shared edges so agree slightly lower than
incoherent). Takeaway: on RDNA4 the matrix cores do not accelerate these
CPU-style RT primitives; the precise fp32 trace (Phase 1) is the path to use.
Transform batching is memory-bound, so WMMA does not help it either.

Notes / not implemented: int4 (iu4) WMMA is not exposed by rocWMMA 2.2 (would
need raw `__builtin_amdgcn_wmma_i32_16x16x16_iu4_w32`); since int8/fp16 already
lose to scalar for leaf intersection, lower-precision int4 (same staging cost)
would not change the verdict, so it is skipped. int16 is not a WMMA input type
(the integer GEMM accumulates int32 from iu8/iu4 inputs). Other experimental
ideas with expected low/negative payoff: WMMA box/slab tests (the min/max
reduction is not a matmul) and full coherent-packet traversal calling the WMMA
leaf kernel inline. The full-GPU LBVH (above) is implemented; a remaining
refinement is a GPU collapse of its binary tree to 4/8-wide nodes for faster
incoherent traversal.

## CUDA GPU Backend (`lightrt_c_cuda.h`)

Optional CUDA (NVIDIA) GPU backend for the C11 triangle kernel — a port of the
HIP backend's **fp32 build + trace** path (Phase 1), with the same
device-resident scene model and public-API shape (`lrt_cuda_*` mirroring
`lrt_hip_*`). Implementation is a single `lightrt_c_cuda.cu` (compiled by `nvcc`
as C++, all symbols `extern "C"`); the header is pure C11 so the C
library/test include it cleanly. Build is opt-in and the test skips (exit 0)
when no CUDA device is present. Defaults to Blackwell (`sm_120`, e.g. RTX
50-series); override with `make CUDA_ARCH=sm_90` or
`-DCMAKE_CUDA_ARCHITECTURES=90`.

The port reuses the HIP `.hip` source verbatim through a one-line launch shim
(`#define hipLaunchKernelGGL(k,grid,block,shmem,stream,...) k<<<grid,block,shmem,stream>>>(__VA_ARGS__)`)
and the runtime-API rename (`hipX`→`cudaX`); the device intersectors (`hp_*`:
triangle, sphere/point, quad/tetra, round/flat curves, cubic Bézier, SDF,
parametric surfaces) and kernels (`k_trace`/`k_occluded`/`k_trace_prim`/
`k_occluded_prim`/`k_shade_normals`/`k_raygen_camera`/`k_refit_*`/`k_centroids`/
`k_morton`) are byte-for-byte identical, compiled `--fmad=false` to stay
bit-faithful to the scalar C kernel.

### Implemented (Phase 1, fp32)
- **Resident trace**: `lrt_cuda_scene_upload` (CPU-built BVH4/BVH8 → device via
  the LRTS blob) then `lrt_cuda_scene_trace` / `_occluded`. Bit-exact vs the CPU
  oracle (`tests/test_lightrt_c_cuda.c`: 50k rays, all hits match
  `lrt_tri_intersect1`, 0 hit/miss mismatch, 0 t-disagreement on an RTX 5060 Ti).
- **Hybrid GPU build (Path B)**: `lrt_cuda_build_scene` (`k_centroids`+`k_morton`
  on GPU, LBVH finish on CPU).
- **GPU refit**: `lrt_cuda_scene_refit` (in-place vertex+bounds update, no
  rebuild) — animation path.
- **Device-resident dynamic pipeline**: `lrt_cuda_dbuffer` + `_raygen_camera` /
  `_scene_trace_device` / `_occluded_device` / `_scene_refit_device`.
- **On-device shading normals**: `lrt_cuda_scene_trace_normals[_device]`.
- **One-shot**: `lrt_cuda_trace_scene` (upload+trace+free).
- Engine: `lrt_cuda_engine_create`/`_destroy`/`_caps`/`_device_name`/
  `_last_error`. Caps report `LRT_CUDA_CAP_COMPUTE` only (fp32-only port).

### Not ported (HIP-only for now, stubbed → `NOT_BUILT`)
The Phase-2 **WMMA** matrix-core leaf kernels (`lightrt_hip_wmma.hip`, rocWMMA)
and the **full-GPU LBVH** builder (`lightrt_hip_lbvh.hip`, hipCUB radix sort)
live in separate TUs that depend on AMD-specific libraries; their public entry
points (`lrt_cuda_have_wmma`/`_have_gpu_build`/`_scene_build_gpu[_device]`/
`_leaf_bench`/`_transform_bench`) are stubbed to return `0`/`NULL`/`NOT_BUILT`.
Porting them would mean nvcuda::wmma + CUB, but the HIP "honest verdict" found
WMMA loses to scalar fp32 for leaf intersection, so it is low priority; the
hybrid Path-B build covers fast rebuilds.

### Build / test
```bash
cmake -S . -B build_cuda -DLIGHTRT_BUILD_CUDA=ON -DBUILD_TESTING=ON
cmake --build build_cuda && ctest --test-dir build_cuda -R lightrt_c_cuda_test
make cuda_test && ./lightrt_c_cuda_test         # Makefile path (opt-in, needs nvcc)
```

## Code Conventions

- C++17, no RTTI (`-fno-rtti`), no exceptions (`-fno-exceptions`)
- SIMD detection via preprocessor: `LIGHTRT_HAS_AVX`, `LIGHTRT_HAS_SSE2`, `LIGHTRT_HAS_NEON`, `LIGHTRT_HAS_SVE`, `LIGHTRT_HAS_FP16`
- All core types are 16-byte aligned (`alignas(16)`)
- Use `kInvalidIndex` (0xFFFFFFFF) for invalid/no-hit results
- No external dependencies
