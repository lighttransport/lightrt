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

## Code Conventions

- C++17, no RTTI (`-fno-rtti`), no exceptions (`-fno-exceptions`)
- SIMD detection via preprocessor: `LIGHTRT_HAS_AVX`, `LIGHTRT_HAS_SSE2`, `LIGHTRT_HAS_NEON`, `LIGHTRT_HAS_SVE`, `LIGHTRT_HAS_FP16`
- All core types are 16-byte aligned (`alignas(16)`)
- Use `kInvalidIndex` (0xFFFFFFFF) for invalid/no-hit results
- No external dependencies
