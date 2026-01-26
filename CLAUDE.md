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
- `BVH`: Single-level BVH with SAH-based construction and SIMD traversal (AABB primitives)
- `TriangleBVH`: BVH over triangles with Moller-Trumbore ray-triangle intersection
- `BLAS`: Wraps BVH for bottom-level geometry
- `TLAS`: Manages instanced scene with `BLASInstance` transforms
- `BVHNode`: Interior/leaf node using union for child indices or primitive offset/count
- `MMapTriangleBVH`: Zero-copy BVH over external triangle data with compact nodes
- `MMapGenericBVH`: Zero-copy BVH for custom primitives via callbacks
- `CompactBVHNode`: 24-byte node with 16-bit quantized bounds (vs 56-byte BVHNode)

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
- `use_mailboxing`: Avoid duplicate tests in SBVH (important when split_ratio > 1)
- `early_termination`: Stop on first hit (for shadow rays)

Presets:
- `TraversalConfig::fast(K)`: Limit to K tests with mailboxing
- `TraversalConfig::anyHit()`: Stop on first hit

`TraversalStats` returns traversal statistics:
- `nodes_visited`, `prims_tested`, `prims_hit`, `terminated_early`

### Build Configuration
`BVHBuildConfig` controls construction:
- `use_sah`: Surface Area Heuristic for optimal splits (default: true)
- `use_binning`: Binned SAH for large datasets (default: true)
- `max_leaf_size`: Maximum primitives per leaf (default: 4)
- `force_max_leaf_size`: Always enforce max_leaf_size, ignore SAH cost (default: false)

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

## Memory Usage

Quantized primitives trade precision for memory savings:

| Primitive | Full Size | Quantized Size | Compression |
|-----------|-----------|----------------|-------------|
| Triangle | 36 bytes | 18 bytes | 2x |
| GaussianSplat | ~220 bytes | ~32 bytes | 7x |

Quantized types require a global bounding box for coordinate reconstruction. Use `quantize()` to compress and `dequantize()` to restore full precision before intersection testing.

## Code Conventions

- C++17, no RTTI (`-fno-rtti`), no exceptions (`-fno-exceptions`)
- SIMD detection via preprocessor: `LIGHTRT_HAS_AVX`, `LIGHTRT_HAS_SSE2`, `LIGHTRT_HAS_NEON`, `LIGHTRT_HAS_SVE`, `LIGHTRT_HAS_FP16`
- All core types are 16-byte aligned (`alignas(16)`)
- Use `kInvalidIndex` (0xFFFFFFFF) for invalid/no-hit results
- No external dependencies
