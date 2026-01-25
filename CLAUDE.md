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
- `Triangle`: Triangle primitive with `intersect()` using Moller-Trumbore algorithm
- `BLAS`: Wraps BVH for bottom-level geometry
- `TLAS`: Manages instanced scene with `BLASInstance` transforms
- `BVHNode`: Interior/leaf node using union for child indices or primitive offset/count

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

The overlapping triangles test demonstrates that for spatially overlapping primitives, BVH traversal is O(N) regardless of structure - no spatial acceleration is possible when primitives cannot be separated.

## Code Conventions

- C++17, no RTTI (`-fno-rtti`), no exceptions (`-fno-exceptions`)
- SIMD detection via preprocessor: `LIGHTRT_HAS_AVX`, `LIGHTRT_HAS_SSE2`, `LIGHTRT_HAS_NEON`, `LIGHTRT_HAS_SVE`, `LIGHTRT_HAS_FP16`
- All core types are 16-byte aligned (`alignas(16)`)
- Use `kInvalidIndex` (0xFFFFFFFF) for invalid/no-hit results
- No external dependencies
