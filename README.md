# lightrt

Lightweight and efficient ray tracing & BVH kernel

## Overview

LightRT is a modern, high-performance BVH (Bounding Volume Hierarchy) construction and ray tracing framework designed with GPU ray tracing algorithms in mind. It provides a clean C++17 implementation with SIMD optimizations, quantization support, and FP16 capabilities.

## Features

- **Two-Level BVH**: TLAS (Top-Level Acceleration Structure) and BLAS (Bottom-Level Acceleration Structure) for efficient instancing
- **SIMD Optimizations**: SSE2, AVX, AVX2 (x86_64), NEON, SVE (ARM)
- **Quantization Support**: 16-bit quantization for memory-efficient BVH storage
- **FP16 Support**: Half-precision floating point conversions (F16C on x86, native on ARM)
- **SAH-based Building**: Surface Area Heuristic for optimal BVH quality
- **Binned SAH**: Fast approximate SAH for large datasets
- **C++17**: Modern C++ with no RTTI, no exceptions
- **Build Systems**: Both Makefile and CMake support
- **Minimal Files**: Just 2 core files - `lightrt.hh` and `lightrt.cc`

## Building

### Using Makefile

```bash
# Build library and example
make

# Build with debug symbols
make DEBUG=1

# Disable specific SIMD features
make NO_AVX=1
make NO_AVX2=1
make NO_F16C=1
make NO_SVE=1   # ARM only

# Run example
make run

# Clean build artifacts
make clean

# Show build configuration
make info
```

### Using CMake

```bash
mkdir build
cd build
cmake ..
make

# Build in debug mode
cmake -DCMAKE_BUILD_TYPE=Debug ..
make

# Disable specific features
cmake -DNO_AVX=ON ..
cmake -DNO_AVX2=ON ..
cmake -DNO_F16C=ON ..
cmake -DNO_SVE=ON ..  # ARM only

# Run example
./lightrt_example
```

## Quick Start

```cpp
#include "lightrt.hh"
using namespace lightrt;

// Create scene primitives (AABBs)
std::vector<AABB> primitives;
primitives.push_back(AABB(Vec3(-1, -1, -1), Vec3(1, 1, 1)));
primitives.push_back(AABB(Vec3(2, -1, -1), Vec3(4, 1, 1)));
// ... add more primitives

// Build BVH
BVH bvh;
BVHBuildConfig config;
config.use_sah = true;        // Use Surface Area Heuristic
config.use_binning = true;    // Use binned SAH for speed
config.max_leaf_size = 4;     // Max primitives per leaf
bvh.build(primitives, config);

// Create ray
Ray ray(Vec3(0, 0, -10), Vec3(0, 0, 1));

// Traverse BVH (SIMD optimized)
float hit_t;
uint32_t hit_prim = bvh.traverseSIMD(ray, hit_t);

if (hit_prim != kInvalidIndex) {
    std::cout << "Hit primitive " << hit_prim << " at t=" << hit_t << "\n";
}
```

## Two-Level BVH Example

```cpp
// Create bottom-level BVHs
std::vector<BLAS> blas_array;
for (int i = 0; i < 3; i++) {
    BLAS blas;
    std::vector<AABB> prims = createPrimitives();
    blas.build(prims);
    blas_array.push_back(blas);
}

// Create instances
std::vector<BLASInstance> instances;
BLASInstance inst;
inst.blas_id = 0;
inst.bounds = computeTransformedBounds(blas_array[0]);
// Set inst.transform and inst.inv_transform for positioning
instances.push_back(inst);

// Build top-level BVH
TLAS tlas;
tlas.build(instances);

// Trace ray through two-level structure
TLAS::TraceResult result = tlas.trace(ray, blas_array);
if (result.instance_id != kInvalidIndex) {
    std::cout << "Hit instance " << result.instance_id 
              << ", primitive " << result.primitive_id << "\n";
}
```

## API Reference

### Core Types

- **Vec3**: 3D vector with basic math operations
- **Ray**: Ray with origin, direction, tmin, tmax
- **AABB**: Axis-aligned bounding box with intersection tests
- **BVHNode**: Single node in the BVH hierarchy
- **BVH**: Single-level BVH structure
- **BLAS**: Bottom-level acceleration structure
- **BLASInstance**: Instance of a BLAS with transformation
- **TLAS**: Top-level acceleration structure

### Build Configuration

```cpp
struct BVHBuildConfig {
    uint32_t max_leaf_size;      // Max primitives per leaf (default: 4)
    uint32_t min_leaf_size;      // Min primitives to create leaf (default: 1)
    float traversal_cost;        // Cost of traversing interior node (default: 1.0)
    float intersection_cost;     // Cost of primitive intersection (default: 1.0)
    bool use_sah;                // Use Surface Area Heuristic (default: true)
    bool use_binning;            // Use binned SAH (default: true)
    uint32_t num_bins;           // Number of bins for binned SAH (default: 16)
};
```

### Quantization

```cpp
// Quantize AABB to 16-bit representation
QuantizedAABB quantized;
quantized.quantize(aabb, global_min, global_max);

// Dequantize back to full precision
AABB dequantized = quantized.dequantize(global_min, global_max);
```

### FP16 Conversion

```cpp
#ifdef LIGHTRT_HAS_FP16
    uint16_t half = floatToFP16(3.14159f);
    float full = fp16ToFloat(half);
#endif
```

## Architecture Support

### x86/x64
- **SSE2**: Baseline SIMD support (always enabled on x64)
- **AVX**: 256-bit SIMD operations
- **AVX2**: Enhanced 256-bit operations with FMA
- **F16C**: Hardware FP16 conversion

### ARM
- **NEON**: 128-bit SIMD (ARMv7/ARMv8)
- **SVE**: Scalable Vector Extension (ARMv8+)
- **FP16**: Native half-precision arithmetic

## Performance Characteristics

- **BVH Construction**: O(n log n) with SAH, O(n) with simple splits
- **Ray Traversal**: O(log n) average case
- **Memory**: ~48 bytes per node (uncompressed), ~24 bytes (quantized)
- **SIMD Speedup**: 1.5-3x depending on architecture and scene

## Requirements

- **C++17** compatible compiler (GCC 7+, Clang 5+, MSVC 2017+)
- **CMake 3.10+** (for CMake builds)
- **GNU Make** (for Makefile builds)

## Compiler Flags

The framework enforces:
- `-std=c++17`: C++17 standard
- `-fno-rtti`: No runtime type information
- `-fno-exceptions`: No exception handling
- `-msse2 -mavx -mavx2 -mfma`: SIMD instructions (x86)
- `-march=armv8-a`: ARM NEON baseline (ARM64)

## License

MIT License - see LICENSE file for details

Copyright (c) 2026 Light Transport Entertainment, Inc.

## Contributing

This is a minimal, focused BVH kernel. Contributions should maintain:
- No external dependencies
- Just 2 core files (lightrt.hh and lightrt.cc)
- No RTTI, no exceptions
- C++17 compatibility
- SIMD-friendly design

## Example Output

```
=== LightRT Capabilities ===
  SSE2: NO
  AVX: YES
  NEON: NO
  SVE: NO
  FP16: YES
  C++ Standard: 201703
  Exceptions: DISABLED
  RTTI: DISABLED

=== Single-Level BVH Test ===
Creating scene with 10000 primitives...
Building BVH...
BVH built successfully in 0 ms

BVH Statistics:
  Total nodes: 1
  Leaf nodes: 1
  Max depth: 0
  Average leaf size: 10000
  SAH cost: 2.50499e+07

Performance test with 10000 rays...
  Traced 10000 rays in 453 ms
  Hit rate: 69.16%
  Rays/second: 22075.1
```

