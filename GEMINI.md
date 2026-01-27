# LightRT Project Context

## Project Overview

**LightRT** is a lightweight, high-performance C++17 ray tracing and BVH (Bounding Volume Hierarchy) construction framework. It is designed for GPU ray tracing algorithms but implemented in clean, dependency-free C++.

**Key Features:**
*   **Core Architecture:** Single-header-style simplicity (just `lightrt.hh` and `lightrt.cc`).
*   **Performance:** SIMD optimizations (SSE2, AVX, AVX2, NEON, SVE), FP16 support, and quantization.
*   **BVH Features:** Two-Level BVH (TLAS/BLAS), SAH-based building, LBVH (Linear BVH), and spatial splits (SBVH).
*   **Primitives:** Supports Triangles, Quads, Spheres, Curves (Hair), Gaussian Splats, and custom geometry.
*   **Zero-Copy:** Memory-mapped BVH support for external data.

## Building and Running

The project supports both `Makefile` and `CMake`.

### Using Makefile (Recommended for Development)

*   **Build Everything (Lib, Example, Benchmark):**
    ```bash
    make
    ```
*   **Build & Run Example:**
    ```bash
    make run
    ```
*   **Build & Run Benchmark:**
    ```bash
    make benchmark
    # Custom params: make benchmark TRIANGLES=50000 RAYS=200000
    ```
*   **Debug Build:**
    ```bash
    make DEBUG=1
    ```
*   **Clean:**
    ```bash
    make clean
    ```
*   **Disable SIMD (if needed):**
    ```bash
    make NO_AVX=1 NO_AVX2=1
    ```

### Using CMake

```bash
mkdir build && cd build
cmake ..
make
./lightrt_example
```

## Development Conventions

*   **Language Standard:** C++17 (`-std=c++17`).
*   **Constraints:** No RTTI (`-fno-rtti`) and no exceptions (`-fno-exceptions`).
*   **Dependencies:** None. The project must remain self-contained.
*   **File Structure:**
    *   `lightrt.hh`: Main header file containing all class definitions and template implementations.
    *   `lightrt.cc`: Implementation file for non-template code.
    *   `example.cc`: Usage demonstration.
    *   `benchmark/`: Performance testing code.
*   **Code Style:**
    *   Align core types to 16 bytes (`alignas(16)`).
    *   Use `kInvalidIndex` (0xFFFFFFFF) for invalid results.
    *   Prefer `uint32_t` and `float` types.

## Key Architecture Components

*   **`BVH`**: The core single-level acceleration structure.
*   **`TLAS` / `BLAS`**: Top-Level and Bottom-Level acceleration structures for instancing.
*   **`SBVH`**: Split BVH for handling problematic geometry (long/large triangles).
*   **`AutoTuner`**: Utility to automatically select the best build/traversal configuration.
*   **`MMapTriangleBVH`**: For loading/using pre-built BVH data with zero-copy.
*   **`HeatmapWriter`**: Zero-dependency image writer (BMP/PNG) for visualizing traversal cost.

## Testing & Verification

*   Run the example to verify basic functionality: `make run`
*   Run benchmarks to ensure performance regressions are not introduced: `make benchmark`
