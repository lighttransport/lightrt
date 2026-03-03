# LightRT Tasks

## Current Status (as of 2026-03-01)

The `lightrt_cli` renderer has two backends:
- **tydra path**: uses tinyusdz's Tydra render-data converter (mature)
- **lightusd-c path**: uses the lightweight C API in `deps/lightusd-c/` (active development)

Recent work has focused on the lightusd-c path. The renderer produces correct
images for: cube-previewsurface, chromeball (ND_standard_surface metallic),
colorchart, geomsubset multi-material, emissive planes, glass sphere.

### Recently Fixed (this session)
- Camera transform convention bug: wrong matrix indices (column 3 = zeros)
  instead of row 3 (translation). Now correctly reads `m[12..14]` for position,
  `-row2` for forward, `row1` for up.
- Removed incorrect Z-up camera rotation that corrupted the matrix without
  converting translation (geometry stays in original coordinate system).
- Emission default bug in `lydra_c_scene.c`: `emission_color` was initialized to
  `(1,1,1)` causing all non-emissive materials to render as pure white.
  Fixed to `(0,0,0)`.

### Previously Fixed
- Brace imbalance in glass/transmission code
- Glass background fallback color mismatch
- ND_standard_surface metalness (`inputs:metalness` not `inputs:base_metalness`)
- `--envmap` CLI flag for loading HDR environment maps
- Delta-specular mirror path for near-mirror metallic (roughness < 0.05)
- Auto-elevate camera for flat/horizontal-plane scenes (Y extent < 15% of XZ)
- GeomSubset per-face material support with BVH reorder fix
- Smooth normals, texture sampling, normal maps, sphere tessellation

---

## TODO

### High Priority

- [x] **Lighting quality**: SphereLight now uses area-light sampling with
  radius-aware geometry factor (uniform surface sampling, `area / r²` term).
  Point lights still use `1/r²`. No ambient term added.

- [x] **Z-up scene support**: Geometry is NOT converted from Z-up to Y-up.
  Camera is correctly left in Z-up space. Default camera fallback now respects
  `upAxis` (Z-up uses `(0,0,1)`, X-up uses `(1,0,0)`, Y-up uses `(0,1,0)`).

- [x] **Texture infrastructure** (from plan): load material textures, store
  per-triangle UVs, sample at hit points. (Plan file
  `~/.claude/plans/fluffy-tumbling-fairy.md` not found; implemented directly.)

- [x] **Asset resolver**: resolve texture paths relative to the USD file
  directory.

### Medium Priority

- [x] **Smooth normals for lightusd-c path**: `tri_normals` populated from
  authored normals or smooth-normal fallback (`lydra_c_compute_smooth_normals()`).

- [x] **Y-up scene camera fix**: Verified fallback camera on Y-up scene
  (e.g., `mtlx-normalmap-cube.usda`).

- [x] **DistantLight support**: Verified lightusd-c render with DistantLight
  scene (`mtlx-normalmap-cube.usda`).

- [x] **Multi-material rendering test**: Verified `geomsubset-test-001.usda`.

### Low Priority / Future

- [x] **USDC support for lightusd-c path**: Verified with
  `cube-previewsurface.usdc` in lightusd-c.

- [x] **Motion blur**: Verified `--mblur-samples 2` path on `skintest.usda`.

- [x] **tydra path parity**: Camera uses the same row-major transform
  convention in `main.cc`.

---

## Proposed Enhancements (Codebase Review)

### High Priority

1. **Documentation for new features**
   - The codebase has several advanced features (SBVH, AutoTuner, MMapBVH) that lack comprehensive documentation in README
   - Consider adding a "Usage" section showing how to use these features

2. **Test coverage for spatial queries**
   - `test_spatial_query.cc` exists but needs to be integrated into CI/test suite
   - Currently standalone, not part of automated build/tests

3. **Memory-mapped BVH documentation**
   - `MMapTriangleBVH` and `MMapGenericBVH` are powerful features but lack usage examples
   - Add "Zero-Copy BVH" section to README with concrete examples

4. **Collision detection examples**
   - BVH-BVH collision detection and swept collision features lack documentation/examples
   - Add "Collision Detection" section with usage patterns

5. **Heatmap writer usage**
   - `HeatmapWriter` class has multiple colormaps and metrics but no README section
   - Add "Visualization" section with example code

6. **Profile traversal examples**
   - `NoProfiler`/`WithProfiler` template policy for profiling traversal lacks documentation
   - Add "Profiling" section showing how to collect traversal stats

7. **Multi-hit traversal examples**
   - `MultiHitResult` for transparency rendering lacks usage guidance
   - Add "Transparency/CSG" section with example

8. **AutoTuner integration**
   - `AutoTuner` class exists but lacks documentation on when/how to use it
   - Add "Automatic Configuration" section

9. **SBVH vs TriangleBVH comparison**
   - When to use SBVH for pathological scenes vs regular BVH
   - Add "Scene Analysis" guidance

10. **Primitive types documentation**
    - Many primitive types (Quad, NGon, Sphere, Disk, etc.) lack usage examples
    - Consider adding "Primitive Types" section with examples

11. **Gaussian Splats examples**
    - `GaussianSplat` and `QuantizedGaussianSplat` for neural radiance fields
    - Lack concrete usage examples in README

12. **Curve primitives**
    - `Curve` with Linear/Bezier/CatmullRom types lacks documentation
    - Add "Hair/Fiber Rendering" section

13. **Custom geometry callback**
    - `CustomGeometry` for user-defined intersection
    - Needs "Extending with Custom Primitives" section

### Medium Priority

14. **Performance comparison table**
    - Add benchmark results comparing LBVH vs SAH build methods
    - Document memory vs speed tradeoffs for MMapBVHConfig presets

15. **Thread safety**
    - Clarify if BVH is thread-safe for concurrent traversal
    - Add note about `TaskSystem` and usage guidelines

16. **CMake vs Makefile**
    - When to use each build system
    - Consider deprecating one or document use cases

17. **WebGPU verification**
    - WebGPU path exists but lacks clear documentation
    - Add "WebGPU Integration" section for WGSL usage

### Low Priority

18. **CLI renderer documentation**
    - `cli/` directory has renderer but lacks docs
    - Consider adding "CLI Usage" for the renderer

19. **Viewer backends**
    - Multiple viewer implementations (Wayland, X11, Windows, WebGPU)
    - Document when to use each backend

20. **Benchmark test suite**
    - `benchmark/benchmark.cc` is comprehensive but lacks test scenarios
    - Consider adding unit tests for edge cases

21. **Memory allocation**
    - Document alignment requirements (`alignas(16)`)
    - Add note on minimum alignment for SIMD traversal

22. **Constants and configuration**
    - `kInfinity`, `kEpsilon`, `kInvalidIndex` - consider making configurable
    - Or document why these values are appropriate

23. **Memory alignment & TaskSystem memory manager**
    - Document alignment constants - Define `kAlignment` = 16 and `kRayContextAlignment` = 32
    - Add alignment verification - Compile-time checks for critical types
    - Document TaskSystemGuard - RAII pattern for automatic cleanup
    - Document thread pool - When/why to use TaskSystem vs direct threading
    - Add memory benchmark - Compare 16-byte vs 32-byte alignment impact
    - Document SIMD requirements - Which traversal modes need which alignment
    - Add alignment comment - Why 16 bytes (not 8 or 32)?
    - Add memory stats - Track TaskSystem memory usage
    - Document queue size - Max tasks in queue before blocking
    - Add alignment test - Verify alignment at runtime with assert

---

## Key Files

| File | Purpose |
|------|---------|
| `cli/main.cc` | Main renderer, scene loading, shading loop |
| `cli/scene.hh` | Scene data structures (MeshBLAS, Instance, Camera, etc.) |
| `common/materials.hh` | OpenPBRMaterial struct with texture ID fields |
| `common/shading.hh` | evalBRDF, evalOpenPBR, evalEnvmap, MIS helpers |
| `deps/lightusd-c/lydra/lydra-c/lydra_c_scene.c` | Material/camera/light extraction (gitignored, not committed) |
| `deps/lightusd-c/src/lusd_stage_tinyusdz.cc` | USD stage loading for lightusd-c |

## Build

```bash
make -C build-minsizerel -j$(nproc)
build-minsizerel/lightrt_cli <file.usda> -o out.png -w 400 -h 300 --spp 16
```

## Proposed Code Enhancements

### Documentation Gaps

1. **SBVH usage examples** - When to use SBVH vs regular BVH for pathological geometry
2. **AutoTuner integration** - How to automatically select optimal BVH config
3. **MMapBVHConfig presets** - Memory vs speed tradeoffs documented
4. **Collision detection** - BVH-BVH collision and swept collision examples
5. **Heatmap visualization** - How to use HeatmapWriter for traversal stats
6. **Profile traversal** - Using NoProfiler/WithProfiler for zero-overhead profiling
7. **Multi-hit traversal** - Transparency rendering with MultiHitResult
8. **Primitive types** - Usage examples for Quad, NGon, Sphere, Disk, Curve
9. **Gaussian Splats** - Neural radiance field rendering examples
10. **Curve primitives** - Hair/fiber rendering with Curve types

### Test Coverage

1. **Spatial queries** - Integrate test_spatial_query.cc into build
2. **Edge cases** - Add unit tests for pathological geometry
3. **Thread safety** - Document concurrent traversal safety
4. **Memory alignment** - Document SIMD alignment requirements

### Build System

1. **CMake vs Makefile** - Document when to use each
2. **WebGPU** - Add documentation for WebGPU/WGSL integration
3. **Viewer backends** - Document Wayland/X11/Windows/WebGPU viewer choices

### CLI Renderer

1. **CLI documentation** - Add usage examples for CLI renderer
2. **Viewer backends** - Document backend selection criteria

---

**Note:** This document should be updated periodically as tasks are completed or priorities shift.