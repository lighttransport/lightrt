# LightRT Tasks

## Current Status (as of 2026-03-01)

The `lightrt_cli` renderer has two backends:
- **tydra path**: uses tinyusdz's Tydra render-data converter (mature)
- **lightusd-c path**: uses the lightweight C API in `deps/tinyusdz/sandbox/lightusd-c/` (active development)

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

## Key Files

| File | Purpose |
|------|---------|
| `cli/main.cc` | Main renderer, scene loading, shading loop |
| `cli/scene.hh` | Scene data structures (MeshBLAS, Instance, Camera, etc.) |
| `common/materials.hh` | OpenPBRMaterial struct with texture ID fields |
| `common/shading.hh` | evalBRDF, evalOpenPBR, evalEnvmap, MIS helpers |
| `deps/tinyusdz/sandbox/lightusd-c/lydra/lydra-c/lydra_c_scene.c` | Material/camera/light extraction (gitignored, not committed) |
| `deps/tinyusdz/sandbox/lightusd-c/src/lusd_stage_tinyusdz.cc` | USD stage loading for lightusd-c |

## Build

```bash
make -C build-minsizerel -j$(nproc)
build-minsizerel/lightrt_cli <file.usda> -o out.png -w 400 -h 300 --spp 16
```
