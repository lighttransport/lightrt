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

- [ ] **Texture infrastructure** (from plan): load material textures, store
  per-triangle UVs, sample at hit points. The plan in
  `~/.claude/plans/fluffy-tumbling-fairy.md` has full details.

- [ ] **Asset resolver**: resolve texture paths relative to the USD file
  directory. Partially designed in the plan.

### Medium Priority

- [ ] **Smooth normals for lightusd-c path**: `tri_normals` is not currently
  populated. Add authored normal extraction + fallback to computed smooth normals
  via `lydra_c_compute_smooth_normals()`. Meshes currently use flat shading
  (face normals from cross product).

- [ ] **Y-up scene camera fix**: For Y-up scenes without an authored camera, the
  auto camera uses `cam_up = (0,1,0)` which is correct. But verify this is
  working well for varied scenes.

- [ ] **DistantLight support**: The lightusd-c path uses
  `-(world_xform[0*4+2], world_xform[1*4+2], world_xform[2*4+2])` for the
  direction (column 2). Verify this is correct with the same row-vector
  convention used for the camera.

- [ ] **Multi-material rendering test**: Verify GeomSubset materials still
  work correctly after the camera fix.

### Low Priority / Future

- [ ] **USDC support for lightusd-c path**: Currently the lightusd-c path
  handles both USDA and USDC (tested). Continue expanding model support.

- [ ] **Motion blur**: Camera shutter interval is read but mblur ray time
  is only used when `--mblur-samples N` > 1. Works for both paths.

- [ ] **tydra path parity**: Ensure tydra path gets the same camera fix if
  it has the same bug. The tydra path uses `node.global_matrix.m[r][c]` with
  the same convention (row-major, translation in row 3).

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
