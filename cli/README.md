# LightRT USD CLI

The CLI loads USD with `lightusd_c`, builds CPU LightRT BLASes and a scene TLAS,
then renders an image. Direct single-layer loading is the low-memory default;
`--compose` resolves the complete PCP arc graph before conversion.

## Setup and build

Dependencies are ordinary clones under `dep/`; no Git submodules are added.
When `$HOME/work/lightusd_c` exists, the setup script clones that local worktree
(the hyphenated `$HOME/work/lightusd-c` spelling is also accepted).

```bash
./scripts/setup_deps.sh
cmake -S cli -B build_usd_cpu -DCMAKE_BUILD_TYPE=Release
cmake --build build_usd_cpu -j
```

`LIGHTRT_USE_LIGHTUSD_C` defaults to `ON`. Set it to `OFF` only to build the
older TinyUSDZ loader instead.

## Usage

```bash
build_usd_cpu/lightrt_cli scene.usdc -o output.png -w 800 -h 600
build_usd_cpu/lightrt_cli scene.usdc --load-only --geometry-only
build_usd_cpu/lightrt_cli scene.usda --compose --load-only
build_usd_cpu/lightrt_cli scene.usdc --camera fallback -w 256 -h 256
```

| Option | Description |
| --- | --- |
| `-o <file>` | PNG, JPEG, BMP, or TGA output (default `output.png`) |
| `-w <width>`, `-h <height>` | Output dimensions |
| `-t <timecode>` | Load one time sample |
| `--time-range <start> <end> <step>` | Render a sequence |
| `--camera <name-or-index>` | Select an authored camera |
| `--camera fallback` | Ignore authored cameras and frame the scene bounds |
| `--mblur-samples <N>` | Motion-blur samples |
| `--spp <N>` | Samples per pixel |
| `--envmap <file>` | Environment map |
| `--compose` | Resolve sublayers, references, payloads, variants, inherits, and specializes through lightusd PCP |
| `--curve-segments <N>` | Curve tessellation samples per cubic/NURBS/Hermite span, from 1 to 64 (default 8) |
| `--geometry-only` | Skip materials, textures, UVs, and shading normals to reduce large-scene memory |
| `--load-only` | Load the layer and build acceleration structures without rendering |

Set `LIGHTRT_USD_VERBOSE=1` for per-primitive loader diagnostics.

## Geometry support

- `Mesh`, including per-face material subsets in the full shading path
- `BasisCurves` with linear, Bezier, Catmull-Rom, or B-spline bases
- Rational `NurbsCurves`, including orders, knots, ranges, and point weights
- `HermiteCurves`, including authored tangent evaluation
- Constant, uniform, varying, and vertex `primvars:displayColor` on curve schemas
- Time-sampled points, widths, display colors, topology counts, Hermite
  tangents, and rational NURBS order/knot/range/weight data
- Authored shutter-open/close sampling with transform, width, color, and
  deformation motion blur for tessellated curves
- `Points`, represented by analytic sphere primitives using authored widths
- `ParticleField3DGaussianSplat`, including anisotropic scale, quaternion
  orientation, opacity, and view-dependent spherical harmonics through degree 3
- `Sphere`, represented analytically, and `Cube`

Meshes, curves, points, and Gaussian fields each build local acceleration
structures. Curves use a per-segment BLAS with tapered capsule intersection;
instances are placed in a top-level BVH, so rays do not linearly scan large
scene graphs or long tessellated strands. Gaussian fields use front-to-back
density compositing in the CPU reference renderer.

Composition serializes the resolved stage to an adopted in-memory USDC layer.
This avoids a second copy, but a very large composed scene still temporarily
holds both PCP stage data and flattened bytes; use direct loading when the input
is already flattened.

## Large-scene examples

```bash
# Flattened, non-composed Caldera Island scene
build_usd_cpu/lightrt_cli \
  /mnt/disk1/data/caldera/build/caldera.flattened.usdc \
  --geometry-only --camera fallback -w 256 -h 144 \
  -o caldera.png

# Individual, non-composed A-Lab payload containing meshes and curves
build_usd_cpu/lightrt_cli \
  /mnt/disk1/data/alab/_merged_ALab/fragment/geocache/animbase/stoat/render_high/cache/mk020_0281_geocache_animbase_stoat_render_high_cache/payload.usdc \
  --geometry-only --camera fallback -w 256 -h 256 \
  -o alab-stoat.png

# Composed A-Lab splat: sublayer + variant + payload + camera reference
build_usd_cpu/lightrt_cli \
  /mnt/disk1/data/alab/_merged_ALab/extras/alab_splat_with_camera.usda \
  --compose -w 512 -h 512 -o alab-splat.png
```

When `-t` is omitted, the loader evaluates time-sampled transforms and cameras
at the layer's authored `startTimeCode`.

Use `--load-only` first when qualifying a new production-scale layer.
