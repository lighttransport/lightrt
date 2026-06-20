# mtlxrender

A tiny, dependency-light **C11** path tracer that renders real
[MaterialX](https://materialx.org/) assets using the LightRT triangle BVH and an
OpenPBR-style layered BSDF. Built to render the MaterialX **Chess set**.

![chess render](docs/chess.png)

The same scene under a Radiance `.hdr` environment (image-based lighting):

![chess HDRI](docs/chess_hdri.png)

## What it does

- Loads a (binary) **glTF** mesh via **tinygltf v3** (pure-C `tg3_*` API).
- Parses a **`.mtlx`** document with a hand-written C11 XML parser and builds an
  in-memory node graph.
- Binds materials to geometry **by name** (`<materialassign geom="...">` matches
  the glTF node/mesh name — the chess `.mtlx` has 15 such assignments).
- Evaluates the node graph with a simple demand-driven **interpreter** (one
  dispatch per node category) producing OpenPBR parameters per shade point.
  Supported node categories:
  - **textures**: `image`, `tiledimage`, `hextiledimage`, `gltf_image`,
    `gltf_colorimage`, `normalmap`, `gltf_normalmap`
  - **math**: `add` `subtract` `multiply` `divide` `modulo` `power` `min` `max`
    `atan2` `sin` `cos` `tan` `asin` `acos` `atan` `sqrt` `ln` `exp` `abs`
    `floor` `ceil` `round` `sign` `normalize` `magnitude` `dotproduct`
    `crossproduct`
  - **adjust/compositing**: `mix` `clamp` `smoothstep` `remap` `range`
    `contrast` `saturate` `luminance` `rgbtohsv` `hsvtorgb` `invert`
  - **channel**: `separate2/3/4` `combine2/3/4` `extract` `convert` `swizzle`
  - **procedural**: `constant` `noise3d` `fractal3d` `cellnoise3d` `ramplr`
    `splitlr`
  - **geometric**: `texcoord` `position` `normal` `tangent` `bitangent`
    `geomcolor` `place2d`
- Supports five surface shader models, all mapped onto the OpenPBR BSDF:
  `standard_surface`, `open_pbr_surface`, `gltf_pbr`, `UsdPreviewSurface`,
  `disney_principled`.
- Path-traces with **NEE + MIS** against an environment light, Russian roulette,
  an OpenPBR-style BSDF (metallic-roughness + dielectric GGX specular + smooth
  glass transmission), and **subsurface scattering** (tinted-diffuse by default,
  or `--sss-walk` for a random walk).
- Writes a linear **EXR** (tinyexr v3) and an optional tonemapped sRGB **PNG**.
  sRGB↔linear colorspace conversion is applied to `srgb_texture`-tagged inputs.

`standard_surface` inputs map onto a single OpenPBR-style BSDF (~1:1), so the
chess set renders unchanged.

## Build

```bash
# from this directory
./vendor_deps.sh     # fetch third-party libs into deps/ (git-ignored)
make                 # -> ./mtlxrender
# or
cmake -S . -B build && cmake --build build -j
```

`vendor_deps.sh` prefers local clones under `$HOME/work` (override with
`TINYGLTF_DIR=` / `TINYEXR_DIR=`) and falls back to cloning from GitHub.

Everything is C11. It links `lightrt_c_tri.c`, `tiny_gltf_v3.c`, and the
tinyexr v3 `src/*.c` directly (vendored under `deps/`). No external libraries.

## Render the chess set

```bash
MTLX=~/work/MaterialX/resources/Materials/Examples/StandardSurface/standard_surface_chess_set.mtlx
GLB=~/work/MaterialX/resources/Geometry/chess_set.glb

./mtlxrender --gltf $GLB --mtlx $MTLX \
    --w 800 --h 600 --spp 128 --bounces 6 \
    --sky --sun --sun-az 125 --sun-el 38 --sun-intensity 3.5 \
    --cam-yaw 30 --cam-pitch 22 --cam-dist 1.05 --exposure 1.3 \
    --out chess.exr --png chess.png
```

`--sun` adds a directional light (NEE shadow rays) for crisp cast shadows;
drop it for soft dome-only lighting. `--env` accepts both **Radiance `.hdr`**
and **`.exr`** lat-long environment maps (importance-sampled). Run
`./mtlxrender --help` for the full option list (camera orbit, thread count, etc.).

## Golden reference tests

`golden.sh` renders a curated set of example materials (across all five shader
models) on the MaterialX shaderball, plus the chess scene, under an HDRI, and
manages them as committed reference images. Renders are deterministic (fixed
seed; per-pixel RNG independent of thread scheduling), so a matching build
reproduces them bit-for-bit.

```bash
./golden.sh gen      # (re)generate references into golden/  (PNG + EXR)
./golden.sh check    # re-render and diff against golden/*.png (RMSE)
```

The committed `golden/*.png` are the visual + regression references; `check`
recomputes each and reports per-material RMSE (PASS within `TOL`, default 0.02).
`mtlxrender --diff a b [tol]` compares any two EXR/PNG images directly.

![golden contact sheet](docs/golden_contact.png)

## Dependencies (vendored, under `deps/`, git-ignored)

| Library        | Source                              | Use                         |
|----------------|-------------------------------------|-----------------------------|
| tinygltf v3    | `syoyo/tinygltf` branch `v3_c`      | pure-C glTF/GLB loader      |
| tinyexr v3     | `syoyo/tinyexr` (`include/exr.h`)   | EXR read/write (pure C)     |
| tinycolorio    | tinyexr `sandbox/tocio`             | OCIO colorspace (available) |
| stb_image(_write) | `nothings/stb`                  | JPG/PNG texture & preview   |

## Notes / limitations

- The node interpreter is intentionally simple (slow but low-effort); it covers
  the node types the chess set uses, not the full MaterialX standard library.
- Colorspace handling is sRGB↔linear (what the chess assets need). The vendored
  tinycolorio is available for full OCIO config-driven transforms.
- SSS defaults to a tinted-diffuse diffusion approximation (accurate for the
  chess set's sub-millimeter mean free path); `--sss-walk` enables a bounded
  random walk.
