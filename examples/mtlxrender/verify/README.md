# MaterialX cross-renderer verification

Verifies lightrt's from-scratch MaterialX shading (`examples/mtlxrender`) against
the canonical **Academy Software Foundation MaterialX** renderers at
`~/work/MaterialX`, by rendering the same material / mesh / camera / environment
through each and comparing the images.

Two reference paths:

| reference | renderer | kind | notes |
|-----------|----------|------|-------|
| **ASF-GLSL** | `MaterialXView` (headless) | rasterizer + IBL | Phase 1. Fast. Matches lightrt well on matte/metal; expected-divergent on glass/SSS (no full GI). |
| **ASF-OSL**  | `MaterialXGenOsl` → `oslc` → `testrender` | path tracer | Phase 2. The tight apples-to-apples check (path tracer vs path tracer). |

Everything runs headless (no GPU needed): the GLSL path uses conda mesa/llvmpipe
software GL under `xvfb-run`.

## One-time setup

```bash
# 0. conda env with the reference renderers' dependencies (no sudo)
bash verify/setup_ref_env.sh

# 1. build the ASF MaterialX viewer + render libs against that env  (Phase 1)
bash verify/build_materialx_ref.sh

# 2. Phase 2 (OSL): build OpenShadingLanguage from source, then the OSL driver
bash verify/build_osl.sh           # clones + builds OSL -> oslc/testrender into the env
bash verify/build_osl_driver.sh    # compiles verify/mtlx_osl_render against MaterialX libs
```

conda-forge has no `openshadinglanguage` package, so `build_osl.sh` builds it from
source against the env (LLVM/OIIO/flex/bison all from conda) and installs
`oslc`/`testrender`/`stdosl.h` into the env prefix.

`setup_ref_env.sh` bootstraps miniforge to `~/work/.miniforge` and creates the
`mtlxref` env (OpenImageIO-free MaterialX build deps + GLFW/mesa + OSL build
deps + numpy/imageio). All paths are overridable via `MTLXREF_FORGE_ROOT`,
`MTLXREF_ENV`, `MATERIALX_SRC` (see `env_common.sh`).

## Running

```bash
make -C ..              # build lightrt mtlxrender first
bash verify/run_verify.sh glsl     # Phase 1: candidate vs ASF-GLSL
bash verify/run_verify.sh osl      # Phase 2: candidate vs ASF-OSL
bash verify/run_verify.sh all      # both reference columns
```

Output lands in `verify/out/`:
- `report.md` — per-material table of **masked-RMSE** (foreground RMSE after a
  best-fit exposure scale; the headline agreement metric).
- `<material>_sheet.png` — contact sheet: `lightrt | reference | 5×|diff|`.
- `<material>_{lightrt,glsl,osl}.png` — the individual renders.

## How the comparison is made fair

Two different renderers never agree on absolute brightness or on global
illumination, so the harness isolates the *shading*:

- **Shared mesh** — `assets/sphere.obj` (UV sphere of radius `2/√3`, the size
  MaterialXView normalizes any mesh to). Loaded identically by lightrt and
  MaterialXView; the OSL scene template uses a sphere of the same radius. So all
  three project the sphere to the *same* image disk (verified: foreground ≈ 26 %).
- **Identical camera** — explicit eye/target/fov (`mtlxrender --cam-eye 0,0,5`,
  `MaterialXView --cameraPosition 0,0,5`, OSL template `Camera eye="0,0,5"`).
- **Identical env** — `table_mountain.hdr`, intensity 1, **env-only** (lightrt
  sun off, `--hide-env` for a black background; MaterialXView
  `--enableDirectLight false`; the OSL template forces a black camera background
  while the env still lights).
- **Calibrated env orientation** — lightrt's lat-long azimuth zero is **180° off**
  the MaterialX renderers' (calibrated to the RMSE minimum on a diffuse sphere;
  `REF_ENV_ROT=180`, applied to the lightrt side). Both references agree on this
  offset.
- **Analytic disk mask** — `compare.py --disk-frac` masks a centered disk of the
  known projected radius, isolating the sphere regardless of background or dark
  (unlit) shading; more robust than a luminance threshold and excludes the
  antialiased rim where renderers differ most.
- **Best-fit exposure** — `compare.py` solves one least-squares scalar exposure
  on the masked pixels before RMSE, cancelling constant brightness offset.

`masked-RMSE` is reported, not gated at a tight tolerance:
- **ASF-GLSL** (rasterizer + prefiltered/FIS IBL) agrees *tightly* on
  matte/metal (masked-RMSE ≈ 0.02–0.10) and diverges on GI-bound materials
  (glass/transmission). It is the smoother, better-behaved reference.
- **ASF-OSL** (`testrender` path tracer) renders the same materials but agrees
  more *loosely* (matte masked-RMSE ≈ 0.1–0.15). The residual is a genuine
  cross-implementation difference: `testrender`'s stochastic env importance
  sampling, OSL closure evaluation, and firefly/sample behavior differ from
  lightrt's integrator and OpenPBR BSDF (the per-quadrant difference is a
  directional lighting gradient, not a framing or encoding error — both of those
  are calibrated out). It is the path-tracer-vs-path-tracer reference; treat a
  *large* outlier there (not the baseline ≈0.12) as a shading bug to chase.

The real deliverable is the quantified per-material table + the side-by-side
contact sheets (`out/<material>_sheet.png`: `lightrt | reference | 5×|diff|`),
which let you *see* and measure where the implementations agree and differ —
not a single pass/fail number, which is meaningless across independent renderers.
