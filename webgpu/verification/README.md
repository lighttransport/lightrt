# WebGPU Pixel Compare (wgpu-native vs Clair+LightRT)

This repository now includes an end-to-end pixel comparison framework between:

- `wgpu-native` reference renderer (headless)
- `clair + lightrt` software WebGPU path

## Components

- `webgpu/webgpu_headless_triangle_dump.cc`
  - Renders the reference triangle through `softrt_webgpu`.
  - Dumps raw RGBA (`.rgba`) and optional BMP.

- `webgpu/wgpu_reference/headless_triangle_dump.c`
  - Renders the same triangle through `wgpu-native`.
  - Dumps raw RGBA (`.rgba`) and optional BMP.

- `scripts/compare_rgba.py`
  - Pixel-wise comparator for two RGBA dumps.
  - Produces summary metrics + optional visual diff (`PPM`).

- `scripts/setup_wgpu_native_reference.sh`
  - Clones/builds `webgpu/wgpu_reference` dependencies and targets.

- `scripts/run_pixel_compare_wgpu_native.sh`
  - Full orchestration: setup/build/render/compare.

## Quick Start

```bash
scripts/run_pixel_compare_wgpu_native.sh
```

Outputs are written under:

- `build_webgpu/pixel_compare/`
  - `triangle_lightrt.rgba`
  - `triangle_wgpu.rgba`
  - `triangle_lightrt.bmp`
  - `triangle_wgpu.bmp`
  - `triangle_diff.ppm`
  - `compare_summary.json`

## Tunable Thresholds

`run_pixel_compare_wgpu_native.sh` supports:

- `--pixel-threshold <n>`
- `--max-mismatch-ratio <r>`
- `--max-mean-abs-error <e>`

Example:

```bash
scripts/run_pixel_compare_wgpu_native.sh \
  --pixel-threshold 2 \
  --max-mismatch-ratio 0.02 \
  --max-mean-abs-error 1.0
```

