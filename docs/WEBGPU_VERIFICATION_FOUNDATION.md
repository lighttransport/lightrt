# WebGPU/WGSL Verification Foundation

Last updated: February 24, 2026

## Scope

This document defines a practical verification baseline for:

- WGSL frontend correctness
- Clair integration (`WGSL -> IR -> CPU_JIT/SPIRV`)
- SoftWebGPU execution correctness for compute shaders

It does **not** claim full WebGPU API conformance yet.

## External Conformance Landscape

### 1) GPUWeb CTS (authoritative)

- Canonical suite: `gpuweb/cts`
- Query-based execution model (e.g. `webgpu:shader,execution:*`)
- Also covers Web Platform Tests integration instructions (`wpt update-webgpu`)

Use this as the source of truth for spec conformance.

### 2) Dawn CTS runners (practical harness)

- Dawn provides Node and browser-backed CTS runners.
- `tools/run run-cts` supports `--bin` and `--cts` for local test execution.
- Dawn includes dedicated docs for CTS query usage and expectations.

Use this as the first external harness before browser CI.

### 3) WPT WebGPU layer (browser integration)

- WPT is the browser-facing integration layer for Web standards tests.
- GPUWeb CTS flows into WPT for browser conformance checks.

Use this after the local + Dawn-node phases are stable.

### 4) Validation tools (non-conformance but useful gates)

- Naga CLI: WGSL parser/validator and cross-IR translator.
- SPIRV-Tools (`spirv-val`): validates generated SPIR-V modules.

Use these as fast static gates around generated shader artifacts.

## Foundation Implemented In This Repo

## 1) CTest matrix for WGSL JIT checks

`webgpu/CMakeLists.txt` registers all WGSL JIT tests with labels:

- `WebGPUWGSL`
- backend labels: `SPIRV`, `CPU_JIT`
- optimization labels: `opt0`, `opt2`

Each test sets environment:

- `SOFTRT_CLAIR_EXECUTION_MODE=<SPIRV|CPU_JIT>`
- `SOFTRT_CLAIR_OPT_LEVEL=<0|2>`

Run:

```bash
ctest --test-dir build_webgpu -L WebGPUWGSL --output-on-failure
```

## 2) Reproducible verification runner

Script:

- `scripts/verify_webgpu_conformance.sh`

Default behavior:

1. Configure with `-DBUILD_TESTING=ON` and WebGPU enabled
2. Build targets
3. Run local `WebGPUWGSL` CTest matrix
4. Optionally run Naga validation on `webgpu/verification/shaders/*.wgsl`
5. Optionally run `spirv-val` on `.spv` artifact directory
6. Optionally run Dawn CTS query via `tools/run run-cts`

Examples:

```bash
./scripts/verify_webgpu_conformance.sh
```

```bash
./scripts/verify_webgpu_conformance.sh \
  --run-dawn-cts \
  --dawn-root /path/to/dawn \
  --dawn-bin-dir /path/to/dawn/out/Release \
  --cts-root /path/to/webgpu-cts \
  --cts-query 'webgpu:shader,execution:*'
```

```bash
./scripts/verify_webgpu_conformance.sh \
  --spirv-val on \
  --spirv-artifacts /path/to/spv/output
```

## 3) WGSL validation corpus seed

Starter shaders for static parser/validator checks:

- `webgpu/verification/shaders/minimal_add.wgsl`
- `webgpu/verification/shaders/heavy_expr.wgsl`
- `webgpu/verification/shaders/control_flow.wgsl`

## 4) CTS WGSL Adapter Layer

When full Dawn CTS execution is unavailable (no network/full Dawn checkout),
use the adapter flow to extract WGSL snippets from a local `webgpu-cts` tree
and compile them through our Clair path.

Scripts:

- `scripts/extract_cts_wgsl.py`
- `scripts/run_cts_wgsl_adapter.sh`

Adapter binary:

- `webgpu/webgpu_wgsl_compile_file.cc`

Example:

```bash
./scripts/run_cts_wgsl_adapter.sh \
  --cts-root /path/to/webgpu-cts \
  --limit 200 \
  --backends SPIRV,CPU_JIT \
  --opt-levels 0,2
```

Outputs:

- Extracted shaders: `<build>/cts_wgsl_adapter/shaders/*.wgsl`
- Manifest: `<build>/cts_wgsl_adapter/manifest.json`
- Compile report: `<build>/cts_wgsl_adapter/compile_report.txt`

## WGSL Shader Conformance Track

As of February 24, 2026, WGSL conformance should be treated as a focused subset
of the WebGPU CTS `shader/` tree (the WGSL spec explicitly points to this).

Recommended rollout order:

1. `webgpu:shader,validation:*`
2. `webgpu:shader,execution:*`
3. `webgpu:shader,execution,expression:*`
4. `webgpu:shader,execution,expression,call,builtin:*`

Notes:

- The CTS helper index exposes shader-specific fixtures and helpers, including
  `ShaderValidationTest` and execution expression utilities.
- Dawn testing docs and dawn-node docs show practical query filtering examples,
  including builtin-only WGSL runs.

Example (Dawn CTS):

```bash
./tools/run run-cts --bin=/path/to/dawn/out/Release 'webgpu:shader,validation:*'
./tools/run run-cts --bin=/path/to/dawn/out/Release 'webgpu:shader,execution:*'
./tools/run run-cts --bin=/path/to/dawn/out/Release 'webgpu:shader,execution,expression,call,builtin:*'
```

Example (this repo wrapper):

```bash
./scripts/verify_webgpu_conformance.sh \
  --run-dawn-cts \
  --dawn-root /path/to/dawn \
  --dawn-bin-dir /path/to/dawn/out/Release \
  --cts-root /path/to/webgpu-cts \
  --cts-query 'webgpu:shader,execution:*'
```

## Recommended Next Phases

1. Add SPIR-V artifact export in Clair path and make `spirv-val` mandatory in CI.
2. Add a curated CTS query allowlist focused on compute + WGSL execution.
3. Add nightly Dawn CTS jobs and track pass/fail deltas by query.
4. Add WPT-based browser integration once Dawn CTS signal is stable.

## Authoritative References

- GPUWeb CTS: https://github.com/gpuweb/cts
- WebGPU spec (living): https://gpuweb.github.io/gpuweb/
- WGSL spec (living): https://gpuweb.github.io/gpuweb/wgsl/
- Dawn Node CTS runner docs: https://dawn.googlesource.com/dawn/+/refs/heads/main/node/README.md
- Chromium WebGPU CTS docs: https://chromium.googlesource.com/chromium/src/+/main/third_party/blink/web_tests/webgpu/README.md
- WPT repository: https://github.com/web-platform-tests/wpt
- Naga CLI docs/source: https://github.com/gfx-rs/wgpu/tree/trunk/naga-cli
- SPIRV-Tools: https://github.com/KhronosGroup/SPIRV-Tools
- webgpu-distribution (wgpu-native packaging): https://github.com/webgpu-native/webgpu-distribution
- CTS helper index (`ShaderValidationTest` and shader helpers): https://gpuweb.github.io/cts/docs/tsdoc/
- CTS standalone query usage (`?q=webgpu:*`): https://gpuweb.github.io/cts/docs/intro/developing.html
- Dawn testing + CTS query filtering examples: https://dawn.googlesource.com/dawn/+/HEAD/docs/dawn/testing.md
- Dawn/Chromium WebGPU CTS runner docs: https://dawn.googlesource.com/dawn/+/HEAD/webgpu-cts/README.md
- Dawn Tint end-to-end WGSL/SPV test harness: https://dawn.googlesource.com/dawn/+/refs/heads/chromium/7455/docs/tint/end-to-end-tests.md
