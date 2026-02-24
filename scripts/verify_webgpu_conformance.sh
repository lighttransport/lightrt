#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_DIR="${BUILD_DIR:-${ROOT_DIR}/build_webgpu}"
JOBS="${JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 8)}"

CONFIGURE=1
BUILD=1
RUN_LOCAL=1
RUN_DAWN_CTS=0
NAGA_MODE="auto"      # auto|on|off
SPIRV_VAL_MODE="auto" # auto|on|off
SPIRV_ARTIFACT_DIR="${SPIRV_ARTIFACT_DIR:-}"

CTS_QUERY="${CTS_QUERY:-webgpu:shader,execution:*}"
DAWN_ROOT="${DAWN_ROOT:-}"
DAWN_BIN_DIR="${DAWN_BIN_DIR:-}"
CTS_ROOT="${CTS_ROOT:-}"

usage() {
  cat <<'EOF'
Usage: verify_webgpu_conformance.sh [options]

Options:
  --build-dir <dir>           CMake build directory (default: ./build_webgpu)
  --jobs <n>                  Parallel jobs for build
  --skip-configure            Skip cmake configure
  --skip-build                Skip cmake build
  --skip-local                Skip local WebGPU WGSL tests (ctest/manual matrix)
  --naga <auto|on|off>        Run naga WGSL validation (default: auto)
  --spirv-val <auto|on|off>   Run spirv-val on .spv artifacts (default: auto)
  --spirv-artifacts <dir>     Directory containing .spv artifacts
  --run-dawn-cts              Run Dawn CTS via DAWN_ROOT/tools/run run-cts
  --cts-query <query>         Dawn CTS query (default: webgpu:shader,execution:*)
  --dawn-root <dir>           Dawn repository root
  --dawn-bin-dir <dir>        Dawn build bin directory for run-cts --bin
  --cts-root <dir>            Optional checkout of webgpu-cts (for --cts)
  -h, --help                  Show this help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --build-dir) BUILD_DIR="$2"; shift 2 ;;
    --jobs) JOBS="$2"; shift 2 ;;
    --skip-configure) CONFIGURE=0; shift ;;
    --skip-build) BUILD=0; shift ;;
    --skip-local) RUN_LOCAL=0; shift ;;
    --naga) NAGA_MODE="$2"; shift 2 ;;
    --spirv-val) SPIRV_VAL_MODE="$2"; shift 2 ;;
    --spirv-artifacts) SPIRV_ARTIFACT_DIR="$2"; shift 2 ;;
    --run-dawn-cts) RUN_DAWN_CTS=1; shift ;;
    --cts-query) CTS_QUERY="$2"; shift 2 ;;
    --dawn-root) DAWN_ROOT="$2"; shift 2 ;;
    --dawn-bin-dir) DAWN_BIN_DIR="$2"; shift 2 ;;
    --cts-root) CTS_ROOT="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "[verify] unknown argument: $1" >&2; usage; exit 2 ;;
  esac
done

if [[ "$NAGA_MODE" != "auto" && "$NAGA_MODE" != "on" && "$NAGA_MODE" != "off" ]]; then
  echo "[verify] invalid --naga value: $NAGA_MODE" >&2
  exit 2
fi
if [[ "$SPIRV_VAL_MODE" != "auto" && "$SPIRV_VAL_MODE" != "on" && "$SPIRV_VAL_MODE" != "off" ]]; then
  echo "[verify] invalid --spirv-val value: $SPIRV_VAL_MODE" >&2
  exit 2
fi

echo "[verify] root: ${ROOT_DIR}"
echo "[verify] build: ${BUILD_DIR}"

if [[ "$CONFIGURE" -eq 1 ]]; then
  echo "[verify] configure"
  cmake -S "${ROOT_DIR}" -B "${BUILD_DIR}" \
    -DLIGHTRT_BUILD_WEBGPU=ON \
    -DBUILD_TESTING=ON
fi

if [[ "$BUILD" -eq 1 ]]; then
  echo "[verify] build"
  cmake --build "${BUILD_DIR}" -j"${JOBS}"
fi

if [[ "$RUN_LOCAL" -eq 1 ]]; then
  echo "[verify] local WGSL/WebGPU checks"
  if ctest --test-dir "${BUILD_DIR}" -N -L WebGPUWGSL >/dev/null 2>&1; then
    ctest --test-dir "${BUILD_DIR}" --output-on-failure -L WebGPUWGSL
  else
    echo "[verify] ctest labels not found; running manual matrix"
    test_bin_dir="${BUILD_DIR}/webgpu"
    tests=(
      webgpu_wgsl_jit_minimal
      webgpu_wgsl_jit_storage_minimal
      webgpu_wgsl_jit_indexed_write
      webgpu_wgsl_jit_complex
      webgpu_wgsl_jit_heavy_expr
      webgpu_wgsl_jit_control_flow
    )
    for mode in SPIRV CPU_JIT; do
      for opt in 0 2; do
        for t in "${tests[@]}"; do
          echo "[verify] run ${t} mode=${mode} opt=${opt}"
          SOFTRT_CLAIR_EXECUTION_MODE="${mode}" \
          SOFTRT_CLAIR_OPT_LEVEL="${opt}" \
            "${test_bin_dir}/${t}"
        done
      done
    done
  fi
fi

run_naga=0
if [[ "$NAGA_MODE" == "on" ]]; then
  run_naga=1
elif [[ "$NAGA_MODE" == "auto" ]] && command -v naga >/dev/null 2>&1; then
  run_naga=1
fi

if [[ "$run_naga" -eq 1 ]]; then
  echo "[verify] naga WGSL validation"
  shopt -s nullglob
  shader_files=("${ROOT_DIR}"/webgpu/verification/shaders/*.wgsl)
  shopt -u nullglob
  if [[ "${#shader_files[@]}" -eq 0 ]]; then
    echo "[verify] no WGSL verification shaders found" >&2
    exit 1
  fi

  naga_help="$(naga --help 2>&1 || true)"
  for s in "${shader_files[@]}"; do
    echo "[verify] naga ${s}"
    if grep -qi "validate" <<<"${naga_help}"; then
      naga validate "${s}" >/dev/null
    else
      naga "${s}" >/dev/null
    fi
  done
elif [[ "$NAGA_MODE" == "on" ]]; then
  echo "[verify] naga requested but not found in PATH" >&2
  exit 1
else
  echo "[verify] naga validation skipped"
fi

run_spirv_val=0
if [[ "$SPIRV_VAL_MODE" == "on" ]]; then
  run_spirv_val=1
elif [[ "$SPIRV_VAL_MODE" == "auto" ]] && command -v spirv-val >/dev/null 2>&1; then
  run_spirv_val=1
fi

if [[ "$run_spirv_val" -eq 1 ]]; then
  if [[ -z "${SPIRV_ARTIFACT_DIR}" ]]; then
    if [[ "$SPIRV_VAL_MODE" == "on" ]]; then
      echo "[verify] --spirv-val on requires --spirv-artifacts <dir>" >&2
      exit 1
    fi
    echo "[verify] spirv-val skipped (no SPIRV_ARTIFACT_DIR)"
  else
    echo "[verify] spirv-val in ${SPIRV_ARTIFACT_DIR}"
    mapfile -t spv_files < <(find "${SPIRV_ARTIFACT_DIR}" -type f -name '*.spv' | sort)
    if [[ "${#spv_files[@]}" -eq 0 ]]; then
      echo "[verify] no .spv files found in ${SPIRV_ARTIFACT_DIR}" >&2
      exit 1
    fi
    for f in "${spv_files[@]}"; do
      echo "[verify] spirv-val ${f}"
      spirv-val "${f}" >/dev/null
    done
  fi
elif [[ "$SPIRV_VAL_MODE" == "on" ]]; then
  echo "[verify] spirv-val requested but not found in PATH" >&2
  exit 1
else
  echo "[verify] spirv-val skipped"
fi

if [[ "$RUN_DAWN_CTS" -eq 1 ]]; then
  if [[ -z "${DAWN_ROOT}" || -z "${DAWN_BIN_DIR}" ]]; then
    echo "[verify] --run-dawn-cts requires --dawn-root and --dawn-bin-dir" >&2
    exit 1
  fi
  if [[ ! -x "${DAWN_ROOT}/tools/run" ]]; then
    echo "[verify] Dawn runner not found: ${DAWN_ROOT}/tools/run" >&2
    exit 1
  fi

  echo "[verify] Dawn CTS query: ${CTS_QUERY}"
  pushd "${DAWN_ROOT}" >/dev/null
  if [[ -n "${CTS_ROOT}" ]]; then
    "${DAWN_ROOT}/tools/run" run-cts --bin="${DAWN_BIN_DIR}" --cts="${CTS_ROOT}" "${CTS_QUERY}"
  else
    "${DAWN_ROOT}/tools/run" run-cts --bin="${DAWN_BIN_DIR}" "${CTS_QUERY}"
  fi
  popd >/dev/null
else
  echo "[verify] Dawn CTS skipped"
fi

echo "[verify] done"
