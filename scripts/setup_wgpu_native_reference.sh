#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REF_DIR="${REF_DIR:-${ROOT_DIR}/webgpu/wgpu_reference}"
BUILD_DIR="${BUILD_DIR:-${ROOT_DIR}/build_wgpu_reference}"
JOBS="${JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 8)}"

if [[ ! -d "${REF_DIR}" ]]; then
  echo "[wgpu-setup] missing directory: ${REF_DIR}" >&2
  exit 1
fi

echo "[wgpu-setup] preparing dependencies in ${REF_DIR}"
"${REF_DIR}/setup.sh"

echo "[wgpu-setup] configuring ${BUILD_DIR}"
cmake -S "${REF_DIR}" -B "${BUILD_DIR}"

echo "[wgpu-setup] building headless targets"
cmake --build "${BUILD_DIR}" -j"${JOBS}" \
  --target headless_triangle headless_triangle_dump wgpu_wgsl_compile_file

echo "[wgpu-setup] done"
echo "  build dir: ${BUILD_DIR}"
