#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LIGHTRT_BUILD_DIR="${LIGHTRT_BUILD_DIR:-${ROOT_DIR}/build_webgpu}"
WGPU_REF_DIR="${WGPU_REF_DIR:-${ROOT_DIR}/webgpu/wgpu_reference}"
WGPU_REF_BUILD_DIR="${WGPU_REF_BUILD_DIR:-${ROOT_DIR}/build_wgpu_reference}"
OUT_DIR="${OUT_DIR:-${LIGHTRT_BUILD_DIR}/pixel_compare}"
WIDTH="${WIDTH:-640}"
HEIGHT="${HEIGHT:-480}"
JOBS="${JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 8)}"
PIXEL_THRESHOLD="${PIXEL_THRESHOLD:-2}"
MAX_MISMATCH_RATIO="${MAX_MISMATCH_RATIO:-0.02}"
MAX_MEAN_ABS_ERROR="${MAX_MEAN_ABS_ERROR:-1.0}"
SKIP_SETUP=0
SKIP_BUILD=0

usage() {
  cat <<'EOF'
Usage: run_pixel_compare_wgpu_native.sh [options]

Options:
  --width <n>               Render width (default: 640)
  --height <n>              Render height (default: 480)
  --out-dir <dir>           Output directory
  --skip-setup              Skip wgpu-native dependency setup
  --skip-build              Skip builds and only run binaries
  --pixel-threshold <n>     Per-channel mismatch threshold
  --max-mismatch-ratio <r>  Allowed mismatch ratio (0..1)
  --max-mean-abs-error <e>  Allowed mean absolute RGBA error
  -h, --help                Show this help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --width) WIDTH="$2"; shift 2 ;;
    --height) HEIGHT="$2"; shift 2 ;;
    --out-dir) OUT_DIR="$2"; shift 2 ;;
    --skip-setup) SKIP_SETUP=1; shift ;;
    --skip-build) SKIP_BUILD=1; shift ;;
    --pixel-threshold) PIXEL_THRESHOLD="$2"; shift 2 ;;
    --max-mismatch-ratio) MAX_MISMATCH_RATIO="$2"; shift 2 ;;
    --max-mean-abs-error) MAX_MEAN_ABS_ERROR="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "[pixel-compare] unknown arg: $1" >&2; usage; exit 2 ;;
  esac
done

mkdir -p "${OUT_DIR}"

if [[ "${SKIP_SETUP}" -eq 0 ]]; then
  REF_DIR="${WGPU_REF_DIR}" BUILD_DIR="${WGPU_REF_BUILD_DIR}" JOBS="${JOBS}" \
    "${ROOT_DIR}/scripts/setup_wgpu_native_reference.sh"
fi

if [[ "${SKIP_BUILD}" -eq 0 ]]; then
  cmake -S "${ROOT_DIR}" -B "${LIGHTRT_BUILD_DIR}" \
    -DLIGHTRT_BUILD_WEBGPU=ON \
    -DBUILD_TESTING=ON
  cmake --build "${LIGHTRT_BUILD_DIR}" -j"${JOBS}" \
    --target webgpu_headless_triangle_dump

  cmake -S "${WGPU_REF_DIR}" -B "${WGPU_REF_BUILD_DIR}"
  cmake --build "${WGPU_REF_BUILD_DIR}" -j"${JOBS}" \
    --target headless_triangle_dump
fi

LIGHTRT_RGBA="${OUT_DIR}/triangle_lightrt.rgba"
WGPU_RGBA="${OUT_DIR}/triangle_wgpu.rgba"
LIGHTRT_BMP="${OUT_DIR}/triangle_lightrt.bmp"
WGPU_BMP="${OUT_DIR}/triangle_wgpu.bmp"
DIFF_PPM="${OUT_DIR}/triangle_diff.ppm"
SUMMARY_JSON="${OUT_DIR}/compare_summary.json"

echo "[pixel-compare] render lightrt"
"${LIGHTRT_BUILD_DIR}/webgpu/webgpu_headless_triangle_dump" \
  --width "${WIDTH}" \
  --height "${HEIGHT}" \
  --out-rgba "${LIGHTRT_RGBA}" \
  --out-bmp "${LIGHTRT_BMP}"

echo "[pixel-compare] render wgpu-native"
(
  cd "${WGPU_REF_BUILD_DIR}"
  ./headless_triangle_dump \
    --width "${WIDTH}" \
    --height "${HEIGHT}" \
    --out-rgba "${WGPU_RGBA}" \
    --out-bmp "${WGPU_BMP}"
)

echo "[pixel-compare] compare pixels"
python3 "${ROOT_DIR}/scripts/compare_rgba.py" \
  --a "${WGPU_RGBA}" \
  --b "${LIGHTRT_RGBA}" \
  --width "${WIDTH}" \
  --height "${HEIGHT}" \
  --pixel-threshold "${PIXEL_THRESHOLD}" \
  --max-mismatch-ratio "${MAX_MISMATCH_RATIO}" \
  --max-mean-abs-error "${MAX_MEAN_ABS_ERROR}" \
  --summary-json "${SUMMARY_JSON}" \
  --diff-ppm "${DIFF_PPM}"

echo "[pixel-compare] done"
echo "  summary: ${SUMMARY_JSON}"
echo "  diff:    ${DIFF_PPM}"
