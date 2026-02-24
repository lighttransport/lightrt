#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_DIR="${BUILD_DIR:-${ROOT_DIR}/build_webgpu}"
WGPU_REF_DIR="${WGPU_REF_DIR:-${ROOT_DIR}/webgpu/wgpu_reference}"
WGPU_REF_BUILD_DIR="${WGPU_REF_BUILD_DIR:-${ROOT_DIR}/build_wgpu_reference}"
OUT_DIR="${OUT_DIR:-${BUILD_DIR}/cts_dual_compare}"
CTS_ROOT=""
LIMIT="${LIMIT:-200}"
STAGES="${STAGES:-compute}"
OURS_BACKENDS="${OURS_BACKENDS:-SPIRV,CPU_JIT}"
OURS_OPT_LEVELS="${OURS_OPT_LEVELS:-0,2}"
ENTRY_DEFAULT="${ENTRY_DEFAULT:-main}"
ALLOW_FAILURES=0
SKIP_SETUP=0
CONFIGURE=1
BUILD=1
JOBS="${JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 8)}"

usage() {
  cat <<'EOF'
Usage: run_cts_dual_backend_compare.sh --cts-root <path> [options]

Options:
  --cts-root <dir>         Path to webgpu-cts checkout (required)
  --build-dir <dir>        LightRT build dir (default: ./build_webgpu)
  --wgpu-build-dir <dir>   wgpu-reference build dir (default: ./build_wgpu_reference)
  --out-dir <dir>          Output dir (default: <build>/cts_dual_compare)
  --limit <n>              Max extracted WGSL snippets (default: 200, 0=all)
  --stages <csv>           Stages to run (default: compute)
  --ours-backends <csv>    Clair backends (default: SPIRV,CPU_JIT)
  --ours-opt-levels <csv>  Clair opt levels (default: 0,2)
  --entry-default <name>   Fallback entry point (default: main)
  --allow-failures         Exit 0 even when compile parity mismatches exist
  --skip-setup             Skip wgpu-reference setup.sh
  --skip-configure         Skip cmake configure
  --skip-build             Skip cmake build
  -h, --help               Show help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --cts-root) CTS_ROOT="$2"; shift 2 ;;
    --build-dir) BUILD_DIR="$2"; shift 2 ;;
    --wgpu-build-dir) WGPU_REF_BUILD_DIR="$2"; shift 2 ;;
    --out-dir) OUT_DIR="$2"; shift 2 ;;
    --limit) LIMIT="$2"; shift 2 ;;
    --stages) STAGES="$2"; shift 2 ;;
    --ours-backends) OURS_BACKENDS="$2"; shift 2 ;;
    --ours-opt-levels) OURS_OPT_LEVELS="$2"; shift 2 ;;
    --entry-default) ENTRY_DEFAULT="$2"; shift 2 ;;
    --allow-failures) ALLOW_FAILURES=1; shift ;;
    --skip-setup) SKIP_SETUP=1; shift ;;
    --skip-configure) CONFIGURE=0; shift ;;
    --skip-build) BUILD=0; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "[dual-cts] unknown arg: $1" >&2; usage; exit 2 ;;
  esac
done

if [[ -z "${CTS_ROOT}" ]]; then
  echo "[dual-cts] --cts-root is required" >&2
  exit 2
fi
if [[ ! -d "${CTS_ROOT}" ]]; then
  echo "[dual-cts] missing cts root: ${CTS_ROOT}" >&2
  exit 2
fi

if [[ "${SKIP_SETUP}" -eq 0 ]]; then
  REF_DIR="${WGPU_REF_DIR}" BUILD_DIR="${WGPU_REF_BUILD_DIR}" JOBS="${JOBS}" \
    "${ROOT_DIR}/scripts/setup_wgpu_native_reference.sh"
fi

if [[ "${CONFIGURE}" -eq 1 ]]; then
  cmake -S "${ROOT_DIR}" -B "${BUILD_DIR}" \
    -DLIGHTRT_BUILD_WEBGPU=ON \
    -DBUILD_TESTING=ON
  cmake -S "${WGPU_REF_DIR}" -B "${WGPU_REF_BUILD_DIR}"
fi

if [[ "${BUILD}" -eq 1 ]]; then
  cmake --build "${BUILD_DIR}" -j"${JOBS}" --target webgpu_wgsl_compile_file
  cmake --build "${WGPU_REF_BUILD_DIR}" -j"${JOBS}" --target wgpu_wgsl_compile_file
fi

OURS_COMPILER="${BUILD_DIR}/webgpu/webgpu_wgsl_compile_file"
WGPU_COMPILER="${WGPU_REF_BUILD_DIR}/wgpu_wgsl_compile_file"
if [[ ! -x "${OURS_COMPILER}" ]]; then
  echo "[dual-cts] missing ours compiler: ${OURS_COMPILER}" >&2
  exit 1
fi
if [[ ! -x "${WGPU_COMPILER}" ]]; then
  echo "[dual-cts] missing wgpu-native compiler: ${WGPU_COMPILER}" >&2
  exit 1
fi

mkdir -p "${OUT_DIR}"
OUT_DIR="$(cd "${OUT_DIR}" && pwd)"
python3 "${ROOT_DIR}/scripts/extract_cts_wgsl.py" \
  --cts-root "${CTS_ROOT}" \
  --out-dir "${OUT_DIR}" \
  --limit "${LIMIT}"

MANIFEST="${OUT_DIR}/manifest.json"
if [[ ! -f "${MANIFEST}" ]]; then
  echo "[dual-cts] missing manifest: ${MANIFEST}" >&2
  exit 1
fi

REPORT_TSV="${OUT_DIR}/dual_compile_report.tsv"
SUMMARY_TXT="${OUT_DIR}/summary.txt"
IMAGE_REPORT="${OUT_DIR}/image_compare_report.txt"
echo -e "shader\tentry\tstage\tours_backend\tours_opt\tours_status\twgpu_status\tparity" >"${REPORT_TSV}"

IFS=',' read -r -a stage_arr <<< "${STAGES}"
IFS=',' read -r -a ours_backend_arr <<< "${OURS_BACKENDS}"
IFS=',' read -r -a ours_opt_arr <<< "${OURS_OPT_LEVELS}"

total_cases=0
stage_filtered=0
parity_mismatches=0
ours_failures=0
wgpu_failures=0

while IFS='|' read -r shader entry stage; do
  if [[ -z "${shader}" || -z "${stage}" ]]; then
    continue
  fi

  selected=0
  for st in "${stage_arr[@]}"; do
    if [[ "${stage}" == "${st}" ]]; then
      selected=1
      break
    fi
  done
  if [[ "${selected}" -eq 0 ]]; then
    continue
  fi
  stage_filtered=$((stage_filtered + 1))

  use_entry="${ENTRY_DEFAULT}"
  if [[ -n "${entry}" ]]; then
    use_entry="${entry}"
  fi

  if (cd "${WGPU_REF_BUILD_DIR}" && "${WGPU_COMPILER}" --input "${shader}" --entry "${use_entry}" --stage "${stage}" >/dev/null 2>&1); then
    wgpu_status="PASS"
  else
    wgpu_status="FAIL"
    wgpu_failures=$((wgpu_failures + 1))
  fi

  for backend in "${ours_backend_arr[@]}"; do
    for opt in "${ours_opt_arr[@]}"; do
      total_cases=$((total_cases + 1))
      if "${OURS_COMPILER}" --input "${shader}" --entry "${use_entry}" --stage "${stage}" --backend "${backend}" --opt "${opt}" >/dev/null 2>&1; then
        ours_status="PASS"
      else
        ours_status="FAIL"
        ours_failures=$((ours_failures + 1))
      fi

      parity="MATCH"
      if [[ "${ours_status}" != "${wgpu_status}" ]]; then
        parity="MISMATCH"
        parity_mismatches=$((parity_mismatches + 1))
      fi

      echo -e "${shader}\t${use_entry}\t${stage}\t${backend}\t${opt}\t${ours_status}\t${wgpu_status}\t${parity}" >>"${REPORT_TSV}"
    done
  done
done < <(python3 - <<'PY' "${MANIFEST}"
import json
import os
import sys

with open(sys.argv[1], "r", encoding="utf-8") as f:
    manifest = json.load(f)

for e in manifest:
    shader = os.path.abspath(e.get("shader_file", ""))
    entries = e.get("entries") or []
    if entries:
        for ent in entries:
            stage = ent.get("stage", e.get("stage", "unknown"))
            name = ent.get("name", "")
            print(f"{shader}|{name}|{stage}")
    else:
        stage = e.get("stage", "unknown")
        print(f"{shader}||{stage}")
PY
)

image_pairs=0
image_different=0
: > "${IMAGE_REPORT}"

OURS_IMG_DIR="${OUT_DIR}/images_ours"
WGPU_IMG_DIR="${OUT_DIR}/images_wgpu"
if [[ -d "${OURS_IMG_DIR}" && -d "${WGPU_IMG_DIR}" ]]; then
  while IFS= read -r f; do
    rel="${f#${OURS_IMG_DIR}/}"
    other="${WGPU_IMG_DIR}/${rel}"
    if [[ -f "${other}" ]]; then
      image_pairs=$((image_pairs + 1))
      if cmp -s "${f}" "${other}"; then
        echo "MATCH ${rel}" >> "${IMAGE_REPORT}"
      else
        echo "DIFF  ${rel}" >> "${IMAGE_REPORT}"
        image_different=$((image_different + 1))
      fi
    fi
  done < <(find "${OURS_IMG_DIR}" -type f \( -name '*.rgba' -o -name '*.bmp' -o -name '*.png' \) | sort)
fi

{
  echo "CTS dual-backend compile comparison"
  echo "cts_root=${CTS_ROOT}"
  echo "manifest=${MANIFEST}"
  echo "stages=${STAGES}"
  echo "stage_filtered_entries=${stage_filtered}"
  echo "total_compile_cases=${total_cases}"
  echo "ours_failures=${ours_failures}"
  echo "wgpu_failures=${wgpu_failures}"
  echo "parity_mismatches=${parity_mismatches}"
  echo "report=${REPORT_TSV}"
  echo "image_pairs=${image_pairs}"
  echo "image_different=${image_different}"
  echo "image_report=${IMAGE_REPORT}"
} | tee "${SUMMARY_TXT}"

if [[ "${parity_mismatches}" -ne 0 && "${ALLOW_FAILURES}" -eq 0 ]]; then
  exit 1
fi

exit 0
