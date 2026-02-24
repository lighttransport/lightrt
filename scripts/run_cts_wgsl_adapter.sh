#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_DIR="${BUILD_DIR:-${ROOT_DIR}/build_webgpu}"
OUT_DIR="${OUT_DIR:-${BUILD_DIR}/cts_wgsl_adapter}"
CTS_ROOT=""
LIMIT="${LIMIT:-0}"
BACKENDS="${BACKENDS:-SPIRV,CPU_JIT}"
OPT_LEVELS="${OPT_LEVELS:-0,2}"
ENTRY="${ENTRY:-main}"
ALLOW_FAILURES=0
CONFIGURE=1
BUILD=1

usage() {
  cat <<'EOF'
Usage: run_cts_wgsl_adapter.sh --cts-root <path> [options]

Options:
  --cts-root <dir>         Path to webgpu-cts checkout (required)
  --build-dir <dir>        CMake build dir (default: ./build_webgpu)
  --out-dir <dir>          Extraction/output dir (default: <build>/cts_wgsl_adapter)
  --limit <n>              Max shaders to extract (0 = all)
  --backends <csv>         Backend list (default: SPIRV,CPU_JIT)
  --opt-levels <csv>       Optimization levels (default: 0,2)
  --entry <name>           Entry point name (default: main)
  --allow-failures         Exit 0 even if compile failures are present
  --skip-configure         Skip cmake configure
  --skip-build             Skip cmake build
  -h, --help               Show help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --cts-root) CTS_ROOT="$2"; shift 2 ;;
    --build-dir) BUILD_DIR="$2"; shift 2 ;;
    --out-dir) OUT_DIR="$2"; shift 2 ;;
    --limit) LIMIT="$2"; shift 2 ;;
    --backends) BACKENDS="$2"; shift 2 ;;
    --opt-levels) OPT_LEVELS="$2"; shift 2 ;;
    --entry) ENTRY="$2"; shift 2 ;;
    --allow-failures) ALLOW_FAILURES=1; shift ;;
    --skip-configure) CONFIGURE=0; shift ;;
    --skip-build) BUILD=0; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "[adapter] unknown arg: $1" >&2; usage; exit 2 ;;
  esac
done

if [[ -z "${CTS_ROOT}" ]]; then
  echo "[adapter] --cts-root is required" >&2
  exit 2
fi
if [[ ! -d "${CTS_ROOT}" ]]; then
  echo "[adapter] cts root does not exist: ${CTS_ROOT}" >&2
  exit 2
fi

if [[ "$CONFIGURE" -eq 1 ]]; then
  cmake -S "${ROOT_DIR}" -B "${BUILD_DIR}" \
    -DLIGHTRT_BUILD_WEBGPU=ON \
    -DBUILD_TESTING=ON
fi

if [[ "$BUILD" -eq 1 ]]; then
  cmake --build "${BUILD_DIR}" -j"$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 8)"
fi

COMPILER_BIN="${BUILD_DIR}/webgpu/webgpu_wgsl_compile_file"
if [[ ! -x "${COMPILER_BIN}" ]]; then
  echo "[adapter] compiler adapter binary not found: ${COMPILER_BIN}" >&2
  exit 1
fi

mkdir -p "${OUT_DIR}"
python3 "${ROOT_DIR}/scripts/extract_cts_wgsl.py" \
  --cts-root "${CTS_ROOT}" \
  --out-dir "${OUT_DIR}" \
  --limit "${LIMIT}"

MANIFEST="${OUT_DIR}/manifest.json"
if [[ ! -f "${MANIFEST}" ]]; then
  echo "[adapter] manifest not found: ${MANIFEST}" >&2
  exit 1
fi

REPORT="${OUT_DIR}/compile_report.txt"
: > "${REPORT}"

IFS=',' read -r -a backend_arr <<< "${BACKENDS}"
IFS=',' read -r -a opt_arr <<< "${OPT_LEVELS}"

total=0
failed=0

while IFS='|' read -r shader entry_from_manifest; do
  use_entry="${ENTRY}"
  if [[ "${ENTRY}" == "main" && -n "${entry_from_manifest}" ]]; then
    use_entry="${entry_from_manifest}"
  fi
  for backend in "${backend_arr[@]}"; do
    for opt in "${opt_arr[@]}"; do
      total=$((total + 1))
      if "${COMPILER_BIN}" --input "${shader}" --entry "${use_entry}" --backend "${backend}" --opt "${opt}" >>"${REPORT}" 2>&1; then
        :
      else
        failed=$((failed + 1))
        echo "[adapter] FAIL shader=${shader} entry=${use_entry} backend=${backend} opt=${opt}" | tee -a "${REPORT}"
      fi
    done
  done
done < <(python3 - <<'PY' "${MANIFEST}"
import json, sys
with open(sys.argv[1], 'r', encoding='utf-8') as f:
    m = json.load(f)
for e in m:
    entry = ""
    if isinstance(e.get("entries"), list) and e["entries"]:
        entry = e["entries"][0].get("name", "")
    print(f'{e["shader_file"]}|{entry}')
PY
)

echo "[adapter] total=${total} failed=${failed} report=${REPORT}"
if [[ "${failed}" -ne 0 ]]; then
  if [[ "${ALLOW_FAILURES}" -eq 1 ]]; then
    exit 0
  fi
  exit 1
fi
