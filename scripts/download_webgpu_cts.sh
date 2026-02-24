#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEST_DIR="${DEST_DIR:-${ROOT_DIR}/third_party/webgpu-cts}"
REF="${REF:-main}"
KEEP_ARCHIVE=0

usage() {
  cat <<'EOF'
Usage: download_webgpu_cts.sh [options]

Options:
  --dest <dir>         Destination directory (default: ./third_party/webgpu-cts)
  --ref <ref>          Git ref/branch/tag to download (default: main)
  --keep-archive       Keep downloaded .tar.gz in destination parent
  -h, --help           Show this help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --dest) DEST_DIR="$2"; shift 2 ;;
    --ref) REF="$2"; shift 2 ;;
    --keep-archive) KEEP_ARCHIVE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "[cts-download] unknown argument: $1" >&2; usage; exit 2 ;;
  esac
done

PARENT_DIR="$(dirname "${DEST_DIR}")"
mkdir -p "${PARENT_DIR}"

ARCHIVE_NAME="webgpu-cts-${REF}.tar.gz"
ARCHIVE_PATH="${PARENT_DIR}/${ARCHIVE_NAME}"
URL_CANDIDATES=(
  "https://github.com/gpuweb/cts/archive/refs/heads/${REF}.tar.gz"
  "https://github.com/gpuweb/cts/archive/refs/tags/${REF}.tar.gz"
  "https://github.com/gpuweb/cts/archive/${REF}.tar.gz"
)

download_with_url() {
  local url="$1"
  if command -v curl >/dev/null 2>&1; then
    curl -fL "${url}" -o "${ARCHIVE_PATH}"
  elif command -v wget >/dev/null 2>&1; then
    wget -O "${ARCHIVE_PATH}" "${url}"
  else
    echo "[cts-download] neither curl nor wget found" >&2
    return 127
  fi
}

download_ok=0
for URL in "${URL_CANDIDATES[@]}"; do
  echo "[cts-download] trying: ${URL}"
  if download_with_url "${URL}"; then
    download_ok=1
    break
  fi
done

if [[ "${download_ok}" -ne 1 ]]; then
  echo "[cts-download] failed to download ref '${REF}' from known archive URLs" >&2
  exit 1
fi

if ! command -v tar >/dev/null 2>&1; then
  echo "[cts-download] tar not found" >&2
  exit 1
fi

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "${TMP_DIR}"' EXIT

if ! tar -xzf "${ARCHIVE_PATH}" -C "${TMP_DIR}"; then
  echo "[cts-download] failed to extract archive: ${ARCHIVE_PATH}" >&2
  exit 1
fi

mapfile -t extracted_dirs < <(find "${TMP_DIR}" -mindepth 1 -maxdepth 1 -type d | sort)
if [[ "${#extracted_dirs[@]}" -ne 1 ]]; then
  echo "[cts-download] expected exactly 1 extracted root directory, got ${#extracted_dirs[@]}" >&2
  exit 1
fi

EXTRACTED_DIR="${extracted_dirs[0]}"
if [[ ! -d "${EXTRACTED_DIR}" ]]; then
  echo "[cts-download] extracted directory missing: ${EXTRACTED_DIR}" >&2
  exit 1
fi

if [[ -d "${DEST_DIR}" ]]; then
  rm -rf "${DEST_DIR}.bak"
  mv "${DEST_DIR}" "${DEST_DIR}.bak"
fi
mv "${EXTRACTED_DIR}" "${DEST_DIR}"

if [[ "${KEEP_ARCHIVE}" -eq 0 ]]; then
  rm -f "${ARCHIVE_PATH}"
fi

echo "[cts-download] extracted to ${DEST_DIR}"
