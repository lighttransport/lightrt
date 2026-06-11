#!/usr/bin/env bash
# Download a pinned Embree 4 prebuilt x86_64 Linux SDK into
# benchmark_c/third_party/embree/ for the bench_c embree backend.
#
# Usage: scripts/download_embree.sh
# Override the version with EMBREE_VERSION=x.y.z (sha256 check is then skipped
# unless EMBREE_SHA256 is also provided).
#
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

EMBREE_VERSION="${EMBREE_VERSION:-4.3.3}"
# sha256 of embree-4.3.3.x86_64.linux.tar.gz (verified at pin time)
PINNED_VERSION="4.3.3"
PINNED_SHA256="757e6e8b987d13ac34aa7c4c3657120fd54a78c2a1034e30dda5cd5df06f3cdd"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEST_DIR="${SCRIPT_DIR}/../third_party/embree"
TARBALL="embree-${EMBREE_VERSION}.x86_64.linux.tar.gz"
URL="https://github.com/RenderKit/embree/releases/download/v${EMBREE_VERSION}/${TARBALL}"

if [ -f "${DEST_DIR}/lib/libembree4.so" ] || ls "${DEST_DIR}"/lib/libembree4.so.* >/dev/null 2>&1; then
    echo "Embree already present at ${DEST_DIR} - delete it to re-download."
    exit 0
fi

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "${TMP_DIR}"' EXIT

echo "Downloading ${URL}"
curl -fL --retry 3 -o "${TMP_DIR}/${TARBALL}" "${URL}"

EXPECTED_SHA256="${EMBREE_SHA256:-}"
if [ -z "${EXPECTED_SHA256}" ] && [ "${EMBREE_VERSION}" = "${PINNED_VERSION}" ]; then
    EXPECTED_SHA256="${PINNED_SHA256}"
fi
if [ -n "${EXPECTED_SHA256}" ]; then
    echo "${EXPECTED_SHA256}  ${TMP_DIR}/${TARBALL}" | sha256sum -c -
else
    echo "WARNING: no sha256 pinned for version ${EMBREE_VERSION}; skipping check."
fi

mkdir -p "${DEST_DIR}"
# The tarball is flat (include/, lib/, ... at the top level).
tar -xzf "${TMP_DIR}/${TARBALL}" -C "${DEST_DIR}"
if [ ! -d "${DEST_DIR}/include/embree4" ]; then
    echo "ERROR: unexpected tarball layout" >&2
    exit 1
fi

echo "Embree ${EMBREE_VERSION} installed at ${DEST_DIR}"
echo "Reconfigure the benchmark: cmake -S benchmark_c -B build_bench_c && cmake --build build_bench_c"
