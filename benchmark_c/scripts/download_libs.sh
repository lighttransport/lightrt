#!/usr/bin/env bash
# Fetch all optional comparison libraries for bench_c into
# benchmark_c/third_party/:
#   - Embree 4 prebuilt SDK (via download_embree.sh, sha256-pinned)
#   - madmann91/bvh   (header-only C++20, pinned commit)
#   - jbikker/tinybvh (single-header C++, pinned commit)
# Re-run cmake afterwards to pick them up.
#
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TP_DIR="${SCRIPT_DIR}/../third_party"
mkdir -p "${TP_DIR}"

# Pinned commits (verified working with the bench_c backends)
MADMANN_BVH_COMMIT="${MADMANN_BVH_COMMIT:-5a9d759c51d9028130b5f25733e2b4b2dc67718b}"
TINYBVH_COMMIT="${TINYBVH_COMMIT:-eea6b625f8fdbbd58fe9020b5475c228dec85e19}"

clone_pinned() {
    local url="$1" dir="$2" commit="$3"
    if [ -e "${dir}/.git" ]; then
        echo "$(basename "${dir}") already present - delete it to re-fetch."
        return 0
    fi
    git clone "${url}" "${dir}"
    git -C "${dir}" checkout --quiet "${commit}"
    echo "$(basename "${dir}") pinned at ${commit}"
}

clone_pinned https://github.com/madmann91/bvh "${TP_DIR}/bvh" "${MADMANN_BVH_COMMIT}"
clone_pinned https://github.com/jbikker/tinybvh "${TP_DIR}/tinybvh" "${TINYBVH_COMMIT}"

"${SCRIPT_DIR}/download_embree.sh"

echo
echo "All comparison libraries ready. Reconfigure with:"
echo "  cmake -S benchmark_c -B build_bench_c -DCMAKE_BUILD_TYPE=Release"
echo "  cmake --build build_bench_c -j"
