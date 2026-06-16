#!/usr/bin/env bash
#
# setup-and-build-glslang.sh — fetch and build a modern glslang into tools/.
#
# The system glslang on many machines predates GL_EXT_ray_query, which the
# trace_ray_query.comp shader needs. This builds a pinned glslang and installs it
# under tools/, so scripts/compile_shaders.sh (which prefers tools/bin) can
# regenerate all of vk/shaders/*.spv.h, including the ray_query shader.
#
# The pinned version (14.3.0) matches the compiler that produced the committed
# SPIR-V, so regeneration is byte-reproducible.
#
# Usage:
#   scripts/setup-and-build-glslang.sh            # build into ./tools
#   FORCE=1 scripts/setup-and-build-glslang.sh    # rebuild even if present
#   GLSLANG_TAG=15.0.0 scripts/setup-and-build-glslang.sh
#
# Env: GLSLANG_REPO, GLSLANG_TAG, JOBS.
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

GLSLANG_REPO="${GLSLANG_REPO:-https://github.com/KhronosGroup/glslang.git}"
GLSLANG_TAG="${GLSLANG_TAG:-14.3.0}"
TOOLS_DIR="${REPO_ROOT}/tools"
WORK_DIR="${REPO_ROOT}/build_glslang"
SRC_DIR="${WORK_DIR}/src"
BUILD_DIR="${WORK_DIR}/build"
JOBS="${JOBS:-$(nproc 2>/dev/null || echo 4)}"

bin="${TOOLS_DIR}/bin/glslangValidator"
if [[ "${FORCE:-0}" != "1" && -x "${bin}" ]]; then
    echo "glslang already installed: ${bin}"
    "${bin}" --version | head -1
    exit 0
fi

echo ">> glslang ${GLSLANG_TAG} -> ${TOOLS_DIR}  (jobs=${JOBS})"

# 1. Checkout (shallow, pinned tag).
if [[ -d "${SRC_DIR}/.git" ]]; then
    git -C "${SRC_DIR}" fetch --depth 1 origin "refs/tags/${GLSLANG_TAG}"
    git -C "${SRC_DIR}" checkout -q FETCH_HEAD
else
    rm -rf "${SRC_DIR}"
    git clone --depth 1 --branch "${GLSLANG_TAG}" "${GLSLANG_REPO}" "${SRC_DIR}"
fi

# 2. Configure. ENABLE_OPT=OFF drops the SPIRV-Tools dependency (the optimizer
#    only runs with -O, which compile_shaders.sh does not use), so the build is
#    self-contained — no update_glslang_sources.py / external fetch needed.
cmake -S "${SRC_DIR}" -B "${BUILD_DIR}" \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_INSTALL_PREFIX="${TOOLS_DIR}" \
    -DENABLE_OPT=OFF \
    -DENABLE_GLSLANG_BINARIES=ON \
    -DGLSLANG_ENABLE_INSTALL=ON \
    -DGLSLANG_TESTS=OFF \
    -DBUILD_TESTING=OFF \
    -DBUILD_EXTERNAL=OFF \
    -DBUILD_SHARED_LIBS=OFF

# 3. Build + install.
cmake --build "${BUILD_DIR}" -j "${JOBS}" --target install

# Some glslang versions install only `glslang`; provide the glslangValidator name.
if [[ ! -x "${bin}" && -x "${TOOLS_DIR}/bin/glslang" ]]; then
    ln -sf glslang "${bin}"
fi

echo ">> installed:"
"${bin}" --version | head -2
echo ">> regenerate shaders with:  GLSLANG=${bin} scripts/compile_shaders.sh"
echo ">> (or just run scripts/compile_shaders.sh — it prefers tools/bin)"
