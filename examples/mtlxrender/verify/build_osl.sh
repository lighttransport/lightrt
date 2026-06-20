#!/usr/bin/env bash
#
# build_osl.sh - Phase 2 prerequisite: build OpenShadingLanguage from source
# (conda-forge has no prebuilt openshadinglanguage / oslc / testrender package),
# against the conda 'mtlxref' env, and install oslc / testrender / testshade +
# stdosl.h into the env prefix so the OSL reference path can run.
#
# OSL is built from `main` because the conda env ships a very recent OpenImageIO
# (3.1.x); tagged OSL releases predate it. Override the ref with OSL_REF.
#
# Usage:  bash verify/build_osl.sh
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env_common.sh"
mtlxref_activate

OSL_SRC="${OSL_SRC:-$HOME/work/OpenShadingLanguage}"
OSL_REF="${OSL_REF:-main}"
OSL_BUILD="${OSL_BUILD:-$OSL_SRC/build-ref}"

# ---- 1. checkout ----------------------------------------------------------
if [ ! -d "$OSL_SRC/.git" ]; then
    echo "[osl] cloning OpenShadingLanguage -> $OSL_SRC"
    git clone https://github.com/AcademySoftwareFoundation/OpenShadingLanguage "$OSL_SRC"
fi
echo "[osl] checking out $OSL_REF"
git -C "$OSL_SRC" fetch --depth 1 origin "$OSL_REF" 2>/dev/null || git -C "$OSL_SRC" fetch origin
git -C "$OSL_SRC" checkout "$OSL_REF" 2>/dev/null || true
git -C "$OSL_SRC" pull --ff-only 2>/dev/null || true

# ---- 2. configure ---------------------------------------------------------
# Install into the conda env prefix so oslc/testrender land on PATH and stdosl.h
# under share/OSL/shaders. LLVM / OIIO / Imath / flex / bison all come from the
# env. The conda cross-toolchain needs find-root BOTH so env headers are seen.
echo "[osl] configuring -> $OSL_BUILD  (LLVM $(llvm-config --version), OIIO $(oiiotool --version | awk '{print $2}'))"
cmake -S "$OSL_SRC" -B "$OSL_BUILD" -G Ninja \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_INSTALL_PREFIX="$CONDA_PREFIX" \
    -DCMAKE_PREFIX_PATH="$CONDA_PREFIX" \
    -DCMAKE_FIND_ROOT_PATH="$CONDA_PREFIX" \
    -DCMAKE_FIND_ROOT_PATH_MODE_INCLUDE=BOTH \
    -DCMAKE_FIND_ROOT_PATH_MODE_LIBRARY=BOTH \
    -DCMAKE_FIND_ROOT_PATH_MODE_PROGRAM=BOTH \
    -DLLVM_ROOT="$CONDA_PREFIX" \
    -DLLVM_DIRECTORY="$CONDA_PREFIX" \
    -DOpenImageIO_ROOT="$CONDA_PREFIX" \
    -DCMAKE_CXX_STANDARD=17 \
    -DUSE_PYTHON=OFF \
    -DUSE_QT=OFF \
    -DOSL_BUILD_TESTS=ON \
    -DINSTALL_DOCS=OFF \
    -DENABLERTTI=ON

# ---- 3. build + install ---------------------------------------------------
echo "[osl] building (-j$(nproc))..."
cmake --build "$OSL_BUILD" -j "$(nproc)"
echo "[osl] installing into $CONDA_PREFIX ..."
cmake --install "$OSL_BUILD"

# ---- 4. verify ------------------------------------------------------------
echo
hash -r
for t in oslc testrender testshade; do
    p="$(command -v "$t" || true)"
    echo "  $t = ${p:-<NOT FOUND>}"
done
inc="$(mtlxref_osl_include || true)"
echo "  stdosl.h dir = ${inc:-<NOT FOUND>}"
echo
echo "[osl] done. Next: bash verify/build_osl_driver.sh   (compiles mtlx_osl_render)"
echo "      then:       bash verify/run_verify.sh osl"
