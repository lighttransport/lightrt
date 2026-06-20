#!/usr/bin/env bash
#
# build_materialx_ref.sh - configure + build the ASF MaterialX checkout at
# ~/work/MaterialX into build-ref/, against the conda 'mtlxref' env, with the
# pieces the verify harness needs:
#   - MaterialXView           (Phase 1 GPU/GLSL reference; headless via Xvfb)
#   - MaterialXRenderOsl lib  (Phase 2 CPU/OSL reference; linked by mtlx_osl_render)
#   - OpenImageIO support     (image I/O from the conda env)
#
# The viewer uses NanoGUI (a git submodule that bundles GLFW); we init it. GLFW
# builds against the conda X11/GL/mesa packages, and runs under Xvfb + llvmpipe.
#
# Usage:  bash verify/build_materialx_ref.sh [extra cmake args...]
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env_common.sh"
mtlxref_activate

if [ ! -d "$MATERIALX_SRC/source/MaterialXCore" ]; then
    echo "error: MaterialX source not found at $MATERIALX_SRC (set MATERIALX_SRC)." >&2
    exit 1
fi

# ---- 1. NanoGUI submodule (required by the viewer) -----------------------
if [ ! -e "$MATERIALX_SRC/source/MaterialXView/NanoGUI/ext/glfw/src/CMakeLists.txt" ]; then
    echo "[build] initializing NanoGUI submodule (viewer dependency)..."
    git -C "$MATERIALX_SRC" submodule update --init --recursive \
        source/MaterialXView/NanoGUI
fi

# ---- 2. configure --------------------------------------------------------
echo "[build] configuring -> $MATERIALX_BUILD  (CONDA_PREFIX=$CONDA_PREFIX)"
# NOTE: MATERIALX_BUILD_OIIO is intentionally OFF. The conda OpenImageIO DSO
# pulls in pugixml, which clashes (hidden-symbol-referenced-by-DSO link error)
# with MaterialXFormat's vendored pugixml. MaterialX's built-in stb image loader
# already handles the formats the harness needs (.hdr env in, .png capture out),
# so OIIO is unnecessary here.
cmake -S "$MATERIALX_SRC" -B "$MATERIALX_BUILD" -G Ninja \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_PREFIX_PATH="$CONDA_PREFIX" \
    -DCMAKE_FIND_ROOT_PATH="$CONDA_PREFIX" \
    -DCMAKE_FIND_ROOT_PATH_MODE_INCLUDE=BOTH \
    -DCMAKE_FIND_ROOT_PATH_MODE_LIBRARY=BOTH \
    -DCMAKE_FIND_ROOT_PATH_MODE_PROGRAM=BOTH \
    -DMATERIALX_BUILD_VIEWER=ON \
    -DMATERIALX_BUILD_GEN_GLSL=ON \
    -DMATERIALX_BUILD_GEN_OSL=ON \
    -DMATERIALX_BUILD_RENDER=ON \
    -DMATERIALX_BUILD_RENDER_PLATFORMS=ON \
    -DMATERIALX_BUILD_OIIO=OFF \
    -DMATERIALX_BUILD_TESTS=OFF \
    -DMATERIALX_BUILD_PYTHON=OFF \
    -DMATERIALX_BUILD_GEN_MSL=OFF \
    -DMATERIALX_BUILD_GEN_MDL=OFF \
    -DMATERIALX_BUILD_GEN_SLANG=OFF \
    "$@"

# ---- 3. build ------------------------------------------------------------
echo "[build] building MaterialXView + render libs (-j$(nproc))..."
cmake --build "$MATERIALX_BUILD" -j "$(nproc)"

view="$MATERIALX_BUILD/bin/MaterialXView"
echo
if [ -x "$view" ]; then
    echo "[build] OK: $view"
    "$view" --help >/dev/null 2>&1 && echo "[build] MaterialXView --help runs." \
        || echo "[build] (note: --help needs a GL context; that's fine, render uses Xvfb)"
else
    echo "[build] WARNING: MaterialXView binary not found at $view" >&2
fi
echo "[build] render-osl lib:"
ls "$MATERIALX_BUILD"/lib/libMaterialXRenderOsl* 2>/dev/null || \
    echo "  (not built -- check MATERIALX_BUILD_GEN_OSL/RENDER)"
echo
echo "[build] done. Next: bash verify/run_verify.sh glsl"
