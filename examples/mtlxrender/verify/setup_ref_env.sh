#!/usr/bin/env bash
#
# setup_ref_env.sh - create the conda-forge environment that hosts the ASF
# MaterialX reference renderers' dependencies.
#
# Provides, as prebuilt conda-forge packages (no sudo):
#   - openimageio           (libOpenImageIO + oiiotool; MaterialX + OSL image I/O)
#   - glfw + mesa GL         (MaterialXView windowing + software GL via llvmpipe) -> Phase 1 GPU ref
#   - cmake/ninja            (build the ~/work/MaterialX checkout)
#   - numpy/imageio/openexr  (compare.py image diff)
#   - llvmdev/clangdev/pugixml/flex/bison/...  (deps to BUILD OpenShadingLanguage
#                            from source in Phase 2 -- conda-forge has no
#                            prebuilt openshadinglanguage/oslc/testrender package,
#                            so verify/build_osl.sh clones + builds it against
#                            this env. These build deps are installed up front so
#                            that step is turnkey.)
#
# Idempotent: re-running is a no-op once the env exists. Source this script's
# sibling env_common.sh from the other verify/ scripts to locate conda + the env.
#
# Usage:  bash verify/setup_ref_env.sh
set -euo pipefail

FORGE_ROOT="${MTLXREF_FORGE_ROOT:-$HOME/work/.miniforge}"
ENV_NAME="${MTLXREF_ENV:-mtlxref}"

# ---- 1. miniforge ---------------------------------------------------------
if [ ! -x "$FORGE_ROOT/bin/conda" ]; then
    echo "[setup] miniforge not found at $FORGE_ROOT; installing..."
    arch="$(uname -m)"
    os="$(uname -s)"
    installer="Miniforge3-${os}-${arch}.sh"
    url="https://github.com/conda-forge/miniforge/releases/latest/download/${installer}"
    tmp="$(mktemp -d)"
    echo "[setup] downloading $url"
    if command -v curl >/dev/null 2>&1; then
        curl -fL "$url" -o "$tmp/$installer"
    else
        wget -O "$tmp/$installer" "$url"
    fi
    bash "$tmp/$installer" -b -p "$FORGE_ROOT"
    rm -rf "$tmp"
else
    echo "[setup] miniforge present at $FORGE_ROOT"
fi

CONDA="$FORGE_ROOT/bin/conda"

# ---- 2. the mtlxref env ---------------------------------------------------
if "$CONDA" env list | awk '{print $1}' | grep -qx "$ENV_NAME"; then
    echo "[setup] conda env '$ENV_NAME' already exists; leaving it as-is."
else
    echo "[setup] creating conda env '$ENV_NAME' (this pulls ~1-2 GB)..."
    # mesa-libgl-devel-cos7-x86_64 gives libGL + headers; llvmpipe (from mesa)
    # provides software GL so MaterialXView runs under Xvfb with no real GPU.
    # llvmdev/clangdev/pugixml/flex/bison are for the Phase-2 OSL source build.
    "$CONDA" create -y -n "$ENV_NAME" -c conda-forge \
        openimageio \
        fmt \
        glfw \
        mesa-libgl-devel-cos7-x86_64 \
        libglu \
        xorg-libx11 xorg-libxrandr xorg-libxinerama xorg-libxcursor xorg-libxi xorg-libxxf86vm \
        xorg-libxt xorg-libxext xorg-libxfixes xorg-libxrender xorg-xorgproto \
        cmake ninja pkg-config make \
        c-compiler cxx-compiler \
        llvmdev clangdev \
        pugixml flex bison zlib \
        python=3.11 numpy imageio openexr-python
fi

PREFIX="$("$CONDA" run -n "$ENV_NAME" printenv CONDA_PREFIX)"

# ---- 3. report resolved tool paths ---------------------------------------
echo
echo "[setup] environment ready:"
echo "  CONDA_PREFIX = $PREFIX"
for t in oiiotool cmake ninja llvm-config; do
    p="$("$CONDA" run -n "$ENV_NAME" bash -lc "command -v $t" 2>/dev/null || true)"
    echo "  $t = ${p:-<NOT FOUND>}"
done
# OSL tools (oslc/testrender) are built in Phase 2 by verify/build_osl.sh.
for t in oslc testrender; do
    p="$("$CONDA" run -n "$ENV_NAME" bash -lc "command -v $t" 2>/dev/null || true)"
    echo "  $t = ${p:-<not built yet -- run verify/build_osl.sh for Phase 2>}"
done
echo
echo "[setup] done."
echo "  Phase 1 (GPU/GLSL): bash verify/build_materialx_ref.sh"
echo "  Phase 2 (CPU/OSL):  bash verify/build_osl.sh  (clones + builds OSL)"
