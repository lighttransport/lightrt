#!/usr/bin/env bash
#
# build_osl_driver.sh - compile verify/mtlx_osl_render (the Phase-2 OSL reference
# driver) against the MaterialX libs built by build_materialx_ref.sh. OslRenderer
# only shells out to oslc/testrender, so the driver links the MaterialX static
# libs alone (no liboslexec).
#
# Usage:  bash verify/build_osl_driver.sh
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env_common.sh"
mtlxref_activate

LIBDIR="$MATERIALX_BUILD/lib"
[ -f "$LIBDIR/libMaterialXRenderOsl.a" ] || {
    echo "error: MaterialX libs not found in $LIBDIR. Run build_materialx_ref.sh first." >&2; exit 1; }

CXX="${CXX:-c++}"
OUT="$VERIFY_DIR/mtlx_osl_render"

echo "[osl-driver] compiling $OUT"
# build-ref/source holds generated headers (MaterialXCore/Generated.h etc.).
"$CXX" -std=c++17 -O2 -I"$MATERIALX_SRC/source" -I"$MATERIALX_BUILD/source" \
    "$VERIFY_DIR/mtlx_osl_render.cpp" \
    -L"$LIBDIR" \
    -lMaterialXRenderOsl -lMaterialXRender -lMaterialXGenOsl -lMaterialXGenShader \
    -lMaterialXFormat -lMaterialXCore \
    -lpthread -ldl \
    -o "$OUT"

echo "[osl-driver] built $OUT"
"$OUT" 2>&1 | head -1 || true   # prints usage (expected nonzero)
echo "[osl-driver] done."
