#!/usr/bin/env bash
#
# golden.sh - render a curated set of MaterialX example materials on the
# shaderball (plus the chess scene) and manage them as 'golden' references.
#
#   ./golden.sh gen      regenerate reference EXR+PNG into golden/
#   ./golden.sh check    re-render to /tmp and diff against golden/ (RMSE)
#   ./golden.sh          same as check
#
# Renders are deterministic (fixed seed, per-pixel RNG independent of thread
# scheduling), so a matching build reproduces references bit-for-bit.
set -uo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
BIN="$HERE/mtlxrender"
MTLX_ROOT="${MATERIALX_ROOT:-$HOME/work/MaterialX}"
RES="$MTLX_ROOT/resources"
SHADERBALL="$RES/Geometry/shaderball.glb"
CHESS_GLB="$RES/Geometry/chess_set.glb"
CHESS_MTLX="$RES/Materials/Examples/StandardSurface/standard_surface_chess_set.mtlx"
HDRI="$RES/Lights/table_mountain.hdr"
GOLDEN="$HERE/golden"
TOL="${TOL:-0.02}"

# Curated materials spanning every supported shader model.
MATERIALS=(
    "StandardSurface/standard_surface_default.mtlx"
    "StandardSurface/standard_surface_gold.mtlx"
    "StandardSurface/standard_surface_jade.mtlx"
    "StandardSurface/standard_surface_plastic.mtlx"
    "StandardSurface/standard_surface_glass.mtlx"
    "StandardSurface/standard_surface_carpaint.mtlx"
    "StandardSurface/standard_surface_velvet.mtlx"
    "StandardSurface/standard_surface_copper.mtlx"
    "StandardSurface/standard_surface_thin_film.mtlx"
    "StandardSurface/standard_surface_onyx_hextiled.mtlx"
    "OpenPbr/open_pbr_default.mtlx"
    "OpenPbr/open_pbr_pearl.mtlx"
    "OpenPbr/open_pbr_carpaint.mtlx"
    "OpenPbr/open_pbr_glass.mtlx"
    "OpenPbr/open_pbr_velvet.mtlx"
    "UsdPreviewSurface/usd_preview_surface_default.mtlx"
    "UsdPreviewSurface/usd_preview_surface_gold.mtlx"
    "UsdPreviewSurface/usd_preview_surface_plastic.mtlx"
    "GltfPbr/gltf_pbr_default.mtlx"
    "GltfPbr/gltf_pbr_gold.mtlx"
    "GltfPbr/gltf_pbr_glass.mtlx"
    "GltfPbr/gltf_pbr_boombox.mtlx"
    "DisneyPrincipled/disney_principled_default.mtlx"
    "DisneyPrincipled/disney_principled_gold.mtlx"
    "DisneyPrincipled/disney_principled_plastic.mtlx"
)

# Fixed, reproducible render settings.
COMMON=(--w 256 --h 256 --spp 48 --bounces 6 --env "$HDRI" --cam-dist 1.3 --exposure 1.2)
CHESS_COMMON=(--w 320 --h 240 --spp 48 --bounces 6 --env "$HDRI" \
              --cam-yaw 30 --cam-pitch 22 --cam-dist 1.05 --exposure 1.2)

render() { # <gltf> <mtlx> <out-prefix> <common-array-name...>
    local gltf="$1" mtlx="$2" out="$3"; shift 3
    "$BIN" --gltf "$gltf" --mtlx "$mtlx" "$@" --out "$out.exr" --png "$out.png" >/dev/null 2>&1
}

mode="${1:-check}"
[ -x "$BIN" ] || { echo "build first: make"; exit 1; }
[ -f "$SHADERBALL" ] || { echo "missing shaderball: $SHADERBALL (set MATERIALX_ROOT)"; exit 1; }

if [ "$mode" = "gen" ]; then
    mkdir -p "$GOLDEN"
    for m in "${MATERIALS[@]}"; do
        name="$(basename "${m%.mtlx}")"
        echo "  gen $name"
        render "$SHADERBALL" "$RES/Materials/Examples/$m" "$GOLDEN/$name" "${COMMON[@]}"
    done
    echo "  gen chess_set"
    render "$CHESS_GLB" "$CHESS_MTLX" "$GOLDEN/chess_set" "${CHESS_COMMON[@]}"
    echo "golden references written to $GOLDEN/ ($(ls "$GOLDEN"/*.png | wc -l) images)"
    exit 0
fi

# check mode
[ -d "$GOLDEN" ] || { echo "no golden/ dir; run: ./golden.sh gen"; exit 1; }
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
pass=0; fail=0
checkone() { # <name> <gltf> <mtlx> <common...>
    local name="$1" gltf="$2" mtlx="$3"; shift 3
    [ -f "$GOLDEN/$name.png" ] || { echo "  SKIP $name (no golden)"; return; }
    render "$gltf" "$mtlx" "$TMP/$name" "$@"
    if "$BIN" --diff "$GOLDEN/$name.png" "$TMP/$name.png" "$TOL" 2>"$TMP/d.txt"; then
        echo "  PASS $name  ($(grep -oE 'rmse=[0-9.]+' "$TMP/d.txt"))"; pass=$((pass+1))
    else
        echo "  FAIL $name  ($(grep -oE 'rmse=[0-9.]+ max=[0-9.]+' "$TMP/d.txt"))"; fail=$((fail+1))
    fi
}
for m in "${MATERIALS[@]}"; do
    name="$(basename "${m%.mtlx}")"
    checkone "$name" "$SHADERBALL" "$RES/Materials/Examples/$m" "${COMMON[@]}"
done
checkone "chess_set" "$CHESS_GLB" "$CHESS_MTLX" "${CHESS_COMMON[@]}"
echo "----"
echo "golden check: $pass passed, $fail failed (tol=$TOL)"
[ "$fail" -eq 0 ]
