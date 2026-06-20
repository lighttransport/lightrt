#!/usr/bin/env bash
#
# render_ref_osl.sh - render one material through the ASF MaterialX OSL path
# (MaterialXGenOsl -> oslc -> testrender) via the mtlx_osl_render driver. This
# is the Phase-2 CPU reference (a path tracer). No GPU/Xvfb needed.
#
# Camera/sphere framing comes from verify/osl_scene_template.xml (matched to the
# lightrt render); the comparison masks to the sphere disk, so the OSL env
# background is irrelevant.
#
# Usage:  bash verify/render_ref_osl.sh <material.mtlx> <out.png>
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env_common.sh"
mtlxref_activate

MTLX="${1:?usage: render_ref_osl.sh <material.mtlx> <out.png>}"
OUT="${2:?usage: render_ref_osl.sh <material.mtlx> <out.png>}"

DRIVER="$VERIFY_DIR/mtlx_osl_render"
[ -x "$DRIVER" ] || { echo "error: $DRIVER not built. Run build_osl_driver.sh." >&2; exit 1; }
command -v oslc >/dev/null      || { echo "error: oslc not on PATH. Run build_osl.sh." >&2; exit 1; }
command -v testrender >/dev/null || { echo "error: testrender not on PATH. Run build_osl.sh." >&2; exit 1; }

OSLC="$(command -v oslc)"
TESTRENDER="$(command -v testrender)"
OSL_INC="$(mtlxref_osl_include)"
UTILS="$MATERIALX_SRC/source/MaterialXTest/MaterialXRenderOsl/Utilities"
SCENE="$VERIFY_DIR/osl_scene_template.xml"

mkdir -p "$(dirname "$OUT")"

echo "[osl] rendering $(basename "$MTLX") -> $OUT"
"$DRIVER" "$MTLX" "$OUT" "$REF_HDR" "$REF_W" "$REF_H" \
    "$MATERIALX_SRC" "$OSLC" "$TESTRENDER" "$OSL_INC" "$UTILS" "$SCENE"
[ -f "$OUT" ] || { echo "error: no OSL capture produced ($OUT)." >&2; exit 1; }
echo "[osl] wrote $OUT"
