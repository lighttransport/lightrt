#!/usr/bin/env bash
#
# render_ref_glsl.sh - render one material through the ASF MaterialX GLSL path
# (MaterialXView) headlessly and capture a PNG. This is the Phase-1 GPU
# reference image. Runs under Xvfb with conda mesa/llvmpipe software GL, so no
# real GPU is required.
#
# The camera / env / resolution are locked to env_common.sh defaults so the
# capture matches the lightrt --cam-eye/--srgb render pixel-for-pixel in framing.
#
# Usage:  bash verify/render_ref_glsl.sh <material.mtlx> <out.png>
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env_common.sh"
mtlxref_activate

MTLX="${1:?usage: render_ref_glsl.sh <material.mtlx> <out.png>}"
OUT="${2:?usage: render_ref_glsl.sh <material.mtlx> <out.png>}"

VIEW="$MATERIALX_BUILD/bin/MaterialXView"
[ -x "$VIEW" ] || { echo "error: MaterialXView not built ($VIEW). Run build_materialx_ref.sh." >&2; exit 1; }
[ -f "$REF_MESH" ] || { echo "error: mesh $REF_MESH missing (run assets/gen_sphere.py)." >&2; exit 1; }
[ -f "$REF_HDR" ]  || { echo "error: env HDR $REF_HDR missing." >&2; exit 1; }

mkdir -p "$(dirname "$OUT")"

# llvmpipe software GL (no GPU). MESA_GL_VERSION_OVERRIDE keeps NanoGUI's
# core-profile request happy on llvmpipe.
export LIBGL_ALWAYS_SOFTWARE=1
export GALLIUM_DRIVER=llvmpipe
export MESA_GL_VERSION_OVERRIDE="4.1"
export MESA_GLSL_VERSION_OVERRIDE="410"

# Env-only lighting (direct light off) so it matches the lightrt env-only render.
# --paths gives MaterialXView the data-library search root (its own resources).
run() {
    xvfb-run -a -s "-screen 0 ${REF_W}x${REF_H}x24" \
    "$VIEW" \
        --material "$MTLX" \
        --mesh "$REF_MESH" \
        --envRad "$REF_HDR" \
        --envMethod 0 \
        --envSampleCount 64 \
        --envLightIntensity 1 \
        --lightRotation 0 \
        --enableDirectLight false \
        --drawEnvironment false \
        --screenColor 0,0,0 \
        --cameraPosition "$REF_CAM_EYE" \
        --cameraTarget "$REF_CAM_TARGET" \
        --cameraViewAngle "$REF_CAM_FOV" \
        --screenWidth "$REF_W" \
        --screenHeight "$REF_H" \
        --captureFilename "$OUT" \
        --path "$MATERIALX_SRC"
}

echo "[glsl] rendering $(basename "$MTLX") -> $OUT"
if ! run; then
    echo "error: MaterialXView render failed for $MTLX" >&2
    exit 1
fi
[ -f "$OUT" ] || { echo "error: no capture produced ($OUT)." >&2; exit 1; }
echo "[glsl] wrote $OUT"
