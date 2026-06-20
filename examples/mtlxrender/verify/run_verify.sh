#!/usr/bin/env bash
#
# run_verify.sh - drive the cross-renderer MaterialX verification.
#
# For each material in a curated set, render the SAME mesh / camera / env through
#   - lightrt mtlxrender        (--srgb, explicit camera)            [candidate]
#   - ASF MaterialX GLSL        (MaterialXView headless)             [reference, GPU]
#   - ASF MaterialX OSL         (testrender via mtlx_osl_render)     [reference, CPU]  (mode osl/all)
# then run compare.py and accumulate verify/out/report.md + per-material contact
# sheets.
#
# Usage:
#   bash verify/run_verify.sh [glsl|osl|all]      (default: glsl)
#
# The candidate vs ASF-OSL masked-RMSE is the real cross-implementation check
# (path tracer vs path tracer). ASF-GLSL is a rasterizer reference: good on
# matte/metal, expected-divergent on glass/SSS (flagged below).
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env_common.sh"

MODE="${1:-glsl}"
OUT="$VERIFY_DIR/out"
mkdir -p "$OUT"

# compare.py needs numpy/imageio from the conda env; the native mtlxrender runs
# from the system, so use the env python directly rather than activating (keeps
# the conda LD_LIBRARY_PATH off the native binary).
PY="$MTLXREF_FORGE_ROOT/envs/$MTLXREF_ENV/bin/python3"
[ -x "$PY" ] || { echo "error: conda env python not found ($PY). Run setup_ref_env.sh." >&2; exit 1; }

MTLXRENDER="$MTLXRENDER_DIR/mtlxrender"
[ -x "$MTLXRENDER" ] || { echo "error: build lightrt mtlxrender first (make -C $MTLXRENDER_DIR)." >&2; exit 1; }

EXAMPLES="$MATERIALX_SRC/resources/Materials/Examples"
SPP="${REF_SPP:-256}"

# Curated set: name | mtlx | class (match = rasterizer can match; divergent = GI-bound)
MATERIALS=(
    "ss_default|$EXAMPLES/StandardSurface/standard_surface_default.mtlx|match"
    "ss_gold|$EXAMPLES/StandardSurface/standard_surface_gold.mtlx|match"
    "ss_copper|$EXAMPLES/StandardSurface/standard_surface_copper.mtlx|match"
    "ss_plastic|$EXAMPLES/StandardSurface/standard_surface_plastic.mtlx|match"
    "ss_chrome|$EXAMPLES/StandardSurface/standard_surface_chrome.mtlx|match"
    "ss_jade|$EXAMPLES/StandardSurface/standard_surface_jade.mtlx|match"
    "ss_marble|$EXAMPLES/StandardSurface/standard_surface_marble_solid.mtlx|match"
    "ss_velvet|$EXAMPLES/StandardSurface/standard_surface_velvet.mtlx|match"
    "opbr_velvet|$EXAMPLES/OpenPbr/open_pbr_velvet.mtlx|match"
    "ss_brick|$EXAMPLES/StandardSurface/standard_surface_brick_procedural.mtlx|match"
    "ss_brass_tiled|$EXAMPLES/StandardSurface/standard_surface_brass_tiled.mtlx|match"
    "ss_onyx|$EXAMPLES/StandardSurface/standard_surface_onyx_hextiled.mtlx|match"
    "opbr_default|$EXAMPLES/OpenPbr/open_pbr_default.mtlx|match"
    "opbr_carpaint|$EXAMPLES/OpenPbr/open_pbr_carpaint.mtlx|match"
    "ss_thin_film|$EXAMPLES/StandardSurface/standard_surface_thin_film.mtlx|match"
    "opbr_pearl|$EXAMPLES/OpenPbr/open_pbr_pearl.mtlx|divergent"
    "gltf_boombox|$EXAMPLES/GltfPbr/gltf_pbr_boombox.mtlx|match"
    "ss_glass|$EXAMPLES/StandardSurface/standard_surface_glass.mtlx|divergent"
    "opbr_honey|$EXAMPLES/OpenPbr/open_pbr_honey.mtlx|divergent"
)

REPORT="$OUT/report.md"
{
    echo "# MaterialX cross-renderer verification report"
    echo
    echo "- candidate: lightrt mtlxrender (\`--srgb\`, ${REF_W}x${REF_H}, spp=$SPP, env-only)"
    echo "- reference: ASF MaterialX $MATERIALX_SRC (mode: **$MODE**)"
    echo "- mesh: \`$(basename "$REF_MESH")\`  env: \`$(basename "$REF_HDR")\` (lightrt rot=$REF_ENV_ROT)  camera: eye=$REF_CAM_EYE target=$REF_CAM_TARGET fov=$REF_CAM_FOV"
    echo
    echo "masked-RMSE = foreground (sphere) RMSE after a best-fit exposure scale. Lower is better."
    echo "GLSL is a rasterizer reference (no full GI); 'divergent' rows are expected to disagree there."
    echo
    echo "| material | class | ASF-GLSL masked-RMSE | ASF-OSL masked-RMSE | sheet |"
    echo "|----------|-------|---------------------|---------------------|-------|"
} > "$REPORT"

render_lightrt() {
    local name="$1" mtlx="$2" out="$3"
    "$MTLXRENDER" --obj "$REF_MESH" --mtlx "$mtlx" \
        --env "$REF_HDR" --env-intensity 1 --env-rotation "$REF_ENV_ROT" --hide-env \
        --cam-eye "$REF_CAM_EYE" --cam-target "$REF_CAM_TARGET" --cam-fov "$REF_CAM_FOV" \
        --w "$REF_W" --h "$REF_H" --spp "$SPP" --bounces 8 \
        --out "$OUT/${name}_lightrt.exr" --srgb "$out" >/dev/null 2>&1
}

for entry in "${MATERIALS[@]}"; do
    IFS='|' read -r name mtlx cls <<< "$entry"
    [ -f "$mtlx" ] || { echo "skip $name (missing $mtlx)"; continue; }
    echo "=== $name ($cls) ==="

    cand="$OUT/${name}_lightrt.png"
    echo "[lightrt] $name"; render_lightrt "$name" "$mtlx" "$cand"

    refs=(); labels=("lightrt")
    glsl_rmse="-"; osl_rmse="-"
    if [ "$MODE" = "glsl" ] || [ "$MODE" = "all" ]; then
        g="$OUT/${name}_glsl.png"
        if bash "$VERIFY_DIR/render_ref_glsl.sh" "$mtlx" "$g" >/dev/null 2>&1; then
            refs+=("$g"); labels+=("ASF-GLSL")
        else echo "  [glsl] render failed"; fi
    fi
    if [ "$MODE" = "osl" ] || [ "$MODE" = "all" ]; then
        o="$OUT/${name}_osl.png"
        if bash "$VERIFY_DIR/render_ref_osl.sh" "$mtlx" "$o" >/dev/null 2>&1; then
            refs+=("$o"); labels+=("ASF-OSL")
        else echo "  [osl] render failed"; fi
    fi

    if [ "${#refs[@]}" -gt 0 ]; then
        sheet="$OUT/${name}_sheet.png"
        json="$("$PY" "$VERIFY_DIR/compare.py" --candidate "$cand" \
                    $(printf -- '--ref %q ' "${refs[@]}") \
                    --labels "$(IFS=,; echo "${labels[*]}")" \
                    --disk-frac "$REF_DISK_FRAC" \
                    --out-sheet "$sheet" --json)"
        echo "  $json"
        glsl_rmse="$(python3 -c "import json,sys; d=json.loads(sys.argv[1]); print('%.4f'%d['ASF-GLSL']['masked_rmse']) if 'ASF-GLSL' in d else print('-')" "$json")"
        osl_rmse="$(python3 -c "import json,sys; d=json.loads(sys.argv[1]); print('%.4f'%d['ASF-OSL']['masked_rmse']) if 'ASF-OSL' in d else print('-')" "$json")"
    fi
    echo "| $name | $cls | $glsl_rmse | $osl_rmse | [sheet](${name}_sheet.png) |" >> "$REPORT"
done

echo
echo "[verify] report: $REPORT"
cat "$REPORT"
