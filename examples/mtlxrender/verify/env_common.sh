# env_common.sh - shared locations for the verify/ scripts. Source, don't run.
#
#   source "$(dirname "$0")/env_common.sh"
#   mtlxref_activate   # puts the conda env's bin on PATH, sets CONDA_PREFIX
#
# Honors overrides: MTLXREF_FORGE_ROOT, MTLXREF_ENV, MATERIALX_SRC.

MTLXREF_FORGE_ROOT="${MTLXREF_FORGE_ROOT:-$HOME/work/.miniforge}"
MTLXREF_ENV="${MTLXREF_ENV:-mtlxref}"
MATERIALX_SRC="${MATERIALX_SRC:-$HOME/work/MaterialX}"

# Directory of the verify/ tree (this file's dir), and the example root.
VERIFY_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MTLXRENDER_DIR="$(cd "$VERIFY_DIR/.." && pwd)"
MATERIALX_BUILD="${MATERIALX_BUILD:-$MATERIALX_SRC/build-ref}"

# Default verification scene (kept identical across all renderers).
REF_HDR="${REF_HDR:-$MATERIALX_SRC/resources/Lights/table_mountain.hdr}"
REF_MESH="${REF_MESH:-$VERIFY_DIR/assets/sphere.obj}"
REF_W="${REF_W:-512}"
REF_H="${REF_H:-512}"
REF_CAM_EYE="${REF_CAM_EYE:-0,0,5}"
REF_CAM_TARGET="${REF_CAM_TARGET:-0,0,0}"
REF_CAM_FOV="${REF_CAM_FOV:-45}"
# lightrt's lat-long azimuth zero is 180deg off MaterialXView's (calibrated on a
# diffuse sphere: env-rotation 180 minimizes RMSE). Applied to the lightrt side
# so the env lights both renders identically. No handedness flip is needed.
REF_ENV_ROT="${REF_ENV_ROT:-180}"
# Analytic sphere-disk radius as a fraction of min(W,H). The sphere (radius
# 2/sqrt(3)) at eye distance 5 with fov_y 45deg projects to a disk of radius
# tan(asin(R/d))/tan(fov/2)/2 ~= 0.2865 of the height; 0.27 stays just inside the
# silhouette so the antialiased rim (where renderers differ most) is excluded.
REF_DISK_FRAC="${REF_DISK_FRAC:-0.27}"

mtlxref_conda() { echo "$MTLXREF_FORGE_ROOT/bin/conda"; }

# Activate the env into the current shell (PATH, CONDA_PREFIX, LD_LIBRARY_PATH).
mtlxref_activate() {
    local conda; conda="$(mtlxref_conda)"
    if [ ! -x "$conda" ]; then
        echo "error: miniforge not found ($conda). Run verify/setup_ref_env.sh first." >&2
        return 1
    fi
    # shellcheck disable=SC1091
    source "$MTLXREF_FORGE_ROOT/etc/profile.d/conda.sh"
    conda activate "$MTLXREF_ENV" || {
        echo "error: conda env '$MTLXREF_ENV' missing. Run verify/setup_ref_env.sh first." >&2
        return 1
    }
    export LD_LIBRARY_PATH="$CONDA_PREFIX/lib:${LD_LIBRARY_PATH:-}"
}

# Locate stdosl.h's directory inside the active env (for oslc -I).
mtlxref_osl_include() {
    local p
    for p in "$CONDA_PREFIX/share/OSL/shaders" "$CONDA_PREFIX/share/OSL/include" \
             "$CONDA_PREFIX/include/OSL"; do
        [ -f "$p/stdosl.h" ] && { echo "$p"; return 0; }
    done
    # last resort: search
    find "$CONDA_PREFIX" -name stdosl.h -printf '%h\n' 2>/dev/null | head -1
}
