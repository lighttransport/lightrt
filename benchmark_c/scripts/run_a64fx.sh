#!/bin/bash
# A64FX benchmark run: scalar baseline vs NEON (BVH4) / SVE (BVH8), fp64-oracle
# verify, and the int8/int16 SDOT leaf microbenchmark. Build first with
# benchmark_c/scripts/build_a64fx.sh.
#   bash benchmark_c/scripts/run_a64fx.sh [build_dir]
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dir="${1:-$here/build_a64fx}"
SCENE=(--scene mandelbulb --fineness "${FINENESS:-128}")
RAYS=(--rays primary,incoherent,shadow --nrays "${NRAYS:-2000000}")
THREADS="${THREADS:-1}"

echo "================ A64FX lightrt C11 benchmark ================"
"$dir/bench_c" --help >/dev/null 2>&1 || true

echo; echo "### SIMD (NEON BVH4 / SVE BVH8), correctness verified vs fp64 oracle:"
"$dir/bench_c" "${SCENE[@]}" --backend c11-bvh4,c11-bvh8 "${RAYS[@]}" \
    --threads "$THREADS" --repeat 5 --verify

echo; echo "### Scalar baseline (same kernel, LRT_TRI_FORCE_SCALAR):"
"$dir/bench_c_scalar" "${SCENE[@]}" --backend c11-bvh4,c11-bvh8 "${RAYS[@]}" \
    --threads "$THREADS" --repeat 5

echo; echo "### int8/int16 SDOT leaf microbenchmark:"
"$dir/bench_sdot"

echo; echo "Compare the SIMD vs scalar Mrays/s above for the NEON/SVE speedup."
