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

echo; echo "### Other prim types (scalar on A64FX: curves/sphere/SDF reinterpret the soup):"
"$dir/bench_c" "${SCENE[@]}" --backend c11-hair,c11-sphere,c11-sdf,c11-user \
    --rays primary,incoherent --nrays "${NRAYS:-2000000}" --threads "$THREADS" --repeat 3

echo; echo "### Parametric surfaces (subd: bicubic Bézier + NURBS, direct ray-patch):"
"$dir/bench_subd" --patches 40 --nurbs 24 --threads "$THREADS" --nrays "${NRAYS:-4000000}"

echo; echo "### Dense-grid volume raymarch (bandwidth/cache-capacity bound):"
"$dir/bench_volume" --sizes 64,128,256,512 --steps 512 --threads "$THREADS" --nrays 2000000

echo; echo "### int8/int16 SDOT leaf microbenchmark:"
"$dir/bench_sdot"

echo; echo "Compare the SIMD vs scalar Mrays/s above for the NEON/SVE speedup."
echo "Curves/subd/volume run the scalar path on A64FX (NEON/SVE leaves are"
echo "triangle-only); see the PR for the measured numbers."
