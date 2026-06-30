#!/bin/bash
# Build the bench_c benchmark on an A64FX node with the Fujitsu compiler.
#   bash benchmark_c/scripts/build_a64fx.sh [output_dir]
# Produces <output_dir>/bench_c (default: benchmark_c/build_a64fx). The C11
# kernel is compiled with -Nclang (clang mode, required for the ACLE NEON/SVE
# intrinsics) and -march=armv8.2-a+sve so lightrt_c_tri.c selects the NEON
# (BVH4) + SVE (BVH8) paths. The two optional C++ comparison backends compile to
# NULL stubs (tinybvh/madmann libs absent) via FCC.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # benchmark_c
root="$(cd "$here/.." && pwd)"                            # repo root
out="${1:-$here/build_a64fx}"
mkdir -p "$out"

FCC_C=${FCC_C:-fcc}
FCC_CXX=${FCC_CXX:-FCC}
ARCH="-march=armv8.2-a+sve"
# -DLRT_TRI_SVE_PACKET enables the 16-ray coherent SVE packet (fast primary
# rays; not bit-identical to single-ray, so it's opt-in and off in the default
# library / unit tests). FORCE_SCALAR builds ignore it (no SVE).
COMMON="-Nclang $ARCH -O3 -DLRT_TRI_SVE_PACKET -D_POSIX_C_SOURCE=200809L -I$here -I$root"

# Benchmark glue + backends (gnu11: strict c11 hides clock_gettime/pthreads).
cglue=(bench_main rays scene_mandelbulb scene_thinspan \
       backend_lightrt_cb backend_lightrt_tri backend_lightrt_ext \
       backend_lightrt_pkt backend_embree backend_lightrt_vk)
for f in "${cglue[@]}"; do
    echo "CC  $f.c"
    $FCC_C $COMMON -std=gnu11 -c "$here/$f.c" -o "$out/$f.o"
done

# Library: c11 (fcc finds stdatomic.h/arm_sve.h only in -std=c11 clang mode).
for f in lightrt_c lightrt_c_tri; do
    echo "CC  $f.c"
    $FCC_C $COMMON -std=c11 -c "$root/$f.c" -o "$out/$f.o"
done

# Optional C++ comparison backends (NULL stubs without third_party libs).
for f in backend_tinybvh backend_madmann; do
    echo "CXX $f.cpp"
    $FCC_CXX $COMMON -std=c++17 -c "$here/$f.cpp" -o "$out/$f.o"
done

echo "LD  bench_c"
$FCC_CXX -Nclang $ARCH -O3 -o "$out/bench_c" "$out"/*.o -lpthread -lm
echo "Built $out/bench_c"

# Scalar-baseline bench (same glue, kernel compiled with LRT_TRI_FORCE_SCALAR)
# to quantify the NEON/SVE speedup. The scalar kernel object lives in a subdir
# so it does not collide with the SIMD lightrt_c_tri.o in the link glob above.
echo "CC  lightrt_c_tri.c [scalar]"
mkdir -p "$out/scalar"
$FCC_C $COMMON -std=c11 -DLRT_TRI_FORCE_SCALAR -c "$root/lightrt_c_tri.c" \
    -o "$out/scalar/lightrt_c_tri.o"
glue=()
for o in "$out"/*.o; do
    case "$o" in */lightrt_c_tri.o) ;; *) glue+=("$o") ;; esac
done
echo "LD  bench_c_scalar"
$FCC_CXX -Nclang $ARCH -O3 -o "$out/bench_c_scalar" "${glue[@]}" \
    "$out/scalar/lightrt_c_tri.o" -lpthread -lm
echo "Built $out/bench_c_scalar"

# int8/int16 SDOT leaf microbenchmark (standalone).
echo "CC  bench_a64fx_sdot.c"
$FCC_C $COMMON -std=gnu11 "$here/bench_a64fx_sdot.c" -o "$out/bench_sdot" -lm
echo "Built $out/bench_sdot"

# Parametric-surface (subd) and dense-grid volume-raymarch benches. Both reuse
# rays.c; subd also needs the kernel (c11) for the patch intersectors. rays.c is
# compiled gnu11 (POSIX clock); the kernel object is the c11 one built above.
echo "CC  rays.c [gnu11 for subd/volume]"
$FCC_C $COMMON -std=gnu11 -c "$here/rays.c" -o "$out/rays_g.o"
echo "CC  bench_a64fx_subd.c"
$FCC_C $COMMON -std=gnu11 -c "$here/bench_a64fx_subd.c" -o "$out/subd.o"
$FCC_C -Nclang $ARCH -O3 -o "$out/bench_subd" "$out/subd.o" "$out/rays_g.o" \
    "$out/lightrt_c_tri.o" -lpthread -lm
echo "Built $out/bench_subd"
echo "CC  bench_a64fx_volume.c"
$FCC_C $COMMON -std=gnu11 -c "$here/bench_a64fx_volume.c" -o "$out/vol.o"
$FCC_C -Nclang $ARCH -O3 -o "$out/bench_volume" "$out/vol.o" "$out/rays_g.o" \
    -lpthread -lm
echo "Built $out/bench_volume"
