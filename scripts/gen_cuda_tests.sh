#!/bin/sh
# Derive the CUDA correctness tests from the HIP ones (the CUDA backend is a
# mechanical port of lightrt_c_hip.hip with the same lrt_*_ API shape).
#   tests/test_lightrt_c_hip.c     -> tests/test_lightrt_c_cuda_prims.c
#   tests/test_lightrt_c_hip_rtc.c -> tests/test_lightrt_c_cuda_parallel.c
set -e
cd "$(dirname "$0")/.."
gen() {
  { echo "/* GENERATED from tests/$1 by scripts/gen_cuda_tests.sh (hip -> cuda); do not edit. */"
    sed -e 's/lightrt_c_hip\.h/lightrt_c_cuda.h/g; s/lrt_hip_/lrt_cuda_/g; s/LRT_HIP_/LRT_CUDA_/g' \
        -e 's/hiprtc Path-A trace (lightrt_c_hip.c + lightrt_hipew.c, no ROCm SDK at/CUDA resident trace (lightrt_c_cuda.cu) vs the CPU kernel, see the HIP original:/' \
        -e 's/no HIP runtime\/device/no CUDA runtime\/device/; s/HIP device/CUDA device/g; s/\bHIP\b/CUDA/g' "tests/$1"
  } > "tests/$2"
}
gen test_lightrt_c_hip.c test_lightrt_c_cuda_prims.c
gen test_lightrt_c_hip_rtc.c test_lightrt_c_cuda_parallel.c
