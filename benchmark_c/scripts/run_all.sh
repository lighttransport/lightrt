#!/usr/bin/env bash
# Build bench_c and run the full benchmark matrix:
#   fineness {64,128,192,256} x workloads {primary,incoherent,shadow}
#   x backends (all available) x threads {1,16,32}
# Results land in benchmark_c/results/bench_<timestamp>.csv and a comparison
# table is printed via compare.py.
#
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"
BUILD_DIR="${BUILD_DIR:-${ROOT_DIR}/build_bench_c}"
RESULTS_DIR="${SCRIPT_DIR}/../results"

FINENESS_LIST="${FINENESS_LIST:-64 128 192 256}"
THREADS_LIST="${THREADS_LIST:-1 16 32}"
NRAYS="${NRAYS:-4000000}"
REPEAT="${REPEAT:-5}"

cmake -S "${ROOT_DIR}/benchmark_c" -B "${BUILD_DIR}" -DCMAKE_BUILD_TYPE=Release
cmake --build "${BUILD_DIR}" -j

mkdir -p "${RESULTS_DIR}"
CSV="${RESULTS_DIR}/bench_$(date +%Y%m%d_%H%M%S).csv"
echo "Writing ${CSV}"

for fineness in ${FINENESS_LIST}; do
    for threads in ${THREADS_LIST}; do
        "${BUILD_DIR}/bench_c" \
            --scene mandelbulb --fineness "${fineness}" \
            --backend all --rays all \
            --nrays "${NRAYS}" --threads "${threads}" --repeat "${REPEAT}" \
            --csv "${CSV}"
    done
done

echo
python3 "${SCRIPT_DIR}/../compare.py" "${CSV}"
echo "Results: ${CSV}"
