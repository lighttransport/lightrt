# Makefile for LightRT - Lightweight ray tracing and BVH kernel
# Copyright (c) 2026 Light Transport Entertainment, Inc.
# SPDX-License-Identifier: MIT

CC ?= gcc
CXX ?= g++
CC ?= cc
AR ?= ar

# Compiler flags
CXXFLAGS ?= -std=c++17 -Wall -Wextra -O3 -fno-rtti -fno-exceptions
CFLAGS ?= -std=c11 -Wall -Wextra -O3
INCLUDES = -I.
LDFLAGS =
GLSLANG ?= glslangValidator

# Detect architecture and enable SIMD
ARCH := $(shell uname -m)

ifeq ($(ARCH),x86_64)
    # x86-64: Enable SSE2 (baseline) and optionally AVX
    CXXFLAGS += -msse2
    C_SIMD = -msse4.1
    ifneq ($(NO_AVX),1)
        CXXFLAGS += -mavx
    endif
    # Optional: Enable AVX2 and FMA
    ifneq ($(NO_AVX2),1)
        CXXFLAGS += -mavx2 -mfma
        C_SIMD += -mavx2 -mfma
    endif
    # Optional: Enable F16C for FP16 support
    ifneq ($(NO_F16C),1)
        CXXFLAGS += -mf16c
    endif
endif

ifeq ($(ARCH),aarch64)
    # ARM64. Detect the Fujitsu compiler (A64FX); fcc/FCC need -Nclang (clang
    # mode) for the ACLE <arm_sve.h>/<arm_neon.h> intrinsics the C kernel uses.
    IS_FCC := $(findstring fcc,$(CC))$(findstring FCC,$(CC))$(findstring fccpx,$(CC))
    ifeq ($(IS_FCC),)
        # GCC / LLVM clang.
        CXXFLAGS += -march=armv8-a
        C_SIMD = -march=armv8.2-a
        ifneq ($(NO_SVE),1)
            CXXFLAGS += -march=armv8-a+sve
            C_SIMD := -march=armv8.2-a+sve
        endif
    else
        # Fujitsu fcc/FCC (A64FX), clang mode for ACLE intrinsics.
        CFLAGS += -Nclang
        CXXFLAGS += -Nclang
        C_SIMD = -march=armv8.2-a
        ifneq ($(NO_SVE),1)
            C_SIMD := -march=armv8.2-a+sve
        endif
    endif
endif

# Debug build
ifeq ($(DEBUG),1)
    CFLAGS := $(filter-out -O3,$(CFLAGS))
    CFLAGS += -O0 -g -DDEBUG
    CXXFLAGS := $(filter-out -O3,$(CXXFLAGS))
    CXXFLAGS += -O0 -g -DDEBUG
endif

# Targets
TARGET_LIB = liblightrt.a
TARGET_EXAMPLE = lightrt_example
TARGET_BENCHMARK = lightrt_benchmark

# Source files
SOURCES = lightrt.cc
OBJECTS = $(SOURCES:.cc=.o)
C_SOURCES = lightrt_c.c
C_OBJECTS = $(C_SOURCES:.c=.o)

# Example source
EXAMPLE_SOURCES = example.cc
EXAMPLE_OBJECTS = $(EXAMPLE_SOURCES:.cc=.o)

# Benchmark source
BENCHMARK_SOURCES = benchmark/benchmark.cc
BENCHMARK_OBJECTS = benchmark/benchmark.o

# OBJ BVH benchmark
OBJ_BENCH_TARGET = obj_bvh_bench
OBJ_BENCH_SOURCES = benchmark/obj_bvh_bench.cc
OBJ_BENCH_OBJECTS = benchmark/obj_bvh_bench.o

# Default target
all: $(TARGET_LIB) $(TARGET_EXAMPLE) $(TARGET_BENCHMARK)

# Build static library
$(TARGET_LIB): $(OBJECTS) $(C_OBJECTS)
	$(AR) rcs $@ $^
	@echo "Built $(TARGET_LIB)"

# Build example
$(TARGET_EXAMPLE): $(EXAMPLE_OBJECTS) $(TARGET_LIB)
	$(CXX) $(CXXFLAGS) -o $@ $(EXAMPLE_OBJECTS) $(TARGET_LIB) $(LDFLAGS)
	@echo "Built $(TARGET_EXAMPLE)"

# Build benchmark
$(TARGET_BENCHMARK): $(BENCHMARK_OBJECTS) $(TARGET_LIB)
	$(CXX) $(CXXFLAGS) -o $@ $(BENCHMARK_OBJECTS) $(TARGET_LIB) $(LDFLAGS)
	@echo "Built $(TARGET_BENCHMARK)"

# Build OBJ BVH benchmark
$(OBJ_BENCH_TARGET): $(OBJ_BENCH_OBJECTS) $(TARGET_LIB)
	$(CXX) $(CXXFLAGS) -o $@ $(OBJ_BENCH_OBJECTS) $(TARGET_LIB) $(LDFLAGS) -lpthread
	@echo "Built $(OBJ_BENCH_TARGET)"

# Compile source files
%.o: %.cc lightrt.hh
	$(CXX) $(CXXFLAGS) $(INCLUDES) -c $< -o $@

%.o: %.c lightrt_c.h
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -c $< -o $@

benchmark/%.o: benchmark/%.cc lightrt.hh
	$(CXX) $(CXXFLAGS) $(INCLUDES) -c $< -o $@

# Clean build artifacts
clean:
	rm -f $(OBJECTS) $(C_OBJECTS) $(EXAMPLE_OBJECTS) $(BENCHMARK_OBJECTS) $(OBJ_BENCH_OBJECTS) $(TARGET_LIB) $(TARGET_EXAMPLE) $(TARGET_BENCHMARK) $(OBJ_BENCH_TARGET)
	@echo "Cleaned build artifacts"

# Run example
run: $(TARGET_EXAMPLE)
	./$(TARGET_EXAMPLE)

# Run benchmark (optional args: TRIANGLES=N RAYS=N)
benchmark: $(TARGET_BENCHMARK)
	./$(TARGET_BENCHMARK) $(TRIANGLES) $(RAYS)

# Print configuration
info:
	@echo "Compiler: $(CXX)"
	@echo "Architecture: $(ARCH)"
	@echo "CXXFLAGS: $(CXXFLAGS)"
	@echo "INCLUDES: $(INCLUDES)"
	@echo "LDFLAGS: $(LDFLAGS)"

obj_bench: $(OBJ_BENCH_TARGET)

# C++ spatial-query regression test (also registered with CTest).
spatial_query_test: test_spatial_query.cc $(TARGET_LIB)
	$(CXX) $(CXXFLAGS) $(INCLUDES) -o lightrt_spatial_query_test test_spatial_query.cc $(TARGET_LIB)
	@echo "Built lightrt_spatial_query_test (run: ./lightrt_spatial_query_test)"

# ---- C11 fp32 triangle kernel self-test (scalar + SSE4/AVX2 on x86,
#      NEON/SVE on aarch64). On A64FX: make c_tri_test CC=fcc && ./lightrt_c_tri_test
C_TRI_TEST_SRC = tests/test_lightrt_c_tri.c lightrt_c_tri.c
c_tri_test: $(C_TRI_TEST_SRC)
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -o lightrt_c_tri_test $^ -lm -lpthread
	@echo "Built lightrt_c_tri_test (run: ./lightrt_c_tri_test)"

# Seam (watertightness) test of the main triangle leaf: default build reports the
# Moller-Trumbore leak count (-DLRT_TRI_NO_WATERTIGHT_TRI); the _wt build (the
# default watertight leaf) requires 0.
c_tri_seam_test: tests/test_lightrt_c_tri_seam.c lightrt_c_tri.c
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -DLRT_TRI_NO_WATERTIGHT_TRI -o lightrt_c_tri_seam_test $^ -lm -lpthread
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -DLRT_TRI_WATERTIGHT_TRI -o lightrt_c_tri_seam_test_wt $^ -lm -lpthread
	./lightrt_c_tri_seam_test && ./lightrt_c_tri_seam_test_wt

# Axis-parallel rays exactly on box faces, all node formats; the _rb build
# (robust slab + exact leaf boxes + watertight leaf) requires 0 misses.
c_tri_parallel_test: tests/test_lightrt_c_tri_parallel.c lightrt_c_tri.c
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -DLRT_TRI_NO_SLAB_ROBUST -DLRT_TRI_NO_LEAF_BOX_EXACT -DLRT_TRI_NO_BITEXACT -DLRT_TRI_NO_WATERTIGHT_TRI -o lightrt_c_tri_parallel_test $^ -lm -lpthread
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -DLRT_TRI_SLAB_ROBUST -DLRT_TRI_LEAF_BOX_EXACT -DLRT_TRI_WATERTIGHT_TRI -o lightrt_c_tri_parallel_test_rb $^ -lm -lpthread
	./lightrt_c_tri_parallel_test && ./lightrt_c_tri_parallel_test_rb

# ---- Vulkan GPU interop (opt-in; runtime dlopen of libvulkan, no SDK, no -lvulkan) ----
# Build + run the GPU-interop self-test:  make vk_test && ./lightrt_c_vk_test
VK_SOURCES = lightrt_vkew.c lightrt_c_vk.c lightrt_c_tri.c
VK_TEST_SRC = tests/test_lightrt_c_vk.c

vk_test: $(VK_SOURCES) $(VK_TEST_SRC)
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -o lightrt_c_vk_test $^ -ldl -lm -lpthread
	@echo "Built lightrt_c_vk_test (run: ./lightrt_c_vk_test)"

# Optional: regenerate the checked-in SPIR-V headers (needs glslang; not in 'all').
shaders:
	GLSLANG=$(GLSLANG) bash scripts/compile_shaders.sh

info_vk:
	@echo "CC: $(CC)"
	@echo "CFLAGS: $(CFLAGS) $(C_SIMD)"

# ---- HIP (ROCm/AMD) GPU backend (opt-in; needs hipcc) ----
# Build + run the HIP self-test:        make hip_test && ./lightrt_c_hip_test
# Build the HIP benchmark:              make benchmark_hip && ./bench_hip
HIPCC ?= hipcc
HIP_ARCH ?= gfx1201
ROCM_PATH ?= /opt/rocm
HIP_FLAGS = --offload-arch=$(HIP_ARCH) -ffp-contract=off -O2 $(INCLUDES)
# rocWMMA / hipCUB are header-only; enable when present.
HIP_WMMA := $(wildcard $(ROCM_PATH)/include/rocwmma/rocwmma.hpp)
ifneq ($(HIP_WMMA),)
HIP_WMMA_FLAGS = -DLIGHTRT_HIP_HAVE_WMMA -I$(ROCM_PATH)/include
endif
HIP_HIPCUB := $(wildcard $(ROCM_PATH)/include/hipcub/hipcub.hpp)
ifneq ($(HIP_HIPCUB),)
HIP_HIPCUB_FLAGS = -DLIGHTRT_HIP_HAVE_HIPCUB -I$(ROCM_PATH)/include
endif
HIP_C_OBJS = /tmp/lrt_hip_c.o /tmp/lrt_hip_c_tri.o
HIP_DEV_OBJS = /tmp/lrt_hip_dev.o /tmp/lrt_hip_wmma.o /tmp/lrt_hip_lbvh.o

hip_dev_objs:
	$(HIPCC) $(HIP_FLAGS) -c lightrt_c_hip.hip -o /tmp/lrt_hip_dev.o
	$(HIPCC) $(HIP_FLAGS) $(HIP_WMMA_FLAGS) -c lightrt_hip_wmma.hip -o /tmp/lrt_hip_wmma.o
	$(HIPCC) $(HIP_FLAGS) $(HIP_HIPCUB_FLAGS) -c lightrt_hip_lbvh.hip -o /tmp/lrt_hip_lbvh.o

hip_test: hip_dev_objs
	$(CC) $(CFLAGS) $(INCLUDES) -c lightrt_c.c -o /tmp/lrt_hip_c.o
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -c lightrt_c_tri.c -o /tmp/lrt_hip_c_tri.o
	$(CC) $(CFLAGS) $(INCLUDES) -c tests/test_lightrt_c_hip.c -o /tmp/lrt_hip_test.o
	$(HIPCC) --offload-arch=$(HIP_ARCH) -O2 /tmp/lrt_hip_test.o $(HIP_DEV_OBJS) $(HIP_C_OBJS) -o lightrt_c_hip_test -lm
	@echo "Built lightrt_c_hip_test (run: ./lightrt_c_hip_test)"

# hiprtc Path-A trace (lightrt_c_hip.c): plain C, dlopen'd HIP/hiprtc via
# lightrt_hipew.c (no hipcc/ROCm SDK at build time). Defines the same lrt_hip_*
# engine symbols as the precompiled lightrt_c_hip.hip backend, so it is built as
# a separate binary. The _rb variant (robust slab + exact leaf boxes +
# watertight leaf) requires 0 GPU misses and GPU == CPU bit for bit.
HIP_RTC_SRC = tests/test_lightrt_c_hip_rtc.c lightrt_c_hip.c lightrt_hipew.c lightrt_c_tri.c lightrt_c.c
hip_rtc_test: $(HIP_RTC_SRC)
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -o lightrt_c_hip_rtc_test $(HIP_RTC_SRC) -ldl -lm -lpthread
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -DLRT_TRI_SLAB_ROBUST -DLRT_TRI_LEAF_BOX_EXACT -DLRT_TRI_WATERTIGHT_TRI -o lightrt_c_hip_rtc_test_rb $(HIP_RTC_SRC) -ldl -lm -lpthread
	./lightrt_c_hip_rtc_test && ./lightrt_c_hip_rtc_test_rb

benchmark_hip: hip_dev_objs
	$(CC) $(CFLAGS) $(INCLUDES) -c lightrt_c.c -o /tmp/lrt_hip_c.o
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -c lightrt_c_tri.c -o /tmp/lrt_hip_c_tri.o
	$(CC) $(CFLAGS) $(INCLUDES) -c benchmark_c/rays.c -o /tmp/lrt_hip_rays.o
	$(CC) $(CFLAGS) $(INCLUDES) -c benchmark_c/scene_mandelbulb.c -o /tmp/lrt_hip_mb.o
	$(CC) $(CFLAGS) $(INCLUDES) -c benchmark_c/scene_thinspan.c -o /tmp/lrt_hip_ts.o
	$(CC) -std=gnu11 $(filter-out -std=c11,$(CFLAGS)) $(INCLUDES) -c benchmark_hip/bench_hip_main.c -o /tmp/lrt_hip_bench.o
	$(HIPCC) --offload-arch=$(HIP_ARCH) -O2 /tmp/lrt_hip_bench.o $(HIP_DEV_OBJS) $(HIP_C_OBJS) /tmp/lrt_hip_rays.o /tmp/lrt_hip_mb.o /tmp/lrt_hip_ts.o -o bench_hip -lm
	@echo "Built bench_hip (run: ./bench_hip --scene mandelbulb  |  ./bench_hip --leaf)"

info_hip:
	@echo "HIPCC: $(HIPCC)"
	@echo "HIP_ARCH: $(HIP_ARCH)"
	@echo "HIP_FLAGS: $(HIP_FLAGS)"

# ---- CUDA (NVIDIA) GPU backend (opt-in; needs nvcc) ----
# A port of the HIP backend's fp32 build+trace path. The WMMA/integer-quantized
# leaf kernels and the full-GPU LBVH builder are HIP-only for now (stubbed).
# Build + run the CUDA self-test:  make cuda_test && ./lightrt_c_cuda_test
# Override the target arch:        make cuda_test CUDA_ARCH=sm_90
NVCC ?= nvcc
CUDA_ARCH ?= sm_120
# --fmad=false keeps the GPU kernel bit-faithful to the scalar C kernel (matches
# the HIP backend's -ffp-contract=off and the CMake build's --fmad=false).
CUDA_FLAGS = -std=c++17 -O2 -arch=$(CUDA_ARCH) --fmad=false $(INCLUDES)

cuda_test:
	$(NVCC) $(CUDA_FLAGS) -c lightrt_c_cuda.cu -o /tmp/lrt_cuda_dev.o
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -c lightrt_c_tri.c -o /tmp/lrt_cuda_c_tri.o
	$(CC) $(CFLAGS) $(INCLUDES) -c tests/test_lightrt_c_cuda.c -o /tmp/lrt_cuda_test.o
	$(NVCC) -arch=$(CUDA_ARCH) /tmp/lrt_cuda_test.o /tmp/lrt_cuda_dev.o /tmp/lrt_cuda_c_tri.o -o lightrt_c_cuda_test -lm
	@echo "Built lightrt_c_cuda_test (run: ./lightrt_c_cuda_test)"

# Full CUDA correctness suite (needs a CUDA device; skips otherwise):
#  - lightrt_c_cuda_test           triangles (resident/one-shot/refit)
#  - lightrt_c_cuda_prims_test     every primitive kind + normals vs the CPU oracle
#  - lightrt_c_cuda_parallel_test  vertical rays exactly on box faces (report);
#    _wt: + LRT_TRI_WATERTIGHT_TRI, requires 0 misses and GPU == CPU bit for bit
# The prims/parallel sources are generated from the HIP tests (scripts/gen_cuda_tests.sh).
CUDA_FULL_OBJ = /tmp/lrt_cuda_full
cuda_full_test: cuda_test
	$(CC) $(CFLAGS) $(INCLUDES) -c tests/test_lightrt_c_cuda_prims.c -o $(CUDA_FULL_OBJ)_prims.o
	$(NVCC) -arch=$(CUDA_ARCH) $(CUDA_FULL_OBJ)_prims.o /tmp/lrt_cuda_dev.o /tmp/lrt_cuda_c_tri.o -o lightrt_c_cuda_prims_test -lm
	$(CC) $(CFLAGS) $(INCLUDES) -c tests/test_lightrt_c_cuda_parallel.c -o $(CUDA_FULL_OBJ)_par.o
	$(NVCC) -arch=$(CUDA_ARCH) $(CUDA_FULL_OBJ)_par.o /tmp/lrt_cuda_dev.o /tmp/lrt_cuda_c_tri.o -o lightrt_c_cuda_parallel_test -lm
	$(NVCC) $(CUDA_FLAGS) -DLRT_TRI_WATERTIGHT_TRI -c lightrt_c_cuda.cu -o $(CUDA_FULL_OBJ)_dev_wt.o
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -DLRT_TRI_WATERTIGHT_TRI -c lightrt_c_tri.c -o $(CUDA_FULL_OBJ)_tri_wt.o
	$(CC) $(CFLAGS) $(INCLUDES) -DLRT_TRI_WATERTIGHT_TRI -c tests/test_lightrt_c_cuda_parallel.c -o $(CUDA_FULL_OBJ)_par_wt.o
	$(NVCC) -arch=$(CUDA_ARCH) $(CUDA_FULL_OBJ)_par_wt.o $(CUDA_FULL_OBJ)_dev_wt.o $(CUDA_FULL_OBJ)_tri_wt.o -o lightrt_c_cuda_parallel_test_wt -lm
	./lightrt_c_cuda_test && ./lightrt_c_cuda_prims_test && ./lightrt_c_cuda_parallel_test && ./lightrt_c_cuda_parallel_test_wt

info_cuda:
	@echo "NVCC: $(NVCC)"
	@echo "CUDA_ARCH: $(CUDA_ARCH)"
	@echo "CUDA_FLAGS: $(CUDA_FLAGS)"

.PHONY: cuda_full_test hip_rtc_test c_tri_parallel_test c_tri_seam_test all clean run benchmark obj_bench info vk_test shaders info_vk hip_dev_objs hip_test benchmark_hip info_hip cuda_test info_cuda formal

# Lean 4 formal verification (formal/): build specs+proofs, check the c2lean
# translation is up to date, the sorry budget, the axiom allowlist, and run
# 3-way differential testing (compiled C vs MiniC vs Lean reference).
FORMAL_SORRY_MAX ?= 0
formal:
	cd formal && lake build
	python3 formal/tools/c2lean.py --check
	sh formal/tools/count_sorry.sh --max $(FORMAL_SORRY_MAX)
	python3 formal/tools/check_axioms.py > /dev/null
	python3 formal/tools/cdiff.py --n 1000
	python3 formal/tools/bvhcheck.py --rays 100 --seeds 2
	$(CC) -O1 -ffp-contract=off -msse4.1 -mavx2 -mfma -w -I. -o formal/.lake/tlascheck formal/tools/tlascheck.c -lm -lpthread
	$(CC) -O1 -ffp-contract=off -msse4.1 -mavx2 -mfma -w -I. -DLRT_TRI_EXACT_NEAREST -o formal/.lake/tlascheck_exn formal/tools/tlascheck.c -lm -lpthread
	for s in 1 2; do formal/.lake/tlascheck $$s 1000 && formal/.lake/tlascheck_exn $$s 1000 || exit 1; done
	$(CC) -O1 -ffp-contract=off -msse4.1 -mavx2 -mfma -w -I. -DLRT_TRI_WATERTIGHT_TRI -o formal/.lake/wtcheck formal/tools/wtcheck.c -lm -lpthread
	formal/.lake/wtcheck 2 3000
	$(CC) -O1 -ffp-contract=off -msse4.1 -mavx2 -mfma -w -I. -DLRT_TRI_WATERTIGHT_TRI -DLRT_TRI_EXACT_NEAREST -o formal/.lake/wtcheck_exn formal/tools/wtcheck.c -lm -lpthread
	formal/.lake/wtcheck_exn 2 3000
	$(CC) -O1 -ffp-contract=off -msse4.1 -mavx2 -mfma -w -I. -o formal/.lake/primboxcheck formal/tools/primboxcheck.c -lm -lpthread
	for s in 1 2 3; do formal/.lake/primboxcheck $$s formal/.lake > formal/.lake/primboxcheck.log || { cat formal/.lake/primboxcheck.log; exit 1; }; done; tail -n 3 formal/.lake/primboxcheck.log
	$(CC) -O2 -ffp-contract=off -msse4.1 -mavx2 -mfma -w -I. -o formal/.lake/primhitcheck formal/tools/primhitcheck.c -lm -lpthread
	for s in 1 2; do formal/.lake/primhitcheck $$s 2000 || exit 1; done
