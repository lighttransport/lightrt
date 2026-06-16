# Makefile for LightRT - Lightweight ray tracing and BVH kernel
# Copyright (c) 2026 Light Transport Entertainment, Inc.
# SPDX-License-Identifier: MIT

CC ?= gcc
CXX ?= g++
CC ?= cc
AR ?= ar

# Compiler flags
CFLAGS = -std=c11 -Wall -Wextra -O3
CXXFLAGS = -std=c++17 -Wall -Wextra -O3 -fno-rtti -fno-exceptions
CFLAGS = -std=c11 -Wall -Wextra -O3
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
    # ARM64: Enable NEON (typically available by default)
    CXXFLAGS += -march=armv8-a
    # Optional: Enable SVE
    ifneq ($(NO_SVE),1)
        CXXFLAGS += -march=armv8-a+sve
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
	$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

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
# rocWMMA is header-only; enable the matrix-core kernels when it is present.
HIP_WMMA := $(wildcard $(ROCM_PATH)/include/rocwmma/rocwmma.hpp)
ifneq ($(HIP_WMMA),)
HIP_WMMA_FLAGS = -DLIGHTRT_HIP_HAVE_WMMA -I$(ROCM_PATH)/include
endif
HIP_C_OBJS = /tmp/lrt_hip_c.o /tmp/lrt_hip_c_tri.o
HIP_DEV_OBJS = /tmp/lrt_hip_dev.o /tmp/lrt_hip_wmma.o

hip_dev_objs:
	$(HIPCC) $(HIP_FLAGS) -c lightrt_c_hip.hip -o /tmp/lrt_hip_dev.o
	$(HIPCC) $(HIP_FLAGS) $(HIP_WMMA_FLAGS) -c lightrt_hip_wmma.hip -o /tmp/lrt_hip_wmma.o

hip_test: hip_dev_objs
	$(CC) $(CFLAGS) $(INCLUDES) -c lightrt_c.c -o /tmp/lrt_hip_c.o
	$(CC) $(CFLAGS) $(C_SIMD) $(INCLUDES) -c lightrt_c_tri.c -o /tmp/lrt_hip_c_tri.o
	$(CC) $(CFLAGS) $(INCLUDES) -c tests/test_lightrt_c_hip.c -o /tmp/lrt_hip_test.o
	$(HIPCC) --offload-arch=$(HIP_ARCH) -O2 /tmp/lrt_hip_test.o $(HIP_DEV_OBJS) $(HIP_C_OBJS) -o lightrt_c_hip_test -lm
	@echo "Built lightrt_c_hip_test (run: ./lightrt_c_hip_test)"

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

.PHONY: all clean run benchmark obj_bench info vk_test shaders info_vk hip_dev_objs hip_test benchmark_hip info_hip
