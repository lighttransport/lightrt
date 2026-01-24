# Makefile for LightRT - Lightweight ray tracing and BVH kernel
# Copyright (c) 2026 Light Transport Entertainment, Inc.
# SPDX-License-Identifier: MIT

CXX ?= g++
AR ?= ar

# Compiler flags
CXXFLAGS = -std=c++17 -Wall -Wextra -O3 -fno-rtti -fno-exceptions
INCLUDES = -I.
LDFLAGS =

# Detect architecture and enable SIMD
ARCH := $(shell uname -m)

ifeq ($(ARCH),x86_64)
    # x86-64: Enable SSE2 (baseline) and optionally AVX
    CXXFLAGS += -msse2
    ifneq ($(NO_AVX),1)
        CXXFLAGS += -mavx
    endif
    # Optional: Enable AVX2 and FMA
    ifneq ($(NO_AVX2),1)
        CXXFLAGS += -mavx2 -mfma
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
    CXXFLAGS := $(filter-out -O3,$(CXXFLAGS))
    CXXFLAGS += -O0 -g -DDEBUG
endif

# Targets
TARGET_LIB = liblightrt.a
TARGET_EXAMPLE = lightrt_example

# Source files
SOURCES = lightrt.cc
OBJECTS = $(SOURCES:.cc=.o)

# Example source
EXAMPLE_SOURCES = example.cc
EXAMPLE_OBJECTS = $(EXAMPLE_SOURCES:.cc=.o)

# Default target
all: $(TARGET_LIB) $(TARGET_EXAMPLE)

# Build static library
$(TARGET_LIB): $(OBJECTS)
	$(AR) rcs $@ $^
	@echo "Built $(TARGET_LIB)"

# Build example
$(TARGET_EXAMPLE): $(EXAMPLE_OBJECTS) $(TARGET_LIB)
	$(CXX) $(CXXFLAGS) -o $@ $(EXAMPLE_OBJECTS) $(TARGET_LIB) $(LDFLAGS)
	@echo "Built $(TARGET_EXAMPLE)"

# Compile source files
%.o: %.cc lightrt.hh
	$(CXX) $(CXXFLAGS) $(INCLUDES) -c $< -o $@

# Clean build artifacts
clean:
	rm -f $(OBJECTS) $(EXAMPLE_OBJECTS) $(TARGET_LIB) $(TARGET_EXAMPLE)
	@echo "Cleaned build artifacts"

# Run example
run: $(TARGET_EXAMPLE)
	./$(TARGET_EXAMPLE)

# Print configuration
info:
	@echo "Compiler: $(CXX)"
	@echo "Architecture: $(ARCH)"
	@echo "CXXFLAGS: $(CXXFLAGS)"
	@echo "INCLUDES: $(INCLUDES)"
	@echo "LDFLAGS: $(LDFLAGS)"

.PHONY: all clean run info
