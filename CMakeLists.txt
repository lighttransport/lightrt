# CMakeLists.txt for LightRT - Lightweight ray tracing and BVH kernel
# Copyright (c) 2026 Light Transport Entertainment, Inc.
# SPDX-License-Identifier: MIT

cmake_minimum_required(VERSION 3.10)
project(lightrt VERSION 1.0.0 LANGUAGES CXX)

# C++17 standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Compiler flags: no RTTI, no exceptions
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti -fno-exceptions")

# Optimization flags
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_DEBUG "-O0 -g -DDEBUG")

# Detect and enable SIMD support
if(CMAKE_SYSTEM_PROCESSOR MATCHES "(x86_64)|(AMD64|amd64)|(^i.86$)")
    message(STATUS "x86/x64 architecture detected")
    
    # Check for SSE2 support (baseline for x64)
    include(CheckCXXCompilerFlag)
    check_cxx_compiler_flag("-msse2" COMPILER_SUPPORTS_SSE2)
    if(COMPILER_SUPPORTS_SSE2)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -msse2")
        message(STATUS "SSE2 support enabled")
    endif()
    
    # Check for AVX support
    check_cxx_compiler_flag("-mavx" COMPILER_SUPPORTS_AVX)
    if(COMPILER_SUPPORTS_AVX AND NOT NO_AVX)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -mavx")
        message(STATUS "AVX support enabled")
    endif()
    
    # Check for AVX2 support
    check_cxx_compiler_flag("-mavx2" COMPILER_SUPPORTS_AVX2)
    if(COMPILER_SUPPORTS_AVX2 AND NOT NO_AVX2)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -mavx2 -mfma")
        message(STATUS "AVX2 support enabled")
    endif()
    
    # Check for F16C support (FP16 conversion)
    check_cxx_compiler_flag("-mf16c" COMPILER_SUPPORTS_F16C)
    if(COMPILER_SUPPORTS_F16C AND NOT NO_F16C)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -mf16c")
        message(STATUS "F16C support enabled")
    endif()
    
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "^(aarch64|arm64)")
    message(STATUS "ARM64 architecture detected")
    
    # ARM NEON is typically available by default on aarch64
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -march=armv8-a")
    message(STATUS "ARM NEON support enabled")
    
    # Check for SVE support
    check_cxx_compiler_flag("-march=armv8-a+sve" COMPILER_SUPPORTS_SVE)
    if(COMPILER_SUPPORTS_SVE AND NOT NO_SVE)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -march=armv8-a+sve")
        message(STATUS "ARM SVE support enabled")
    endif()
    
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "^arm")
    message(STATUS "ARM32 architecture detected")
    
    # Check for NEON support on ARM32
    include(CheckCXXCompilerFlag)
    check_cxx_compiler_flag("-mfpu=neon" COMPILER_SUPPORTS_NEON)
    if(COMPILER_SUPPORTS_NEON)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -mfpu=neon")
        message(STATUS "ARM NEON support enabled")
    endif()
endif()

# Library target
add_library(lightrt STATIC
    lightrt.cc
    lightrt.hh
)

target_include_directories(lightrt PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
)

# Example executable
add_executable(lightrt_example
    example.cc
)

target_link_libraries(lightrt_example
    lightrt
)

# Installation
install(TARGETS lightrt
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
)

install(FILES lightrt.hh
    DESTINATION include
)

# Print configuration summary
message(STATUS "")
message(STATUS "LightRT Configuration Summary:")
message(STATUS "  Build type: ${CMAKE_BUILD_TYPE}")
message(STATUS "  C++ standard: ${CMAKE_CXX_STANDARD}")
message(STATUS "  Compiler flags: ${CMAKE_CXX_FLAGS}")
message(STATUS "  System processor: ${CMAKE_SYSTEM_PROCESSOR}")
message(STATUS "")
