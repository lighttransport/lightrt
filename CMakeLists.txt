# CMakeLists.txt for LightRT - Lightweight ray tracing and BVH kernel
# Copyright (c) 2026 Light Transport Entertainment, Inc.
# SPDX-License-Identifier: MIT

cmake_minimum_required(VERSION 3.10)
project(lightrt VERSION 1.0.0 LANGUAGES CXX)

include(CTest)

# C++17 standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Compiler flags: no RTTI, no exceptions
if(MSVC)
    # Remove default /GR to avoid override warning, keep /EHsc for MSVC
    string(REPLACE "/GR" "" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /GR-")
    add_definitions(-DNOMINMAX -D_CRT_SECURE_NO_WARNINGS)
else()
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti -fno-exceptions")
endif()

# Optimization flags
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

if(MSVC)
    set(CMAKE_CXX_FLAGS_RELEASE "/O2 /DNDEBUG")
    set(CMAKE_CXX_FLAGS_DEBUG "/Od /Zi /DDEBUG")
else()
    set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG")
    set(CMAKE_CXX_FLAGS_DEBUG "-O0 -g -DDEBUG")
endif()

# Detect and enable SIMD support
if(CMAKE_SYSTEM_PROCESSOR MATCHES "(x86_64)|(AMD64|amd64)|(^i.86$)")
    message(STATUS "x86/x64 architecture detected")

    include(CheckCXXCompilerFlag)

    if(MSVC)
        # MSVC: SSE2 is default on x64, use /arch: for AVX/AVX2
        if(CMAKE_SIZEOF_VOID_P EQUAL 4)
            # SSE2 flag only needed for 32-bit MSVC
            set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /arch:SSE2")
            message(STATUS "SSE2 support enabled")
        else()
            message(STATUS "SSE2 support enabled (default on x64)")
        endif()

        if(NOT NO_AVX2)
            check_cxx_compiler_flag("/arch:AVX2" COMPILER_SUPPORTS_AVX2)
            if(COMPILER_SUPPORTS_AVX2)
                set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /arch:AVX2")
                message(STATUS "AVX2 support enabled (includes AVX, FMA, F16C)")
            endif()
        elseif(NOT NO_AVX)
            check_cxx_compiler_flag("/arch:AVX" COMPILER_SUPPORTS_AVX)
            if(COMPILER_SUPPORTS_AVX)
                set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /arch:AVX")
                message(STATUS "AVX support enabled")
            endif()
        endif()
    else()
        # GCC/Clang
        check_cxx_compiler_flag("-msse2" COMPILER_SUPPORTS_SSE2)
        if(COMPILER_SUPPORTS_SSE2)
            set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -msse2")
            message(STATUS "SSE2 support enabled")
        endif()

        check_cxx_compiler_flag("-mavx" COMPILER_SUPPORTS_AVX)
        if(COMPILER_SUPPORTS_AVX AND NOT NO_AVX)
            set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -mavx")
            message(STATUS "AVX support enabled")
        endif()

        check_cxx_compiler_flag("-mavx2" COMPILER_SUPPORTS_AVX2)
        if(COMPILER_SUPPORTS_AVX2 AND NOT NO_AVX2)
            set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -mavx2 -mfma")
            message(STATUS "AVX2 support enabled")
        endif()

        check_cxx_compiler_flag("-mf16c" COMPILER_SUPPORTS_F16C)
        if(COMPILER_SUPPORTS_F16C AND NOT NO_F16C)
            set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -mf16c")
            message(STATUS "F16C support enabled")
        endif()
    endif()

elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "^(aarch64|arm64)")
    message(STATUS "ARM64 architecture detected")

    if(NOT MSVC)
        # ARM NEON is typically available by default on aarch64
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -march=armv8-a")
        message(STATUS "ARM NEON support enabled")

        # Check for SVE support
        include(CheckCXXCompilerFlag)
        check_cxx_compiler_flag("-march=armv8-a+sve" COMPILER_SUPPORTS_SVE)
        if(COMPILER_SUPPORTS_SVE AND NOT NO_SVE)
            set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -march=armv8-a+sve")
            message(STATUS "ARM SVE support enabled")
        endif()
    else()
        message(STATUS "ARM NEON support enabled (default on ARM64 MSVC)")
    endif()

elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "^arm")
    message(STATUS "ARM32 architecture detected")

    if(NOT MSVC)
        include(CheckCXXCompilerFlag)
        check_cxx_compiler_flag("-mfpu=neon" COMPILER_SUPPORTS_NEON)
        if(COMPILER_SUPPORTS_NEON)
            set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -mfpu=neon")
            message(STATUS "ARM NEON support enabled")
        endif()
    endif()
endif()

# Library target
add_library(lightrt STATIC
    lightrt.cc
    lightrt.hh
    lightrt_c.cc
    lightrt_c.h
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

# Benchmark executable
add_executable(lightrt_benchmark
    benchmark/benchmark.cc
)

target_link_libraries(lightrt_benchmark
    lightrt
)

option(LIGHTRT_BUILD_WEBGPU "Build WebGPU software backend targets" ON)
if(LIGHTRT_BUILD_WEBGPU)
    add_subdirectory(webgpu)
endif()

# Build viewer_windows by default on Windows
if(WIN32)
    option(LIGHTRT_BUILD_VIEWER_WINDOWS "Build Windows viewer" ON)
    if(LIGHTRT_BUILD_VIEWER_WINDOWS)
        add_subdirectory(viewer_windows)
    endif()
endif()

# Installation
install(TARGETS lightrt
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
)

install(FILES lightrt.hh lightrt_c.h
    DESTINATION include
)

# Print configuration summary
message(STATUS "")
message(STATUS "LightRT Configuration Summary:")
message(STATUS "  Build type: ${CMAKE_BUILD_TYPE}")
message(STATUS "  C++ standard: ${CMAKE_CXX_STANDARD}")
message(STATUS "  Compiler flags: ${CMAKE_CXX_FLAGS}")
message(STATUS "  System processor: ${CMAKE_SYSTEM_PROCESSOR}")
message(STATUS "  Build WebGPU: ${LIGHTRT_BUILD_WEBGPU}")
if(WIN32)
    message(STATUS "  Build Windows viewer: ${LIGHTRT_BUILD_VIEWER_WINDOWS}")
endif()
message(STATUS "")
