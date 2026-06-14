# CMakeLists.txt for LightRT - Lightweight ray tracing and BVH kernel
# Copyright (c) 2026 Light Transport Entertainment, Inc.
# SPDX-License-Identifier: MIT

cmake_minimum_required(VERSION 3.10)
project(lightrt VERSION 1.0.0 LANGUAGES CXX C)

include(CTest)

# C++17 standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# C11 standard (for the pure-C binding lightrt_c.c and its test)
set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

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

# C binding implementation. lightrt_c.c is a standalone pure-C11 BVH +
# callback implementation; the C API does not depend on the C++ BVH wrapper.
option(LIGHTRT_BUILD_FUZZERS
       "Build libFuzzer harnesses for LightRT"
       OFF)
# Vulkan GPU interop (lightrt_vkew + lightrt_c_vk). Runtime dlopen of libvulkan;
# NO Vulkan SDK headers and NO link-time -lvulkan (we deliberately do not call
# find_package(Vulkan)). SPIR-V is checked in under vk/shaders, so no shader
# toolchain is needed either.
option(LIGHTRT_BUILD_VK
       "Build the Vulkan GPU-interop trace/build backend"
       OFF)
set(LIGHTRT_C_BINDING_SRC lightrt_c.c)

# Library target
add_library(lightrt STATIC
    lightrt.cc
    lightrt.hh
    ${LIGHTRT_C_BINDING_SRC}
    lightrt_c.h
    lightrt_c_tri.c
    lightrt_c_tri.h
)

# SIMD flags above are CXX-only; the C11 triangle BVH needs its own C flags or
# it silently builds scalar kernels (lrt_tri_kernel_name() reports which).
include(CheckCCompilerFlag)
set(LIGHTRT_C_TRI_SIMD_FLAGS "")
if(NOT MSVC)
    check_c_compiler_flag("-msse4.1" C_COMPILER_SUPPORTS_SSE41)
    if(C_COMPILER_SUPPORTS_SSE41)
        list(APPEND LIGHTRT_C_TRI_SIMD_FLAGS -msse4.1)
    endif()
    check_c_compiler_flag("-mavx2" C_COMPILER_SUPPORTS_AVX2)
    if(C_COMPILER_SUPPORTS_AVX2)
        list(APPEND LIGHTRT_C_TRI_SIMD_FLAGS -mavx2 -mfma)
    endif()
endif()
if(LIGHTRT_C_TRI_SIMD_FLAGS)
    set_source_files_properties(lightrt_c_tri.c PROPERTIES
        COMPILE_OPTIONS "${LIGHTRT_C_TRI_SIMD_FLAGS}")
endif()

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

# Pure-C11 binding self-test (compiles lightrt_c.c directly; no C++ dependency).
if(BUILD_TESTING)
    add_executable(lightrt_c_test lightrt_c.c tests/test_lightrt_c.c)
    if(NOT MSVC)
        target_link_libraries(lightrt_c_test m)
    endif()
    add_test(NAME lightrt_c_test COMMAND lightrt_c_test)

    # fp32 triangle BVH self-test (pure C11, SIMD kernels when available)
    add_executable(lightrt_c_tri_test lightrt_c_tri.c tests/test_lightrt_c_tri.c)
    if(LIGHTRT_C_TRI_SIMD_FLAGS)
        target_compile_options(lightrt_c_tri_test PRIVATE ${LIGHTRT_C_TRI_SIMD_FLAGS})
    endif()
    find_package(Threads QUIET)
    if(Threads_FOUND)
        target_link_libraries(lightrt_c_tri_test Threads::Threads)
    endif()
    if(NOT MSVC)
        target_link_libraries(lightrt_c_tri_test m)
    endif()
    add_test(NAME lightrt_c_tri_test COMMAND lightrt_c_tri_test)

    # Vulkan GPU interop self-test. Skips (exit 0) when no Vulkan device is
    # present, so GPU-less CI stays green.
    if(LIGHTRT_BUILD_VK)
        add_executable(lightrt_c_vk_test
            lightrt_vkew.c lightrt_c_vk.c lightrt_c_tri.c
            tests/test_lightrt_c_vk.c)
        target_include_directories(lightrt_c_vk_test PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
        if(LIGHTRT_C_TRI_SIMD_FLAGS)
            set_source_files_properties(lightrt_c_tri.c PROPERTIES
                COMPILE_OPTIONS "${LIGHTRT_C_TRI_SIMD_FLAGS}")
        endif()
        target_link_libraries(lightrt_c_vk_test ${CMAKE_DL_LIBS})
        find_package(Threads QUIET)
        if(Threads_FOUND)
            target_link_libraries(lightrt_c_vk_test Threads::Threads)
        endif()
        if(NOT MSVC)
            target_link_libraries(lightrt_c_vk_test m)
        endif()
        add_test(NAME lightrt_c_vk_test COMMAND lightrt_c_vk_test)
    endif()
endif()

# Static library for embedding the Vulkan GPU-interop backend in other targets.
if(LIGHTRT_BUILD_VK)
    add_library(lightrt_vk STATIC lightrt_vkew.c lightrt_c_vk.c)
    target_include_directories(lightrt_vk PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
    target_link_libraries(lightrt_vk PUBLIC ${CMAKE_DL_LIBS})
    if(NOT MSVC)
        target_link_libraries(lightrt_vk PUBLIC m)
    endif()
endif()

# Optional: regenerate the checked-in SPIR-V headers (developers with glslang
# only; never part of the default build / ALL target).
find_program(LIGHTRT_GLSLANG glslangValidator)
if(LIGHTRT_GLSLANG)
    add_custom_target(shaders
        COMMAND ${CMAKE_COMMAND} -E env GLSLANG=${LIGHTRT_GLSLANG}
                bash ${CMAKE_CURRENT_SOURCE_DIR}/scripts/compile_shaders.sh
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
        COMMENT "Regenerating checked-in SPIR-V headers (optional)"
        VERBATIM)
endif()

if(LIGHTRT_BUILD_FUZZERS)
    if(NOT CMAKE_C_COMPILER_ID MATCHES "Clang")
        message(FATAL_ERROR "LIGHTRT_BUILD_FUZZERS requires Clang/libFuzzer")
    endif()

    add_executable(lightrt_c_fuzzer lightrt_c.c tests/fuzz_lightrt_c.c)
    target_compile_options(lightrt_c_fuzzer PRIVATE
        -fsanitize=fuzzer,address,undefined
        -fno-omit-frame-pointer
    )
    target_link_options(lightrt_c_fuzzer PRIVATE
        -fsanitize=fuzzer,address,undefined
    )
    if(NOT MSVC)
        target_link_libraries(lightrt_c_fuzzer m)
    endif()
endif()

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

install(FILES lightrt.hh lightrt_c.h lightrt_c_tri.h
    DESTINATION include
)
if(LIGHTRT_BUILD_VK)
    install(FILES lightrt_c_vk.h lightrt_vkew.h DESTINATION include)
endif()

# Standalone C11 benchmark vs Embree (benchmark_c/README.md)
option(LIGHTRT_BUILD_BENCHMARK_C "Build the C11 lightrt-vs-Embree benchmark" OFF)
if(LIGHTRT_BUILD_BENCHMARK_C)
    add_subdirectory(benchmark_c)
endif()

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
