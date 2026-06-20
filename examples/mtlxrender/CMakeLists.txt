# CMakeLists.txt for mtlxrender - C11 MaterialX path tracer.
# Standalone: `cmake -S . -B build && cmake --build build -j`.
cmake_minimum_required(VERSION 3.13)
project(mtlxrender LANGUAGES C)

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

set(LIGHTRT_ROOT ${CMAKE_CURRENT_SOURCE_DIR}/../..)
set(DEPS ${CMAKE_CURRENT_SOURCE_DIR}/deps)
set(TINYEXR ${DEPS}/tinyexr)

file(GLOB TINYEXR_SRC ${TINYEXR}/src/*.c)

# First-party sources (full warnings).
set(APP_SRC
    main.c pathtrace.c bsdf.c env.c framebuffer.c color.c
    gltf_load.c mtlx_xml.c mtlx_doc.c mtlx_eval.c material_bind.c texture.c)
# Third-party sources (compiled quietly).
set(TP_SRC
    third_party_impl.c
    ${LIGHTRT_ROOT}/lightrt_c_tri.c
    ${DEPS}/tiny_gltf_v3.c
    ${TINYEXR_SRC})

add_executable(mtlxrender ${APP_SRC} ${TP_SRC})
target_include_directories(mtlxrender PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR} ${LIGHTRT_ROOT} ${DEPS} ${TINYEXR}/include)
target_compile_definitions(mtlxrender PRIVATE
    _POSIX_C_SOURCE=200809L TINYGLTF3_ENABLE_FS EXR_NO_ZSTD EXR_USE_THREADS)

# SIMD for the C triangle BVH (optional; scalar fallback otherwise).
include(CheckCCompilerFlag)
if(CMAKE_SYSTEM_PROCESSOR MATCHES "(x86_64|amd64|AMD64)")
    check_c_compiler_flag(-msse4.1 HAS_SSE41)
    check_c_compiler_flag(-mavx2 HAS_AVX2)
    if(HAS_SSE41)
        target_compile_options(mtlxrender PRIVATE -msse4.1)
    endif()
    if(HAS_AVX2)
        target_compile_options(mtlxrender PRIVATE -mavx2 -mfma)
    endif()
endif()

# Quiet warnings for vendored third-party translation units.
set_source_files_properties(${TP_SRC} PROPERTIES COMPILE_OPTIONS "-w")
set_source_files_properties(${APP_SRC} PROPERTIES COMPILE_OPTIONS "-Wall;-Wextra")

find_package(Threads REQUIRED)
target_link_libraries(mtlxrender PRIVATE Threads::Threads m)

# Per-node numeric ground-truth tests.
enable_testing()
add_executable(node_truth
    tests/node_truth.c mtlx_doc.c mtlx_xml.c mtlx_eval.c texture.c color.c third_party_impl.c)
target_include_directories(node_truth PRIVATE ${CMAKE_CURRENT_SOURCE_DIR} ${LIGHTRT_ROOT} ${DEPS})
target_compile_definitions(node_truth PRIVATE _POSIX_C_SOURCE=200809L)
set_source_files_properties(third_party_impl.c PROPERTIES COMPILE_OPTIONS "-w")
target_link_libraries(node_truth PRIVATE m)
add_test(NAME node_truth COMMAND node_truth)
