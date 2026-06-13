# benchmark_c — standalone C11 ray tracing benchmark: lightrt C11 backends vs
# Embree 4. Configure with:
#   cmake -S benchmark_c -B build_bench_c -DCMAKE_BUILD_TYPE=Release
# Embree is picked up automatically after scripts/download_embree.sh, or via
# -DEMBREE_ROOT=<sdk dir>.
cmake_minimum_required(VERSION 3.15)
project(lightrt_bench_c LANGUAGES C CXX)

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)
# C++ is used only by optional comparison backends (tinybvh, madmann91/bvh,
# fetched by scripts/download_libs.sh); madmann91/bvh needs C++20.
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

add_executable(bench_c
    bench_main.c
    rays.c
    scene_mandelbulb.c
    scene_thinspan.c
    backend_lightrt_cb.c
    backend_lightrt_tri.c
    backend_lightrt_ext.c
    backend_lightrt_pkt.c
    backend_embree.c
    backend_tinybvh.cpp
    backend_madmann.cpp
    backend_lightrt_vk.c
    ../lightrt_c.c
    ../lightrt_c_tri.c
)

target_include_directories(bench_c PRIVATE ..)

target_compile_options(bench_c PRIVATE -O3 -Wall -Wextra)
# Strict -std=c11 hides POSIX declarations (clock_gettime, pthreads).
target_compile_definitions(bench_c PRIVATE _POSIX_C_SOURCE=200809L)

include(CheckCCompilerFlag)
check_c_compiler_flag(-msse4.1 HAS_C_SSE41)
if(HAS_C_SSE41)
    target_compile_options(bench_c PRIVATE -msse4.1)
endif()
check_c_compiler_flag(-mavx2 HAS_C_AVX2)
if(HAS_C_AVX2)
    target_compile_options(bench_c PRIVATE -mavx2 -mfma)
endif()

find_package(Threads REQUIRED)
target_link_libraries(bench_c PRIVATE Threads::Threads m)

# --- hair_bench: CyHair loader + round-linear ray-curve benchmark/renderer ---
add_executable(hair_bench
    hair_bench.c
    cyhair.c
    furball.c
    ../lightrt_c_tri.c
)
target_include_directories(hair_bench PRIVATE ..)
target_compile_options(hair_bench PRIVATE -O3 -Wall -Wextra)
target_compile_definitions(hair_bench PRIVATE _POSIX_C_SOURCE=200809L)
if(HAS_C_SSE41)
    target_compile_options(hair_bench PRIVATE -msse4.1)
endif()
if(HAS_C_AVX2)
    target_compile_options(hair_bench PRIVATE -mavx2 -mfma)
endif()
target_link_libraries(hair_bench PRIVATE Threads::Threads m)

# --- Optional Vulkan GPU trace backend (runtime dlopen; no SDK, no -lvulkan) ---
# backend_lightrt_vk.c always compiles (NULL stub) unless LRTBENCH_VK is set.
option(LRTBENCH_VK "Build the Vulkan GPU trace backend" OFF)
if(LRTBENCH_VK)
    target_sources(bench_c PRIVATE ../lightrt_vkew.c ../lightrt_c_vk.c)
    target_compile_definitions(bench_c PRIVATE LRTBENCH_HAVE_VK)
    target_link_libraries(bench_c PRIVATE ${CMAKE_DL_LIBS})
    message(STATUS "bench_c: Vulkan GPU backend enabled (runtime dlopen)")
else()
    message(STATUS "bench_c: Vulkan GPU backend disabled (-DLRTBENCH_VK=ON to enable)")
endif()

# --- Optional jbikker/tinybvh (scripts/download_libs.sh) ---
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/third_party/tinybvh/tiny_bvh.h")
    target_include_directories(bench_c PRIVATE
        "${CMAKE_CURRENT_SOURCE_DIR}/third_party/tinybvh")
    target_compile_definitions(bench_c PRIVATE LRTBENCH_HAVE_TINYBVH)
    message(STATUS "bench_c: tinybvh backend enabled")
else()
    message(STATUS "bench_c: tinybvh NOT found (run scripts/download_libs.sh)")
endif()

# --- Optional madmann91/bvh (scripts/download_libs.sh) ---
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/third_party/bvh/src/bvh/v2/bvh.h")
    target_include_directories(bench_c PRIVATE
        "${CMAKE_CURRENT_SOURCE_DIR}/third_party/bvh/src")
    target_compile_definitions(bench_c PRIVATE LRTBENCH_HAVE_MADMANN_BVH)
    message(STATUS "bench_c: madmann91/bvh backend enabled")
else()
    message(STATUS "bench_c: madmann91/bvh NOT found (run scripts/download_libs.sh)")
endif()

# --- Optional Embree 4 (pinned SDK from scripts/download_embree.sh) ---
set(EMBREE_ROOT "" CACHE PATH "Embree SDK root (overrides third_party/embree)")
set(_embree_search "${CMAKE_CURRENT_SOURCE_DIR}/third_party/embree")
if(EMBREE_ROOT)
    set(_embree_search "${EMBREE_ROOT}")
endif()

find_package(embree 4 CONFIG QUIET
    PATHS "${_embree_search}"
    PATH_SUFFIXES lib/cmake/embree-4.3.3 lib/cmake/embree-4.4.0 lib/cmake
    NO_DEFAULT_PATH)
if(embree_FOUND)
    target_link_libraries(bench_c PRIVATE embree)
    target_compile_definitions(bench_c PRIVATE LRTBENCH_HAVE_EMBREE)
    target_link_libraries(hair_bench PRIVATE embree)
    target_compile_definitions(hair_bench PRIVATE LRTBENCH_HAVE_EMBREE)
    # The SDK tarball bundles libembree4/libtbb in lib/; run from build dir.
    set_target_properties(bench_c hair_bench PROPERTIES
        BUILD_RPATH "${_embree_search}/lib"
        INSTALL_RPATH "${_embree_search}/lib")
    message(STATUS "bench_c: Embree found at ${_embree_search}")
else()
    message(STATUS "bench_c: Embree NOT found (run scripts/download_embree.sh); "
                   "the embree backend will be unavailable")
endif()
