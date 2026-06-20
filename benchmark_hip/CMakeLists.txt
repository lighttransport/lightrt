# benchmark_hip/CMakeLists.txt — HIP GPU ray-tracing benchmark.
# Built only when LIGHTRT_BUILD_BENCHMARK_HIP=ON (which requires LIGHTRT_BUILD_HIP).

add_executable(bench_hip
    bench_hip_main.c
    ../benchmark_c/rays.c
    ../benchmark_c/scene_mandelbulb.c
    ../benchmark_c/scene_thinspan.c
    ../lightrt_c.c
    ../lightrt_c_tri.c
)

# These are all C sources (the HIP device code lives in the lightrt_hip lib).
set_source_files_properties(
    bench_hip_main.c
    ../benchmark_c/rays.c
    ../benchmark_c/scene_mandelbulb.c
    ../benchmark_c/scene_thinspan.c
    ../lightrt_c.c
    ../lightrt_c_tri.c
    PROPERTIES LANGUAGE C)

target_include_directories(bench_hip PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/..)

# GNU statement-expressions are used in the timing macro.
set_source_files_properties(bench_hip_main.c PROPERTIES
    COMPILE_OPTIONS "$<$<C_COMPILER_ID:GNU>:-std=gnu11>;$<$<C_COMPILER_ID:Clang>:-std=gnu11>")

if(LIGHTRT_C_TRI_SIMD_FLAGS)
    set_source_files_properties(../lightrt_c_tri.c PROPERTIES
        COMPILE_OPTIONS "${LIGHTRT_C_TRI_SIMD_FLAGS}")
endif()

target_link_libraries(bench_hip lightrt_hip)
find_package(Threads QUIET)
if(Threads_FOUND)
    target_link_libraries(bench_hip Threads::Threads)
endif()
if(NOT MSVC)
    target_link_libraries(bench_hip m)
endif()
