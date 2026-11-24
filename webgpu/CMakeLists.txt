cmake_minimum_required(VERSION 3.16)

project(lightrt_webgpu LANGUAGES CXX)

# Clair is an optional WGSL compute backend.  The software raster path below
# does not require it, so keep ordinary WebGPU builds self-contained and make
# the external dependency an explicit opt-in.
option(SOFTRT_WEBGPU_ENABLE_CLAIR "Enable Clair WGSL JIT integration" OFF)
option(SOFTRT_WEBGPU_CLAIR_SAFE_OPT "Force conservative optimization for libclair" ON)
set(SOFTRT_CLAIR_SOURCE_DIR "/home/syoyo/work/clair/main"
    CACHE PATH "Path to Clair source tree")

find_package(Threads REQUIRED)

set(SOFTRT_WEBGPU_HAVE_CLAIR OFF)
if (SOFTRT_WEBGPU_ENABLE_CLAIR)
  if (EXISTS "${SOFTRT_CLAIR_SOURCE_DIR}/CMakeLists.txt")
    message(STATUS "WebGPU: enabling Clair from ${SOFTRT_CLAIR_SOURCE_DIR}")

    set(LIBCLAIR_BUILD_TESTS OFF CACHE BOOL "" FORCE)
    set(LIBCLAIR_BUILD_EXAMPLES OFF CACHE BOOL "" FORCE)
    set(LIBCLAIR_BUILD_WAMR OFF CACHE BOOL "" FORCE)
    set(LIBCLAIR_ENABLE_LTO OFF CACHE BOOL "" FORCE)
    set(LIBCLAIR_BUILD_MCP OFF CACHE BOOL "" FORCE)
    set(LIBCLAIR_BUILD_JS_BINDINGS OFF CACHE BOOL "" FORCE)
    set(LIBCLAIR_BUILD_A64FX_SIM OFF CACHE BOOL "" FORCE)
    set(LIBCLAIR_BUILD_PTX_SIM OFF CACHE BOOL "" FORCE)
    set(LIBCLAIR_BUILD_RDNA4_SIM OFF CACHE BOOL "" FORCE)
    set(LIBCLAIR_BUILD_QLAIR OFF CACHE BOOL "" FORCE)
    set(LIBCLAIR_BUILD_JIT ON CACHE BOOL "" FORCE)
    set(LIBCLAIR_JIT_STANDALONE OFF CACHE BOOL "" FORCE)

    add_subdirectory("${SOFTRT_CLAIR_SOURCE_DIR}"
                     "${CMAKE_BINARY_DIR}/clair-build"
                     EXCLUDE_FROM_ALL)

    if (SOFTRT_WEBGPU_CLAIR_SAFE_OPT AND TARGET libclair)
      target_compile_options(libclair PRIVATE -O0)
    endif ()
    set(SOFTRT_WEBGPU_HAVE_CLAIR ON)
  else ()
    message(WARNING
            "WebGPU: Clair source not found at '${SOFTRT_CLAIR_SOURCE_DIR}'. "
            "WGSL JIT will be disabled.")
  endif ()
endif ()

add_library(softrt_webgpu STATIC
  webgpu_lightrt.cc
  webgpu_lightrt.hh
  wgsl_clair_adapter.cc
  wgsl_clair_adapter.hh
)

target_compile_features(softrt_webgpu PUBLIC cxx_std_17)
target_include_directories(softrt_webgpu
  PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)
target_link_libraries(softrt_webgpu
  PUBLIC
    lightrt
    Threads::Threads
)

if (SOFTRT_WEBGPU_HAVE_CLAIR)
  target_compile_definitions(softrt_webgpu PUBLIC SOFTRT_ENABLE_CLAIR=1)
  target_include_directories(softrt_webgpu PUBLIC
    "${SOFTRT_CLAIR_SOURCE_DIR}/src")
  target_link_libraries(softrt_webgpu PUBLIC libclair)
endif ()

add_executable(webgpu_example webgpu_example.cc)
target_link_libraries(webgpu_example PRIVATE softrt_webgpu)

add_executable(webgpu_headless_triangle_dump webgpu_headless_triangle_dump.cc)
target_link_libraries(webgpu_headless_triangle_dump PRIVATE softrt_webgpu)

if (SOFTRT_WEBGPU_HAVE_CLAIR)
  add_executable(webgpu_wgsl_jit_minimal webgpu_wgsl_jit_minimal.cc)
  target_link_libraries(webgpu_wgsl_jit_minimal PRIVATE softrt_webgpu)

  add_executable(webgpu_wgsl_jit_storage_minimal webgpu_wgsl_jit_storage_minimal.cc)
  target_link_libraries(webgpu_wgsl_jit_storage_minimal PRIVATE softrt_webgpu)

  add_executable(webgpu_wgsl_jit_complex webgpu_wgsl_jit_complex.cc)
  target_link_libraries(webgpu_wgsl_jit_complex PRIVATE softrt_webgpu)

  add_executable(webgpu_wgsl_jit_indexed_write webgpu_wgsl_jit_indexed_write.cc)
  target_link_libraries(webgpu_wgsl_jit_indexed_write PRIVATE softrt_webgpu)

  add_executable(webgpu_wgsl_jit_heavy_expr webgpu_wgsl_jit_heavy_expr.cc)
  target_link_libraries(webgpu_wgsl_jit_heavy_expr PRIVATE softrt_webgpu)

  add_executable(webgpu_wgsl_jit_control_flow webgpu_wgsl_jit_control_flow.cc)
  target_link_libraries(webgpu_wgsl_jit_control_flow PRIVATE softrt_webgpu)

  add_executable(webgpu_wgsl_compile_file webgpu_wgsl_compile_file.cc)
  target_link_libraries(webgpu_wgsl_compile_file PRIVATE softrt_webgpu)
endif ()

# This test exercises the self-contained software raster path.  It remains
# available when Clair is disabled, and writes only inside the build tree.
if (BUILD_TESTING)
  add_test(NAME webgpu_non_clair_raster
           COMMAND $<TARGET_FILE:webgpu_headless_triangle_dump>
                   --width 64 --height 64
                   --out-rgba ${CMAKE_CURRENT_BINARY_DIR}/non_clair.rgba
                   --out-bmp ${CMAKE_CURRENT_BINARY_DIR}/non_clair.bmp)
  set_tests_properties(webgpu_non_clair_raster PROPERTIES LABELS "WebGPUNonClair")
endif ()

if (BUILD_TESTING AND SOFTRT_WEBGPU_HAVE_CLAIR)
  set(SOFTRT_WGSL_JIT_TEST_TARGETS
      webgpu_wgsl_jit_minimal
      webgpu_wgsl_jit_storage_minimal
      webgpu_wgsl_jit_indexed_write
      webgpu_wgsl_jit_complex
      webgpu_wgsl_jit_heavy_expr
      webgpu_wgsl_jit_control_flow)

  foreach(_mode IN ITEMS SPIRV CPU_JIT)
    foreach(_opt IN ITEMS 0 2)
      foreach(_target IN LISTS SOFTRT_WGSL_JIT_TEST_TARGETS)
        set(_test_name "${_target}_${_mode}_O${_opt}")
        add_test(NAME "${_test_name}" COMMAND $<TARGET_FILE:${_target}>)
        set_tests_properties("${_test_name}" PROPERTIES
          LABELS "WebGPUWGSL;${_mode};opt${_opt}"
          ENVIRONMENT
            "SOFTRT_CLAIR_EXECUTION_MODE=${_mode};SOFTRT_CLAIR_OPT_LEVEL=${_opt}")
      endforeach ()
    endforeach ()
  endforeach ()
endif ()
