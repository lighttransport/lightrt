cmake_minimum_required(VERSION 3.15)
project(viewer_x11 LANGUAGES CXX C)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# USD backend (optional, same flag as the CLI)
option(LIGHTRT_USE_LIGHTUSD_C
  "Use lightusd-c + lydra USD backend instead of tinyusdz + tydra" OFF)

set(TINYUSDZ_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../deps/tinyusdz")

# Sources
set(SOURCES
    viewer_x11.cc
    ../viewer/common/viewer_common.cc
    ../lightrt.cc
    ../lightrt_c.c
    ../common/renderer.cc
    ../common/usd_loader.cc
)

add_executable(viewer_x11 ${SOURCES})

target_include_directories(viewer_x11 PRIVATE
    ..
    ../viewer
    ../viewer/third_party
    ../viewer/common
    ../common
)

# Compiler flags
target_compile_options(viewer_x11 PRIVATE
    -O3 -Wall -Wextra -fno-rtti -fno-exceptions
)

# Enable AVX2 on x86
include(CheckCXXCompilerFlag)
check_cxx_compiler_flag(-mavx2 HAS_AVX2)
if(HAS_AVX2)
    target_compile_options(viewer_x11 PRIVATE -mavx2 -mfma)
endif()

# Link dl (for dlopen/dlsym) and threads — no X11 dev headers needed
find_package(Threads REQUIRED)
target_link_libraries(viewer_x11 PRIVATE
    ${CMAKE_DL_LIBS}
    Threads::Threads
)

# --- Optional USD backend ---
if(LIGHTRT_USE_LIGHTUSD_C)
  set(LIGHTUSD_C_DIR "${TINYUSDZ_DIR}/sandbox/lightusd-c")
  if(NOT EXISTS "${LIGHTUSD_C_DIR}/CMakeLists.txt")
    message(FATAL_ERROR "lightusd-c not found at ${LIGHTUSD_C_DIR}.")
  endif()
  set(LUSD_TINYUSDZ_DIR OFF CACHE BOOL "" FORCE)
  add_subdirectory("${LIGHTUSD_C_DIR}" "${CMAKE_CURRENT_BINARY_DIR}/lightusd-c")
  target_include_directories(viewer_x11 PRIVATE
    "${LIGHTUSD_C_DIR}/include"
    "${LIGHTUSD_C_DIR}/src"
    "${LIGHTUSD_C_DIR}/lydra/lydra-c"
    "${LIGHTUSD_C_DIR}/lydra"
  )
  target_link_libraries(viewer_x11 PRIVATE lightusd-c lydra-c)
  target_compile_definitions(viewer_x11 PRIVATE LIGHTRT_USE_LIGHTUSD_C)
  message(STATUS "Viewer USD backend: lightusd-c + lydra-c")
elseif(EXISTS "${TINYUSDZ_DIR}/CMakeLists.txt")
  set(TINYUSDZ_NO_WERROR ON CACHE BOOL "" FORCE)
  set(_saved_bt "${CMAKE_BUILD_TYPE}")
  set(CMAKE_BUILD_TYPE MinSizeRel)
  add_subdirectory("${TINYUSDZ_DIR}" "${CMAKE_CURRENT_BINARY_DIR}/tinyusdz")
  set(CMAKE_BUILD_TYPE "${_saved_bt}")
  target_include_directories(viewer_x11 PRIVATE
    "${TINYUSDZ_DIR}/src"
    "${TINYUSDZ_DIR}/src/external"
  )
  target_link_libraries(viewer_x11 PRIVATE tinyusdz_static)
  target_compile_definitions(viewer_x11 PRIVATE LIGHTRT_HAS_TINYUSDZ)
  message(STATUS "Viewer USD backend: tinyusdz + tydra (${TINYUSDZ_DIR})")
else()
  message(STATUS "Viewer USD backend: none (USD files will not load)")
endif()
