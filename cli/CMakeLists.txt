cmake_minimum_required(VERSION 3.16)
project(lightrt_cli LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

if(MSVC)
  set(CMAKE_CXX_FLAGS_RELEASE "/O2 /DNDEBUG")
  set(CMAKE_CXX_FLAGS_DEBUG "/Od /Zi /DDEBUG")
  add_compile_definitions(WIN32_LEAN_AND_MEAN NOMINMAX _CRT_SECURE_NO_WARNINGS)
  if(CMAKE_SYSTEM_PROCESSOR MATCHES "(AMD64|amd64|x86_64)")
    add_compile_options(/arch:AVX2)
  endif()
else()
  set(CMAKE_CXX_FLAGS_RELEASE "-O2 -DNDEBUG")
  set(CMAKE_CXX_FLAGS_DEBUG "-O0 -g -DDEBUG")
  # SIMD flags
  include(CheckCXXCompilerFlag)
  if(CMAKE_SYSTEM_PROCESSOR MATCHES "(x86_64)|(AMD64|amd64)|(^i.86$)")
    check_cxx_compiler_flag("-mavx2" HAS_AVX2)
    if(HAS_AVX2)
      add_compile_options(-mavx2 -mfma -mf16c)
    endif()
  endif()
endif()

# USD backend selection
# OFF (default): tinyusdz + tydra
# ON:            lightusd-c + lydra  (sandbox/lightusd-c inside the tinyusdz repo)
option(LIGHTRT_USE_LIGHTUSD_C
  "Use lightusd-c + lydra USD backend instead of tinyusdz + tydra" OFF)

set(TINYUSDZ_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../deps/tinyusdz")
if(NOT EXISTS "${TINYUSDZ_DIR}/CMakeLists.txt")
  message(FATAL_ERROR "TinyUSDZ not found at ${TINYUSDZ_DIR}. Run: bash scripts/setup_deps.sh")
endif()

# LightRT sources
set(LIGHTRT_DIR "${CMAKE_CURRENT_SOURCE_DIR}/..")

# CLI executable
add_executable(lightrt_cli main.cc stb_image_write_impl.cc stb_image_impl.cc "${LIGHTRT_DIR}/lightrt.cc")

target_include_directories(lightrt_cli PRIVATE
  "${LIGHTRT_DIR}"
  "${LIGHTRT_DIR}/common"
  # stb_image_write.h is a standalone header used by both backends
  "${TINYUSDZ_DIR}/src/external"
)

if(LIGHTRT_USE_LIGHTUSD_C)
  # lightusd-c + lydra backend (no tinyusdz dependency)
  set(LIGHTUSD_C_DIR "${TINYUSDZ_DIR}/sandbox/lightusd-c")
  if(NOT EXISTS "${LIGHTUSD_C_DIR}")
    message(FATAL_ERROR
      "lightusd-c not found at ${LIGHTUSD_C_DIR}.\n"
      "Make sure tinyusdz is on the 'lightusd' branch: bash scripts/setup_deps.sh")
  endif()

  # Build lightusd-c (C11) + lydra (C++) as a subdirectory.
  # Force pure-C backend: do not link tinyusdz_static when using lightusd-c.
  set(LUSD_TINYUSDZ_DIR OFF CACHE BOOL "" FORCE)
  # No tinyusdz dependency; use native reader stubs only.
  if(EXISTS "${LIGHTUSD_C_DIR}/CMakeLists.txt")
    add_subdirectory("${LIGHTUSD_C_DIR}" "${CMAKE_CURRENT_BINARY_DIR}/lightusd-c")
  else()
    message(FATAL_ERROR "lightusd-c has no CMakeLists.txt at ${LIGHTUSD_C_DIR}")
  endif()

  # Include: C public headers, internal headers (for LusdLayer_T/LusdPrim_T),
  # lydra-c pure-C headers, and lydra C++ headers (kept for reference)
  target_include_directories(lightrt_cli PRIVATE
    "${LIGHTUSD_C_DIR}/include"
    "${LIGHTUSD_C_DIR}/src"
    "${LIGHTUSD_C_DIR}/lydra/lydra-c"
    "${LIGHTUSD_C_DIR}/lydra"
  )
  # Link lightusd-c and lydra-c (pure C) — no C++ lydra needed
  target_link_libraries(lightrt_cli PRIVATE lightusd-c lydra-c)
  target_compile_definitions(lightrt_cli PRIVATE LIGHTRT_USE_LIGHTUSD_C)
  message(STATUS "USD backend: lightusd-c + lydra-c (${LIGHTUSD_C_DIR})")
else()
  # tinyusdz + tydra backend (default)
  # Build tinyusdz with MinSizeRel to reduce library size.
  set(_saved_build_type "${CMAKE_BUILD_TYPE}")
  set(CMAKE_BUILD_TYPE MinSizeRel)

  set(TINYUSDZ_NO_WERROR ON CACHE BOOL "" FORCE)
  add_subdirectory("${TINYUSDZ_DIR}" "${CMAKE_CURRENT_BINARY_DIR}/tinyusdz")

  # Restore original build type for lightrt_cli itself.
  set(CMAKE_BUILD_TYPE "${_saved_build_type}")

  target_include_directories(lightrt_cli PRIVATE
    "${TINYUSDZ_DIR}/src"
    "${TINYUSDZ_DIR}/src/external"
  )
  target_link_libraries(lightrt_cli PRIVATE tinyusdz_static)
  message(STATUS "USD backend: tinyusdz + tydra (${TINYUSDZ_DIR})")
endif()
