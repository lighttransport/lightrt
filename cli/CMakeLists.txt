cmake_minimum_required(VERSION 3.16)
project(lightrt_cli LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

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

# TinyUSDZ
set(TINYUSDZ_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../deps/tinyusdz")
if(NOT EXISTS "${TINYUSDZ_DIR}/CMakeLists.txt")
  message(FATAL_ERROR "TinyUSDZ not found at ${TINYUSDZ_DIR}. Run: bash scripts/setup_deps.sh")
endif()
set(TINYUSDZ_NO_WERROR ON CACHE BOOL "" FORCE)
add_subdirectory("${TINYUSDZ_DIR}" "${CMAKE_CURRENT_BINARY_DIR}/tinyusdz")

# LightRT sources
set(LIGHTRT_DIR "${CMAKE_CURRENT_SOURCE_DIR}/..")

# CLI executable
add_executable(lightrt_cli main.cc stb_image_write_impl.cc "${LIGHTRT_DIR}/lightrt.cc")

target_include_directories(lightrt_cli PRIVATE
  "${LIGHTRT_DIR}"
  "${LIGHTRT_DIR}/common"
  "${TINYUSDZ_DIR}/src"
  "${TINYUSDZ_DIR}/src/external"
)

target_link_libraries(lightrt_cli PRIVATE tinyusdz_static)
