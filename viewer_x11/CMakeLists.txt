cmake_minimum_required(VERSION 3.15)
project(viewer_x11 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Sources
set(SOURCES
    viewer_x11.cc
    ../viewer/common/viewer_common.cc
    ../lightrt.cc
)

add_executable(viewer_x11 ${SOURCES})

target_include_directories(viewer_x11 PRIVATE
    ..
    ../viewer
    ../viewer/third_party
    ../viewer/common
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
