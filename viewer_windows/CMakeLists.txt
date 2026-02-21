cmake_minimum_required(VERSION 3.15)
project(viewer_windows LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Sources
set(SOURCES
    viewer_windows.cc
    ../viewer/common/viewer_common.cc
    ../lightrt.cc
)

add_executable(viewer_windows WIN32 ${SOURCES})

target_include_directories(viewer_windows PRIVATE
    ..
    ../viewer
    ../viewer/third_party
    ../viewer/common
)

# MSVC-specific flags
if(MSVC)
    # Replace default /EHsc and /GR with our no-RTTI/no-exceptions settings
    string(REPLACE "/GR" "/GR-" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
    string(REPLACE "/EHsc" "/EHs-c-" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
    target_compile_options(viewer_windows PRIVATE
        /W4
        /arch:AVX2    # AVX2 + FMA
    )
    target_compile_definitions(viewer_windows PRIVATE
        _CRT_SECURE_NO_WARNINGS
        _HAS_EXCEPTIONS=0
        WIN32_LEAN_AND_MEAN
        NOMINMAX
    )
else()
    # MinGW / GCC / Clang
    target_compile_options(viewer_windows PRIVATE
        -O3 -Wall -Wextra -fno-rtti -fno-exceptions -mavx2 -mfma
    )
endif()

# Link Win32 libraries
target_link_libraries(viewer_windows PRIVATE
    gdi32
    user32
    kernel32
    shell32
)

# Threads
find_package(Threads REQUIRED)
target_link_libraries(viewer_windows PRIVATE Threads::Threads)
