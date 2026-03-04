cmake_minimum_required(VERSION 3.15)

# Only set project when building standalone (not as subdirectory)
if(NOT CMAKE_PROJECT_NAME OR CMAKE_PROJECT_NAME STREQUAL "viewer_windows")
    project(viewer_windows LANGUAGES CXX)
    set(CMAKE_CXX_STANDARD 17)
    set(CMAKE_CXX_STANDARD_REQUIRED ON)
    set(CMAKE_CXX_EXTENSIONS OFF)
endif()

# TinyUSDZ (optional)
set(TINYUSDZ_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../deps/tinyusdz")
if(EXISTS "${TINYUSDZ_DIR}/CMakeLists.txt")
    set(LIGHTRT_HAS_TINYUSDZ ON)
    set(TINYUSDZ_NO_WERROR ON CACHE BOOL "" FORCE)
    add_subdirectory("${TINYUSDZ_DIR}" "${CMAKE_CURRENT_BINARY_DIR}/tinyusdz")
else()
    set(LIGHTRT_HAS_TINYUSDZ OFF)
    message(STATUS "TinyUSDZ not found at ${TINYUSDZ_DIR} - USD loading disabled")
endif()

# Sources - reuse lightrt target if available (building as subdirectory)
if(TARGET lightrt)
    set(SOURCES
        viewer_windows.cc
        ../viewer/common/viewer_common.cc
        ../common/usd_loader.cc
    )
else()
    set(SOURCES
        viewer_windows.cc
        ../viewer/common/viewer_common.cc
        ../common/usd_loader.cc
        ../lightrt.cc
    )
endif()

add_executable(viewer_windows WIN32 ${SOURCES})

target_include_directories(viewer_windows PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/..
    ${CMAKE_CURRENT_SOURCE_DIR}/../viewer
    ${CMAKE_CURRENT_SOURCE_DIR}/../viewer/third_party
    ${CMAKE_CURRENT_SOURCE_DIR}/../viewer/common
)

if(TARGET lightrt)
    target_link_libraries(viewer_windows PRIVATE lightrt)
endif()

if(LIGHTRT_HAS_TINYUSDZ)
    target_compile_definitions(viewer_windows PRIVATE LIGHTRT_HAS_TINYUSDZ)
    target_include_directories(viewer_windows PRIVATE
        "${TINYUSDZ_DIR}/src"
        "${TINYUSDZ_DIR}/src/external"
    )
    target_link_libraries(viewer_windows PRIVATE tinyusdz_static)
endif()

# MSVC-specific flags
if(MSVC)
    # Replace default /EHsc and /GR with our no-RTTI/no-exceptions settings
    # Only do this when building standalone (parent project already handles it)
    if(NOT TARGET lightrt)
        string(REPLACE "/GR" "/GR-" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
        string(REPLACE "/EHsc" "/EHs-c-" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
    endif()
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
    comdlg32
)

# Threads
find_package(Threads REQUIRED)
target_link_libraries(viewer_windows PRIVATE Threads::Threads)
