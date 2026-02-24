cmake_minimum_required(VERSION 3.20)
project(wgpu_reference C)

# WebGPU-distribution (provides "webgpu" target with wgpu-native)
add_subdirectory(webgpu)

# GLFW (for windowed example only)
set(GLFW_BUILD_DOCS OFF CACHE BOOL "" FORCE)
set(GLFW_BUILD_EXAMPLES OFF CACHE BOOL "" FORCE)
set(GLFW_BUILD_TESTS OFF CACHE BOOL "" FORCE)
set(GLFW_INSTALL OFF CACHE BOOL "" FORCE)
add_subdirectory(glfw)

# glfw3webgpu (GLFW <-> WebGPU surface bridge)
add_subdirectory(glfw3webgpu)

# Copy triangle.wgsl next to executables
configure_file(triangle.wgsl ${CMAKE_CURRENT_BINARY_DIR}/triangle.wgsl COPYONLY)

# --- Headless example ---
add_executable(headless_triangle headless_triangle.c)
target_link_libraries(headless_triangle PRIVATE webgpu)
target_copy_webgpu_binaries(headless_triangle)

add_executable(headless_triangle_dump headless_triangle_dump.c)
target_link_libraries(headless_triangle_dump PRIVATE webgpu)
target_copy_webgpu_binaries(headless_triangle_dump)

# --- Windowed example ---
add_executable(windowed_triangle windowed_triangle.c)
target_link_libraries(windowed_triangle PRIVATE webgpu glfw glfw3webgpu)
target_copy_webgpu_binaries(windowed_triangle)
