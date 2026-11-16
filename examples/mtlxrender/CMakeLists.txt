# CMakeLists.txt for mtlxrender - C11 MaterialX path tracer.
# Standalone: `cmake -S . -B build && cmake --build build -j`.
cmake_minimum_required(VERSION 3.13)
project(mtlxrender LANGUAGES C)

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

set(LIGHTRT_ROOT ${CMAKE_CURRENT_SOURCE_DIR}/../..)
set(DEPS ${CMAKE_CURRENT_SOURCE_DIR}/deps)
set(TINYEXR ${DEPS}/tinyexr)

file(GLOB TINYEXR_SRC ${TINYEXR}/src/*.c)

# First-party sources (full warnings).
set(APP_SRC
    main.c pathtrace.c bsdf.c env.c framebuffer.c color.c
    gltf_load.c mesh_build.c obj_load.c mtlx_xml.c mtlx_doc.c mtlx_eval.c
    material_bind.c texture.c)
# Third-party sources (compiled quietly).
set(TP_SRC
    third_party_impl.c
    ${LIGHTRT_ROOT}/lightrt_c_tri.c
    ${DEPS}/tiny_gltf_v3.c
    ${TINYEXR_SRC})

# Keep the standalone CMake product in sync with the verified backend used by
# the Makefile and the LightUSD integration. These schedules require strict FP.
set(VERIFIED_SRC verified_float.c verified_math.c verified_eval.c
    verified_bounds.c verified_ranges.c verified_fixed.c verified_normal.c verified_direction.c verified_single_power.c verified_local_geometry.c verified_vndf.c passive_film.c)
add_executable(mtlxrender ${APP_SRC} ${TP_SRC} ${VERIFIED_SRC})
if(MSVC)
    set_source_files_properties(${VERIFIED_SRC} PROPERTIES COMPILE_OPTIONS "/fp:strict")
else()
    set_source_files_properties(${VERIFIED_SRC} PROPERTIES
        COMPILE_OPTIONS "-fno-fast-math;-frounding-math;-ffp-contract=off")
endif()
target_include_directories(mtlxrender PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR} ${LIGHTRT_ROOT} ${DEPS} ${TINYEXR}/include)
target_compile_definitions(mtlxrender PRIVATE
    _POSIX_C_SOURCE=200809L TINYGLTF3_ENABLE_FS EXR_NO_ZSTD EXR_USE_THREADS)

# SIMD for the C triangle BVH (optional; scalar fallback otherwise).
include(CheckCCompilerFlag)
if(CMAKE_SYSTEM_PROCESSOR MATCHES "(x86_64|amd64|AMD64)")
    check_c_compiler_flag(-msse4.1 HAS_SSE41)
    check_c_compiler_flag(-mavx2 HAS_AVX2)
    if(HAS_SSE41)
        target_compile_options(mtlxrender PRIVATE -msse4.1)
    endif()
    if(HAS_AVX2)
        target_compile_options(mtlxrender PRIVATE -mavx2 -mfma)
    endif()
endif()

# Quiet warnings for vendored third-party translation units.
set_source_files_properties(${TP_SRC} PROPERTIES COMPILE_OPTIONS "-w")
set_source_files_properties(${APP_SRC} PROPERTIES COMPILE_OPTIONS "-Wall;-Wextra")

set(APP_VK_SRC raytracer.c pathtrace_wf.c raytracer_vk.c)
target_sources(mtlxrender PRIVATE ${APP_VK_SRC})
set_source_files_properties(${APP_VK_SRC} PROPERTIES COMPILE_OPTIONS "-Wall;-Wextra")

# MTLXRENDER_VK: build mtlxrender's Vulkan GPU-traced backend (--backend vk /
# --gpu-validate). Runtime dlopen of libvulkan; no Vulkan SDK / find_package.
option(MTLXRENDER_VK "Build mtlxrender with the Vulkan GPU-traced backend" OFF)
if(MTLXRENDER_VK)
    target_sources(mtlxrender PRIVATE
        ${LIGHTRT_ROOT}/lightrt_vkew.c ${LIGHTRT_ROOT}/lightrt_c_vk.c)
    set_source_files_properties(
        ${LIGHTRT_ROOT}/lightrt_vkew.c ${LIGHTRT_ROOT}/lightrt_c_vk.c
        PROPERTIES COMPILE_OPTIONS "-w")
    target_compile_definitions(mtlxrender PRIVATE MTLX_HAVE_VK)
    target_link_libraries(mtlxrender PRIVATE ${CMAKE_DL_LIBS})
endif()

find_package(Threads REQUIRED)
target_link_libraries(mtlxrender PRIVATE Threads::Threads m)

# MaterialX -> GPU shading bridge (Vulkan compute). Opt-in; runtime dlopen of
# libvulkan via lightrt_vkew (no Vulkan SDK / find_package(Vulkan) needed).
option(MTLXVK "Build the MaterialX->GPU (Vulkan) shading bridge" ON)
if(MTLXVK)
    add_executable(mtlxvk
        mtlxvk.c mtlx_doc.c mtlx_xml.c mtlx_eval.c texture.c color.c
        third_party_impl.c
        ${LIGHTRT_ROOT}/lightrt_c_tri.c
        ${LIGHTRT_ROOT}/lightrt_vkew.c
        ${LIGHTRT_ROOT}/lightrt_c_vk.c)
    target_include_directories(mtlxvk PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR} ${LIGHTRT_ROOT} ${DEPS})
    target_compile_definitions(mtlxvk PRIVATE _POSIX_C_SOURCE=200809L)
    set_source_files_properties(
        third_party_impl.c ${LIGHTRT_ROOT}/lightrt_c_tri.c
        ${LIGHTRT_ROOT}/lightrt_vkew.c ${LIGHTRT_ROOT}/lightrt_c_vk.c
        PROPERTIES COMPILE_OPTIONS "-w")
    if(HAS_SSE41)
        set_source_files_properties(${LIGHTRT_ROOT}/lightrt_c_tri.c
            PROPERTIES COMPILE_OPTIONS "-w;-msse4.1")
    endif()
    target_link_libraries(mtlxvk PRIVATE m ${CMAKE_DL_LIBS})
endif()

# Per-node numeric ground-truth tests.
enable_testing()
add_executable(node_truth
    tests/node_truth.c mtlx_doc.c mtlx_xml.c mtlx_eval.c texture.c color.c third_party_impl.c)
target_include_directories(node_truth PRIVATE ${CMAKE_CURRENT_SOURCE_DIR} ${LIGHTRT_ROOT} ${DEPS})
target_compile_definitions(node_truth PRIVATE _POSIX_C_SOURCE=200809L)
set_source_files_properties(third_party_impl.c PROPERTIES COMPILE_OPTIONS "-w")
target_link_libraries(node_truth PRIVATE m)
add_test(NAME node_truth COMMAND node_truth)
add_executable(volume_lobes tests/volume_lobes.c tests/texture_stub.c
    mtlx_doc.c mtlx_xml.c mtlx_eval.c color.c)
target_include_directories(volume_lobes PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(volume_lobes PRIVATE _POSIX_C_SOURCE=200809L)
target_link_libraries(volume_lobes PRIVATE m)
add_test(NAME volume_lobes COMMAND volume_lobes)

add_executable(pixel_filter tests/pixel_filter.c)
target_include_directories(pixel_filter PRIVATE ${CMAKE_CURRENT_SOURCE_DIR} ${LIGHTRT_ROOT} ${DEPS} ${TINYEXR}/include)
target_link_libraries(pixel_filter PRIVATE m)
add_test(NAME pixel_filter COMMAND pixel_filter)

add_executable(eon_response tests/eon_response.c bsdf.c)
target_include_directories(eon_response PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(eon_response PRIVATE m)
add_test(NAME eon_response COMMAND eon_response)

add_executable(rough_diffuse tests/rough_diffuse.c bsdf.c)
target_include_directories(rough_diffuse PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(rough_diffuse PRIVATE m)
add_test(NAME rough_diffuse COMMAND rough_diffuse)

add_executable(diffuse_mixture tests/diffuse_mixture.c tests/texture_stub.c mtlx_doc.c mtlx_xml.c mtlx_eval.c color.c bsdf.c)
target_include_directories(diffuse_mixture PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(diffuse_mixture PRIVATE _POSIX_C_SOURCE=200809L)
target_link_libraries(diffuse_mixture PRIVATE m)
add_test(NAME diffuse_mixture COMMAND diffuse_mixture)

add_executable(sheen_mixture tests/sheen_mixture.c tests/texture_stub.c mtlx_doc.c mtlx_xml.c mtlx_eval.c color.c bsdf.c)
target_include_directories(sheen_mixture PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(sheen_mixture PRIVATE _POSIX_C_SOURCE=200809L)
target_link_libraries(sheen_mixture PRIVATE m)
add_test(NAME sheen_mixture COMMAND sheen_mixture)

# End-to-end coverage of view-dependent shading in both CPU integrators.
find_package(Python3 COMPONENTS Interpreter QUIET)
if(Python3_Interpreter_FOUND)
    add_test(NAME conductor_anisotropic_render
        COMMAND ${CMAKE_COMMAND} -E env MTLXRENDER_BINARY=$<TARGET_FILE:mtlxrender>
                ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/tests/conductor_anisotropic_render.py)
    add_test(NAME viewdirection_render
        COMMAND ${CMAKE_COMMAND} -E env MTLXRENDER_BINARY=$<TARGET_FILE:mtlxrender>
                ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/tests/viewdirection_render.py)
endif()

add_executable(conductor_response tests/conductor_response.c bsdf.c)
target_include_directories(conductor_response PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(conductor_response PRIVATE m)
add_test(NAME conductor_response COMMAND conductor_response)

add_executable(conductor_mixture tests/conductor_mixture.c tests/texture_stub.c mtlx_doc.c mtlx_xml.c mtlx_eval.c color.c bsdf.c)
target_include_directories(conductor_mixture PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(conductor_mixture PRIVATE _POSIX_C_SOURCE=200809L)
target_link_libraries(conductor_mixture PRIVATE m)
add_test(NAME conductor_mixture COMMAND conductor_mixture)

add_executable(cert_energy tests/cert_energy.c bsdf.c)
target_include_directories(cert_energy PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(cert_energy PRIVATE _POSIX_C_SOURCE=200809L)
target_link_libraries(cert_energy PRIVATE m)
add_test(NAME cert_energy COMMAND cert_energy)

add_executable(film_energy tests/film_energy.c bsdf.c)
target_include_directories(film_energy PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(film_energy PRIVATE _POSIX_C_SOURCE=200809L)
target_link_libraries(film_energy PRIVATE m)
add_test(NAME film_energy COMMAND film_energy)

add_executable(interior_energy tests/interior_energy.c bsdf.c)
target_include_directories(interior_energy PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(interior_energy PRIVATE _POSIX_C_SOURCE=200809L)
target_link_libraries(interior_energy PRIVATE m)
add_test(NAME interior_energy COMMAND interior_energy)

add_executable(conservative_sweep tests/conservative_sweep.c bsdf.c)
target_include_directories(conservative_sweep PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(conservative_sweep PRIVATE _POSIX_C_SOURCE=200809L)
target_link_libraries(conservative_sweep PRIVATE m)
add_test(NAME conservative_sweep COMMAND conservative_sweep)
set_tests_properties(conservative_sweep PROPERTIES TIMEOUT 600)

add_executable(f32_lobe_error tests/f32_lobe_error.c bsdf.c)
target_include_directories(f32_lobe_error PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(f32_lobe_error PRIVATE _POSIX_C_SOURCE=200809L)
target_link_libraries(f32_lobe_error PRIVATE m)
add_test(NAME f32_lobe_error COMMAND f32_lobe_error)

# Special values (NaN, infinities, signed zero, flags) of the verified binary32 ops
# versus verif/lean/MtlxSpec/Binary32Special.lean.
add_executable(vf_special tests/vf_special.c verified_float.c)
target_include_directories(vf_special PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
if(NOT MSVC)
    set_source_files_properties(tests/vf_special.c PROPERTIES
        COMPILE_OPTIONS "-fno-fast-math;-frounding-math;-ffp-contract=off")
endif()
target_link_libraries(vf_special PRIVATE m)
add_test(NAME vf_special COMMAND vf_special)
set_tests_properties(vf_special PROPERTIES SKIP_RETURN_CODE 77)
