cmake_minimum_required(VERSION 3.10)
project(lightrt-wasm)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++17 -fno-exceptions -DNO_AVX=1 -DNO_AVX2=1 -DNO_SVE=1 -DNO_F16C=1")

include_directories(${CMAKE_SOURCE_DIR}/..)

set(CMAKE_EXECUTABLE_OUTPUT_PATH ${CMAKE_BINARY_DIR})

add_executable(lightrt-wasm bindings.cc ../lightrt.cc)

set_target_properties(lightrt-wasm PROPERTIES
    OUTPUT_NAME "lightrt-wasm"
    LINK_FLAGS
        "--bind
         -s ALLOW_MEMORY_GROWTH=1
         -s EXPORT_ES6=1
         -s MODULARIZE=1
         -s EXPORT_NAME=loadLightRT
         -s ASSERTIONS=0
         -Oz
         -s FILESYSTEM=0
         -s MALLOC=emmalloc
         -s DISABLE_EXCEPTION_CATCHING=1
         -s EXPORTED_RUNTIME_METHODS=[]
         --emit-tsd ${CMAKE_BINARY_DIR}/lightrt.d.ts"
)
