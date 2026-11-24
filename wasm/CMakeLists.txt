cmake_minimum_required(VERSION 3.13)
project(lightrt-wasm)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++17 -fno-exceptions -DNO_AVX=1 -DNO_AVX2=1 -DNO_SVE=1 -DNO_F16C=1")

include_directories(${CMAKE_SOURCE_DIR}/..)

set(CMAKE_EXECUTABLE_OUTPUT_PATH ${CMAKE_BINARY_DIR})

add_executable(lightrt-wasm bindings.cc ../lightrt.cc)

set_target_properties(lightrt-wasm PROPERTIES OUTPUT_NAME "lightrt")
target_link_options(lightrt-wasm PRIVATE
    --bind
    -sALLOW_MEMORY_GROWTH=1
    -sEXPORT_ES6=1
    -sMODULARIZE=1
    -sEXPORT_NAME=loadLightRT
    -sASSERTIONS=0
    -Oz
    -sFILESYSTEM=0
    -sMALLOC=emmalloc
    -sDISABLE_EXCEPTION_CATCHING=1
    -sEXPORTED_RUNTIME_METHODS=[]
    --emit-tsd "${CMAKE_BINARY_DIR}/lightrt.d.ts"
)
