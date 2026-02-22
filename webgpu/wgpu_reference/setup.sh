#!/bin/bash
# setup.sh — Clone dependencies for wgpu-native reference build
set -e
cd "$(dirname "$0")"

# WebGPU-distribution (provides wgpu-native + webgpu.h CMake target)
if [ ! -d webgpu ]; then
    echo "Cloning WebGPU-distribution..."
    git clone https://github.com/eliemichel/WebGPU-distribution.git webgpu
else
    echo "webgpu/ already exists, skipping."
fi

# GLFW (for windowed example)
if [ ! -d glfw ]; then
    echo "Cloning GLFW..."
    git clone https://github.com/glfw/glfw.git glfw
else
    echo "glfw/ already exists, skipping."
fi

# glfw3webgpu (bridge between GLFW and WebGPU surface creation)
if [ ! -d glfw3webgpu ]; then
    echo "Cloning glfw3webgpu..."
    git clone https://github.com/eliemichel/glfw3webgpu.git glfw3webgpu
else
    echo "glfw3webgpu/ already exists, skipping."
fi

echo ""
echo "Dependencies ready. Build with:"
echo "  cmake -B build && cmake --build build"
