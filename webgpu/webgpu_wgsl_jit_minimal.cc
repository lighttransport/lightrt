#include <cstdio>
#include "webgpu_lightrt.hh"

int main() {
  using namespace softrt;

  GPUAdapter* adapter = GPU::requestAdapter();
  GPUDevice* device = adapter->requestDevice();

  const char* shader_source = R"(
@compute @workgroup_size(1)
fn main() {
  // minimal no-op kernel for JIT smoke test
}
)";

  GPUShaderModule* shader = device->createShaderModule(shader_source);
  if (!shader->compileComputeShader("main")) {
    std::printf("WGSL compile failed: %s\n", shader->lastError().c_str());
    return 1;
  }

  if (!shader->dispatchCompute({1, 1, 1}, {})) {
    std::printf("WGSL dispatch failed: %s\n", shader->lastError().c_str());
    return 2;
  }

  std::printf("WGSL JIT smoke test passed (compiled + dispatched no-op kernel)\n");
  return 0;
}
