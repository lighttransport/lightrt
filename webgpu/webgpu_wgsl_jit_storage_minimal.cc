#include <cstdio>

#include "webgpu_lightrt.hh"

int main() {
  using namespace softrt;

  GPUAdapter* adapter = GPU::requestAdapter();
  GPUDevice* device = adapter->requestDevice();

  const char* shader_source = R"(
@group(0) @binding(0)
var<storage, read_write> out_buf : array<f32>;

@compute @workgroup_size(1)
fn main() {
  out_buf[0] = 42.0;
}
)";

  GPUShaderModule* shader = device->createShaderModule(shader_source);
  if (!shader->compileComputeShader("main")) {
    std::printf("WGSL compile failed: %s\n", shader->lastError().c_str());
    return 1;
  }

  GPUBuffer* out = device->createBuffer(4 * sizeof(float), GPUBufferUsage_STORAGE);
  float init[4] = {0.0f, 0.0f, 0.0f, 0.0f};
  device->getQueue()->writeBuffer(out, 0, init, sizeof(init));

  std::vector<GPUBufferBindingInfo> bindings;
  bindings.push_back({out, false});

  if (!shader->dispatchCompute({1, 1, 1}, bindings)) {
    std::printf("WGSL dispatch failed: %s\n", shader->lastError().c_str());
    return 2;
  }

  const float* out_vals = reinterpret_cast<const float*>(out->data());
  if (!(out_vals[0] > 41.9f && out_vals[0] < 42.1f)) {
    std::printf("WGSL JIT wrote unexpected value: out[0]=%.9f (expected 42.0)\n",
                out_vals[0]);
    return 3;
  }

  std::printf("WGSL storage write test passed (out[0]=%.3f)\n", out_vals[0]);
  return 0;
}
