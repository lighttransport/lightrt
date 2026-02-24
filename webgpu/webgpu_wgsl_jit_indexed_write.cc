#include <cmath>
#include <cstdio>
#include <vector>

#include "webgpu_lightrt.hh"

int main() {
  using namespace softrt;

  constexpr uint32_t kElems = 16;
  constexpr uint32_t kWorkgroupSize = 16;
  constexpr uint32_t kNumWorkgroups = kElems / kWorkgroupSize;

  GPUAdapter* adapter = GPU::requestAdapter();
  GPUDevice* device = adapter->requestDevice();

  const char* shader_source = R"(
@group(0) @binding(0)
var<storage, read_write> out_buf : array<u32>;

@compute @workgroup_size(16, 1, 1)
fn main(@builtin(local_invocation_index) idx : u32) {
  out_buf[idx] = idx + 1u;
}
)";

  GPUShaderModule* shader = device->createShaderModule(shader_source);
  if (!shader->compileComputeShader("main")) {
    std::printf("WGSL compile failed: %s\n", shader->lastError().c_str());
    return 1;
  }

  GPUBuffer* out = device->createBuffer(kElems * sizeof(uint32_t), GPUBufferUsage_STORAGE);
  std::vector<uint32_t> init(kElems, 0xFFFFFFFFu);
  device->getQueue()->writeBuffer(out, 0, init.data(), init.size() * sizeof(uint32_t));

  std::vector<GPUBufferBindingInfo> bindings;
  bindings.push_back({out, false});

  if (!shader->dispatchCompute({kNumWorkgroups, 1, 1}, bindings)) {
    std::printf("WGSL dispatch failed: %s\n", shader->lastError().c_str());
    return 2;
  }

  const uint32_t* vals = reinterpret_cast<const uint32_t*>(out->data());
  for (uint32_t i = 0; i < kElems; ++i) {
    uint32_t expected = i + 1u;
    if (vals[i] != expected) {
      std::printf("Output snapshot:");
      for (uint32_t j = 0; j < kElems; ++j) {
        std::printf(" %u", vals[j]);
      }
      std::printf("\n");
      std::printf("Mismatch at %u: got %u expected %u\n", i, vals[i], expected);
      return 3;
    }
  }

  std::printf("WGSL indexed write test passed (%u elements)\n", kElems);
  return 0;
}
