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
var<storage, read> in_a : array<u32>;

@group(0) @binding(1)
var<storage, read> in_b : array<u32>;

@group(0) @binding(2)
var<storage, read_write> out_c : array<u32>;

@compute @workgroup_size(16, 1, 1)
fn main(@builtin(local_invocation_index) idx : u32) {
  out_c[idx] = in_a[idx] * 3u + in_b[idx] + ((idx & 1u) << 4u);
}
)";

  GPUShaderModule* shader = device->createShaderModule(shader_source);
  if (!shader->compileComputeShader("main")) {
    std::printf("WGSL compile failed: %s\n", shader->lastError().c_str());
    return 1;
  }

  GPUBuffer* in_a = device->createBuffer(kElems * sizeof(uint32_t), GPUBufferUsage_STORAGE);
  GPUBuffer* in_b = device->createBuffer(kElems * sizeof(uint32_t), GPUBufferUsage_STORAGE);
  GPUBuffer* out_c = device->createBuffer(kElems * sizeof(uint32_t), GPUBufferUsage_STORAGE);

  std::vector<uint32_t> a(kElems);
  std::vector<uint32_t> b(kElems);
  std::vector<uint32_t> out_init(kElems, 0xdeadbeefu);
  for (uint32_t i = 0; i < kElems; ++i) {
    a[i] = 10u + i;
    b[i] = 100u - i;
  }

  GPUQueue* queue = device->getQueue();
  queue->writeBuffer(in_a, 0, a.data(), a.size() * sizeof(float));
  queue->writeBuffer(in_b, 0, b.data(), b.size() * sizeof(float));
  queue->writeBuffer(out_c, 0, out_init.data(), out_init.size() * sizeof(float));

  std::vector<GPUBufferBindingInfo> bindings;
  bindings.push_back({in_a, true});
  bindings.push_back({in_b, true});
  bindings.push_back({out_c, false});

  if (!shader->dispatchCompute({kNumWorkgroups, 1, 1}, bindings)) {
    std::printf("WGSL dispatch failed: %s\n", shader->lastError().c_str());
    return 2;
  }

  const uint32_t* out_vals = reinterpret_cast<const uint32_t*>(out_c->data());
  for (uint32_t idx = 0; idx < kElems; ++idx) {
    uint32_t expected = a[idx] * 3u + b[idx] + ((idx & 1u) << 4u);
    if (out_vals[idx] != expected) {
      std::printf("Mismatch at %u: got %u expected %u\n", idx, out_vals[idx], expected);
      return 3;
    }
  }

  std::printf("WGSL complex test passed (%u elements)\n", kElems);
  return 0;
}
