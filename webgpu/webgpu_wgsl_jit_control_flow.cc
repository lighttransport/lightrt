#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "webgpu_lightrt.hh"

int main() {
  using namespace softrt;

  constexpr uint32_t kElems = 64;
  constexpr uint32_t kWorkgroupSize = 64;
  constexpr uint32_t kNumWorkgroups = kElems / kWorkgroupSize;

  GPUAdapter* adapter = GPU::requestAdapter();
  GPUDevice* device = adapter->requestDevice();

  const char* shader_source = R"(
@group(0) @binding(0)
var<storage, read> in_a : array<u32>;

@group(0) @binding(1)
var<storage, read> in_b : array<u32>;

@group(0) @binding(2)
var<storage, read_write> out_u : array<u32>;

@compute @workgroup_size(64, 1, 1)
fn main(@builtin(local_invocation_index) idx : u32) {
  let a = in_a[idx];
  let b = in_b[idx];
  var acc : u32 = a + b;

  if ((idx & 1u) == 0u) {
    acc = acc * 3u + (a >> 1u);
  } else {
    acc = acc + 17u;
  }

  out_u[idx] = acc;
}
)";

  GPUShaderModule* shader = device->createShaderModule(shader_source);
  if (!shader->compileComputeShader("main")) {
    std::printf("WGSL compile failed: %s\n", shader->lastError().c_str());
    return 1;
  }

  GPUBuffer* in_a = device->createBuffer(kElems * sizeof(uint32_t), GPUBufferUsage_STORAGE);
  GPUBuffer* in_b = device->createBuffer(kElems * sizeof(uint32_t), GPUBufferUsage_STORAGE);
  GPUBuffer* out_u = device->createBuffer(kElems * sizeof(uint32_t), GPUBufferUsage_STORAGE);

  std::vector<uint32_t> a(kElems);
  std::vector<uint32_t> b(kElems);
  std::vector<uint32_t> out_u_init(kElems, 0xFFFFFFFFu);

  for (uint32_t i = 0; i < kElems; ++i) {
    a[i] = 10u + i * 3u;
    b[i] = 100u + i * 5u;
  }

  GPUQueue* queue = device->getQueue();
  queue->writeBuffer(in_a, 0, a.data(), a.size() * sizeof(uint32_t));
  queue->writeBuffer(in_b, 0, b.data(), b.size() * sizeof(uint32_t));
  queue->writeBuffer(out_u, 0, out_u_init.data(), out_u_init.size() * sizeof(uint32_t));

  std::vector<GPUBufferBindingInfo> bindings;
  bindings.push_back({in_a, true});
  bindings.push_back({in_b, true});
  bindings.push_back({out_u, false});

  if (!shader->dispatchCompute({kNumWorkgroups, 1, 1}, bindings)) {
    std::printf("WGSL dispatch failed: %s\n", shader->lastError().c_str());
    return 2;
  }

  const uint32_t* out_u_vals = reinterpret_cast<const uint32_t*>(out_u->data());

  for (uint32_t idx = 0; idx < kElems; ++idx) {
    const uint32_t ai = a[idx];
    const uint32_t bi = b[idx];
    uint32_t acc = ai + bi;

    if ((idx & 1u) == 0u) {
      acc = acc * 3u + (ai >> 1u);
    } else {
      acc = acc + 17u;
    }

    if (out_u_vals[idx] != acc) {
      std::printf("control_flow mismatch at %u: got %u expected %u\n",
                  idx, out_u_vals[idx], acc);
      return 3;
    }
  }

  std::printf("WGSL control-flow test passed (%u elements)\n", kElems);
  return 0;
}
