// webgpu_lightrt.hh — Minimal WebGPU-compatible API with LightRT ray-tracing backend
// Software rasterizer: orthographic ray-casting through NDC cube using TriangleBVH
#pragma once

#include <cstdint>
#include <array>
#include <cstring>
#include <memory>
#include <string>
#include <vector>

namespace softrt {

// ============================================================================
// Enums
// ============================================================================

enum GPUBufferUsage : uint32_t {
  GPUBufferUsage_VERTEX = 0x0020,
  GPUBufferUsage_INDEX = 0x0010,
  GPUBufferUsage_COPY_DST = 0x0008,
  GPUBufferUsage_STORAGE = 0x0080,
};

enum class GPUTextureFormat : uint8_t {
  RGBA8Unorm,
  BGRA8Unorm,
};

enum class GPUPrimitiveTopology : uint8_t {
  TriangleList,
};

enum class GPUIndexFormat : uint8_t {
  Uint16,
  Uint32,
};

enum class GPUVertexFormat : uint8_t {
  Float32x2,
  Float32x3,
  Float32x4,
};

enum class GPULoadOp : uint8_t {
  Clear,
  Load,
};

enum class GPUStoreOp : uint8_t {
  Store,
  Discard,
};

// ============================================================================
// Forward Declarations
// ============================================================================

class GPUBuffer;
class GPUTexture;
class GPUTextureView;
class GPUShaderModule;
class GPURenderPipeline;
class GPURenderPassEncoder;
class GPUCommandEncoder;
class GPUCommandBuffer;
class GPUQueue;
class GPUDevice;
class GPUAdapter;
class GPUCanvasContext;
class Canvas;

// ============================================================================
// Descriptors
// ============================================================================

struct GPUVertexAttribute {
  GPUVertexFormat format = GPUVertexFormat::Float32x3;
  uint64_t offset = 0;
  uint32_t shaderLocation = 0;
};

struct GPUVertexBufferLayout {
  uint64_t arrayStride = 0;
  std::vector<GPUVertexAttribute> attributes;
};

struct GPURenderPipelineDescriptor {
  GPUShaderModule* vertex_module = nullptr;
  GPUShaderModule* fragment_module = nullptr;
  std::vector<GPUVertexBufferLayout> vertex_buffers;
  GPUPrimitiveTopology topology = GPUPrimitiveTopology::TriangleList;
  float constant_color[4] = {1.0f, 1.0f, 1.0f, 1.0f};
};

struct GPURenderPassColorAttachment {
  GPUTextureView* view = nullptr;
  GPULoadOp loadOp = GPULoadOp::Clear;
  GPUStoreOp storeOp = GPUStoreOp::Store;
  float clearValue[4] = {0.0f, 0.0f, 0.0f, 1.0f};
};

struct GPURenderPassDescriptor {
  GPURenderPassColorAttachment colorAttachment;
};

struct GPUBufferBindingInfo {
  GPUBuffer* buffer = nullptr;
  bool readonly = false;
};

// ============================================================================
// Resource Classes
// ============================================================================

class GPUBuffer {
 public:
  GPUBuffer(uint64_t size, uint32_t usage)
      : data_(size, 0), usage_(usage) {}

  const uint8_t* data() const { return data_.data(); }
  uint8_t* data() { return data_.data(); }
  uint64_t size() const { return data_.size(); }
  uint32_t usage() const { return usage_; }

 private:
  std::vector<uint8_t> data_;
  uint32_t usage_;
};

class GPUTexture {
 public:
  GPUTexture(uint32_t w, uint32_t h, GPUTextureFormat fmt)
      : width_(w), height_(h), format_(fmt), pixels_(w * h * 4, 0) {}

  GPUTextureView* createView();

  uint32_t width() const { return width_; }
  uint32_t height() const { return height_; }
  GPUTextureFormat format() const { return format_; }
  uint8_t* pixels() { return pixels_.data(); }
  const uint8_t* pixels() const { return pixels_.data(); }

 private:
  uint32_t width_, height_;
  GPUTextureFormat format_;
  std::vector<uint8_t> pixels_;
  std::unique_ptr<GPUTextureView> view_;
};

class GPUTextureView {
 public:
  explicit GPUTextureView(GPUTexture* tex) : texture_(tex) {}
  GPUTexture* texture() const { return texture_; }

 private:
  GPUTexture* texture_;
};

class GPUShaderModule {
 public:
  explicit GPUShaderModule(const std::string& code);
  ~GPUShaderModule();

  bool compileComputeShader(const std::string& entry_point = "main");
  bool dispatchCompute(const std::array<uint32_t, 3>& num_workgroups,
                       const std::vector<GPUBufferBindingInfo>& buffer_bindings);
  bool isComputeShaderReady() const;
  const std::string& lastError() const { return last_error_; }

 private:
  struct JITState;

  std::string code_;
  std::string last_error_;
  std::unique_ptr<JITState> jit_state_;
};

class GPURenderPipeline {
 public:
  explicit GPURenderPipeline(const GPURenderPipelineDescriptor& desc)
      : vertex_buffers_(desc.vertex_buffers),
        topology_(desc.topology) {
    std::memcpy(constant_color_, desc.constant_color, sizeof(constant_color_));
  }

  const std::vector<GPUVertexBufferLayout>& vertexBuffers() const {
    return vertex_buffers_;
  }
  GPUPrimitiveTopology topology() const { return topology_; }
  const float* constantColor() const { return constant_color_; }

 private:
  std::vector<GPUVertexBufferLayout> vertex_buffers_;
  GPUPrimitiveTopology topology_;
  float constant_color_[4];
};

// ============================================================================
// Draw Call Recording
// ============================================================================

struct DrawCall {
  GPURenderPipeline* pipeline = nullptr;
  GPUBuffer* vertex_buffers[8] = {};
  GPUBuffer* index_buffer = nullptr;
  GPUIndexFormat index_format = GPUIndexFormat::Uint16;
  uint32_t vertex_count = 0;
  uint32_t index_count = 0;
  uint32_t first_vertex = 0;
  uint32_t first_index = 0;
  bool indexed = false;
};

class GPURenderPassEncoder {
 public:
  explicit GPURenderPassEncoder(const GPURenderPassDescriptor& desc)
      : desc_(desc) {}

  void setPipeline(GPURenderPipeline* pipeline) {
    current_pipeline_ = pipeline;
  }

  void setVertexBuffer(uint32_t slot, GPUBuffer* buffer) {
    current_vertex_buffers_[slot] = buffer;
  }

  void setIndexBuffer(GPUBuffer* buffer, GPUIndexFormat format) {
    current_index_buffer_ = buffer;
    current_index_format_ = format;
  }

  void draw(uint32_t vertex_count, uint32_t instance_count = 1,
            uint32_t first_vertex = 0, uint32_t first_instance = 0) {
    (void)instance_count;
    (void)first_instance;
    DrawCall dc;
    dc.pipeline = current_pipeline_;
    std::memcpy(dc.vertex_buffers, current_vertex_buffers_,
                sizeof(dc.vertex_buffers));
    dc.vertex_count = vertex_count;
    dc.first_vertex = first_vertex;
    dc.indexed = false;
    draw_calls_.push_back(dc);
  }

  void drawIndexed(uint32_t index_count, uint32_t instance_count = 1,
                   uint32_t first_index = 0, int32_t base_vertex = 0,
                   uint32_t first_instance = 0) {
    (void)instance_count;
    (void)base_vertex;
    (void)first_instance;
    DrawCall dc;
    dc.pipeline = current_pipeline_;
    std::memcpy(dc.vertex_buffers, current_vertex_buffers_,
                sizeof(dc.vertex_buffers));
    dc.index_buffer = current_index_buffer_;
    dc.index_format = current_index_format_;
    dc.index_count = index_count;
    dc.first_index = first_index;
    dc.indexed = true;
    draw_calls_.push_back(dc);
  }

  void end() { ended_ = true; }

  bool ended() const { return ended_; }
  const GPURenderPassDescriptor& descriptor() const { return desc_; }
  std::vector<DrawCall>& drawCalls() { return draw_calls_; }

 private:
  GPURenderPassDescriptor desc_;
  GPURenderPipeline* current_pipeline_ = nullptr;
  GPUBuffer* current_vertex_buffers_[8] = {};
  GPUBuffer* current_index_buffer_ = nullptr;
  GPUIndexFormat current_index_format_ = GPUIndexFormat::Uint16;
  std::vector<DrawCall> draw_calls_;
  bool ended_ = false;
};

struct RenderPassRecord {
  GPURenderPassDescriptor desc;
  std::vector<DrawCall> draw_calls;
};

class GPUCommandBuffer {
 public:
  std::vector<RenderPassRecord> passes;
};

class GPUCommandEncoder {
 public:
  GPURenderPassEncoder beginRenderPass(const GPURenderPassDescriptor& desc) {
    return GPURenderPassEncoder(desc);
  }

  void addPass(GPURenderPassEncoder& pass) {
    RenderPassRecord rec;
    rec.desc = pass.descriptor();
    rec.draw_calls = std::move(pass.drawCalls());
    passes_.push_back(std::move(rec));
  }

  GPUCommandBuffer* finish() {
    auto* cmd = new GPUCommandBuffer();
    cmd->passes = std::move(passes_);
    return cmd;
  }

 private:
  std::vector<RenderPassRecord> passes_;
};

// ============================================================================
// Queue & Device
// ============================================================================

class GPUQueue {
 public:
  void submit(GPUCommandBuffer* cmd);

  void writeBuffer(GPUBuffer* buffer, uint64_t offset, const void* data,
                   uint64_t size) {
    std::memcpy(buffer->data() + offset, data, size);
  }
};

class GPUDevice {
 public:
  GPUDevice();
  ~GPUDevice();

  GPUBuffer* createBuffer(uint64_t size, uint32_t usage);
  GPUTexture* createTexture(uint32_t width, uint32_t height,
                            GPUTextureFormat format);
  GPUShaderModule* createShaderModule(const std::string& code);
  GPURenderPipeline* createRenderPipeline(
      const GPURenderPipelineDescriptor& desc);
  GPUCommandEncoder* createCommandEncoder();
  GPUQueue* getQueue() { return &queue_; }

 private:
  GPUQueue queue_;
  std::vector<std::unique_ptr<GPUBuffer>> buffers_;
  std::vector<std::unique_ptr<GPUTexture>> textures_;
  std::vector<std::unique_ptr<GPUShaderModule>> shaders_;
  std::vector<std::unique_ptr<GPURenderPipeline>> pipelines_;
  std::vector<std::unique_ptr<GPUCommandEncoder>> encoders_;
};

// ============================================================================
// Adapter & GPU Entry Point
// ============================================================================

class GPUAdapter {
 public:
  GPUDevice* requestDevice();
  ~GPUAdapter();

 private:
  std::vector<std::unique_ptr<GPUDevice>> devices_;
};

class GPU {
 public:
  static GPUAdapter* requestAdapter();
};

// ============================================================================
// Canvas & Context
// ============================================================================

class GPUCanvasContext {
 public:
  explicit GPUCanvasContext(Canvas* canvas) : canvas_(canvas) {}
  void configure(GPUDevice* device, GPUTextureFormat format);
  GPUTexture* getCurrentTexture();

 private:
  Canvas* canvas_;
  GPUDevice* device_ = nullptr;
  GPUTextureFormat format_ = GPUTextureFormat::RGBA8Unorm;
};

class Canvas {
 public:
  Canvas(uint32_t width, uint32_t height);

  GPUCanvasContext* getContext();
  uint32_t width() const { return width_; }
  uint32_t height() const { return height_; }

  bool saveBMP(const char* filename) const;
  bool savePPM(const char* filename) const;
  bool savePNG(const char* filename) const;

  const uint8_t* getPixels() const;
  GPUTexture* getTexture() { return texture_.get(); }

 private:
  uint32_t width_, height_;
  std::unique_ptr<GPUTexture> texture_;
  std::unique_ptr<GPUCanvasContext> context_;
};

}  // namespace softrt
