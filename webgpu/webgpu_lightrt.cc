// webgpu_lightrt.cc — Implementation of minimal WebGPU API using LightRT
#include "webgpu_lightrt.hh"

#include <algorithm>
#include <cmath>
#include <cstring>
#include <limits>

#include "../lightrt.hh"

namespace softrt {

// ============================================================================
// GPUTexture
// ============================================================================

GPUTextureView* GPUTexture::createView() {
  if (!view_) {
    view_ = std::make_unique<GPUTextureView>(this);
  }
  return view_.get();
}

// ============================================================================
// GPUDevice
// ============================================================================

GPUDevice::GPUDevice() = default;
GPUDevice::~GPUDevice() = default;

GPUBuffer* GPUDevice::createBuffer(uint64_t size, uint32_t usage) {
  buffers_.push_back(std::make_unique<GPUBuffer>(size, usage));
  return buffers_.back().get();
}

GPUTexture* GPUDevice::createTexture(uint32_t width, uint32_t height,
                                     GPUTextureFormat format) {
  textures_.push_back(std::make_unique<GPUTexture>(width, height, format));
  return textures_.back().get();
}

GPUShaderModule* GPUDevice::createShaderModule(const std::string& code) {
  shaders_.push_back(std::make_unique<GPUShaderModule>(code));
  return shaders_.back().get();
}

GPURenderPipeline* GPUDevice::createRenderPipeline(
    const GPURenderPipelineDescriptor& desc) {
  pipelines_.push_back(std::make_unique<GPURenderPipeline>(desc));
  return pipelines_.back().get();
}

GPUCommandEncoder* GPUDevice::createCommandEncoder() {
  encoders_.push_back(std::make_unique<GPUCommandEncoder>());
  return encoders_.back().get();
}

// ============================================================================
// GPUAdapter & GPU
// ============================================================================

GPUDevice* GPUAdapter::requestDevice() {
  devices_.push_back(std::make_unique<GPUDevice>());
  return devices_.back().get();
}

GPUAdapter::~GPUAdapter() = default;

static GPUAdapter g_adapter;

GPUAdapter* GPU::requestAdapter() { return &g_adapter; }

// ============================================================================
// Canvas & GPUCanvasContext
// ============================================================================

Canvas::Canvas(uint32_t width, uint32_t height)
    : width_(width),
      height_(height),
      texture_(std::make_unique<GPUTexture>(width, height,
                                            GPUTextureFormat::RGBA8Unorm)),
      context_(std::make_unique<GPUCanvasContext>(this)) {}

GPUCanvasContext* Canvas::getContext() { return context_.get(); }

const uint8_t* Canvas::getPixels() const { return texture_->pixels(); }

bool Canvas::saveBMP(const char* filename) const {
  uint32_t w = width_;
  uint32_t h = height_;
  const uint8_t* rgba = texture_->pixels();

  // Convert RGBA to RGB8
  std::vector<lightrt::RGB8> rgb(w * h);
  for (uint32_t i = 0; i < w * h; ++i) {
    rgb[i] = lightrt::RGB8(rgba[i * 4 + 0], rgba[i * 4 + 1],
                            rgba[i * 4 + 2]);
  }
  return lightrt::HeatmapWriter::writeImage(filename, rgb.data(), w, h,
                                             lightrt::ImageFormat::BMP);
}

bool Canvas::savePPM(const char* filename) const {
  uint32_t w = width_;
  uint32_t h = height_;
  const uint8_t* rgba = texture_->pixels();

  std::vector<lightrt::RGB8> rgb(w * h);
  for (uint32_t i = 0; i < w * h; ++i) {
    rgb[i] = lightrt::RGB8(rgba[i * 4 + 0], rgba[i * 4 + 1],
                            rgba[i * 4 + 2]);
  }
  return lightrt::HeatmapWriter::writeImage(filename, rgb.data(), w, h,
                                             lightrt::ImageFormat::PPM);
}

bool Canvas::savePNG(const char* filename) const {
  uint32_t w = width_;
  uint32_t h = height_;
  const uint8_t* rgba = texture_->pixels();

  std::vector<lightrt::RGB8> rgb(w * h);
  for (uint32_t i = 0; i < w * h; ++i) {
    rgb[i] = lightrt::RGB8(rgba[i * 4 + 0], rgba[i * 4 + 1],
                            rgba[i * 4 + 2]);
  }
  return lightrt::HeatmapWriter::writeImage(filename, rgb.data(), w, h,
                                             lightrt::ImageFormat::PNG);
}

void GPUCanvasContext::configure(GPUDevice* device, GPUTextureFormat format) {
  device_ = device;
  format_ = format;
}

GPUTexture* GPUCanvasContext::getCurrentTexture() {
  return canvas_->getTexture();
}

// ============================================================================
// Vertex Reading Helpers
// ============================================================================

namespace {

// Read a position from a vertex buffer given layout info.
// Returns (x, y, z) in NDC. For Float32x4, applies perspective divide (x/w,
// y/w, z/w).
void readPosition(const uint8_t* buf, uint64_t vertex_index,
                  uint64_t array_stride, uint64_t offset,
                  GPUVertexFormat format, float& x, float& y, float& z) {
  const uint8_t* ptr = buf + vertex_index * array_stride + offset;
  float components[4] = {0.0f, 0.0f, 0.0f, 1.0f};

  uint32_t count = 0;
  switch (format) {
    case GPUVertexFormat::Float32x2:
      count = 2;
      break;
    case GPUVertexFormat::Float32x3:
      count = 3;
      break;
    case GPUVertexFormat::Float32x4:
      count = 4;
      break;
  }

  std::memcpy(components, ptr, count * sizeof(float));

  if (format == GPUVertexFormat::Float32x4 &&
      std::fabs(components[3]) > 1e-12f) {
    float w_inv = 1.0f / components[3];
    x = components[0] * w_inv;
    y = components[1] * w_inv;
    z = components[2] * w_inv;
  } else {
    x = components[0];
    y = components[1];
    z = components[2];
  }
}

// Find the position attribute (shaderLocation == 0) in the vertex layout.
bool findPositionAttribute(const GPURenderPipeline* pipeline,
                           uint32_t& slot_out, uint64_t& stride_out,
                           uint64_t& offset_out, GPUVertexFormat& fmt_out) {
  const auto& layouts = pipeline->vertexBuffers();
  for (uint32_t s = 0; s < layouts.size(); ++s) {
    const auto& layout = layouts[s];
    for (const auto& attr : layout.attributes) {
      if (attr.shaderLocation == 0) {
        slot_out = s;
        stride_out = layout.arrayStride;
        offset_out = attr.offset;
        fmt_out = attr.format;
        return true;
      }
    }
  }
  return false;
}

// Read an index from an index buffer.
uint32_t readIndex(const GPUBuffer* ib, GPUIndexFormat fmt, uint32_t idx) {
  if (fmt == GPUIndexFormat::Uint16) {
    uint16_t val;
    std::memcpy(&val, ib->data() + idx * 2, 2);
    return val;
  } else {
    uint32_t val;
    std::memcpy(&val, ib->data() + idx * 4, 4);
    return val;
  }
}

}  // namespace

// ============================================================================
// GPUQueue::submit — Core Rendering via LightRT
// ============================================================================

void GPUQueue::submit(GPUCommandBuffer* cmd) {
  for (auto& pass : cmd->passes) {
    // Get render target
    GPUTexture* target = pass.desc.colorAttachment.view->texture();
    uint32_t w = target->width();
    uint32_t h = target->height();
    uint8_t* pixels = target->pixels();

    // Clear if requested
    if (pass.desc.colorAttachment.loadOp == GPULoadOp::Clear) {
      const float* cv = pass.desc.colorAttachment.clearValue;
      uint8_t cr = static_cast<uint8_t>(std::min(cv[0], 1.0f) * 255.0f);
      uint8_t cg = static_cast<uint8_t>(std::min(cv[1], 1.0f) * 255.0f);
      uint8_t cb = static_cast<uint8_t>(std::min(cv[2], 1.0f) * 255.0f);
      uint8_t ca = static_cast<uint8_t>(std::min(cv[3], 1.0f) * 255.0f);
      for (uint32_t i = 0; i < w * h; ++i) {
        pixels[i * 4 + 0] = cr;
        pixels[i * 4 + 1] = cg;
        pixels[i * 4 + 2] = cb;
        pixels[i * 4 + 3] = ca;
      }
    }

    // Collect all triangles and their colors from draw calls
    std::vector<lightrt::Triangle> triangles;
    std::vector<uint32_t> tri_colors;  // packed RGBA per triangle

    for (auto& dc : pass.draw_calls) {
      if (!dc.pipeline) continue;

      uint32_t slot = 0;
      uint64_t stride = 0, offset = 0;
      GPUVertexFormat fmt = GPUVertexFormat::Float32x3;
      if (!findPositionAttribute(dc.pipeline, slot, stride, offset, fmt))
        continue;

      GPUBuffer* vb = dc.vertex_buffers[slot];
      if (!vb) continue;

      const float* color = dc.pipeline->constantColor();
      uint8_t r8 = static_cast<uint8_t>(std::min(color[0], 1.0f) * 255.0f);
      uint8_t g8 = static_cast<uint8_t>(std::min(color[1], 1.0f) * 255.0f);
      uint8_t b8 = static_cast<uint8_t>(std::min(color[2], 1.0f) * 255.0f);
      uint8_t a8 = static_cast<uint8_t>(std::min(color[3], 1.0f) * 255.0f);
      uint32_t packed =
          (uint32_t(r8)) | (uint32_t(g8) << 8) | (uint32_t(b8) << 16) |
          (uint32_t(a8) << 24);

      auto getVertexIndex = [&](uint32_t i) -> uint32_t {
        if (dc.indexed) {
          return readIndex(dc.index_buffer, dc.index_format,
                           dc.first_index + i);
        }
        return dc.first_vertex + i;
      };

      uint32_t count = dc.indexed ? dc.index_count : dc.vertex_count;

      for (uint32_t i = 0; i + 2 < count; i += 3) {
        float x0, y0, z0, x1, y1, z1, x2, y2, z2;
        readPosition(vb->data(), getVertexIndex(i + 0), stride, offset, fmt,
                     x0, y0, z0);
        readPosition(vb->data(), getVertexIndex(i + 1), stride, offset, fmt,
                     x1, y1, z1);
        readPosition(vb->data(), getVertexIndex(i + 2), stride, offset, fmt,
                     x2, y2, z2);

        triangles.push_back(lightrt::Triangle(lightrt::Vec3(x0, y0, z0),
                                              lightrt::Vec3(x1, y1, z1),
                                              lightrt::Vec3(x2, y2, z2)));
        tri_colors.push_back(packed);
      }
    }

    if (triangles.empty()) continue;

    // Build BVH
    lightrt::TriangleBVH bvh;
    bvh.build(triangles);

    // Generate rays — orthographic through NDC cube
    uint32_t num_pixels = w * h;
    std::vector<lightrt::Ray> rays(num_pixels);
    for (uint32_t py = 0; py < h; ++py) {
      for (uint32_t px = 0; px < w; ++px) {
        float ndc_x = 2.0f * (float(px) + 0.5f) / float(w) - 1.0f;
        float ndc_y = 1.0f - 2.0f * (float(py) + 0.5f) / float(h);
        uint32_t idx = py * w + px;
        rays[idx] = lightrt::Ray(lightrt::Vec3(ndc_x, ndc_y, 1.5f),
                                 lightrt::Vec3(0.0f, 0.0f, -1.0f),
                                 lightrt::kEpsilon, 3.0f);
      }
    }

    // Batch traversal
    std::vector<uint32_t> hit_ids(num_pixels);
    std::vector<float> hit_ts(num_pixels);
    std::vector<float> hit_us(num_pixels);
    std::vector<float> hit_vs(num_pixels);

    bvh.traverseBatch(rays.data(), num_pixels, hit_ids.data(), hit_ts.data(),
                      hit_us.data(), hit_vs.data(), 0);

    // Write hit pixels
    for (uint32_t i = 0; i < num_pixels; ++i) {
      if (hit_ids[i] != lightrt::kInvalidIndex) {
        uint32_t packed = tri_colors[hit_ids[i]];
        pixels[i * 4 + 0] = static_cast<uint8_t>(packed & 0xFF);
        pixels[i * 4 + 1] = static_cast<uint8_t>((packed >> 8) & 0xFF);
        pixels[i * 4 + 2] = static_cast<uint8_t>((packed >> 16) & 0xFF);
        pixels[i * 4 + 3] = static_cast<uint8_t>((packed >> 24) & 0xFF);
      }
    }
  }

  delete cmd;
}

}  // namespace softrt
