#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <string>

#include "webgpu_lightrt.hh"

namespace {

void usage(const char* argv0) {
  std::fprintf(stderr,
               "Usage: %s [--width N] [--height N] [--out-rgba file] "
               "[--out-bmp file]\n",
               argv0);
}

bool writeRGBA(const std::string& path, const uint8_t* rgba, uint32_t width,
               uint32_t height) {
  std::ofstream ofs(path, std::ios::binary);
  if (!ofs) return false;
  ofs.write(reinterpret_cast<const char*>(rgba),
            static_cast<std::streamsize>(width) *
                static_cast<std::streamsize>(height) * 4);
  return ofs.good();
}

}  // namespace

int main(int argc, char** argv) {
  using namespace softrt;

  uint32_t width = 640;
  uint32_t height = 480;
  std::string out_rgba = "triangle_lightrt.rgba";
  std::string out_bmp = "triangle_lightrt.bmp";

  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--width" && i + 1 < argc) {
      width = static_cast<uint32_t>(std::strtoul(argv[++i], nullptr, 10));
    } else if (arg == "--height" && i + 1 < argc) {
      height = static_cast<uint32_t>(std::strtoul(argv[++i], nullptr, 10));
    } else if (arg == "--out-rgba" && i + 1 < argc) {
      out_rgba = argv[++i];
    } else if (arg == "--out-bmp" && i + 1 < argc) {
      out_bmp = argv[++i];
    } else if (arg == "-h" || arg == "--help") {
      usage(argv[0]);
      return 0;
    } else {
      std::fprintf(stderr, "Unknown argument: %s\n", arg.c_str());
      usage(argv[0]);
      return 2;
    }
  }

  if (width == 0 || height == 0) {
    std::fprintf(stderr, "width/height must be > 0\n");
    return 2;
  }

  Canvas canvas(width, height);
  GPUAdapter* adapter = GPU::requestAdapter();
  GPUDevice* device = adapter->requestDevice();
  GPUQueue* queue = device->getQueue();

  GPUCanvasContext* ctx = canvas.getContext();
  ctx->configure(device, GPUTextureFormat::RGBA8Unorm);

  float vertices[] = {
      0.0f,  0.5f,  0.5f,   // top
      -0.5f, -0.5f, 0.5f,   // bottom-left
      0.5f,  -0.5f, 0.5f,   // bottom-right
  };

  GPUBuffer* vb = device->createBuffer(sizeof(vertices),
                                       GPUBufferUsage_VERTEX |
                                           GPUBufferUsage_COPY_DST);
  queue->writeBuffer(vb, 0, vertices, sizeof(vertices));

  GPUShaderModule* shader = device->createShaderModule("/* stub */");

  GPURenderPipelineDescriptor pd;
  pd.vertex_module = shader;
  pd.fragment_module = shader;
  pd.topology = GPUPrimitiveTopology::TriangleList;
  pd.constant_color[0] = 0.0f;
  pd.constant_color[1] = 0.6f;
  pd.constant_color[2] = 1.0f;
  pd.constant_color[3] = 1.0f;

  GPUVertexBufferLayout vbl;
  vbl.arrayStride = 3 * sizeof(float);
  GPUVertexAttribute attr;
  attr.format = GPUVertexFormat::Float32x3;
  attr.offset = 0;
  attr.shaderLocation = 0;
  vbl.attributes.push_back(attr);
  pd.vertex_buffers.push_back(vbl);

  GPURenderPipeline* pipeline = device->createRenderPipeline(pd);

  GPUTexture* target_tex = ctx->getCurrentTexture();
  GPUTextureView* target_view = target_tex->createView();

  GPURenderPassDescriptor rpd;
  rpd.colorAttachment.view = target_view;
  rpd.colorAttachment.loadOp = GPULoadOp::Clear;
  rpd.colorAttachment.storeOp = GPUStoreOp::Store;
  rpd.colorAttachment.clearValue[0] = 0.2f;
  rpd.colorAttachment.clearValue[1] = 0.2f;
  rpd.colorAttachment.clearValue[2] = 0.2f;
  rpd.colorAttachment.clearValue[3] = 1.0f;

  GPUCommandEncoder* encoder = device->createCommandEncoder();
  GPURenderPassEncoder pass = encoder->beginRenderPass(rpd);
  pass.setPipeline(pipeline);
  pass.setVertexBuffer(0, vb);
  pass.draw(3);
  pass.end();
  encoder->addPass(pass);
  queue->submit(encoder->finish());

  const uint8_t* rgba = canvas.getPixels();
  if (!writeRGBA(out_rgba, rgba, width, height)) {
    std::fprintf(stderr, "Failed to write RGBA file: %s\n", out_rgba.c_str());
    return 1;
  }

  if (!out_bmp.empty()) {
    if (!canvas.saveBMP(out_bmp.c_str())) {
      std::fprintf(stderr, "Failed to write BMP file: %s\n", out_bmp.c_str());
      return 1;
    }
  }

  std::printf("Rendered %ux%u\n", width, height);
  std::printf("RGBA: %s\n", out_rgba.c_str());
  if (!out_bmp.empty()) {
    std::printf("BMP:  %s\n", out_bmp.c_str());
  }
  return 0;
}

