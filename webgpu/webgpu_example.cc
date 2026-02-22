// webgpu_example.cc — Render a blue triangle to BMP using the softrt WebGPU API
#include <cstdio>

#include "webgpu_lightrt.hh"

int main() {
  using namespace softrt;

  // Create canvas (render target)
  Canvas canvas(640, 480);
  GPUAdapter* adapter = GPU::requestAdapter();
  GPUDevice* device = adapter->requestDevice();
  GPUQueue* queue = device->getQueue();

  // Configure canvas context
  GPUCanvasContext* ctx = canvas.getContext();
  ctx->configure(device, GPUTextureFormat::RGBA8Unorm);

  // Triangle vertices in clip space (x, y, z)
  // Pointing up, centered at origin, z=0.5
  float vertices[] = {
      0.0f,  0.5f,  0.5f,   // top
      -0.5f, -0.5f, 0.5f,   // bottom-left
      0.5f,  -0.5f, 0.5f,   // bottom-right
  };

  // Create vertex buffer and upload data
  GPUBuffer* vb = device->createBuffer(sizeof(vertices),
                                       GPUBufferUsage_VERTEX |
                                           GPUBufferUsage_COPY_DST);
  queue->writeBuffer(vb, 0, vertices, sizeof(vertices));

  // Create shader module (stub — not executed)
  GPUShaderModule* shader = device->createShaderModule("/* stub */");

  // Pipeline descriptor
  GPURenderPipelineDescriptor pd;
  pd.vertex_module = shader;
  pd.fragment_module = shader;
  pd.topology = GPUPrimitiveTopology::TriangleList;
  pd.constant_color[0] = 0.0f;   // R
  pd.constant_color[1] = 0.6f;   // G
  pd.constant_color[2] = 1.0f;   // B
  pd.constant_color[3] = 1.0f;   // A

  // Vertex buffer layout: 3 floats per vertex, position at location 0
  GPUVertexBufferLayout vbl;
  vbl.arrayStride = 3 * sizeof(float);
  GPUVertexAttribute attr;
  attr.format = GPUVertexFormat::Float32x3;
  attr.offset = 0;
  attr.shaderLocation = 0;
  vbl.attributes.push_back(attr);
  pd.vertex_buffers.push_back(vbl);

  GPURenderPipeline* pipeline = device->createRenderPipeline(pd);

  // Get render target view from canvas
  GPUTexture* target_tex = ctx->getCurrentTexture();
  GPUTextureView* target_view = target_tex->createView();

  // Render pass
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

  // Render pass is complete — add it to the encoder
  encoder->addPass(pass);

  // Submit (triggers ray tracing)
  queue->submit(encoder->finish());

  // Save result
  if (canvas.saveBMP("triangle.bmp")) {
    std::printf("Saved triangle.bmp (640x480)\n");
  } else {
    std::printf("Failed to save triangle.bmp\n");
    return 1;
  }

  return 0;
}
