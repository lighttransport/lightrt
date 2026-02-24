// webgpu_embind.cc — Emscripten Embind bindings for the softrt WebGPU API
#ifdef __EMSCRIPTEN__

#include <emscripten/bind.h>
#include <emscripten/val.h>

#include "webgpu_lightrt.hh"

using namespace emscripten;
using namespace softrt;

// ============================================================================
// JS-interop wrapper functions
// ============================================================================

namespace {

// Write data into a GPUBuffer from a WASM heap pointer.
// Called from JS after copying TypedArray data into the heap.
void queue_writeBuffer_ptr(GPUQueue& queue, GPUBuffer* buffer, uint64_t offset,
                           uintptr_t data_ptr, uint32_t size) {
  const void* data = reinterpret_cast<const void*>(data_ptr);
  queue.writeBuffer(buffer, offset, data, size);
}

// Parse a JS object into a GPURenderPipelineDescriptor and create the pipeline
GPURenderPipeline* device_createRenderPipeline_js(GPUDevice& device,
                                                  val desc_val) {
  GPURenderPipelineDescriptor desc;

  // vertex module
  if (desc_val.hasOwnProperty("vertex") &&
      desc_val["vertex"].hasOwnProperty("module")) {
    desc.vertex_module = desc_val["vertex"]["module"].as<GPUShaderModule*>(
        allow_raw_pointers());
  }

  // fragment module
  if (desc_val.hasOwnProperty("fragment") &&
      desc_val["fragment"].hasOwnProperty("module")) {
    desc.fragment_module = desc_val["fragment"]["module"].as<GPUShaderModule*>(
        allow_raw_pointers());
  }

  // topology
  if (desc_val.hasOwnProperty("primitive") &&
      desc_val["primitive"].hasOwnProperty("topology")) {
    std::string topo = desc_val["primitive"]["topology"].as<std::string>();
    if (topo == "triangle-list") {
      desc.topology = GPUPrimitiveTopology::TriangleList;
    }
  }

  // constant_color (extension)
  if (desc_val.hasOwnProperty("constantColor")) {
    val cc = desc_val["constantColor"];
    desc.constant_color[0] = cc[0].as<float>();
    desc.constant_color[1] = cc[1].as<float>();
    desc.constant_color[2] = cc[2].as<float>();
    desc.constant_color[3] = cc[3].as<float>();
  }

  // vertex buffers
  if (desc_val.hasOwnProperty("vertex") &&
      desc_val["vertex"].hasOwnProperty("buffers")) {
    val buffers = desc_val["vertex"]["buffers"];
    unsigned int num_bufs = buffers["length"].as<unsigned int>();
    for (unsigned int i = 0; i < num_bufs; ++i) {
      val buf = buffers[i];
      GPUVertexBufferLayout layout;
      layout.arrayStride = buf["arrayStride"].as<uint64_t>();

      if (buf.hasOwnProperty("attributes")) {
        val attrs = buf["attributes"];
        unsigned int num_attrs = attrs["length"].as<unsigned int>();
        for (unsigned int j = 0; j < num_attrs; ++j) {
          val a = attrs[j];
          GPUVertexAttribute attr;
          attr.offset = a["offset"].as<uint64_t>();
          attr.shaderLocation = a["shaderLocation"].as<uint32_t>();
          std::string fmt = a["format"].as<std::string>();
          if (fmt == "float32x2") {
            attr.format = GPUVertexFormat::Float32x2;
          } else if (fmt == "float32x3") {
            attr.format = GPUVertexFormat::Float32x3;
          } else if (fmt == "float32x4") {
            attr.format = GPUVertexFormat::Float32x4;
          }
          layout.attributes.push_back(attr);
        }
      }
      desc.vertex_buffers.push_back(layout);
    }
  }

  return device.createRenderPipeline(desc);
}

// Parse a JS object into a GPURenderPassDescriptor, return heap-allocated
// encoder. Caller must call .delete() on the returned object.
GPURenderPassEncoder* encoder_beginRenderPass_js(GPUCommandEncoder& encoder,
                                                 val desc_val) {
  GPURenderPassDescriptor desc;

  if (desc_val.hasOwnProperty("colorAttachments")) {
    val ca_array = desc_val["colorAttachments"];
    if (ca_array["length"].as<unsigned int>() > 0) {
      val ca = ca_array[0];

      if (ca.hasOwnProperty("view")) {
        desc.colorAttachment.view =
            ca["view"].as<GPUTextureView*>(allow_raw_pointers());
      }

      if (ca.hasOwnProperty("loadOp")) {
        std::string op = ca["loadOp"].as<std::string>();
        if (op == "clear")
          desc.colorAttachment.loadOp = GPULoadOp::Clear;
        else if (op == "load")
          desc.colorAttachment.loadOp = GPULoadOp::Load;
      }

      if (ca.hasOwnProperty("storeOp")) {
        std::string op = ca["storeOp"].as<std::string>();
        if (op == "store")
          desc.colorAttachment.storeOp = GPUStoreOp::Store;
        else if (op == "discard")
          desc.colorAttachment.storeOp = GPUStoreOp::Discard;
      }

      if (ca.hasOwnProperty("clearValue")) {
        val cv = ca["clearValue"];
        if (cv.hasOwnProperty("r")) {
          desc.colorAttachment.clearValue[0] = cv["r"].as<float>();
          desc.colorAttachment.clearValue[1] = cv["g"].as<float>();
          desc.colorAttachment.clearValue[2] = cv["b"].as<float>();
          desc.colorAttachment.clearValue[3] = cv["a"].as<float>();
        } else {
          // Array form [r, g, b, a]
          desc.colorAttachment.clearValue[0] = cv[0].as<float>();
          desc.colorAttachment.clearValue[1] = cv[1].as<float>();
          desc.colorAttachment.clearValue[2] = cv[2].as<float>();
          desc.colorAttachment.clearValue[3] = cv[3].as<float>();
        }
      }
    }
  }

  // Heap-allocate so JS can hold a reference; caller calls .delete()
  auto* pass = new GPURenderPassEncoder(desc);
  return pass;
}

// Return pixel data as a JS Uint8Array view into WASM memory
val canvas_getPixelData(const Canvas& canvas) {
  const uint8_t* pixels = canvas.getPixels();
  uint32_t size = canvas.width() * canvas.height() * 4;
  return val(typed_memory_view(size, pixels));
}

}  // namespace

// ============================================================================
// EMSCRIPTEN_BINDINGS
// ============================================================================

EMSCRIPTEN_BINDINGS(softrt) {
  // --- Enums ---

  enum_<GPUTextureFormat>("GPUTextureFormat")
      .value("RGBA8Unorm", GPUTextureFormat::RGBA8Unorm)
      .value("BGRA8Unorm", GPUTextureFormat::BGRA8Unorm);

  enum_<GPUPrimitiveTopology>("GPUPrimitiveTopology")
      .value("TriangleList", GPUPrimitiveTopology::TriangleList);

  enum_<GPUIndexFormat>("GPUIndexFormat")
      .value("Uint16", GPUIndexFormat::Uint16)
      .value("Uint32", GPUIndexFormat::Uint32);

  enum_<GPUVertexFormat>("GPUVertexFormat")
      .value("Float32x2", GPUVertexFormat::Float32x2)
      .value("Float32x3", GPUVertexFormat::Float32x3)
      .value("Float32x4", GPUVertexFormat::Float32x4);

  enum_<GPULoadOp>("GPULoadOp")
      .value("Clear", GPULoadOp::Clear)
      .value("Load", GPULoadOp::Load);

  enum_<GPUStoreOp>("GPUStoreOp")
      .value("Store", GPUStoreOp::Store)
      .value("Discard", GPUStoreOp::Discard);

  // --- GPUBufferUsage constants ---
  constant("GPUBufferUsage_VERTEX", (uint32_t)GPUBufferUsage_VERTEX);
  constant("GPUBufferUsage_INDEX", (uint32_t)GPUBufferUsage_INDEX);
  constant("GPUBufferUsage_COPY_DST", (uint32_t)GPUBufferUsage_COPY_DST);
  constant("GPUBufferUsage_STORAGE", (uint32_t)GPUBufferUsage_STORAGE);

  // --- Classes ---

  class_<GPUBuffer>("GPUBuffer")
      .function("size", &GPUBuffer::size)
      .function("usage", &GPUBuffer::usage);

  class_<GPUTexture>("GPUTexture")
      .function("createView", &GPUTexture::createView,
                allow_raw_pointers())
      .function("width", &GPUTexture::width)
      .function("height", &GPUTexture::height);

  class_<GPUTextureView>("GPUTextureView")
      .function("texture", &GPUTextureView::texture, allow_raw_pointers());

  class_<GPUShaderModule>("GPUShaderModule");

  class_<GPURenderPipeline>("GPURenderPipeline");

  class_<GPURenderPassEncoder>("GPURenderPassEncoder")
      .function("setPipeline", &GPURenderPassEncoder::setPipeline,
                allow_raw_pointers())
      .function("setVertexBuffer", &GPURenderPassEncoder::setVertexBuffer,
                allow_raw_pointers())
      .function("setIndexBuffer", &GPURenderPassEncoder::setIndexBuffer,
                allow_raw_pointers())
      .function(
          "draw",
          optional_override([](GPURenderPassEncoder& self,
                               uint32_t vertex_count) { self.draw(vertex_count); }))
      .function("drawFull",
                optional_override([](GPURenderPassEncoder& self,
                                     uint32_t vertex_count,
                                     uint32_t instance_count,
                                     uint32_t first_vertex,
                                     uint32_t first_instance) {
                  self.draw(vertex_count, instance_count, first_vertex,
                            first_instance);
                }))
      .function(
          "drawIndexed",
          optional_override([](GPURenderPassEncoder& self,
                               uint32_t index_count) {
            self.drawIndexed(index_count);
          }))
      .function(
          "drawIndexedFull",
          optional_override([](GPURenderPassEncoder& self,
                               uint32_t index_count, uint32_t instance_count,
                               uint32_t first_index, int32_t base_vertex,
                               uint32_t first_instance) {
            self.drawIndexed(index_count, instance_count, first_index,
                             base_vertex, first_instance);
          }))
      .function("end", &GPURenderPassEncoder::end);

  class_<GPUCommandBuffer>("GPUCommandBuffer");

  class_<GPUCommandEncoder>("GPUCommandEncoder")
      .function("beginRenderPass_js", &encoder_beginRenderPass_js,
                allow_raw_pointers())
      .function("addPass", &GPUCommandEncoder::addPass)
      .function("finish", &GPUCommandEncoder::finish,
                allow_raw_pointers());

  class_<GPUQueue>("GPUQueue")
      .function("submit", &GPUQueue::submit, allow_raw_pointers())
      .function("writeBuffer_ptr", &queue_writeBuffer_ptr,
                allow_raw_pointers());

  class_<GPUDevice>("GPUDevice")
      .function("createBuffer", &GPUDevice::createBuffer,
                allow_raw_pointers())
      .function("createTexture", &GPUDevice::createTexture,
                allow_raw_pointers())
      .function("createShaderModule", &GPUDevice::createShaderModule,
                allow_raw_pointers())
      .function("createRenderPipeline_js", &device_createRenderPipeline_js,
                allow_raw_pointers())
      .function("createCommandEncoder", &GPUDevice::createCommandEncoder,
                allow_raw_pointers())
      .function("getQueue", &GPUDevice::getQueue, allow_raw_pointers());

  class_<GPUAdapter>("GPUAdapter")
      .function("requestDevice", &GPUAdapter::requestDevice,
                allow_raw_pointers());

  class_<GPU>("GPU")
      .class_function("requestAdapter", &GPU::requestAdapter,
                      allow_raw_pointers());

  class_<GPUCanvasContext>("GPUCanvasContext")
      .function("configure", &GPUCanvasContext::configure,
                allow_raw_pointers())
      .function("getCurrentTexture", &GPUCanvasContext::getCurrentTexture,
                allow_raw_pointers());

  class_<Canvas>("Canvas")
      .constructor<uint32_t, uint32_t>()
      .function("getContext", &Canvas::getContext, allow_raw_pointers())
      .function("width", &Canvas::width)
      .function("height", &Canvas::height)
      .function("saveBMP",
                optional_override([](Canvas& self, const std::string& path) {
                  return self.saveBMP(path.c_str());
                }))
      .function("savePPM",
                optional_override([](Canvas& self, const std::string& path) {
                  return self.savePPM(path.c_str());
                }))
      .function("savePNG",
                optional_override([](Canvas& self, const std::string& path) {
                  return self.savePNG(path.c_str());
                }))
      .function("getPixelData", &canvas_getPixelData);
}

#endif  // __EMSCRIPTEN__
