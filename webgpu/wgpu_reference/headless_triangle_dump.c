/*
 * headless_triangle_dump.c
 * Render an offscreen triangle with wgpu-native, dump raw RGBA, optional BMP.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include <webgpu/webgpu.h>
#include <webgpu/wgpu.h>

#include "bmp_writer.h"

/* ---- Async callback helpers ---- */

static WGPUAdapter g_adapter = NULL;
static WGPUDevice g_device = NULL;
static int g_mapped = 0;

static void on_adapter(WGPURequestAdapterStatus status, WGPUAdapter adapter,
                       WGPUStringView message, void* userdata1,
                       void* userdata2) {
  (void)userdata1;
  (void)userdata2;
  if (status != WGPURequestAdapterStatus_Success) {
    fprintf(stderr, "Adapter request failed: %.*s\n", (int)message.length,
            message.data ? message.data : "");
    return;
  }
  g_adapter = adapter;
}

static void on_device(WGPURequestDeviceStatus status, WGPUDevice device,
                      WGPUStringView message, void* userdata1,
                      void* userdata2) {
  (void)userdata1;
  (void)userdata2;
  if (status != WGPURequestDeviceStatus_Success) {
    fprintf(stderr, "Device request failed: %.*s\n", (int)message.length,
            message.data ? message.data : "");
    return;
  }
  g_device = device;
}

static void on_mapped(WGPUMapAsyncStatus status, WGPUStringView message,
                      void* userdata1, void* userdata2) {
  (void)message;
  (void)userdata1;
  (void)userdata2;
  g_mapped = (status == WGPUMapAsyncStatus_Success);
}

static void on_device_error(WGPUDevice const* device, WGPUErrorType type,
                            WGPUStringView message, void* userdata1,
                            void* userdata2) {
  (void)device;
  (void)userdata1;
  (void)userdata2;
  fprintf(stderr, "Device error (%d): %.*s\n", (int)type, (int)message.length,
          message.data ? message.data : "");
}

static char* read_file(const char* path, size_t* out_len) {
  FILE* f = fopen(path, "rb");
  if (!f) {
    fprintf(stderr, "Cannot open %s\n", path);
    return NULL;
  }
  fseek(f, 0, SEEK_END);
  long len = ftell(f);
  fseek(f, 0, SEEK_SET);
  char* buf = (char*)malloc((size_t)len + 1);
  if (!buf) {
    fclose(f);
    return NULL;
  }
  fread(buf, 1, (size_t)len, f);
  buf[len] = '\0';
  fclose(f);
  if (out_len) *out_len = (size_t)len;
  return buf;
}

static int write_rgba(const char* path, const uint8_t* rgba, uint32_t width,
                      uint32_t height) {
  FILE* f = fopen(path, "wb");
  if (!f) return 0;
  size_t n = fwrite(rgba, 1, (size_t)width * (size_t)height * 4u, f);
  fclose(f);
  return n == (size_t)width * (size_t)height * 4u;
}

static void usage(const char* argv0) {
  fprintf(stderr,
          "Usage: %s [--width N] [--height N] [--out-rgba file] "
          "[--out-bmp file]\n",
          argv0);
}

int main(int argc, char** argv) {
  uint32_t width = 640;
  uint32_t height = 480;
  const char* out_rgba = "triangle_wgpu.rgba";
  const char* out_bmp = "triangle_wgpu.bmp";

  for (int i = 1; i < argc; ++i) {
    if (strcmp(argv[i], "--width") == 0 && i + 1 < argc) {
      width = (uint32_t)strtoul(argv[++i], NULL, 10);
    } else if (strcmp(argv[i], "--height") == 0 && i + 1 < argc) {
      height = (uint32_t)strtoul(argv[++i], NULL, 10);
    } else if (strcmp(argv[i], "--out-rgba") == 0 && i + 1 < argc) {
      out_rgba = argv[++i];
    } else if (strcmp(argv[i], "--out-bmp") == 0 && i + 1 < argc) {
      out_bmp = argv[++i];
    } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
      usage(argv[0]);
      return 0;
    } else {
      fprintf(stderr, "Unknown arg: %s\n", argv[i]);
      usage(argv[0]);
      return 2;
    }
  }

  if (width == 0 || height == 0) {
    fprintf(stderr, "width/height must be > 0\n");
    return 2;
  }

  WGPUInstance instance = wgpuCreateInstance(NULL);
  if (!instance) {
    fprintf(stderr, "Failed to create instance\n");
    return 1;
  }

  WGPURequestAdapterOptions adapter_opts = {0};
  adapter_opts.powerPreference = WGPUPowerPreference_HighPerformance;
  wgpuInstanceRequestAdapter(instance, &adapter_opts,
                             (WGPURequestAdapterCallbackInfo){
                                 .callback = on_adapter,
                             });
  if (!g_adapter) {
    fprintf(stderr, "No adapter\n");
    return 1;
  }

  WGPUDeviceDescriptor device_desc = {0};
  device_desc.uncapturedErrorCallbackInfo = (WGPUUncapturedErrorCallbackInfo){
      .callback = on_device_error,
  };
  wgpuAdapterRequestDevice(g_adapter, &device_desc,
                           (WGPURequestDeviceCallbackInfo){
                               .callback = on_device,
                           });
  if (!g_device) {
    fprintf(stderr, "No device\n");
    return 1;
  }
  WGPUQueue queue = wgpuDeviceGetQueue(g_device);

  float vertices[] = {
      0.0f, 0.5f,  0.5f,  /* top */
      -0.5f, -0.5f, 0.5f, /* bottom-left */
      0.5f, -0.5f, 0.5f,  /* bottom-right */
  };
  WGPUBufferDescriptor vb_desc = {0};
  vb_desc.size = sizeof(vertices);
  vb_desc.usage = WGPUBufferUsage_Vertex | WGPUBufferUsage_CopyDst;
  vb_desc.mappedAtCreation = false;
  WGPUBuffer vertex_buf = wgpuDeviceCreateBuffer(g_device, &vb_desc);
  wgpuQueueWriteBuffer(queue, vertex_buf, 0, vertices, sizeof(vertices));

  size_t wgsl_len = 0;
  char* wgsl_src = read_file("triangle.wgsl", &wgsl_len);
  if (!wgsl_src) return 1;

  WGPUShaderSourceWGSL wgsl_desc = {0};
  wgsl_desc.chain.sType = WGPUSType_ShaderSourceWGSL;
  wgsl_desc.code = (WGPUStringView){.data = wgsl_src, .length = wgsl_len};

  WGPUShaderModuleDescriptor sm_desc = {0};
  sm_desc.nextInChain = (WGPUChainedStruct*)&wgsl_desc;
  WGPUShaderModule shader = wgpuDeviceCreateShaderModule(g_device, &sm_desc);
  free(wgsl_src);

  WGPUVertexAttribute pos_attr = {0};
  pos_attr.format = WGPUVertexFormat_Float32x3;
  pos_attr.offset = 0;
  pos_attr.shaderLocation = 0;

  WGPUVertexBufferLayout vb_layout = {0};
  vb_layout.arrayStride = 3 * sizeof(float);
  vb_layout.stepMode = WGPUVertexStepMode_Vertex;
  vb_layout.attributeCount = 1;
  vb_layout.attributes = &pos_attr;

  WGPUColorTargetState color_target = {0};
  color_target.format = WGPUTextureFormat_RGBA8Unorm;
  color_target.writeMask = WGPUColorWriteMask_All;

  WGPUFragmentState frag_state = {0};
  frag_state.module = shader;
  frag_state.entryPoint = (WGPUStringView){.data = "fs_main",
                                           .length = WGPU_STRLEN};
  frag_state.targetCount = 1;
  frag_state.targets = &color_target;

  WGPURenderPipelineDescriptor pip_desc = {0};
  pip_desc.vertex.module = shader;
  pip_desc.vertex.entryPoint = (WGPUStringView){.data = "vs_main",
                                                .length = WGPU_STRLEN};
  pip_desc.vertex.bufferCount = 1;
  pip_desc.vertex.buffers = &vb_layout;
  pip_desc.fragment = &frag_state;
  pip_desc.primitive.topology = WGPUPrimitiveTopology_TriangleList;
  pip_desc.multisample.count = 1;
  pip_desc.multisample.mask = 0xFFFFFFFF;
  WGPURenderPipeline pipeline = wgpuDeviceCreateRenderPipeline(g_device, &pip_desc);

  WGPUTextureDescriptor tex_desc = {0};
  tex_desc.size.width = width;
  tex_desc.size.height = height;
  tex_desc.size.depthOrArrayLayers = 1;
  tex_desc.mipLevelCount = 1;
  tex_desc.sampleCount = 1;
  tex_desc.dimension = WGPUTextureDimension_2D;
  tex_desc.format = WGPUTextureFormat_RGBA8Unorm;
  tex_desc.usage = WGPUTextureUsage_RenderAttachment | WGPUTextureUsage_CopySrc;
  WGPUTexture render_tex = wgpuDeviceCreateTexture(g_device, &tex_desc);

  WGPUTextureViewDescriptor tv_desc = {0};
  tv_desc.format = WGPUTextureFormat_RGBA8Unorm;
  tv_desc.dimension = WGPUTextureViewDimension_2D;
  tv_desc.mipLevelCount = 1;
  tv_desc.arrayLayerCount = 1;
  WGPUTextureView render_view = wgpuTextureCreateView(render_tex, &tv_desc);

  uint32_t bytes_per_row = ((width * 4 + 255) & ~255u);
  uint32_t readback_size = bytes_per_row * height;
  WGPUBufferDescriptor rb_desc = {0};
  rb_desc.size = readback_size;
  rb_desc.usage = WGPUBufferUsage_CopyDst | WGPUBufferUsage_MapRead;
  WGPUBuffer readback_buf = wgpuDeviceCreateBuffer(g_device, &rb_desc);

  WGPURenderPassColorAttachment ca = {0};
  ca.view = render_view;
  ca.loadOp = WGPULoadOp_Clear;
  ca.storeOp = WGPUStoreOp_Store;
  ca.clearValue = (WGPUColor){0.2, 0.2, 0.2, 1.0};

  WGPURenderPassDescriptor rp_desc = {0};
  rp_desc.colorAttachmentCount = 1;
  rp_desc.colorAttachments = &ca;

  WGPUCommandEncoder encoder = wgpuDeviceCreateCommandEncoder(g_device, NULL);
  WGPURenderPassEncoder pass = wgpuCommandEncoderBeginRenderPass(encoder, &rp_desc);
  wgpuRenderPassEncoderSetPipeline(pass, pipeline);
  wgpuRenderPassEncoderSetVertexBuffer(pass, 0, vertex_buf, 0, sizeof(vertices));
  wgpuRenderPassEncoderDraw(pass, 3, 1, 0, 0);
  wgpuRenderPassEncoderEnd(pass);
  wgpuRenderPassEncoderRelease(pass);

  WGPUTexelCopyTextureInfo src = {0};
  src.texture = render_tex;
  src.mipLevel = 0;
  src.origin = (WGPUOrigin3D){0, 0, 0};
  src.aspect = WGPUTextureAspect_All;

  WGPUTexelCopyBufferInfo dst = {0};
  dst.buffer = readback_buf;
  dst.layout.offset = 0;
  dst.layout.bytesPerRow = bytes_per_row;
  dst.layout.rowsPerImage = height;

  WGPUExtent3D copy_size = {width, height, 1};
  wgpuCommandEncoderCopyTextureToBuffer(encoder, &src, &dst, &copy_size);

  WGPUCommandBuffer cmd = wgpuCommandEncoderFinish(encoder, NULL);
  wgpuQueueSubmit(queue, 1, &cmd);
  wgpuCommandBufferRelease(cmd);
  wgpuCommandEncoderRelease(encoder);

  wgpuDevicePoll(g_device, true, NULL);

  wgpuBufferMapAsync(readback_buf, WGPUMapMode_Read, 0, readback_size,
                     (WGPUBufferMapCallbackInfo){
                         .callback = on_mapped,
                     });
  wgpuDevicePoll(g_device, true, NULL);

  if (!g_mapped) {
    fprintf(stderr, "Buffer map failed\n");
    return 1;
  }

  const uint8_t* mapped = (const uint8_t*)wgpuBufferGetConstMappedRange(
      readback_buf, 0, readback_size);
  uint8_t* pixels = (uint8_t*)malloc((size_t)width * (size_t)height * 4u);
  if (!pixels) {
    fprintf(stderr, "OOM for pixel buffer\n");
    return 1;
  }
  for (uint32_t y = 0; y < height; y++) {
    memcpy(pixels + (size_t)y * (size_t)width * 4u, mapped + (size_t)y * bytes_per_row,
           (size_t)width * 4u);
  }
  wgpuBufferUnmap(readback_buf);

  if (!write_rgba(out_rgba, pixels, width, height)) {
    fprintf(stderr, "Failed to write RGBA: %s\n", out_rgba);
    free(pixels);
    return 1;
  }

  if (out_bmp && out_bmp[0] != '\0') {
    if (!write_bmp(out_bmp, width, height, pixels)) {
      fprintf(stderr, "Failed to write BMP: %s\n", out_bmp);
      free(pixels);
      return 1;
    }
  }

  printf("Rendered %ux%u\n", width, height);
  printf("RGBA: %s\n", out_rgba);
  if (out_bmp && out_bmp[0] != '\0') {
    printf("BMP:  %s\n", out_bmp);
  }

  free(pixels);

  wgpuBufferRelease(readback_buf);
  wgpuTextureViewRelease(render_view);
  wgpuTextureRelease(render_tex);
  wgpuRenderPipelineRelease(pipeline);
  wgpuShaderModuleRelease(shader);
  wgpuBufferRelease(vertex_buf);
  wgpuQueueRelease(queue);
  wgpuDeviceRelease(g_device);
  wgpuAdapterRelease(g_adapter);
  wgpuInstanceRelease(instance);
  return 0;
}
