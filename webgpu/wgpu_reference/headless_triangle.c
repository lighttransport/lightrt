/*
 * headless_triangle.c — Render a blue triangle offscreen using wgpu-native,
 * then save the result as triangle_wgpu.bmp.
 *
 * Same geometry and colors as the softrt example for comparison.
 *
 * Targets the current webgpu-headers API (WGPUStringView, CallbackInfo
 * structs, WGPUShaderSourceWGSL, etc.) as shipped by WebGPU-distribution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <webgpu/webgpu.h>
#include "bmp_writer.h"

#define WIDTH  640
#define HEIGHT 480

/* ---- Async callback helpers ---- */

static WGPUAdapter g_adapter = NULL;
static WGPUDevice  g_device  = NULL;
static int         g_mapped  = 0;

static void on_adapter(WGPURequestAdapterStatus status, WGPUAdapter adapter,
                       WGPUStringView message,
                       void *userdata1, void *userdata2) {
    (void)userdata1; (void)userdata2;
    if (status != WGPURequestAdapterStatus_Success) {
        fprintf(stderr, "Adapter request failed: %.*s\n",
                (int)message.length, message.data ? message.data : "");
        return;
    }
    g_adapter = adapter;
}

static void on_device(WGPURequestDeviceStatus status, WGPUDevice device,
                      WGPUStringView message,
                      void *userdata1, void *userdata2) {
    (void)userdata1; (void)userdata2;
    if (status != WGPURequestDeviceStatus_Success) {
        fprintf(stderr, "Device request failed: %.*s\n",
                (int)message.length, message.data ? message.data : "");
        return;
    }
    g_device = device;
}

static void on_mapped(WGPUMapAsyncStatus status, WGPUStringView message,
                      void *userdata1, void *userdata2) {
    (void)message; (void)userdata1; (void)userdata2;
    g_mapped = (status == WGPUMapAsyncStatus_Success);
}

static void on_device_error(WGPUDevice const *device, WGPUErrorType type,
                            WGPUStringView message, void *userdata1,
                            void *userdata2) {
    (void)device; (void)userdata1; (void)userdata2;
    fprintf(stderr, "Device error (%d): %.*s\n", (int)type,
            (int)message.length, message.data ? message.data : "");
}

/* ---- Read shader file ---- */

static char *read_file(const char *path, size_t *out_len) {
    FILE *f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "Cannot open %s\n", path); return NULL; }
    fseek(f, 0, SEEK_END);
    long len = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = (char *)malloc(len + 1);
    fread(buf, 1, len, f);
    buf[len] = '\0';
    fclose(f);
    if (out_len) *out_len = (size_t)len;
    return buf;
}

int main(void) {
    /* 1. Instance */
    WGPUInstance instance = wgpuCreateInstance(NULL);
    if (!instance) { fprintf(stderr, "Failed to create instance\n"); return 1; }

    /* 2. Adapter (headless — no compatible surface) */
    WGPURequestAdapterOptions adapter_opts = {0};
    adapter_opts.powerPreference = WGPUPowerPreference_HighPerformance;
    wgpuInstanceRequestAdapter(instance, &adapter_opts,
        (WGPURequestAdapterCallbackInfo){
            .callback = on_adapter,
        });
    if (!g_adapter) { fprintf(stderr, "No adapter\n"); return 1; }

    /* 3. Device */
    wgpuAdapterRequestDevice(g_adapter, NULL,
        (WGPURequestDeviceCallbackInfo){
            .callback = on_device,
        });
    if (!g_device) { fprintf(stderr, "No device\n"); return 1; }
    wgpuDeviceSetUncapturedErrorCallback(g_device,
        (WGPUUncapturedErrorCallbackInfo){
            .callback = on_device_error,
        });
    WGPUQueue queue = wgpuDeviceGetQueue(g_device);

    /* 4. Vertex buffer — same triangle as softrt */
    float vertices[] = {
         0.0f,  0.5f, 0.5f,   /* top */
        -0.5f, -0.5f, 0.5f,   /* bottom-left */
         0.5f, -0.5f, 0.5f,   /* bottom-right */
    };
    WGPUBufferDescriptor vb_desc = {0};
    vb_desc.size = sizeof(vertices);
    vb_desc.usage = WGPUBufferUsage_Vertex | WGPUBufferUsage_CopyDst;
    vb_desc.mappedAtCreation = false;
    WGPUBuffer vertex_buf = wgpuDeviceCreateBuffer(g_device, &vb_desc);
    wgpuQueueWriteBuffer(queue, vertex_buf, 0, vertices, sizeof(vertices));

    /* 5. Shader module */
    size_t wgsl_len = 0;
    char *wgsl_src = read_file("triangle.wgsl", &wgsl_len);
    if (!wgsl_src) { return 1; }

    WGPUShaderSourceWGSL wgsl_desc = {0};
    wgsl_desc.chain.sType = WGPUSType_ShaderSourceWGSL;
    wgsl_desc.code = (WGPUStringView){.data = wgsl_src, .length = wgsl_len};

    WGPUShaderModuleDescriptor sm_desc = {0};
    sm_desc.nextInChain = (WGPUChainedStruct *)&wgsl_desc;
    WGPUShaderModule shader = wgpuDeviceCreateShaderModule(g_device, &sm_desc);
    free(wgsl_src);

    /* 6. Render pipeline */
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
    frag_state.entryPoint = (WGPUStringView){.data = "fs_main", .length = WGPU_STRLEN};
    frag_state.targetCount = 1;
    frag_state.targets = &color_target;

    WGPURenderPipelineDescriptor pip_desc = {0};
    pip_desc.vertex.module = shader;
    pip_desc.vertex.entryPoint = (WGPUStringView){.data = "vs_main", .length = WGPU_STRLEN};
    pip_desc.vertex.bufferCount = 1;
    pip_desc.vertex.buffers = &vb_layout;
    pip_desc.fragment = &frag_state;
    pip_desc.primitive.topology = WGPUPrimitiveTopology_TriangleList;
    pip_desc.multisample.count = 1;
    pip_desc.multisample.mask = 0xFFFFFFFF;

    WGPURenderPipeline pipeline =
        wgpuDeviceCreateRenderPipeline(g_device, &pip_desc);

    /* 7. Render target texture */
    WGPUTextureDescriptor tex_desc = {0};
    tex_desc.size.width = WIDTH;
    tex_desc.size.height = HEIGHT;
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

    /* 8. Readback buffer */
    uint32_t bytes_per_row = ((WIDTH * 4 + 255) & ~255u); /* 256-byte aligned */
    uint32_t readback_size = bytes_per_row * HEIGHT;
    WGPUBufferDescriptor rb_desc = {0};
    rb_desc.size = readback_size;
    rb_desc.usage = WGPUBufferUsage_CopyDst | WGPUBufferUsage_MapRead;
    WGPUBuffer readback_buf = wgpuDeviceCreateBuffer(g_device, &rb_desc);

    /* 9. Render pass */
    WGPURenderPassColorAttachment ca = {0};
    ca.view = render_view;
    ca.loadOp = WGPULoadOp_Clear;
    ca.storeOp = WGPUStoreOp_Store;
    ca.clearValue = (WGPUColor){0.2, 0.2, 0.2, 1.0};

    WGPURenderPassDescriptor rp_desc = {0};
    rp_desc.colorAttachmentCount = 1;
    rp_desc.colorAttachments = &ca;

    WGPUCommandEncoder encoder =
        wgpuDeviceCreateCommandEncoder(g_device, NULL);
    WGPURenderPassEncoder pass =
        wgpuCommandEncoderBeginRenderPass(encoder, &rp_desc);
    wgpuRenderPassEncoderSetPipeline(pass, pipeline);
    wgpuRenderPassEncoderSetVertexBuffer(pass, 0, vertex_buf, 0,
                                         sizeof(vertices));
    wgpuRenderPassEncoderDraw(pass, 3, 1, 0, 0);
    wgpuRenderPassEncoderEnd(pass);
    wgpuRenderPassEncoderRelease(pass);

    /* 10. Copy texture to readback buffer */
    WGPUTexelCopyTextureInfo src = {0};
    src.texture = render_tex;
    src.mipLevel = 0;
    src.origin = (WGPUOrigin3D){0, 0, 0};
    src.aspect = WGPUTextureAspect_All;

    WGPUTexelCopyBufferInfo dst = {0};
    dst.buffer = readback_buf;
    dst.layout.offset = 0;
    dst.layout.bytesPerRow = bytes_per_row;
    dst.layout.rowsPerImage = HEIGHT;

    WGPUExtent3D copy_size = {WIDTH, HEIGHT, 1};
    wgpuCommandEncoderCopyTextureToBuffer(encoder, &src, &dst, &copy_size);

    /* 11. Submit */
    WGPUCommandBuffer cmd = wgpuCommandEncoderFinish(encoder, NULL);
    wgpuQueueSubmit(queue, 1, &cmd);
    wgpuCommandBufferRelease(cmd);
    wgpuCommandEncoderRelease(encoder);

    /* Poll to complete GPU work (wgpu-native extension) */
    wgpuDevicePoll(g_device, true, NULL);

    /* 12. Map readback buffer */
    wgpuBufferMapAsync(readback_buf, WGPUMapMode_Read, 0, readback_size,
        (WGPUBufferMapCallbackInfo){
            .callback = on_mapped,
        });
    wgpuDevicePoll(g_device, true, NULL);

    if (!g_mapped) {
        fprintf(stderr, "Buffer map failed\n");
        return 1;
    }

    /* 13. Read pixels and write BMP */
    const uint8_t *mapped =
        (const uint8_t *)wgpuBufferGetConstMappedRange(readback_buf, 0,
                                                        readback_size);
    /* Copy to tightly-packed RGBA (readback may have row padding) */
    uint8_t *pixels = (uint8_t *)malloc(WIDTH * HEIGHT * 4);
    for (uint32_t y = 0; y < HEIGHT; y++) {
        memcpy(pixels + y * WIDTH * 4, mapped + y * bytes_per_row, WIDTH * 4);
    }
    wgpuBufferUnmap(readback_buf);

    if (write_bmp("triangle_wgpu.bmp", WIDTH, HEIGHT, pixels)) {
        printf("Saved triangle_wgpu.bmp (%dx%d)\n", WIDTH, HEIGHT);
    } else {
        fprintf(stderr, "Failed to write BMP\n");
    }
    free(pixels);

    /* 14. Cleanup */
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
