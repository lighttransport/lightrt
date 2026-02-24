/*
 * windowed_triangle.c — Render a blue triangle in a GLFW window using
 * wgpu-native.  Same geometry and colors as the softrt example.
 *
 * Targets the current webgpu-headers API (WGPUStringView, CallbackInfo
 * structs, WGPUShaderSourceWGSL, etc.) as shipped by WebGPU-distribution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <webgpu/webgpu.h>
#include <GLFW/glfw3.h>
#include <glfw3webgpu.h>

#define WIDTH  640
#define HEIGHT 480

/* ---- Async callback helpers ---- */

static WGPUAdapter g_adapter = NULL;
static WGPUDevice  g_device  = NULL;

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
    /* 1. GLFW window */
    if (!glfwInit()) { fprintf(stderr, "GLFW init failed\n"); return 1; }
    glfwWindowHint(GLFW_CLIENT_API, GLFW_NO_API);
    glfwWindowHint(GLFW_RESIZABLE, GLFW_FALSE);
    GLFWwindow *window = glfwCreateWindow(WIDTH, HEIGHT,
                                          "wgpu-native triangle", NULL, NULL);
    if (!window) { fprintf(stderr, "Window creation failed\n"); return 1; }

    /* 2. Instance + surface */
    WGPUInstance instance = wgpuCreateInstance(NULL);
    if (!instance) { fprintf(stderr, "Failed to create instance\n"); return 1; }
    WGPUSurface surface = glfwCreateWindowWGPUSurface(instance, window);

    /* 3. Adapter (compatible with surface) */
    WGPURequestAdapterOptions adapter_opts = {0};
    adapter_opts.compatibleSurface = surface;
    adapter_opts.powerPreference = WGPUPowerPreference_HighPerformance;
    wgpuInstanceRequestAdapter(instance, &adapter_opts,
        (WGPURequestAdapterCallbackInfo){
            .callback = on_adapter,
        });
    if (!g_adapter) { fprintf(stderr, "No adapter\n"); return 1; }

    /* 4. Device */
    WGPUDeviceDescriptor device_desc = {0};
    device_desc.uncapturedErrorCallbackInfo =
        (WGPUUncapturedErrorCallbackInfo){
            .callback = on_device_error,
        };
    wgpuAdapterRequestDevice(g_adapter, &device_desc,
        (WGPURequestDeviceCallbackInfo){
            .callback = on_device,
        });
    if (!g_device) { fprintf(stderr, "No device\n"); return 1; }
    WGPUQueue queue = wgpuDeviceGetQueue(g_device);

    /* 5. Configure surface */
    WGPUSurfaceCapabilities caps = {0};
    wgpuSurfaceGetCapabilities(surface, g_adapter, &caps);
    WGPUTextureFormat surface_format = caps.formats[0];

    WGPUSurfaceConfiguration surf_config = {0};
    surf_config.device = g_device;
    surf_config.format = surface_format;
    surf_config.usage = WGPUTextureUsage_RenderAttachment;
    surf_config.width = WIDTH;
    surf_config.height = HEIGHT;
    surf_config.presentMode = WGPUPresentMode_Fifo;
    surf_config.alphaMode = caps.alphaModes[0];
    wgpuSurfaceConfigure(surface, &surf_config);
    wgpuSurfaceCapabilitiesFreeMembers(caps);

    /* 6. Vertex buffer */
    float vertices[] = {
         0.0f,  0.5f, 0.5f,
        -0.5f, -0.5f, 0.5f,
         0.5f, -0.5f, 0.5f,
    };
    WGPUBufferDescriptor vb_desc = {0};
    vb_desc.size = sizeof(vertices);
    vb_desc.usage = WGPUBufferUsage_Vertex | WGPUBufferUsage_CopyDst;
    WGPUBuffer vertex_buf = wgpuDeviceCreateBuffer(g_device, &vb_desc);
    wgpuQueueWriteBuffer(queue, vertex_buf, 0, vertices, sizeof(vertices));

    /* 7. Shader module */
    size_t wgsl_len = 0;
    char *wgsl_src = read_file("triangle.wgsl", &wgsl_len);
    if (!wgsl_src) return 1;

    WGPUShaderSourceWGSL wgsl_desc = {0};
    wgsl_desc.chain.sType = WGPUSType_ShaderSourceWGSL;
    wgsl_desc.code = (WGPUStringView){.data = wgsl_src, .length = wgsl_len};

    WGPUShaderModuleDescriptor sm_desc = {0};
    sm_desc.nextInChain = (WGPUChainedStruct *)&wgsl_desc;
    WGPUShaderModule shader = wgpuDeviceCreateShaderModule(g_device, &sm_desc);
    free(wgsl_src);

    /* 8. Render pipeline */
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
    color_target.format = surface_format;
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

    /* 9. Main loop */
    while (!glfwWindowShouldClose(window)) {
        glfwPollEvents();

        /* Get current surface texture */
        WGPUSurfaceTexture surf_tex = {0};
        wgpuSurfaceGetCurrentTexture(surface, &surf_tex);
        if (surf_tex.status != WGPUSurfaceGetCurrentTextureStatus_SuccessOptimal &&
            surf_tex.status != WGPUSurfaceGetCurrentTextureStatus_SuccessSuboptimal) {
            fprintf(stderr, "Failed to get surface texture (status=%d)\n",
                    (int)surf_tex.status);
            break;
        }

        WGPUTextureViewDescriptor tv_desc = {0};
        tv_desc.format = surface_format;
        tv_desc.dimension = WGPUTextureViewDimension_2D;
        tv_desc.mipLevelCount = 1;
        tv_desc.arrayLayerCount = 1;
        WGPUTextureView view = wgpuTextureCreateView(surf_tex.texture, &tv_desc);

        /* Render pass */
        WGPURenderPassColorAttachment ca = {0};
        ca.view = view;
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

        WGPUCommandBuffer cmd = wgpuCommandEncoderFinish(encoder, NULL);
        wgpuQueueSubmit(queue, 1, &cmd);
        wgpuCommandBufferRelease(cmd);
        wgpuCommandEncoderRelease(encoder);

        /* Present */
        wgpuSurfacePresent(surface);
        wgpuTextureViewRelease(view);
        wgpuTextureRelease(surf_tex.texture);
    }

    /* 10. Cleanup */
    wgpuRenderPipelineRelease(pipeline);
    wgpuShaderModuleRelease(shader);
    wgpuBufferRelease(vertex_buf);
    wgpuQueueRelease(queue);
    wgpuSurfaceUnconfigure(surface);
    wgpuSurfaceRelease(surface);
    wgpuDeviceRelease(g_device);
    wgpuAdapterRelease(g_adapter);
    wgpuInstanceRelease(instance);
    glfwDestroyWindow(window);
    glfwTerminate();

    return 0;
}
