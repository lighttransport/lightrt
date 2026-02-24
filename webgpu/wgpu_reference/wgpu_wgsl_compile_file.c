/*
 * wgpu_wgsl_compile_file.c
 * Compile a WGSL shader file through wgpu-native.
 *
 * Notes:
 * - compute: validates by creating a compute pipeline.
 * - vertex: validates by creating a vertex-only render pipeline.
 * - fragment: validates shader-module creation (pipeline linkage is omitted
 *   to avoid false negatives from unknown vertex/fragment interface pairing).
 */
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <webgpu/webgpu.h>
#include <webgpu/wgpu.h>

typedef enum ShaderStage {
  STAGE_AUTO = 0,
  STAGE_COMPUTE,
  STAGE_VERTEX,
  STAGE_FRAGMENT,
} ShaderStage;

static WGPUAdapter g_adapter = NULL;
static WGPUDevice g_device = NULL;

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
  long len;
  char* buf;
  if (!f) {
    fprintf(stderr, "Cannot open %s\n", path);
    return NULL;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    fclose(f);
    return NULL;
  }
  len = ftell(f);
  if (len < 0) {
    fclose(f);
    return NULL;
  }
  if (fseek(f, 0, SEEK_SET) != 0) {
    fclose(f);
    return NULL;
  }
  buf = (char*)malloc((size_t)len + 1u);
  if (!buf) {
    fclose(f);
    return NULL;
  }
  if (fread(buf, 1, (size_t)len, f) != (size_t)len) {
    free(buf);
    fclose(f);
    return NULL;
  }
  buf[len] = '\0';
  fclose(f);
  if (out_len) *out_len = (size_t)len;
  return buf;
}

static ShaderStage parse_stage_arg(const char* s) {
  if (strcmp(s, "auto") == 0) return STAGE_AUTO;
  if (strcmp(s, "compute") == 0) return STAGE_COMPUTE;
  if (strcmp(s, "vertex") == 0) return STAGE_VERTEX;
  if (strcmp(s, "fragment") == 0) return STAGE_FRAGMENT;
  return STAGE_AUTO;
}

static ShaderStage detect_stage(const char* wgsl, ShaderStage requested) {
  if (requested != STAGE_AUTO) return requested;
  if (strstr(wgsl, "@compute")) return STAGE_COMPUTE;
  if (strstr(wgsl, "@vertex")) return STAGE_VERTEX;
  if (strstr(wgsl, "@fragment")) return STAGE_FRAGMENT;
  return STAGE_COMPUTE;
}

static int compile_compute_pipeline(WGPUDevice device, WGPUShaderModule module,
                                    const char* entry) {
  WGPUComputePipelineDescriptor cp_desc = {0};
  cp_desc.compute.module = module;
  cp_desc.compute.entryPoint =
      (WGPUStringView){.data = entry, .length = WGPU_STRLEN};
  WGPUComputePipeline pipeline = wgpuDeviceCreateComputePipeline(device, &cp_desc);
  if (!pipeline) {
    fprintf(stderr, "Failed to create compute pipeline\n");
    return 0;
  }
  wgpuComputePipelineRelease(pipeline);
  return 1;
}

static int compile_vertex_pipeline(WGPUDevice device, WGPUShaderModule module,
                                   const char* entry) {
  WGPURenderPipelineDescriptor rp_desc = {0};
  rp_desc.vertex.module = module;
  rp_desc.vertex.entryPoint =
      (WGPUStringView){.data = entry, .length = WGPU_STRLEN};
  rp_desc.primitive.topology = WGPUPrimitiveTopology_TriangleList;
  rp_desc.multisample.count = 1;
  rp_desc.multisample.mask = 0xFFFFFFFF;

  WGPURenderPipeline pipeline = wgpuDeviceCreateRenderPipeline(device, &rp_desc);
  if (!pipeline) {
    fprintf(stderr, "Failed to create vertex render pipeline\n");
    return 0;
  }
  wgpuRenderPipelineRelease(pipeline);
  return 1;
}

static void usage(const char* argv0) {
  fprintf(stderr,
          "Usage: %s --input <shader.wgsl> [--entry main] "
          "[--stage auto|compute|vertex|fragment]\n",
          argv0);
}

int main(int argc, char** argv) {
  const char* input_path = NULL;
  const char* entry = "main";
  const char* stage_arg = "auto";
  size_t wgsl_len = 0;
  char* wgsl_src = NULL;
  ShaderStage stage;

  int i;
  for (i = 1; i < argc; ++i) {
    if (strcmp(argv[i], "--input") == 0 && i + 1 < argc) {
      input_path = argv[++i];
    } else if (strcmp(argv[i], "--entry") == 0 && i + 1 < argc) {
      entry = argv[++i];
    } else if (strcmp(argv[i], "--stage") == 0 && i + 1 < argc) {
      stage_arg = argv[++i];
    } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
      usage(argv[0]);
      return 0;
    } else {
      fprintf(stderr, "Unknown argument: %s\n", argv[i]);
      usage(argv[0]);
      return 2;
    }
  }

  if (!input_path) {
    fprintf(stderr, "--input is required\n");
    usage(argv[0]);
    return 2;
  }

  wgsl_src = read_file(input_path, &wgsl_len);
  if (!wgsl_src) {
    fprintf(stderr, "Failed to read input: %s\n", input_path);
    return 2;
  }

  stage = detect_stage(wgsl_src, parse_stage_arg(stage_arg));

  {
    WGPUInstance instance = wgpuCreateInstance(NULL);
    WGPURequestAdapterOptions adapter_opts = {0};
    WGPUDeviceDescriptor device_desc = {0};
    WGPUQueue queue = NULL;
    WGPUShaderSourceWGSL wgsl_desc = {0};
    WGPUShaderModuleDescriptor sm_desc = {0};
    WGPUShaderModule shader = NULL;
    int ok = 0;

    if (!instance) {
      fprintf(stderr, "Failed to create instance\n");
      free(wgsl_src);
      return 1;
    }

    adapter_opts.powerPreference = WGPUPowerPreference_HighPerformance;
    wgpuInstanceRequestAdapter(instance, &adapter_opts,
                               (WGPURequestAdapterCallbackInfo){
                                   .callback = on_adapter,
                               });
    if (!g_adapter) {
      fprintf(stderr, "No adapter\n");
      wgpuInstanceRelease(instance);
      free(wgsl_src);
      return 1;
    }

    device_desc.uncapturedErrorCallbackInfo = (WGPUUncapturedErrorCallbackInfo){
        .callback = on_device_error,
    };
    wgpuAdapterRequestDevice(g_adapter, &device_desc,
                             (WGPURequestDeviceCallbackInfo){
                                 .callback = on_device,
                             });
    if (!g_device) {
      fprintf(stderr, "No device\n");
      wgpuAdapterRelease(g_adapter);
      wgpuInstanceRelease(instance);
      free(wgsl_src);
      return 1;
    }
    queue = wgpuDeviceGetQueue(g_device);

    wgsl_desc.chain.sType = WGPUSType_ShaderSourceWGSL;
    wgsl_desc.code = (WGPUStringView){.data = wgsl_src, .length = wgsl_len};
    sm_desc.nextInChain = (WGPUChainedStruct*)&wgsl_desc;
    shader = wgpuDeviceCreateShaderModule(g_device, &sm_desc);

    if (!shader) {
      fprintf(stderr, "Failed to create shader module\n");
      ok = 0;
    } else if (stage == STAGE_COMPUTE) {
      ok = compile_compute_pipeline(g_device, shader, entry);
    } else if (stage == STAGE_VERTEX) {
      ok = compile_vertex_pipeline(g_device, shader, entry);
    } else {
      /* Fragment path: module validation only (linkage may need matching VS). */
      ok = 1;
    }

    /* Process pending validation callbacks. */
    wgpuDevicePoll(g_device, true, NULL);

    if (shader) wgpuShaderModuleRelease(shader);
    if (queue) wgpuQueueRelease(queue);
    wgpuDeviceRelease(g_device);
    wgpuAdapterRelease(g_adapter);
    wgpuInstanceRelease(instance);
    free(wgsl_src);

    if (!ok) {
      return 1;
    }
  }

  printf("OK: %s entry=%s stage=%s\n", input_path, entry, stage_arg);
  return 0;
}
