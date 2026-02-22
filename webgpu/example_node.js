// example_node.js — Render a blue triangle to BMP using softrt WASM module
// Mirrors webgpu_example.cc

const createSoftRT = require('./softrt.js');

async function main() {
  const Module = await createSoftRT();

  // Mount real filesystem via NODEFS so saveBMP can write files
  Module.FS.mkdir('/work');
  Module.FS.mount(Module.FS.filesystems.NODEFS, { root: '.' }, '/work');

  // Create canvas (render target)
  const canvas = new Module.Canvas(640, 480);
  const adapter = Module.GPU.requestAdapter();
  const device = adapter.requestDevice();
  const queue = device.getQueue();

  // Configure canvas context
  const ctx = canvas.getContext();
  ctx.configure(device, Module.GPUTextureFormat.RGBA8Unorm);

  // Triangle vertices in clip space (x, y, z)
  const vertices = new Float32Array([
     0.0,  0.5, 0.5,   // top
    -0.5, -0.5, 0.5,   // bottom-left
     0.5, -0.5, 0.5,   // bottom-right
  ]);

  // Create vertex buffer and upload data
  const vb = device.createBuffer(
    vertices.byteLength,
    Module.GPUBufferUsage_VERTEX | Module.GPUBufferUsage_COPY_DST
  );
  // Copy vertex data into WASM heap and write to buffer
  const bytes = new Uint8Array(vertices.buffer, vertices.byteOffset, vertices.byteLength);
  const ptr = Module._malloc(bytes.byteLength);
  Module.HEAPU8.set(bytes, ptr);
  queue.writeBuffer_ptr(vb, 0, ptr, bytes.byteLength);
  Module._free(ptr);

  // Create shader module (stub)
  const shader = device.createShaderModule('/* stub */');

  // Create render pipeline via JS-object descriptor
  const pipeline = device.createRenderPipeline_js({
    vertex: {
      module: shader,
      buffers: [{
        arrayStride: 3 * 4,  // 3 floats × 4 bytes
        attributes: [{
          format: 'float32x3',
          offset: 0,
          shaderLocation: 0,
        }],
      }],
    },
    fragment: {
      module: shader,
    },
    primitive: {
      topology: 'triangle-list',
    },
    constantColor: [0.0, 0.6, 1.0, 1.0],  // blue
  });

  // Get render target view from canvas
  const targetTex = ctx.getCurrentTexture();
  const targetView = targetTex.createView();

  // Create command encoder and render pass via JS-object descriptor
  const encoder = device.createCommandEncoder();
  const pass = encoder.beginRenderPass_js({
    colorAttachments: [{
      view: targetView,
      loadOp: 'clear',
      storeOp: 'store',
      clearValue: { r: 0.2, g: 0.2, b: 0.2, a: 1.0 },
    }],
  });

  pass.setPipeline(pipeline);
  pass.setVertexBuffer(0, vb);
  pass.draw(3);
  pass.end();

  // Add pass to encoder and submit (triggers ray tracing)
  encoder.addPass(pass);
  queue.submit(encoder.finish());

  // Save result
  if (canvas.saveBMP('/work/triangle_wasm.bmp')) {
    console.log('Saved triangle_wasm.bmp (640x480)');
  } else {
    console.error('Failed to save triangle_wasm.bmp');
    process.exit(1);
  }

  // Clean up Embind objects
  pass.delete();
  canvas.delete();
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
