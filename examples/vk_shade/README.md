# vk_shade — Vulkan compute shading of analytic primitives

A small demo of a **Vulkan compute shading backend** for LightRT. Scope is
deliberately narrow — *GPU shading evaluation only*, on analytic **spheres** and
**axis-aligned boxes** (no triangle BVH, no MaterialX node graph on the GPU).

It is the GPU counterpart to the CPU `mtlxrender` path tracer: the idea is that a
MaterialX node graph is evaluated **once per object on the CPU** to bake constant
OpenPBR parameters (base colour / metalness / roughness / emission), which are
then uploaded and shaded en masse on the GPU.

## What it does

- Uploads a handful of analytic primitives (`lrt_vk_shade_prim`) and a
  camera/lighting description (`lrt_vk_shade_desc`).
- Runs `vk/shaders/shade_analytic.comp`: one invocation per pixel casts a primary
  ray, intersects every primitive (linear scan), and forward-shades the closest
  hit with an **OpenPBR-core BSDF** — Lambert diffuse + GGX specular with
  metallic/dielectric Schlick Fresnel — lit by one directional **sun** (hard
  shadow ray / NEE) plus a 2-colour **hemisphere environment**: diffuse
  irradiance *and* a Fresnel-weighted specular reflection of the env in the
  roughness-blurred mirror direction (so metals show their tinted reflection).
  Anti-aliased with deterministic sub-pixel jitter.
- Reads back a linear RGBA image and writes a tonemapped **PPM**.
- Reports GPU vs (single-threaded) CPU **shading throughput** and speedup.

The host API lives in `lightrt_c_vk.h`:

```c
int lrt_vk_shade_analytic(lrt_vk_engine *e, const lrt_vk_shade_prim *prims,
                          uint32_t nprims, const lrt_vk_shade_desc *desc,
                          float *out_rgba, lrt_result *err);
```

It reuses the existing `lightrt_c_vk` engine (runtime `dlopen` of libvulkan via
`lightrt_vkew` — no Vulkan SDK headers, no link-time `-lvulkan`) and its
buffer/pipeline/dispatch helpers. The SPIR-V is checked in
(`vk/shaders/shade_analytic.spv.h`), so no shader toolchain is needed to build.

## Validation

The exact same shading math is reimplemented on the CPU in `vk_shade.c`
(`shade_cpu`, a byte-for-byte mirror of the GLSL) and the GPU image is compared
against it: the run **PASSES** when overall RMSE is low *and* ≥99% of pixels
agree within a per-channel tolerance. A small number of silhouette / shadow-edge
pixels legitimately differ because a sub-sample flips hit/miss between the GLSL
and C float paths (sub-ULP divergence in `sqrt`/`normalize`); those are expected.

## Build & run

```bash
# standalone (from this directory)
make run                       # -> ./vk_shade, writes vk_shade_{cpu,gpu}.ppm

# or via CMake (from the repo root)
cmake -S . -B build -DLIGHTRT_BUILD_VK=ON
cmake --build build --target lightrt_vk_shade
./build/lightrt_vk_shade --w 512 --h 384 --spp 4
```

If no Vulkan device/loader is present the program writes the CPU reference image,
prints a notice, and exits 0 (so GPU-less CI stays green). It is also registered
as the `lightrt_vk_shade` CTest case when `LIGHTRT_BUILD_VK=ON`.

### Performance

The demo uses the **resident-scene API** (`lrt_vk_shade_scene_build` /
`_render` / `_free`): the primitives are uploaded once and the device buffers +
descriptor set are reused across frames (it times an average of 30 renders, like
an animation loop). The output lives in `DEVICE_LOCAL` memory — the shader writes
it at full bandwidth instead of over PCIe to host-coherent memory — and is copied
to a host-visible staging buffer for readback in the same submission.

On an RTX 5060 Ti this sustains ≈9 Mpix/s, **9–20× the single-threaded CPU
reference** (the ratio grows with resolution / spp as the CPU cost rises). The
one-shot `lrt_vk_shade_analytic()` is simpler but re-allocates and uploads every
buffer per call (host-visible), so it is roughly half as fast for repeated
rendering — use the resident API in a loop.

## Regenerating the shader

Only needed after editing `vk/shaders/shade_analytic.comp`:

```bash
GLSLANG=/path/to/glslangValidator scripts/compile_shaders.sh
```
