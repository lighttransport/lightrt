#define TINYOBJLOADER_IMPLEMENTATION
#define TINYGLTF_IMPLEMENTATION
#define STB_IMAGE_IMPLEMENTATION
#define STB_IMAGE_WRITE_IMPLEMENTATION
#define TINYGLTF_NO_INCLUDE_STB_IMAGE
#define TINYGLTF_NO_INCLUDE_STB_IMAGE_WRITE
#define TINYGLTF_NO_INCLUDE_JSON

#include "third_party/json.hpp"
#include "third_party/stb_image.h"
#include "third_party/stb_image_write.h"
#include "third_party/tiny_obj_loader.h"
#include "third_party/tiny_gltf.h"

#include "viewer_common.h"

#include <iostream>
#include <thread>
#include <algorithm>
#include <cmath>
#include <cstring>
#include <random>

#include "common/sss_render.hh"

namespace lightrt_viewer {

static constexpr float kPi = lightrt_common::shading::kPi;

// Component-wise Vec3 multiply (Vec3 only has operator*(float))
static Vec3 vmul(const Vec3& a, const Vec3& b) {
    return Vec3(a.x * b.x, a.y * b.y, a.z * b.z);
}

// --- Color helpers ---

static Vec3 hashColor(const std::string& name) {
    uint32_t h = 5381;
    for (char c : name) h = h * 33 + (uint32_t)(unsigned char)c;
    float r = 0.3f + 0.5f * ((h & 0xFF) / 255.0f);
    float g = 0.3f + 0.5f * (((h >> 8) & 0xFF) / 255.0f);
    float b = 0.3f + 0.5f * (((h >> 16) & 0xFF) / 255.0f);
    return Vec3(r, g, b);
}

// --- Scene helpers ---

// Add a mesh (triangles + base color) to a scene::Scene with identity transform.
static void addMeshToScene(scene::Scene& sc,
                            std::vector<Triangle> tris,
                            Vec3 color) {
    if (tris.empty()) return;

    // Material
    int32_t mat_id = (int32_t)sc.materials.size();
    scene::MaterialData mat;
    mat.base_color = color;
    sc.materials.push_back(mat);

    // MeshBLAS
    uint32_t mesh_id = (uint32_t)sc.meshes.size();
    sc.meshes.emplace_back();
    auto& blas = sc.meshes.back();
    blas.default_material_id = mat_id;
    for (const auto& tri : tris) {
        blas.local_bounds.expand(tri.v0);
        blas.local_bounds.expand(tri.v1);
        blas.local_bounds.expand(tri.v2);
    }
    lightrt::BVHBuildConfig cfg;
    blas.bvh.build(tris, cfg);

    // Instance (identity transform)
    sc.instances.emplace_back();
    auto& inst = sc.instances.back();
    inst.mesh_id = mesh_id;
    const float id[12] = {1,0,0,0, 0,1,0,0, 0,0,1,0};
    std::memcpy(inst.transform,           id, sizeof(id));
    std::memcpy(inst.inv_transform,       id, sizeof(id));
    std::memcpy(inst.transform_close,     id, sizeof(id));
    std::memcpy(inst.inv_transform_close, id, sizeof(id));
    inst.world_bounds = blas.local_bounds;

    sc.scene_bounds.expand(inst.world_bounds);
}

// Resolve material for a hit (inline, shared with SSS path)
static const scene::MaterialData& resolveMaterial(const scene::Scene& scene,
                                                   const scene::HitInfo& hit) {
  static const scene::MaterialData kDefaultMat;
  if (hit.instance_id == lightrt::kInvalidIndex) return kDefaultMat;
  const auto& mesh = scene.meshes[scene.instances[hit.instance_id].mesh_id];
  if (hit.triangle_id < mesh.tri_material_ids.size()) {
    int32_t mat_id = mesh.tri_material_ids[hit.triangle_id];
    if (mat_id >= 0 && static_cast<size_t>(mat_id) < scene.materials.size())
      return scene.materials[static_cast<size_t>(mat_id)];
  }
  if (mesh.default_material_id >= 0 &&
      static_cast<size_t>(mesh.default_material_id) < scene.materials.size())
    return scene.materials[static_cast<size_t>(mesh.default_material_id)];
  return kDefaultMat;
}

// Return the diffuse albedo for a scene hit.
static Vec3 getHitAlbedo(const scene::Scene& sc, const scene::HitInfo& hit) {
    const auto& blas = sc.meshes[sc.instances[hit.instance_id].mesh_id];
    int32_t mat_id = blas.default_material_id;
    if (hit.triangle_id < (uint32_t)blas.tri_material_ids.size())
        mat_id = blas.tri_material_ids[hit.triangle_id];
    if (mat_id >= 0 && mat_id < (int32_t)sc.materials.size())
        return sc.materials[mat_id].base_color;
    return hashColor(std::to_string(hit.instance_id));
}

// --- Model Loading ---

bool LoadOBJ(const std::string& filename, scene::Scene& sc) {
    tinyobj::attrib_t attrib;
    std::vector<tinyobj::shape_t> shapes;
    std::vector<tinyobj::material_t> materials;
    std::string warn, err;

    if (!tinyobj::LoadObj(&attrib, &shapes, &materials, &warn, &err, filename.c_str())) {
        std::cerr << "TinyObj Error: " << warn << err << "\n";
        return false;
    }

    for (const auto& shape : shapes) {
        std::string name = shape.name.empty() ? "mesh" : shape.name;
        Vec3 color = hashColor(name);

        std::vector<Triangle> tris;
        size_t index_offset = 0;
        for (size_t f = 0; f < shape.mesh.num_face_vertices.size(); f++) {
            int fv = shape.mesh.num_face_vertices[f];
            if (fv == 3) {
                tinyobj::index_t idx0 = shape.mesh.indices[index_offset + 0];
                tinyobj::index_t idx1 = shape.mesh.indices[index_offset + 1];
                tinyobj::index_t idx2 = shape.mesh.indices[index_offset + 2];

                Triangle tri;
                tri.v0 = Vec3(attrib.vertices[3*idx0.vertex_index+0], attrib.vertices[3*idx0.vertex_index+1], attrib.vertices[3*idx0.vertex_index+2]);
                tri.v1 = Vec3(attrib.vertices[3*idx1.vertex_index+0], attrib.vertices[3*idx1.vertex_index+1], attrib.vertices[3*idx1.vertex_index+2]);
                tri.v2 = Vec3(attrib.vertices[3*idx2.vertex_index+0], attrib.vertices[3*idx2.vertex_index+1], attrib.vertices[3*idx2.vertex_index+2]);
                tris.push_back(tri);
            }
            index_offset += fv;
        }

        addMeshToScene(sc, std::move(tris), color);
    }
    return true;
}

bool LoadGLTF(const std::string& filename, scene::Scene& sc) {
    tinygltf::Model model;
    tinygltf::TinyGLTF loader;
    std::string err, warn;

    bool ret;
    if (filename.find(".glb") != std::string::npos) {
         ret = loader.LoadBinaryFromFile(&model, &err, &warn, filename);
    } else {
         ret = loader.LoadASCIIFromFile(&model, &err, &warn, filename);
    }

    if (!warn.empty()) std::cout << "GLTF Warn: " << warn << "\n";
    if (!err.empty()) std::cout << "GLTF Err: " << err << "\n";
    if (!ret) return false;

    for (size_t mi = 0; mi < model.meshes.size(); ++mi) {
        const auto& gltfMesh = model.meshes[mi];
        for (size_t pi = 0; pi < gltfMesh.primitives.size(); ++pi) {
            const auto& primitive = gltfMesh.primitives[pi];

            std::string name = gltfMesh.name.empty() ? ("mesh_" + std::to_string(mi)) : gltfMesh.name;
            if (gltfMesh.primitives.size() > 1)
                name += "_prim" + std::to_string(pi);
            Vec3 color = hashColor(name);

            const float* positionBuffer = nullptr;
            const unsigned char* indexBuffer = nullptr;
            int posStride = 0;
            int idxType = 0;
            size_t indexCount = 0;

            auto it = primitive.attributes.find("POSITION");
            if (it != primitive.attributes.end()) {
                const auto& accessor = model.accessors[it->second];
                const auto& view = model.bufferViews[accessor.bufferView];
                positionBuffer = reinterpret_cast<const float*>(&model.buffers[view.buffer].data[accessor.byteOffset + view.byteOffset]);
                posStride = accessor.ByteStride(view) / sizeof(float);
            }

            if (primitive.indices >= 0) {
                const auto& accessor = model.accessors[primitive.indices];
                const auto& view = model.bufferViews[accessor.bufferView];
                indexBuffer = &model.buffers[view.buffer].data[accessor.byteOffset + view.byteOffset];
                idxType = accessor.componentType;
                indexCount = accessor.count;
            }

            std::vector<Triangle> tris;
            if (positionBuffer && indexCount > 0) {
                for (size_t i = 0; i < indexCount; i += 3) {
                    uint32_t i0 = 0, i1 = 0, i2 = 0;
                    if (idxType == TINYGLTF_COMPONENT_TYPE_UNSIGNED_SHORT) {
                        const uint16_t* buf = (const uint16_t*)indexBuffer;
                        i0 = buf[i]; i1 = buf[i+1]; i2 = buf[i+2];
                    } else if (idxType == TINYGLTF_COMPONENT_TYPE_UNSIGNED_INT) {
                        const uint32_t* buf = (const uint32_t*)indexBuffer;
                        i0 = buf[i]; i1 = buf[i+1]; i2 = buf[i+2];
                    } else if (idxType == TINYGLTF_COMPONENT_TYPE_UNSIGNED_BYTE) {
                        const uint8_t* buf = (const uint8_t*)indexBuffer;
                        i0 = buf[i]; i1 = buf[i+1]; i2 = buf[i+2];
                    }

                    Triangle tri;
                    tri.v0 = Vec3(positionBuffer[i0*posStride], positionBuffer[i0*posStride+1], positionBuffer[i0*posStride+2]);
                    tri.v1 = Vec3(positionBuffer[i1*posStride], positionBuffer[i1*posStride+1], positionBuffer[i1*posStride+2]);
                    tri.v2 = Vec3(positionBuffer[i2*posStride], positionBuffer[i2*posStride+1], positionBuffer[i2*posStride+2]);
                    tris.push_back(tri);
                }
            }

            addMeshToScene(sc, std::move(tris), color);
        }
    }
    return true;
}

static bool hasExtension(const std::string& filename, const std::string& ext) {
    if (filename.size() < ext.size()) return false;
    std::string lower;
    lower.reserve(ext.size());
    for (size_t i = filename.size() - ext.size(); i < filename.size(); i++) {
        lower.push_back(static_cast<char>(std::tolower(static_cast<unsigned char>(filename[i]))));
    }
    return lower == ext;
}

bool LoadModel(const std::string& filename, scene::Scene& sc) {
    if (hasExtension(filename, ".obj")) {
        return LoadOBJ(filename, sc);
    }
    if (hasExtension(filename, ".usd")  || hasExtension(filename, ".usda") ||
        hasExtension(filename, ".usdc") || hasExtension(filename, ".usdz")) {
        // Delegate to common USD loader (tinyusdz or lightusd-c backend)
        return lightrt_common::loadUSDScene(filename, -1e30, sc);
    }
    return LoadGLTF(filename, sc);
}

// --- Camera ---

void UpdateCameraFromOrbit(Camera& cam) {
    float yawRad = cam.yaw * kPi / 180.0f;
    float pitchRad = cam.pitch * kPi / 180.0f;

    float cosPitch = cosf(pitchRad);
    Vec3 offset;
    offset.x = cosf(yawRad) * cosPitch;
    offset.y = sinf(pitchRad);
    offset.z = sinf(yawRad) * cosPitch;

    cam.position = cam.orbitCenter + offset * cam.orbitDistance;
    cam.forward = (cam.orbitCenter - cam.position).normalize();
    cam.right = cam.forward.cross(Vec3(0, 1, 0)).normalize();
    cam.up = cam.right.cross(cam.forward).normalize();
}

void FitToScene(ViewerState& state) {
    const AABB& bounds = state.scene.scene_bounds;
    Vec3 ext = bounds.extents();
    if (ext.length() < 1e-6f) return;

    Vec3 center = bounds.center();
    float radius = ext.length() * 0.5f;

    state.camera.orbitCenter = center;
    float halfFovRad = state.camera.fov * 0.5f * kPi / 180.0f;
    state.camera.orbitDistance = radius * 1.2f / tanf(halfFovRad);
    state.camera.yaw = 90.0f;
    state.camera.pitch = 25.0f;
    UpdateCameraFromOrbit(state.camera);
    state.cameraDirty = true;
}

void OrbitCamera(ViewerState& state, float dx, float dy) {
    float sensitivity = 0.25f;
    state.camera.yaw += dx * sensitivity;
    state.camera.pitch += dy * sensitivity;
    if (state.camera.pitch > 89.0f) state.camera.pitch = 89.0f;
    if (state.camera.pitch < -89.0f) state.camera.pitch = -89.0f;
    UpdateCameraFromOrbit(state.camera);
    state.cameraDirty = true;
}

void PanCamera(ViewerState& state, float dx, float dy) {
    float scale = state.camera.orbitDistance * 0.002f;
    state.camera.orbitCenter = state.camera.orbitCenter - state.camera.right * (dx * scale) + state.camera.up * (dy * scale);
    UpdateCameraFromOrbit(state.camera);
    state.cameraDirty = true;
}

void DollyCamera(ViewerState& state, float delta) {
    float speed = state.camera.orbitDistance * 0.005f;
    state.camera.orbitDistance -= delta * speed;
    if (state.camera.orbitDistance < 0.01f) state.camera.orbitDistance = 0.01f;
    UpdateCameraFromOrbit(state.camera);
    state.cameraDirty = true;
}

void OnMouseDown(ViewerState& state, double x, double y) {
    state.lastX = x;
    state.lastY = y;
    state.dragging = true;
}

void OnMouseDrag(ViewerState& state, double x, double y) {
    if (!state.dragging) return;

    float dx = (float)(x - state.lastX);
    float dy = (float)(y - state.lastY);
    state.lastX = x;
    state.lastY = y;

    bool wantOrbit = (state.altPressed && state.lmbPressed) ||
                     (state.shiftPressed && !state.ctrlPressed && !state.tabPressed && state.lmbPressed);
    bool wantPan   = (state.altPressed && state.mmbPressed) ||
                     (state.ctrlPressed && !state.shiftPressed && !state.tabPressed && state.lmbPressed);
    bool wantDolly = (state.altPressed && state.rmbPressed) ||
                     (state.ctrlPressed && state.shiftPressed && state.lmbPressed) ||
                     (state.tabPressed && state.lmbPressed);

    if (wantOrbit) {
        OrbitCamera(state, dx, dy);
    } else if (wantPan) {
        PanCamera(state, dx, dy);
    } else if (wantDolly) {
        DollyCamera(state, dx);
    }
}

// --- Input Processing ---

bool ProcessInput(ViewerState& state, float /*dt*/) {
    if (state.keys[KEY_ESCAPE]) return true;

    bool fKeyPressed = state.keys[KEY_F];
    if (fKeyPressed && !state.fKeyWasPressed) {
        state.framelessMode = !state.framelessMode;
        std::cout << "Frameless: " << (state.framelessMode ? "ON" : "OFF") << "\n";
    }
    state.fKeyWasPressed = fKeyPressed;

    bool rKeyPressed = state.keys[KEY_R];
    if (rKeyPressed && !state.rKeyWasPressed) {
        FitToScene(state);
    }
    state.rKeyWasPressed = rKeyPressed;

    bool sKeyPressed = state.keys[KEY_S];
    if (sKeyPressed && !state.sKeyWasPressed) {
        state.shadowMode = (ShadowMode)(((int)state.shadowMode + 1) % SHADOW_MODE_COUNT);
        state.cameraDirty = true;
    }
    state.sKeyWasPressed = sKeyPressed;

    bool plusKeyPressed = state.keys[KEY_PLUS];
    if (plusKeyPressed && !state.plusKeyWasPressed) {
        state.fontScale = (state.fontScale == 1) ? 2 : 1;
    }
    state.plusKeyWasPressed = plusKeyPressed;

    return false;
}

// --- Sun/Sky ---

Vec3 SampleSky(const Vec3& dir, const Vec3& sun_dir) {
    if (dir.y < 0.0f) {
        return Vec3(0.3f, 0.25f, 0.2f);
    }

    float t = sqrtf(std::max(0.0f, dir.y));
    Vec3 horizon(0.7f, 0.8f, 1.0f);
    Vec3 zenith(0.3f, 0.5f, 0.9f);
    Vec3 sky = horizon * (1.0f - t) + zenith * t;

    float sun_dot = dir.dot(sun_dir);
    if (sun_dot > 0.9995f) {
        sky = Vec3(3.0f, 2.8f, 2.5f);
    } else if (sun_dot > 0.99f) {
        float glow = (sun_dot - 0.99f) / (0.9995f - 0.99f);
        glow = glow * glow;
        sky = sky + Vec3(1.0f, 0.9f, 0.7f) * glow;
    }

    return sky;
}

// --- Path Tracing ---

static uint32_t pcg_hash(uint32_t input) {
    uint32_t state = input * 747796405u + 2891336453u;
    uint32_t word = ((state >> ((state >> 28u) + 4u)) ^ state) * 277803737u;
    return (word >> 22u) ^ word;
}

static float rand_float(uint32_t& seed) {
    seed = pcg_hash(seed);
    return (float)(seed & 0xFFFFFFu) / (float)0x1000000u;
}

static Vec3 cosine_hemisphere(float u1, float u2, const Vec3& normal) {
    return lightrt_common::shading::cosineHemisphere(u1, u2, normal);
}

static Vec3 jitter_direction(const Vec3& dir, float half_angle, uint32_t& seed) {
    float u1 = rand_float(seed);
    float u2 = rand_float(seed);
    float cos_max = cosf(half_angle);
    float cos_theta = 1.0f - u1 * (1.0f - cos_max);
    float sin_theta = sqrtf(std::max(0.0f, 1.0f - cos_theta * cos_theta));
    float phi = 2.0f * kPi * u2;

    Vec3 tangent;
    if (fabsf(dir.x) > 0.9f)
        tangent = Vec3(0, 1, 0).cross(dir).normalize();
    else
        tangent = Vec3(1, 0, 0).cross(dir).normalize();
    Vec3 bitangent = dir.cross(tangent);

    return (tangent * (sin_theta * cosf(phi)) +
            bitangent * (sin_theta * sinf(phi)) +
            dir * cos_theta).normalize();
}

// Get world-space normal for a scene hit
static Vec3 getHitNormal(const scene::Scene& sc, const scene::HitInfo& hit) {
    const auto& inst = sc.instances[hit.instance_id];
    const Triangle& tri = sc.meshes[inst.mesh_id].bvh.getTriangles()[hit.triangle_id];
    Vec3 local_n = tri.normal();
    return scene::transformNormal(inst.inv_transform, local_n).normalize();
}

void PathTrace(ViewerState& state) {
    int width = (int)state.width;
    int height = (int)state.height;

    if (state.cameraDirty) {
        std::fill(state.accumBuffer.begin(), state.accumBuffer.end(), 0.0f);
        state.sampleCount = 0;
        state.cameraDirty = false;
    }

    float invWidth = 1.0f / width;
    float invHeight = 1.0f / height;
    float aspectRatio = (float)width / height;
    float scale = tanf(state.camera.fov * 0.5f * kPi / 180.0f);

    uint32_t sampleIdx = state.sampleCount;
    Vec3 sunDir = state.sunDirection;
    ShadowMode shadowMode = state.shadowMode;

    float shadowConeAngle = 0.0f;
    if (shadowMode == SHADOW_SOFT) shadowConeAngle = 0.035f;
    else if (shadowMode == SHADOW_STRONG_SOFT) shadowConeAngle = 0.087f;

    int num_threads = std::max(1, (int)std::thread::hardware_concurrency());
    std::vector<std::thread> threads;
    int rows_per_thread = height / num_threads;

    for (int t = 0; t < num_threads; ++t) {
        threads.emplace_back([&, t, sampleIdx, sunDir, shadowMode, shadowConeAngle]() {
            int start_y = t * rows_per_thread;
            int end_y = (t == num_threads - 1) ? height : (t + 1) * rows_per_thread;

            for (int y = start_y; y < end_y; ++y) {
                for (int x = 0; x < width; ++x) {
                    uint32_t seed = pcg_hash((uint32_t)x + (uint32_t)y * 65537u + sampleIdx * 1000003u);

                    float jx = rand_float(seed);
                    float jy = rand_float(seed);

                    float px = (2.0f * (x + jx) * invWidth - 1.0f) * aspectRatio * scale;
                    float py = (1.0f - 2.0f * (y + jy) * invHeight) * scale;

                    Vec3 dir = (state.camera.forward + state.camera.right * px + state.camera.up * py).normalize();
                    Ray ray(state.camera.position, dir);

                    scene::HitInfo hit = scene::traceScene(state.scene, ray);

                    Vec3 color(0, 0, 0);

                    if (hit.instance_id == kInvalidIndex) {
                        color = SampleSky(dir, sunDir);
                    } else {
                        Vec3 normal = getHitNormal(state.scene, hit);
                        if (normal.dot(dir) > 0.0f) normal = normal * -1.0f;

                        Vec3 hitPos = ray.at(hit.t);
                        Vec3 albedo = getHitAlbedo(state.scene, hit);

                        // Direct lighting (with optional soft shadow)
                        Vec3 shadowDir = sunDir;
                        if (shadowConeAngle > 0.0f)
                            shadowDir = jitter_direction(sunDir, shadowConeAngle, seed);

                        float NdotL = std::max(0.0f, normal.dot(shadowDir));
                        float directLight = 0.0f;
                        if (NdotL > 0.0f) {
                            bool occluded = false;
                            if (shadowMode != SHADOW_OFF) {
                                Ray shadowRay(hitPos + normal * 0.001f, shadowDir, 0.0f, 1e10f);
                                occluded = scene::traceSceneAnyHit(state.scene, shadowRay,
                                                                   hit.instance_id, hit.triangle_id);
                            }
                            if (!occluded) {
                                directLight = NdotL;
                            }
                        }

                        Vec3 sunColor(1.5f, 1.4f, 1.2f);
                        Vec3 direct = sunColor * directLight;
                        Vec3 ambient = SampleSky(normal, sunDir) * 0.15f;

                        // Subsurface scattering (random walk)
                        Vec3 sss_contrib(0, 0, 0);
                        float sss_weight = 0.0f;
                        {
                          const auto& mat = resolveMaterial(state.scene, hit);
                          sss_weight = mat.subsurface_weight - 1e-4f;
                          if (sss_weight > 0.0f) {
                            std::mt19937 sss_rng(seed);
                            std::uniform_real_distribution<float> sss_dist;
                            auto sss_r = lightrt_common::sss_render::randomWalkSSS(
                                state.scene, hitPos, normal, hit.instance_id, mat,
                                sss_rng, sss_dist);
                            if (sss_r.success) {
                              float exit_NdotL = std::max(0.0f, sss_r.exit_normal.dot(shadowDir));
                              float exit_direct = 0.0f;
                              if (exit_NdotL > 0.0f && shadowMode != SHADOW_OFF) {
                                Ray exit_shadow(sss_r.exit_pos + sss_r.exit_normal * 0.001f,
                                                shadowDir, 0.0f, 1e10f);
                                if (!scene::traceSceneAnyHit(state.scene, exit_shadow,
                                      sss_r.exit_instance_id, sss_r.exit_triangle_id))
                                  exit_direct = exit_NdotL;
                              } else if (exit_NdotL > 0.0f) {
                                exit_direct = exit_NdotL;
                              }
                              Vec3 exit_sun = sunColor * exit_direct;
                              Vec3 exit_ambient = SampleSky(sss_r.exit_normal, sunDir) * 0.15f;
                              sss_contrib = Vec3(
                                (exit_sun.x + exit_ambient.x) * mat.base_color.x * sss_r.throughput.x,
                                (exit_sun.y + exit_ambient.y) * mat.base_color.y * sss_r.throughput.y,
                                (exit_sun.z + exit_ambient.z) * mat.base_color.z * sss_r.throughput.z);
                            }
                          }
                        }

                        // Indirect (1 bounce)
                        Vec3 indirect(0, 0, 0);
                        {
                            float u1 = rand_float(seed);
                            float u2 = rand_float(seed);
                            Vec3 bounceDir = cosine_hemisphere(u1, u2, normal);
                            Ray bounceRay(hitPos + normal * 0.001f, bounceDir);

                            scene::HitInfo bhit = scene::traceScene(state.scene, bounceRay);

                            if (bhit.instance_id == kInvalidIndex) {
                                indirect = SampleSky(bounceDir, sunDir);
                            } else {
                                Vec3 bnorm = getHitNormal(state.scene, bhit);
                                if (bnorm.dot(bounceDir) > 0.0f) bnorm = bnorm * -1.0f;

                                Vec3 bHitPos = bounceRay.at(bhit.t);
                                Vec3 bShadowDir = sunDir;
                                if (shadowConeAngle > 0.0f)
                                    bShadowDir = jitter_direction(sunDir, shadowConeAngle, seed);

                                float bNdotL = std::max(0.0f, bnorm.dot(bShadowDir));
                                float bDirect = 0.0f;
                                if (bNdotL > 0.0f) {
                                    bool bOcc = false;
                                    if (shadowMode != SHADOW_OFF) {
                                        Ray bShadow(bHitPos + bnorm * 0.001f, bShadowDir, 0.0f, 1e10f);
                                        bOcc = scene::traceSceneAnyHit(state.scene, bShadow,
                                                                       bhit.instance_id, bhit.triangle_id);
                                    }
                                    if (!bOcc) bDirect = bNdotL;
                                }
                                Vec3 bAlbedo = getHitAlbedo(state.scene, bhit);
                                Vec3 bAmbient = SampleSky(bnorm, sunDir) * 0.15f;
                                indirect = vmul(sunColor * bDirect + bAmbient, bAlbedo);
                            }
                        }

                        float brdf_scale = std::max(0.0f, 1.0f - sss_weight);
                        color = vmul(direct + ambient + indirect, albedo) * brdf_scale + sss_contrib * (sss_weight > 0.0f ? 1.0f : 0.0f);
                    }

                    size_t idx = ((size_t)y * width + x) * 3;
                    state.accumBuffer[idx + 0] += color.x;
                    state.accumBuffer[idx + 1] += color.y;
                    state.accumBuffer[idx + 2] += color.z;
                }
            }
        });
    }

    for (auto& th : threads) th.join();

    state.sampleCount++;

    using lightrt_common::shading::reinhardTonemap;
    using lightrt_common::shading::linearToSRGB;
    float invSamples = 1.0f / (float)state.sampleCount;

    for (int i = 0; i < width * height; ++i) {
        float r = reinhardTonemap(state.accumBuffer[i * 3 + 0] * invSamples);
        float g = reinhardTonemap(state.accumBuffer[i * 3 + 1] * invSamples);
        float b = reinhardTonemap(state.accumBuffer[i * 3 + 2] * invSamples);

        r = linearToSRGB(r);
        g = linearToSRGB(g);
        b = linearToSRGB(b);

        int ir = std::min(255, (int)(r * 255.0f + 0.5f));
        int ig = std::min(255, (int)(g * 255.0f + 0.5f));
        int ib = std::min(255, (int)(b * 255.0f + 0.5f));

        state.pixels[i] = 0xFF000000u | ((uint32_t)ir << 16) | ((uint32_t)ig << 8) | (uint32_t)ib;
    }
}

// --- Rendering ---

void RenderFrame(ViewerState& state) {
    int w = (int)state.width;
    int h = (int)state.height;

    PathTrace(state);

    int fs = state.fontScale;
    int lineH = 10 * fs;

    std::string stats = "FPS: " + std::to_string((int)state.fps);
    DrawString(10, 10, stats.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h, fs);

    std::string tris = "Tris: " + std::to_string(sceneTriangleCount(state.scene));
    DrawString(10, 10 + lineH, tris.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h, fs);

    std::string meshCount = "Meshes: " + std::to_string(state.scene.meshes.size());
    DrawString(10, 10 + lineH * 2, meshCount.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h, fs);

    std::string samples = "Samples: " + std::to_string(state.sampleCount);
    DrawString(10, 10 + lineH * 3, samples.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h, fs);

    std::string help = "Alt+LMB/Shift+LMB Orbit, Alt+MMB/Ctrl+LMB Pan, Alt+RMB/Ctrl+Shift+LMB/Tab+LMB Dolly";
    DrawString(10, h - lineH * 3, help.c_str(), 0xFFFFFF00, state.pixels.data(), w, h, fs);

    static const char* shadowModeNames[] = {"OFF", "HARD", "SOFT", "STRONG_SOFT"};
    std::string help2 = "F: Fit, S: Shadow [" + std::string(shadowModeNames[state.shadowMode]) + "], +: Font 2x [" + std::string(fs == 2 ? "ON" : "OFF") + "], O: Open File";
    DrawString(10, h - lineH * 2, help2.c_str(), 0xFFFFFF00, state.pixels.data(), w, h, fs);
}

void ResizeFramebuffer(ViewerState& state, uint32_t w, uint32_t h) {
    state.width = w;
    state.height = h;
    state.pixels.resize(w * h);
    state.accumBuffer.resize((size_t)w * h * 3, 0.0f);
    state.pixelSampleCount.resize(w * h, 0u);
    state.cameraDirty = true;
    BuildPixelOrder(state);
}

// --- Procedural Primitives ---

void GeneratePlane(std::vector<Triangle>& out, Vec3 center, float halfSize) {
    Vec3 p0(center.x - halfSize, center.y, center.z - halfSize);
    Vec3 p1(center.x + halfSize, center.y, center.z - halfSize);
    Vec3 p2(center.x + halfSize, center.y, center.z + halfSize);
    Vec3 p3(center.x - halfSize, center.y, center.z + halfSize);

    Triangle t0; t0.v0 = p0; t0.v1 = p1; t0.v2 = p2;
    Triangle t1; t1.v0 = p0; t1.v1 = p2; t1.v2 = p3;
    out.push_back(t0);
    out.push_back(t1);
}

void GenerateUVSphere(std::vector<Triangle>& out, Vec3 center, float radius, int segments, int rings) {
    std::vector<Vec3> verts;
    verts.push_back(Vec3(center.x, center.y + radius, center.z)); // top pole

    for (int r = 1; r < rings; ++r) {
        float phi = kPi * (float)r / (float)rings;
        float y = cosf(phi) * radius;
        float ringR = sinf(phi) * radius;
        for (int s = 0; s < segments; ++s) {
            float theta = 2.0f * kPi * (float)s / (float)segments;
            verts.push_back(Vec3(center.x + cosf(theta)*ringR, center.y + y, center.z + sinf(theta)*ringR));
        }
    }
    verts.push_back(Vec3(center.x, center.y - radius, center.z)); // bottom pole

    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri; tri.v0 = verts[0]; tri.v1 = verts[1 + s]; tri.v2 = verts[1 + next];
        out.push_back(tri);
    }

    for (int r = 0; r < rings - 2; ++r) {
        int row0 = 1 + r * segments;
        int row1 = 1 + (r + 1) * segments;
        for (int s = 0; s < segments; ++s) {
            int next = (s + 1) % segments;
            Triangle t0, t1;
            t0.v0 = verts[row0 + s]; t0.v1 = verts[row1 + s]; t0.v2 = verts[row1 + next];
            t1.v0 = verts[row0 + s]; t1.v1 = verts[row1 + next]; t1.v2 = verts[row0 + next];
            out.push_back(t0); out.push_back(t1);
        }
    }

    int bottomPole = (int)verts.size() - 1;
    int lastRow = 1 + (rings - 2) * segments;
    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri; tri.v0 = verts[bottomPole]; tri.v1 = verts[lastRow + next]; tri.v2 = verts[lastRow + s];
        out.push_back(tri);
    }
}

void GenerateCube(std::vector<Triangle>& out, Vec3 center, float halfSize) {
    float h = halfSize;
    Vec3 c = center;
    Vec3 v[8] = {
        {c.x-h, c.y-h, c.z-h}, {c.x+h, c.y-h, c.z-h},
        {c.x+h, c.y+h, c.z-h}, {c.x-h, c.y+h, c.z-h},
        {c.x-h, c.y-h, c.z+h}, {c.x+h, c.y-h, c.z+h},
        {c.x+h, c.y+h, c.z+h}, {c.x-h, c.y+h, c.z+h}
    };

    auto addQuad = [&](Vec3 a, Vec3 b, Vec3 cc, Vec3 d) {
        Triangle t0, t1;
        t0.v0 = a; t0.v1 = b; t0.v2 = cc;
        t1.v0 = a; t1.v1 = cc; t1.v2 = d;
        out.push_back(t0); out.push_back(t1);
    };

    addQuad(v[0], v[3], v[2], v[1]);
    addQuad(v[4], v[5], v[6], v[7]);
    addQuad(v[0], v[1], v[5], v[4]);
    addQuad(v[2], v[3], v[7], v[6]);
    addQuad(v[0], v[4], v[7], v[3]);
    addQuad(v[1], v[2], v[6], v[5]);
}

void GenerateCone(std::vector<Triangle>& out, Vec3 center, float radius, float height, int segments) {
    Vec3 apex(center.x, center.y + height, center.z);

    std::vector<Vec3> ring;
    for (int s = 0; s < segments; ++s) {
        float theta = 2.0f * kPi * (float)s / (float)segments;
        ring.push_back(Vec3(center.x + cosf(theta)*radius, center.y, center.z + sinf(theta)*radius));
    }

    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri; tri.v0 = apex; tri.v1 = ring[next]; tri.v2 = ring[s];
        out.push_back(tri);
    }

    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri; tri.v0 = center; tri.v1 = ring[s]; tri.v2 = ring[next];
        out.push_back(tri);
    }
}

void GenerateTube(std::vector<Triangle>& out, Vec3 center, float radius, float height, int segments) {
    float halfH = height * 0.5f;

    std::vector<Vec3> topRing, botRing;
    for (int s = 0; s < segments; ++s) {
        float theta = 2.0f * kPi * (float)s / (float)segments;
        float x = cosf(theta) * radius;
        float z = sinf(theta) * radius;
        topRing.push_back(Vec3(center.x + x, center.y + halfH, center.z + z));
        botRing.push_back(Vec3(center.x + x, center.y - halfH, center.z + z));
    }

    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle t0, t1;
        t0.v0 = botRing[s]; t0.v1 = topRing[s]; t0.v2 = topRing[next];
        t1.v0 = botRing[s]; t1.v1 = topRing[next]; t1.v2 = botRing[next];
        out.push_back(t0); out.push_back(t1);
    }
}

void GenerateCapsule(std::vector<Triangle>& out, Vec3 center, float radius, float cylHeight, int segments, int rings) {
    float halfH = cylHeight * 0.5f;

    std::vector<std::vector<Vec3>> allRings;
    allRings.push_back(std::vector<Vec3>()); // top pole placeholder

    for (int r = 1; r <= rings; ++r) {
        float phi = kPi * 0.5f * (float)r / (float)rings;
        float y = cosf(phi) * radius + halfH;
        float ringR = sinf(phi) * radius;
        std::vector<Vec3> ring;
        for (int s = 0; s < segments; ++s) {
            float theta = 2.0f * kPi * (float)s / (float)segments;
            ring.push_back(Vec3(center.x + cosf(theta)*ringR, center.y + y, center.z + sinf(theta)*ringR));
        }
        allRings.push_back(ring);
    }

    for (int r = 1; r < rings; ++r) {
        float phi = kPi * 0.5f + kPi * 0.5f * (float)r / (float)rings;
        float y = cosf(phi) * radius - halfH;
        float ringR = sinf(phi) * radius;
        std::vector<Vec3> ring;
        for (int s = 0; s < segments; ++s) {
            float theta = 2.0f * kPi * (float)s / (float)segments;
            ring.push_back(Vec3(center.x + cosf(theta)*ringR, center.y + y, center.z + sinf(theta)*ringR));
        }
        allRings.push_back(ring);
    }

    Vec3 topPole(center.x, center.y + halfH + radius, center.z);
    Vec3 botPole(center.x, center.y - halfH - radius, center.z);

    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri; tri.v0 = topPole; tri.v1 = allRings[1][s]; tri.v2 = allRings[1][next];
        out.push_back(tri);
    }

    for (size_t r = 1; r + 1 < allRings.size(); ++r) {
        for (int s = 0; s < segments; ++s) {
            int next = (s + 1) % segments;
            Triangle t0, t1;
            t0.v0 = allRings[r][s]; t0.v1 = allRings[r+1][s]; t0.v2 = allRings[r+1][next];
            t1.v0 = allRings[r][s]; t1.v1 = allRings[r+1][next]; t1.v2 = allRings[r][next];
            out.push_back(t0); out.push_back(t1);
        }
    }

    const auto& lastRing = allRings.back();
    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri; tri.v0 = botPole; tri.v1 = lastRing[next]; tri.v2 = lastRing[s];
        out.push_back(tri);
    }
}

void CreateDefaultScene(scene::Scene& sc) {
    sc = scene::Scene{}; // clear

    { std::vector<Triangle> tris; GeneratePlane(tris, Vec3(0,0,0), 5.0f);             addMeshToScene(sc, std::move(tris), Vec3(0.9f,0.9f,0.85f)); }
    { std::vector<Triangle> tris; GenerateUVSphere(tris, Vec3(-2.0f,0.5f,0), 0.5f);  addMeshToScene(sc, std::move(tris), Vec3(0.85f,0.25f,0.25f)); }
    { std::vector<Triangle> tris; GenerateCube(tris, Vec3(-0.8f,0.4f,0), 0.4f);       addMeshToScene(sc, std::move(tris), Vec3(0.25f,0.65f,0.85f)); }
    { std::vector<Triangle> tris; GenerateCone(tris, Vec3(0.4f,0,0), 0.4f, 0.9f);    addMeshToScene(sc, std::move(tris), Vec3(0.25f,0.85f,0.35f)); }
    { std::vector<Triangle> tris; GenerateTube(tris, Vec3(1.6f,0.45f,0), 0.3f, 0.9f); addMeshToScene(sc, std::move(tris), Vec3(0.85f,0.75f,0.25f)); }
    { std::vector<Triangle> tris; GenerateCapsule(tris, Vec3(2.8f,0.45f,0), 0.25f, 0.5f); addMeshToScene(sc, std::move(tris), Vec3(0.7f,0.35f,0.85f)); }
}

// --- Build pixel order for frameless rendering ---

void BuildPixelOrder(ViewerState& state) {
    uint32_t n = state.width * state.height;
    state.pixelOrder.resize(n);
    for (uint32_t i = 0; i < n; i++) state.pixelOrder[i] = i;
    uint32_t seed = 42u;
    for (uint32_t i = n - 1; i > 0; i--) {
        uint32_t j = pcg_hash(seed + i) % (i + 1);
        std::swap(state.pixelOrder[i], state.pixelOrder[j]);
    }
    state.nextPixelIdx = 0;
}

// --- Tonemap accumBuffer → pixels[] using per-pixel sample counts ---

void Tonemap(ViewerState& state) {
    int w = (int)state.width;
    int h = (int)state.height;

    using lightrt_common::shading::reinhardTonemap;
    using lightrt_common::shading::linearToSRGB;

    std::fill(state.pixels.begin(), state.pixels.end(), 0xFF000000u);

    for (int i = 0; i < w * h; i++) {
        uint32_t ns = state.pixelSampleCount[i];
        if (ns == 0) continue;

        float invSamples = 1.0f / (float)ns;
        float r = reinhardTonemap(state.accumBuffer[i * 3 + 0] * invSamples);
        float g = reinhardTonemap(state.accumBuffer[i * 3 + 1] * invSamples);
        float b = reinhardTonemap(state.accumBuffer[i * 3 + 2] * invSamples);

        r = linearToSRGB(r);
        g = linearToSRGB(g);
        b = linearToSRGB(b);

        int ir = std::min(255, (int)(r * 255.0f + 0.5f));
        int ig = std::min(255, (int)(g * 255.0f + 0.5f));
        int ib = std::min(255, (int)(b * 255.0f + 0.5f));

        state.pixels[i] = 0xFF000000u | ((uint32_t)ir << 16) | ((uint32_t)ig << 8) | (uint32_t)ib;
    }
}

} // namespace lightrt_viewer
