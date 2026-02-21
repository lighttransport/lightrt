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

namespace lightrt_viewer {

static constexpr float kPi = 3.14159265358979323846f;

// Component-wise Vec3 multiply (Vec3 only has operator*(float))
static Vec3 vmul(const Vec3& a, const Vec3& b) {
    return Vec3(a.x * b.x, a.y * b.y, a.z * b.z);
}

// --- Scene ---

void Scene::build() {
    allTriangles.clear();
    meshIdPerTri.clear();
    for (uint32_t mi = 0; mi < (uint32_t)meshes.size(); ++mi) {
        for (const auto& tri : meshes[mi].triangles) {
            allTriangles.push_back(tri);
            meshIdPerTri.push_back(mi);
        }
    }
    if (!allTriangles.empty()) {
        lightrt::BVHBuildConfig config;
        bvh.build(allTriangles, config);
    }
}

Vec3 Scene::getMeshColor(uint32_t triIdx) const {
    if (triIdx < (uint32_t)meshIdPerTri.size()) {
        return meshes[meshIdPerTri[triIdx]].color;
    }
    return Vec3(0.8f, 0.8f, 0.8f);
}

// --- Model Loading ---

static Vec3 hashColor(const std::string& name) {
    uint32_t h = 5381;
    for (char c : name) h = h * 33 + (uint32_t)(unsigned char)c;
    float r = 0.3f + 0.5f * ((h & 0xFF) / 255.0f);
    float g = 0.3f + 0.5f * (((h >> 8) & 0xFF) / 255.0f);
    float b = 0.3f + 0.5f * (((h >> 16) & 0xFF) / 255.0f);
    return Vec3(r, g, b);
}

bool LoadOBJ(const std::string& filename, Scene& scene) {
    tinyobj::attrib_t attrib;
    std::vector<tinyobj::shape_t> shapes;
    std::vector<tinyobj::material_t> materials;
    std::string warn, err;

    if (!tinyobj::LoadObj(&attrib, &shapes, &materials, &warn, &err, filename.c_str())) {
        std::cerr << "TinyObj Error: " << warn << err << "\n";
        return false;
    }

    for (const auto& shape : shapes) {
        SceneMesh sm;
        sm.name = shape.name.empty() ? "mesh" : shape.name;
        sm.color = hashColor(sm.name);

        size_t index_offset = 0;
        for (size_t f = 0; f < shape.mesh.num_face_vertices.size(); f++) {
            int fv = shape.mesh.num_face_vertices[f];
            if (fv == 3) {
                tinyobj::index_t idx0 = shape.mesh.indices[index_offset + 0];
                tinyobj::index_t idx1 = shape.mesh.indices[index_offset + 1];
                tinyobj::index_t idx2 = shape.mesh.indices[index_offset + 2];

                Vec3 v0(attrib.vertices[3 * idx0.vertex_index + 0], attrib.vertices[3 * idx0.vertex_index + 1], attrib.vertices[3 * idx0.vertex_index + 2]);
                Vec3 v1(attrib.vertices[3 * idx1.vertex_index + 0], attrib.vertices[3 * idx1.vertex_index + 1], attrib.vertices[3 * idx1.vertex_index + 2]);
                Vec3 v2(attrib.vertices[3 * idx2.vertex_index + 0], attrib.vertices[3 * idx2.vertex_index + 1], attrib.vertices[3 * idx2.vertex_index + 2]);

                Triangle tri;
                tri.v0 = v0;
                tri.v1 = v1;
                tri.v2 = v2;
                sm.triangles.push_back(tri);
            }
            index_offset += fv;
        }

        if (!sm.triangles.empty()) {
            scene.meshes.push_back(std::move(sm));
        }
    }
    return true;
}

bool LoadGLTF(const std::string& filename, Scene& scene) {
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

            SceneMesh sm;
            sm.name = gltfMesh.name.empty() ? ("mesh_" + std::to_string(mi)) : gltfMesh.name;
            if (gltfMesh.primitives.size() > 1) {
                sm.name += "_prim" + std::to_string(pi);
            }
            sm.color = hashColor(sm.name);

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

                    Vec3 v0(positionBuffer[i0 * posStride], positionBuffer[i0 * posStride + 1], positionBuffer[i0 * posStride + 2]);
                    Vec3 v1(positionBuffer[i1 * posStride], positionBuffer[i1 * posStride + 1], positionBuffer[i1 * posStride + 2]);
                    Vec3 v2(positionBuffer[i2 * posStride], positionBuffer[i2 * posStride + 1], positionBuffer[i2 * posStride + 2]);
                    Triangle tri; tri.v0 = v0; tri.v1 = v1; tri.v2 = v2;
                    sm.triangles.push_back(tri);
                }
            }

            if (!sm.triangles.empty()) {
                scene.meshes.push_back(std::move(sm));
            }
        }
    }
    return true;
}

bool LoadModel(const std::string& filename, Scene& scene) {
    if (filename.find(".obj") != std::string::npos) {
        return LoadOBJ(filename, scene);
    } else {
        return LoadGLTF(filename, scene);
    }
}

// --- Camera ---

void UpdateCameraFromOrbit(Camera& cam) {
    float yawRad = cam.yaw * kPi / 180.0f;
    float pitchRad = cam.pitch * kPi / 180.0f;

    // Position on sphere around orbitCenter
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
    const auto& nodes = state.scene.bvh.getBVH().getNodes();
    if (nodes.empty()) return;

    AABB bounds = nodes[0].bounds;
    Vec3 center = bounds.center();
    Vec3 ext = bounds.extents();
    float radius = ext.length() * 0.5f;

    state.camera.orbitCenter = center;
    float halfFovRad = state.camera.fov * 0.5f * kPi / 180.0f;
    state.camera.orbitDistance = radius * 1.2f / tanf(halfFovRad);
    state.camera.yaw = -90.0f;
    state.camera.pitch = 15.0f;
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

    // Alt+button: Maya-style navigation
    // Shift+LMB: orbit (touchpad-friendly)
    // Ctrl+LMB: pan (touchpad-friendly)
    // Ctrl+Shift+LMB: dolly (touchpad-friendly)
    bool wantOrbit = (state.altPressed && state.lmbPressed) ||
                     (state.shiftPressed && !state.ctrlPressed && state.lmbPressed);
    bool wantPan   = (state.altPressed && state.mmbPressed) ||
                     (state.ctrlPressed && !state.shiftPressed && state.lmbPressed);
    bool wantDolly = (state.altPressed && state.rmbPressed) ||
                     (state.ctrlPressed && state.shiftPressed && state.lmbPressed);

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

    // F key - fit to scene (edge-triggered)
    bool fKeyPressed = state.keys[KEY_F];
    if (fKeyPressed && !state.fKeyWasPressed) {
        FitToScene(state);
    }
    state.fKeyWasPressed = fKeyPressed;

    // S key - toggle shadows (edge-triggered)
    bool sKeyPressed = state.keys[KEY_S];
    if (sKeyPressed && !state.sKeyWasPressed) {
        state.shadowsEnabled = !state.shadowsEnabled;
        state.cameraDirty = true;
    }
    state.sKeyWasPressed = sKeyPressed;

    return false;
}

// --- Sun/Sky ---

Vec3 SampleSky(const Vec3& dir, const Vec3& sun_dir) {
    // Below horizon: ground color
    if (dir.y < 0.0f) {
        return Vec3(0.3f, 0.25f, 0.2f);
    }

    // Sky gradient: horizon -> zenith
    float t = sqrtf(std::max(0.0f, dir.y));
    Vec3 horizon(0.7f, 0.8f, 1.0f);
    Vec3 zenith(0.3f, 0.5f, 0.9f);
    Vec3 sky = horizon * (1.0f - t) + zenith * t;

    // Sun
    float sun_dot = dir.dot(sun_dir);
    if (sun_dot > 0.9995f) {
        // Hard sun disk
        sky = Vec3(3.0f, 2.8f, 2.5f);
    } else if (sun_dot > 0.99f) {
        // Glow halo
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

// Cosine-weighted hemisphere sample
static Vec3 cosine_hemisphere(float u1, float u2, const Vec3& normal) {
    // Build tangent frame
    Vec3 tangent;
    if (fabsf(normal.x) > 0.9f) {
        tangent = Vec3(0, 1, 0).cross(normal).normalize();
    } else {
        tangent = Vec3(1, 0, 0).cross(normal).normalize();
    }
    Vec3 bitangent = normal.cross(tangent);

    float r = sqrtf(u1);
    float theta = 2.0f * kPi * u2;
    float x = r * cosf(theta);
    float y = r * sinf(theta);
    float z = sqrtf(std::max(0.0f, 1.0f - u1));

    return (tangent * x + bitangent * y + normal * z).normalize();
}

void PathTrace(ViewerState& state) {
    int width = (int)state.width;
    int height = (int)state.height;

    // Reset accumulation if camera moved
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
    bool shadows = state.shadowsEnabled;

    int num_threads = std::max(1, (int)std::thread::hardware_concurrency());
    std::vector<std::thread> threads;
    int rows_per_thread = height / num_threads;

    for (int t = 0; t < num_threads; ++t) {
        threads.emplace_back([&, t, sampleIdx, sunDir, shadows]() {
            int start_y = t * rows_per_thread;
            int end_y = (t == num_threads - 1) ? height : (t + 1) * rows_per_thread;

            for (int y = start_y; y < end_y; ++y) {
                for (int x = 0; x < width; ++x) {
                    // Per-pixel RNG seed
                    uint32_t seed = pcg_hash((uint32_t)x + (uint32_t)y * 65537u + sampleIdx * 1000003u);

                    // Sub-pixel jitter
                    float jx = rand_float(seed);
                    float jy = rand_float(seed);

                    float px = (2.0f * (x + jx) * invWidth - 1.0f) * aspectRatio * scale;
                    float py = (1.0f - 2.0f * (y + jy) * invHeight) * scale;

                    Vec3 dir = (state.camera.forward + state.camera.right * px + state.camera.up * py).normalize();
                    Ray ray(state.camera.position, dir);

                    float t_hit, u, v;
                    uint32_t hit_prim = state.scene.bvh.traverse(ray, t_hit, u, v);

                    Vec3 color(0, 0, 0);

                    if (hit_prim == kInvalidIndex) {
                        // Background sky
                        color = SampleSky(dir, sunDir);
                    } else {
                        const Triangle& tri = state.scene.allTriangles[hit_prim];
                        Vec3 normal = tri.normal();

                        // Flip normal if backfacing
                        if (normal.dot(dir) > 0.0f) normal = normal * -1.0f;

                        Vec3 hitPos = ray.at(t_hit);
                        Vec3 albedo = state.scene.getMeshColor(hit_prim);

                        // Direct lighting
                        float NdotL = std::max(0.0f, normal.dot(sunDir));
                        float directLight = 0.0f;
                        if (NdotL > 0.0f) {
                            bool occluded = false;
                            if (shadows) {
                                Ray shadowRay(hitPos + normal * 0.001f, sunDir, 0.0f, 1e10f);
                                occluded = state.scene.bvh.traverseAnyHit(shadowRay, hit_prim);
                            }
                            if (!occluded) {
                                directLight = NdotL;
                            }
                        }

                        // Sun color
                        Vec3 sunColor(1.5f, 1.4f, 1.2f);
                        Vec3 direct = sunColor * directLight;

                        // Ambient from sky
                        Vec3 ambient = SampleSky(normal, sunDir) * 0.15f;

                        // Indirect (1 bounce)
                        Vec3 indirect(0, 0, 0);
                        {
                            float u1 = rand_float(seed);
                            float u2 = rand_float(seed);
                            Vec3 bounceDir = cosine_hemisphere(u1, u2, normal);
                            Ray bounceRay(hitPos + normal * 0.001f, bounceDir);

                            float bt, bu, bv;
                            uint32_t bhit = state.scene.bvh.traverse(bounceRay, bt, bu, bv);

                            if (bhit == kInvalidIndex) {
                                indirect = SampleSky(bounceDir, sunDir);
                            } else {
                                // Direct + ambient at bounce point
                                const Triangle& btri = state.scene.allTriangles[bhit];
                                Vec3 bnorm = btri.normal();
                                if (bnorm.dot(bounceDir) > 0.0f) bnorm = bnorm * -1.0f;

                                Vec3 bHitPos = bounceRay.at(bt);
                                float bNdotL = std::max(0.0f, bnorm.dot(sunDir));
                                float bDirect = 0.0f;
                                if (bNdotL > 0.0f) {
                                    bool bOcc = false;
                                    if (shadows) {
                                        Ray bShadow(bHitPos + bnorm * 0.001f, sunDir, 0.0f, 1e10f);
                                        bOcc = state.scene.bvh.traverseAnyHit(bShadow, bhit);
                                    }
                                    if (!bOcc) bDirect = bNdotL;
                                }
                                Vec3 bAlbedo = state.scene.getMeshColor(bhit);
                                Vec3 bAmbient = SampleSky(bnorm, sunDir) * 0.15f;
                                indirect = vmul(sunColor * bDirect + bAmbient, bAlbedo);
                            }
                        }

                        color = vmul(direct + ambient + indirect, albedo);
                    }

                    // Accumulate
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

    // Tonemap + gamma: accum/sampleCount -> Reinhard -> gamma 2.2 -> pixels
    float invSamples = 1.0f / (float)state.sampleCount;
    float invGamma = 1.0f / 2.2f;

    for (int i = 0; i < width * height; ++i) {
        float r = state.accumBuffer[i * 3 + 0] * invSamples;
        float g = state.accumBuffer[i * 3 + 1] * invSamples;
        float b = state.accumBuffer[i * 3 + 2] * invSamples;

        // Reinhard tonemap
        r = r / (1.0f + r);
        g = g / (1.0f + g);
        b = b / (1.0f + b);

        // Gamma
        r = powf(std::max(0.0f, r), invGamma);
        g = powf(std::max(0.0f, g), invGamma);
        b = powf(std::max(0.0f, b), invGamma);

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

    // Text overlay
    std::string stats = "FPS: " + std::to_string((int)state.fps);
    DrawString(10, 10, stats.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h);

    std::string tris = "Tris: " + std::to_string(state.scene.allTriangles.size());
    DrawString(10, 25, tris.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h);

    std::string meshCount = "Meshes: " + std::to_string(state.scene.meshes.size());
    DrawString(10, 40, meshCount.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h);

    std::string samples = "Samples: " + std::to_string(state.sampleCount);
    DrawString(10, 55, samples.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h);

    std::string help = "Alt+LMB/Shift+LMB Orbit, Alt+MMB/Ctrl+LMB Pan, Alt+RMB/Ctrl+Shift+LMB Dolly";
    DrawString(10, h - 30, help.c_str(), 0xFFFFFF00, state.pixels.data(), w, h);

    std::string help2 = "F: Fit, S: Shadow [" + std::string(state.shadowsEnabled ? "ON" : "OFF") + "]";
    DrawString(10, h - 17, help2.c_str(), 0xFFFFFF00, state.pixels.data(), w, h);
}

void ResizeFramebuffer(ViewerState& state, uint32_t w, uint32_t h) {
    state.width = w;
    state.height = h;
    state.pixels.resize(w * h);
    state.accumBuffer.resize((size_t)w * h * 3, 0.0f);
    state.cameraDirty = true;
}

// --- Procedural Primitives ---

void GeneratePlane(SceneMesh& out, Vec3 center, float halfSize) {
    Vec3 p0(center.x - halfSize, center.y, center.z - halfSize);
    Vec3 p1(center.x + halfSize, center.y, center.z - halfSize);
    Vec3 p2(center.x + halfSize, center.y, center.z + halfSize);
    Vec3 p3(center.x - halfSize, center.y, center.z + halfSize);

    Triangle t0; t0.v0 = p0; t0.v1 = p1; t0.v2 = p2;
    Triangle t1; t1.v0 = p0; t1.v1 = p2; t1.v2 = p3;
    out.triangles.push_back(t0);
    out.triangles.push_back(t1);
}

void GenerateUVSphere(SceneMesh& out, Vec3 center, float radius, int segments, int rings) {
    // Generate vertices
    std::vector<Vec3> verts;
    verts.push_back(Vec3(center.x, center.y + radius, center.z)); // top pole

    for (int r = 1; r < rings; ++r) {
        float phi = kPi * (float)r / (float)rings;
        float y = cosf(phi) * radius;
        float ringR = sinf(phi) * radius;
        for (int s = 0; s < segments; ++s) {
            float theta = 2.0f * kPi * (float)s / (float)segments;
            float x = cosf(theta) * ringR;
            float z = sinf(theta) * ringR;
            verts.push_back(Vec3(center.x + x, center.y + y, center.z + z));
        }
    }

    verts.push_back(Vec3(center.x, center.y - radius, center.z)); // bottom pole

    // Top cap
    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri;
        tri.v0 = verts[0];
        tri.v1 = verts[1 + s];
        tri.v2 = verts[1 + next];
        out.triangles.push_back(tri);
    }

    // Middle rings
    for (int r = 0; r < rings - 2; ++r) {
        int row0 = 1 + r * segments;
        int row1 = 1 + (r + 1) * segments;
        for (int s = 0; s < segments; ++s) {
            int next = (s + 1) % segments;
            Triangle t0, t1;
            t0.v0 = verts[row0 + s];
            t0.v1 = verts[row1 + s];
            t0.v2 = verts[row1 + next];
            t1.v0 = verts[row0 + s];
            t1.v1 = verts[row1 + next];
            t1.v2 = verts[row0 + next];
            out.triangles.push_back(t0);
            out.triangles.push_back(t1);
        }
    }

    // Bottom cap
    int bottomPole = (int)verts.size() - 1;
    int lastRow = 1 + (rings - 2) * segments;
    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri;
        tri.v0 = verts[bottomPole];
        tri.v1 = verts[lastRow + next];
        tri.v2 = verts[lastRow + s];
        out.triangles.push_back(tri);
    }
}

void GenerateCube(SceneMesh& out, Vec3 center, float halfSize) {
    float h = halfSize;
    Vec3 c = center;
    // 8 corners
    Vec3 v[8] = {
        {c.x - h, c.y - h, c.z - h}, {c.x + h, c.y - h, c.z - h},
        {c.x + h, c.y + h, c.z - h}, {c.x - h, c.y + h, c.z - h},
        {c.x - h, c.y - h, c.z + h}, {c.x + h, c.y - h, c.z + h},
        {c.x + h, c.y + h, c.z + h}, {c.x - h, c.y + h, c.z + h}
    };

    // 6 faces, 2 tris each (CCW from outside)
    auto addQuad = [&](Vec3 a, Vec3 b, Vec3 c, Vec3 d) {
        Triangle t0, t1;
        t0.v0 = a; t0.v1 = b; t0.v2 = c;
        t1.v0 = a; t1.v1 = c; t1.v2 = d;
        out.triangles.push_back(t0);
        out.triangles.push_back(t1);
    };

    addQuad(v[0], v[3], v[2], v[1]); // -Z face
    addQuad(v[4], v[5], v[6], v[7]); // +Z face
    addQuad(v[0], v[1], v[5], v[4]); // -Y face
    addQuad(v[2], v[3], v[7], v[6]); // +Y face
    addQuad(v[0], v[4], v[7], v[3]); // -X face
    addQuad(v[1], v[2], v[6], v[5]); // +X face
}

void GenerateCone(SceneMesh& out, Vec3 center, float radius, float height, int segments) {
    Vec3 apex(center.x, center.y + height, center.z);
    Vec3 baseCenter = center;

    // Base ring vertices
    std::vector<Vec3> ring;
    for (int s = 0; s < segments; ++s) {
        float theta = 2.0f * kPi * (float)s / (float)segments;
        ring.push_back(Vec3(center.x + cosf(theta) * radius, center.y, center.z + sinf(theta) * radius));
    }

    // Side triangles
    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri;
        tri.v0 = apex;
        tri.v1 = ring[next];
        tri.v2 = ring[s];
        out.triangles.push_back(tri);
    }

    // Base cap
    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri;
        tri.v0 = baseCenter;
        tri.v1 = ring[s];
        tri.v2 = ring[next];
        out.triangles.push_back(tri);
    }
}

void GenerateTube(SceneMesh& out, Vec3 center, float radius, float height, int segments) {
    float halfH = height * 0.5f;

    std::vector<Vec3> topRing, botRing;
    for (int s = 0; s < segments; ++s) {
        float theta = 2.0f * kPi * (float)s / (float)segments;
        float x = cosf(theta) * radius;
        float z = sinf(theta) * radius;
        topRing.push_back(Vec3(center.x + x, center.y + halfH, center.z + z));
        botRing.push_back(Vec3(center.x + x, center.y - halfH, center.z + z));
    }

    // Side quads
    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle t0, t1;
        t0.v0 = botRing[s]; t0.v1 = topRing[s]; t0.v2 = topRing[next];
        t1.v0 = botRing[s]; t1.v1 = topRing[next]; t1.v2 = botRing[next];
        out.triangles.push_back(t0);
        out.triangles.push_back(t1);
    }
}

void GenerateCapsule(SceneMesh& out, Vec3 center, float radius, float cylHeight, int segments, int rings) {
    float halfH = cylHeight * 0.5f;

    // Build vertex rings: top hemisphere + cylinder top/bottom + bottom hemisphere
    std::vector<std::vector<Vec3>> allRings;

    // Top hemisphere (from pole down to equator)
    allRings.push_back(std::vector<Vec3>()); // top pole placeholder
    for (int r = 1; r <= rings; ++r) {
        float phi = kPi * 0.5f * (float)r / (float)rings; // 0 to pi/2
        float y = cosf(phi) * radius + halfH;
        float ringR = sinf(phi) * radius;
        std::vector<Vec3> ring;
        for (int s = 0; s < segments; ++s) {
            float theta = 2.0f * kPi * (float)s / (float)segments;
            ring.push_back(Vec3(center.x + cosf(theta) * ringR, center.y + y, center.z + sinf(theta) * ringR));
        }
        allRings.push_back(ring);
    }

    // Bottom hemisphere (from equator down to pole)
    for (int r = 1; r < rings; ++r) {
        float phi = kPi * 0.5f + kPi * 0.5f * (float)r / (float)rings;
        float y = cosf(phi) * radius - halfH;
        float ringR = sinf(phi) * radius;
        std::vector<Vec3> ring;
        for (int s = 0; s < segments; ++s) {
            float theta = 2.0f * kPi * (float)s / (float)segments;
            ring.push_back(Vec3(center.x + cosf(theta) * ringR, center.y + y, center.z + sinf(theta) * ringR));
        }
        allRings.push_back(ring);
    }

    // Poles
    Vec3 topPole(center.x, center.y + halfH + radius, center.z);
    Vec3 botPole(center.x, center.y - halfH - radius, center.z);

    // Top cap (pole to first ring)
    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri;
        tri.v0 = topPole;
        tri.v1 = allRings[1][s];
        tri.v2 = allRings[1][next];
        out.triangles.push_back(tri);
    }

    // Rings (top hemisphere + cylinder + bottom hemisphere)
    for (size_t r = 1; r + 1 < allRings.size(); ++r) {
        for (int s = 0; s < segments; ++s) {
            int next = (s + 1) % segments;
            Triangle t0, t1;
            t0.v0 = allRings[r][s]; t0.v1 = allRings[r + 1][s]; t0.v2 = allRings[r + 1][next];
            t1.v0 = allRings[r][s]; t1.v1 = allRings[r + 1][next]; t1.v2 = allRings[r][next];
            out.triangles.push_back(t0);
            out.triangles.push_back(t1);
        }
    }

    // Bottom cap (last ring to pole)
    const auto& lastRing = allRings.back();
    for (int s = 0; s < segments; ++s) {
        int next = (s + 1) % segments;
        Triangle tri;
        tri.v0 = botPole;
        tri.v1 = lastRing[next];
        tri.v2 = lastRing[s];
        out.triangles.push_back(tri);
    }
}

void CreateDefaultScene(Scene& scene) {
    scene.meshes.clear();

    // Ground plane
    {
        SceneMesh m;
        m.name = "Ground";
        m.color = Vec3(0.9f, 0.9f, 0.85f);
        GeneratePlane(m, Vec3(0, 0, 0), 5.0f);
        scene.meshes.push_back(std::move(m));
    }

    // Sphere
    {
        SceneMesh m;
        m.name = "Sphere";
        m.color = Vec3(0.85f, 0.25f, 0.25f);
        GenerateUVSphere(m, Vec3(-2.0f, 0.5f, 0.0f), 0.5f, 16, 8);
        scene.meshes.push_back(std::move(m));
    }

    // Cube
    {
        SceneMesh m;
        m.name = "Cube";
        m.color = Vec3(0.25f, 0.65f, 0.85f);
        GenerateCube(m, Vec3(-0.8f, 0.4f, 0.0f), 0.4f);
        scene.meshes.push_back(std::move(m));
    }

    // Cone
    {
        SceneMesh m;
        m.name = "Cone";
        m.color = Vec3(0.25f, 0.85f, 0.35f);
        GenerateCone(m, Vec3(0.4f, 0.0f, 0.0f), 0.4f, 0.9f, 16);
        scene.meshes.push_back(std::move(m));
    }

    // Tube
    {
        SceneMesh m;
        m.name = "Tube";
        m.color = Vec3(0.85f, 0.75f, 0.25f);
        GenerateTube(m, Vec3(1.6f, 0.45f, 0.0f), 0.3f, 0.9f, 16);
        scene.meshes.push_back(std::move(m));
    }

    // Capsule
    {
        SceneMesh m;
        m.name = "Capsule";
        m.color = Vec3(0.7f, 0.35f, 0.85f);
        GenerateCapsule(m, Vec3(2.8f, 0.45f, 0.0f), 0.25f, 0.5f, 16, 4);
        scene.meshes.push_back(std::move(m));
    }
}

} // namespace lightrt_viewer
