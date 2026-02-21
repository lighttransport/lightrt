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

// --- Model Loading ---

bool LoadOBJ(const std::string& filename, SimpleMesh& mesh) {
    tinyobj::attrib_t attrib;
    std::vector<tinyobj::shape_t> shapes;
    std::vector<tinyobj::material_t> materials;
    std::string warn, err;

    if (!tinyobj::LoadObj(&attrib, &shapes, &materials, &warn, &err, filename.c_str())) {
        std::cerr << "TinyObj Error: " << warn << err << "\n";
        return false;
    }

    for (const auto& shape : shapes) {
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
                mesh.triangles.push_back(tri);
            }
            index_offset += fv;
        }
    }
    return true;
}

bool LoadGLTF(const std::string& filename, SimpleMesh& mesh) {
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

    for (const auto& meshIdx : model.meshes) {
        for (const auto& primitive : meshIdx.primitives) {
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
                    mesh.triangles.push_back(tri);
                }
            }
        }
    }
    return true;
}

bool LoadModel(const std::string& filename, SimpleMesh& mesh) {
    if (filename.find(".obj") != std::string::npos) {
        return LoadOBJ(filename, mesh);
    } else {
        return LoadGLTF(filename, mesh);
    }
}

// --- Input Processing ---

bool ProcessInput(ViewerState& state, float dt) {
    if (state.keys[KEY_ESCAPE]) return true;

    float speed = 2.5f * dt;
    if (state.keys[KEY_W]) state.camera.position = state.camera.position + state.camera.forward * speed;
    if (state.keys[KEY_S]) state.camera.position = state.camera.position - state.camera.forward * speed;
    if (state.keys[KEY_A]) state.camera.position = state.camera.position - state.camera.right * speed;
    if (state.keys[KEY_D]) state.camera.position = state.camera.position + state.camera.right * speed;

    // Toggle render mode with F key
    bool fKeyPressed = state.keys[KEY_F];
    if (fKeyPressed && !state.fKeyWasPressed) {
        state.renderMode = (RenderMode)(((int)state.renderMode + 1) % RENDER_MODE_COUNT);
    }
    state.fKeyWasPressed = fKeyPressed;

    return false;
}

void OnMouseMove(ViewerState& state, double xpos, double ypos) {
    if (!state.mouseCaptured) return;
    if (state.firstMouse) {
        state.lastX = xpos;
        state.lastY = ypos;
        state.firstMouse = false;
    }

    float xoffset = (float)(xpos - state.lastX);
    float yoffset = (float)(state.lastY - ypos);
    state.lastX = xpos;
    state.lastY = ypos;

    float sensitivity = 0.1f;
    xoffset *= sensitivity;
    yoffset *= sensitivity;

    state.camera.yaw += xoffset;
    state.camera.pitch += yoffset;

    if (state.camera.pitch > 89.0f) state.camera.pitch = 89.0f;
    if (state.camera.pitch < -89.0f) state.camera.pitch = -89.0f;

    Vec3 front;
    front.x = cos(state.camera.yaw * 3.14159f / 180.0f) * cos(state.camera.pitch * 3.14159f / 180.0f);
    front.y = sin(state.camera.pitch * 3.14159f / 180.0f);
    front.z = sin(state.camera.yaw * 3.14159f / 180.0f) * cos(state.camera.pitch * 3.14159f / 180.0f);
    state.camera.forward = front.normalize();
    state.camera.right = state.camera.forward.cross(Vec3(0, 1, 0)).normalize();
    state.camera.up = state.camera.right.cross(state.camera.forward).normalize();
}

bool OnMouseButtonToggle(ViewerState& state) {
    state.mouseCaptured = !state.mouseCaptured;
    if (state.mouseCaptured) {
        state.firstMouse = true;
    }
    return state.mouseCaptured;
}

// --- Drawing Primitives ---

bool ProjectToScreen(const Vec3& worldPos, const Camera& cam,
                     int width, int height, int& screenX, int& screenY) {
    Vec3 toPoint = worldPos - cam.position;

    float z = toPoint.dot(cam.forward);
    if (z <= 0.001f) return false;

    float x = toPoint.dot(cam.right);
    float y = toPoint.dot(cam.up);

    float aspectRatio = (float)width / height;
    float scale = tan(cam.fov * 0.5f * 3.14159f / 180.0f);

    float ndcX = x / (z * aspectRatio * scale);
    float ndcY = y / (z * scale);

    screenX = (int)((ndcX + 1.0f) * 0.5f * width);
    screenY = (int)((1.0f - ndcY) * 0.5f * height);

    return true;
}

void DrawLine(std::vector<uint32_t>& buffer, int width, int height,
              int x0, int y0, int x1, int y1, uint32_t color) {
    auto computeCode = [width, height](int x, int y) -> int {
        int code = 0;
        if (x < 0) code |= 1;
        if (x >= width) code |= 2;
        if (y < 0) code |= 4;
        if (y >= height) code |= 8;
        return code;
    };

    int code0 = computeCode(x0, y0);
    int code1 = computeCode(x1, y1);

    if (code0 & code1) return;

    auto clipLine = [&]() -> bool {
        for (int i = 0; i < 4; i++) {
            if (code0 == 0 && code1 == 0) return true;
            if (code0 & code1) return false;

            int code = code0 ? code0 : code1;
            int x, y;

            if (code & 8) {
                x = x0 + (x1 - x0) * (height - 1 - y0) / (y1 - y0);
                y = height - 1;
            } else if (code & 4) {
                x = x0 + (x1 - x0) * (0 - y0) / (y1 - y0);
                y = 0;
            } else if (code & 2) {
                y = y0 + (y1 - y0) * (width - 1 - x0) / (x1 - x0);
                x = width - 1;
            } else {
                y = y0 + (y1 - y0) * (0 - x0) / (x1 - x0);
                x = 0;
            }

            if (code == code0) {
                x0 = x; y0 = y;
                code0 = computeCode(x0, y0);
            } else {
                x1 = x; y1 = y;
                code1 = computeCode(x1, y1);
            }
        }
        return code0 == 0 && code1 == 0;
    };

    if (!clipLine()) return;

    int dx = abs(x1 - x0);
    int dy = abs(y1 - y0);
    int sx = x0 < x1 ? 1 : -1;
    int sy = y0 < y1 ? 1 : -1;
    int err = dx - dy;

    while (true) {
        if (x0 >= 0 && x0 < width && y0 >= 0 && y0 < height) {
            buffer[y0 * width + x0] = color;
        }

        if (x0 == x1 && y0 == y1) break;

        int e2 = 2 * err;
        if (e2 > -dy) {
            err -= dy;
            x0 += sx;
        }
        if (e2 < dx) {
            err += dx;
            y0 += sy;
        }
    }
}

// --- Rendering ---

void RenderWireframe(std::vector<uint32_t>& buffer, int width, int height,
                     const std::vector<Triangle>& triangles,
                     const Camera& cam, uint32_t edgeColor) {
    for (const auto& tri : triangles) {
        int sx0 = 0, sy0 = 0, sx1 = 0, sy1 = 0, sx2 = 0, sy2 = 0;

        bool v0_visible = ProjectToScreen(tri.v0, cam, width, height, sx0, sy0);
        bool v1_visible = ProjectToScreen(tri.v1, cam, width, height, sx1, sy1);
        bool v2_visible = ProjectToScreen(tri.v2, cam, width, height, sx2, sy2);

        if (v0_visible && v1_visible)
            DrawLine(buffer, width, height, sx0, sy0, sx1, sy1, edgeColor);
        if (v1_visible && v2_visible)
            DrawLine(buffer, width, height, sx1, sy1, sx2, sy2, edgeColor);
        if (v2_visible && v0_visible)
            DrawLine(buffer, width, height, sx2, sy2, sx0, sy0, edgeColor);
    }
}

void RayTrace(ViewerState& state) {
    int width = (int)state.width;
    int height = (int)state.height;
    float invWidth = 1.0f / width;
    float invHeight = 1.0f / height;
    float aspectRatio = (float)width / height;
    float scale = tan(state.camera.fov * 0.5f * 3.14159f / 180.0f);

    int num_threads = std::thread::hardware_concurrency();
    std::vector<std::thread> threads;
    int rows_per_thread = height / num_threads;

    for (int t = 0; t < num_threads; ++t) {
        threads.emplace_back([&, t]() {
            int start_y = t * rows_per_thread;
            int end_y = (t == num_threads - 1) ? height : (t + 1) * rows_per_thread;

            for (int y = start_y; y < end_y; ++y) {
                for (int x = 0; x < width; ++x) {
                    float px = (2 * (x + 0.5f) * invWidth - 1) * aspectRatio * scale;
                    float py = (1 - 2 * (y + 0.5f) * invHeight) * scale;

                    Vec3 dir = (state.camera.forward + state.camera.right * px + state.camera.up * py).normalize();
                    Ray ray(state.camera.position, dir);

                    float t_hit, u, v;
                    uint32_t hit_prim = state.mesh.bvh.traverse(ray, t_hit, u, v);

                    uint32_t color = 0xFF111111;
                    if (hit_prim != kInvalidIndex) {
                        const Triangle& tri = state.mesh.triangles[hit_prim];
                        Vec3 normal = (tri.v1 - tri.v0).cross(tri.v2 - tri.v0).normalize();
                        float diff = std::max(0.0f, normal.dot(Vec3(0, 1, 0)));

                        int r = (hit_prim * 123) % 255;
                        int g = (hit_prim * 456) % 255;
                        int b = (hit_prim * 789) % 255;

                        r = std::min(255, (int)(r * (0.2f + 0.8f * diff)));
                        g = std::min(255, (int)(g * (0.2f + 0.8f * diff)));
                        b = std::min(255, (int)(b * (0.2f + 0.8f * diff)));

                        color = 0xFF000000 | (r << 16) | (g << 8) | b;
                    }

                    state.pixels[y * width + x] = color;
                }
            }
        });
    }

    for (auto& th : threads) th.join();
}

void RenderFrame(ViewerState& state) {
    int w = (int)state.width;
    int h = (int)state.height;

    if (state.renderMode == RENDER_SOLID || state.renderMode == RENDER_OVERLAY) {
        RayTrace(state);
    }
    if (state.renderMode == RENDER_WIREFRAME) {
        std::fill(state.pixels.begin(), state.pixels.end(), (uint32_t)0xFF111111);
    }
    if (state.renderMode == RENDER_WIREFRAME || state.renderMode == RENDER_OVERLAY) {
        RenderWireframe(state.pixels, w, h, state.mesh.triangles, state.camera, 0xFF00FF00);
    }

    // Text overlay
    std::string stats = "FPS: " + std::to_string((int)state.fps);
    DrawString(10, 10, stats.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h);

    std::string tris = "Tris: " + std::to_string(state.mesh.triangles.size());
    DrawString(10, 25, tris.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h);

    std::string help = "WASD Move, Click Mouse Capture, F: Mode [" + std::string(RenderModeName(state.renderMode)) + "]";
    DrawString(10, h - 20, help.c_str(), 0xFFFFFF00, state.pixels.data(), w, h);
}

void ResizeFramebuffer(ViewerState& state, uint32_t w, uint32_t h) {
    state.width = w;
    state.height = h;
    state.pixels.resize(w * h);
}

const char* RenderModeName(RenderMode mode) {
    static const char* names[] = {"Solid", "Wire", "Overlay"};
    return names[(int)mode % RENDER_MODE_COUNT];
}

} // namespace lightrt_viewer
