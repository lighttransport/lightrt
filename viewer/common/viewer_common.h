#pragma once

#include "../../lightrt.hh"
#include "bitmap_font.h"

#include <vector>
#include <string>
#include <cstdint>

namespace lightrt_viewer {

using namespace lightrt;

// --- Key Indices (platform-independent) ---

enum ViewerKey {
    KEY_W = 0,
    KEY_A,
    KEY_S,
    KEY_D,
    KEY_F,
    KEY_ESCAPE,
    KEY_COUNT
};

// --- Render Mode ---

enum RenderMode {
    RENDER_SOLID = 0,
    RENDER_WIREFRAME = 1,
    RENDER_OVERLAY = 2,
    RENDER_MODE_COUNT = 3
};

// --- Data Structures ---

struct SimpleMesh {
    std::vector<Triangle> triangles;
    TriangleBVH bvh;
};

struct Camera {
    Vec3 position{0, 0, 5};
    Vec3 forward{0, 0, -1};
    Vec3 up{0, 1, 0};
    Vec3 right{1, 0, 0};
    float fov = 60.0f;
    float yaw = -90.0f;
    float pitch = 0.0f;
};

struct ViewerState {
    SimpleMesh mesh;
    Camera camera;
    uint32_t width = 1280;
    uint32_t height = 720;

    // Input
    bool keys[KEY_COUNT] = {};
    bool fKeyWasPressed = false;
    double lastX = 0, lastY = 0;
    bool firstMouse = true;
    bool mouseCaptured = false;

    // Rendering
    RenderMode renderMode = RENDER_SOLID;
    std::vector<uint32_t> pixels;

    // Stats
    float fps = 0;
    int frameCount = 0;
};

// --- Model Loading ---

bool LoadOBJ(const std::string& filename, SimpleMesh& mesh);
bool LoadGLTF(const std::string& filename, SimpleMesh& mesh);
bool LoadModel(const std::string& filename, SimpleMesh& mesh);

// --- Input Processing ---
// Returns true if the viewer should close (Escape pressed)
bool ProcessInput(ViewerState& state, float dt);

// Mouse movement callback - updates camera orientation
void OnMouseMove(ViewerState& state, double xpos, double ypos);

// Mouse button toggle - returns new capture state
bool OnMouseButtonToggle(ViewerState& state);

// --- Rendering ---

void RayTrace(ViewerState& state);

void RenderWireframe(std::vector<uint32_t>& buffer, int width, int height,
                     const std::vector<Triangle>& triangles,
                     const Camera& cam, uint32_t edgeColor);

// Full frame render: ray trace / wireframe + text overlay
void RenderFrame(ViewerState& state);

// Resize framebuffer
void ResizeFramebuffer(ViewerState& state, uint32_t w, uint32_t h);

// --- Drawing Primitives ---

bool ProjectToScreen(const Vec3& worldPos, const Camera& cam,
                     int width, int height, int& screenX, int& screenY);

void DrawLine(std::vector<uint32_t>& buffer, int width, int height,
              int x0, int y0, int x1, int y1, uint32_t color);

// --- Render mode name ---

const char* RenderModeName(RenderMode mode);

} // namespace lightrt_viewer
