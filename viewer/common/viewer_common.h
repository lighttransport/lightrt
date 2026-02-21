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
    KEY_F = 0,
    KEY_S,
    KEY_ESCAPE,
    KEY_COUNT
};

// --- Data Structures ---

struct SceneMesh {
    std::string name;
    std::vector<Triangle> triangles;
    Vec3 color{0.8f, 0.8f, 0.8f};
};

struct Scene {
    std::vector<SceneMesh> meshes;
    std::vector<Triangle> allTriangles;
    std::vector<uint32_t> meshIdPerTri;
    TriangleBVH bvh;

    void build();
    Vec3 getMeshColor(uint32_t triIdx) const;
};

struct Camera {
    Vec3 position{0, 0, 5};
    Vec3 forward{0, 0, -1};
    Vec3 up{0, 1, 0};
    Vec3 right{1, 0, 0};
    float fov = 60.0f;
    float yaw = -90.0f;
    float pitch = 0.0f;
    Vec3 orbitCenter{0, 0, 0};
    float orbitDistance = 5.0f;
};

struct ViewerState {
    Scene scene;
    Camera camera;
    uint32_t width = 1280;
    uint32_t height = 720;

    // Input
    bool keys[KEY_COUNT] = {};
    bool fKeyWasPressed = false;
    bool sKeyWasPressed = false;
    bool altPressed = false;
    bool shiftPressed = false;
    bool ctrlPressed = false;
    bool lmbPressed = false, mmbPressed = false, rmbPressed = false;
    bool dragging = false;
    double lastX = 0, lastY = 0;

    // Rendering
    bool shadowsEnabled = true;
    std::vector<float> accumBuffer;   // w*h*3 HDR floats
    uint32_t sampleCount = 0;
    bool cameraDirty = true;
    Vec3 sunDirection;
    std::vector<uint32_t> pixels;

    // Stats
    float fps = 0;
    int frameCount = 0;
};

// --- Model Loading ---

bool LoadOBJ(const std::string& filename, Scene& scene);
bool LoadGLTF(const std::string& filename, Scene& scene);
bool LoadModel(const std::string& filename, Scene& scene);

// --- Input Processing ---
// Returns true if the viewer should close (Escape pressed)
bool ProcessInput(ViewerState& state, float dt);

// --- Camera ---

void UpdateCameraFromOrbit(Camera& cam);
void FitToScene(ViewerState& state);
void OrbitCamera(ViewerState& state, float dx, float dy);
void PanCamera(ViewerState& state, float dx, float dy);
void DollyCamera(ViewerState& state, float delta);
void OnMouseDown(ViewerState& state, double x, double y);
void OnMouseDrag(ViewerState& state, double x, double y);

// --- Rendering ---

Vec3 SampleSky(const Vec3& dir, const Vec3& sun_dir);
void PathTrace(ViewerState& state);

// Full frame render: path trace + text overlay
void RenderFrame(ViewerState& state);

// Resize framebuffer
void ResizeFramebuffer(ViewerState& state, uint32_t w, uint32_t h);

// --- Procedural Primitives ---

void GeneratePlane(SceneMesh& out, Vec3 center, float halfSize);
void GenerateUVSphere(SceneMesh& out, Vec3 center, float radius, int segments = 16, int rings = 8);
void GenerateCube(SceneMesh& out, Vec3 center, float halfSize);
void GenerateCone(SceneMesh& out, Vec3 center, float radius, float height, int segments = 16);
void GenerateTube(SceneMesh& out, Vec3 center, float radius, float height, int segments = 16);
void GenerateCapsule(SceneMesh& out, Vec3 center, float radius, float cylHeight, int segments = 16, int rings = 4);
void CreateDefaultScene(Scene& scene);

} // namespace lightrt_viewer
