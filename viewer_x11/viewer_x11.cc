// Pure X11 viewer — no GLFW, no Vulkan, no external deps beyond lightrt + X11
// X11 loaded at runtime via dlopen — no libx11-dev needed at compile time.

#include "x11/lightrt_x11.h"
#define LIGHTRT_X11_IMPLEMENTATION
#include "x11/lightrt_x11_loader.h"

#include "common/viewer_common.h"
#include "lightrt_c.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <time.h>

using namespace lightrt_viewer;

// --- Globals ---
static ViewerState g_state;
static bool        g_running = true;
static Display*    g_dpy = nullptr;
static Window      g_win = 0;

// --- File loading ---

static void ShowOpenFileDialog();
static void LoadAndRebuildC11(const std::string& path);

static void ShowOpenFileDialog() {
    // Try zenity (GNOME/GTK), then kdialog (KDE)
    FILE* f = popen("zenity --file-selection --title='Open File' 2>/dev/null", "r");
    if (!f) f = popen("kdialog --getopenfilename . 2>/dev/null", "r");
    if (!f) {
        std::cerr << "No file dialog available — install zenity or kdialog\n";
        return;
    }
    char buf[4096] = {};
    if (fgets(buf, sizeof(buf), f)) {
        size_t len = strlen(buf);
        if (len > 0 && buf[len - 1] == '\n') buf[len - 1] = '\0';
        if (buf[0] != '\0') LoadAndRebuildC11(buf);
    }
    pclose(f);
}

// --- C11 flat scene (replaces C++ TriangleBVH traversal) ---

struct C11Scene {
    std::vector<float> vertices;       // 9 * num_tris (v0x,v0y,v0z,v1x,v1y,v1z,v2x,v2y,v2z)
    std::vector<float> colors;         // 3 * num_tris (base color per triangle)
    std::vector<uint32_t> instance_ids; // instance index per triangle (for albedo lookup)
    int num_tris = 0;
    int num_threads = 1;
    std::vector<lrt_scene*> scenes;    // one lrt_scene per thread (not thread-safe otherwise)

    ~C11Scene() {
        for (auto* s : scenes) lrt_scene_free(s);
    }
};

static C11Scene g_c11scene;

static lrt_aabb c11_bounds_cb(unsigned prim, void* user) {
    C11Scene* cs = static_cast<C11Scene*>(user);
    float* v = &cs->vertices[prim * 9];
    lrt_aabb bb;
    bb.lo[0] = bb.hi[0] = v[0];
    bb.lo[1] = bb.hi[1] = v[1];
    bb.lo[2] = bb.hi[2] = v[2];
    for (int i = 1; i < 3; i++) {
        float* p = &v[i * 3];
        if (p[0] < bb.lo[0]) bb.lo[0] = p[0];
        if (p[1] < bb.lo[1]) bb.lo[1] = p[1];
        if (p[2] < bb.lo[2]) bb.lo[2] = p[2];
        if (p[0] > bb.hi[0]) bb.hi[0] = p[0];
        if (p[1] > bb.hi[1]) bb.hi[1] = p[1];
        if (p[2] > bb.hi[2]) bb.hi[2] = p[2];
    }
    return bb;
}

static int c11_intersect_cb(const double org[3], const double dir[3],
                            double tmin, double tmax, unsigned prim,
                            void* user, double* t, double* u, double* v) {
    C11Scene* cs = static_cast<C11Scene*>(user);
    float* verts = &cs->vertices[prim * 9];

    double v0[3] = {verts[0], verts[1], verts[2]};
    double v1[3] = {verts[3], verts[4], verts[5]};
    double v2[3] = {verts[6], verts[7], verts[8]};

    double e1[3] = {v1[0] - v0[0], v1[1] - v0[1], v1[2] - v0[2]};
    double e2[3] = {v2[0] - v0[0], v2[1] - v0[1], v2[2] - v0[2]};

    double pvec[3];
    pvec[0] = dir[1] * e2[2] - dir[2] * e2[1];
    pvec[1] = dir[2] * e2[0] - dir[0] * e2[2];
    pvec[2] = dir[0] * e2[1] - dir[1] * e2[0];

    double det = e1[0] * pvec[0] + e1[1] * pvec[1] + e1[2] * pvec[2];
    if (det > -1e-12 && det < 1e-12) return 0;

    double inv_det = 1.0 / det;

    double tvec[3] = {org[0] - v0[0], org[1] - v0[1], org[2] - v0[2]};

    double uu = (tvec[0] * pvec[0] + tvec[1] * pvec[1] + tvec[2] * pvec[2]) * inv_det;
    if (uu < 0.0 || uu > 1.0) return 0;

    double qvec[3];
    qvec[0] = tvec[1] * e1[2] - tvec[2] * e1[1];
    qvec[1] = tvec[2] * e1[0] - tvec[0] * e1[2];
    qvec[2] = tvec[0] * e1[1] - tvec[1] * e1[0];

    double vv = (dir[0] * qvec[0] + dir[1] * qvec[1] + dir[2] * qvec[2]) * inv_det;
    if (vv < 0.0 || uu + vv > 1.0) return 0;

    double tt = (e2[0] * qvec[0] + e2[1] * qvec[1] + e2[2] * qvec[2]) * inv_det;
    if (tt < tmin || tt > tmax) return 0;

    *t = tt;
    *u = uu;
    *v = vv;
    return 1;
}

static void buildC11Scene(C11Scene& cs, const scene::Scene& sc, int num_threads) {
    for (auto* s : cs.scenes) lrt_scene_free(s);
    cs.scenes.clear();
    cs.vertices.clear();
    cs.colors.clear();
    cs.instance_ids.clear();
    cs.num_tris = 0;
    cs.num_threads = num_threads;

    int total = 0;
    for (const auto& inst : sc.instances)
        total += (int)sc.meshes[inst.mesh_id].bvh.getTriangles().size();
    cs.num_tris = total;
    if (total == 0) return;

    cs.vertices.reserve(total * 9);
    cs.colors.reserve(total * 3);
    cs.instance_ids.reserve(total);

    for (uint32_t i = 0; i < (uint32_t)sc.instances.size(); i++) {
        const auto& inst = sc.instances[i];
        const auto& blas = sc.meshes[inst.mesh_id];
        const auto& tris = blas.bvh.getTriangles();

        lightrt::Vec3 color(0.8f, 0.8f, 0.8f);
        int32_t mat_id = blas.default_material_id;
        if (mat_id >= 0 && mat_id < (int32_t)sc.materials.size())
            color = sc.materials[mat_id].base_color;

        for (const auto& tri : tris) {
            lightrt::Vec3 v0 = lightrt_common::transformPoint(inst.transform, tri.v0);
            lightrt::Vec3 v1 = lightrt_common::transformPoint(inst.transform, tri.v1);
            lightrt::Vec3 v2 = lightrt_common::transformPoint(inst.transform, tri.v2);

            cs.vertices.push_back(v0.x); cs.vertices.push_back(v0.y); cs.vertices.push_back(v0.z);
            cs.vertices.push_back(v1.x); cs.vertices.push_back(v1.y); cs.vertices.push_back(v1.z);
            cs.vertices.push_back(v2.x); cs.vertices.push_back(v2.y); cs.vertices.push_back(v2.z);
            cs.colors.push_back(color.x); cs.colors.push_back(color.y); cs.colors.push_back(color.z);
            cs.instance_ids.push_back(i);
        }
    }

    cs.scenes.resize(num_threads);
    for (int t = 0; t < num_threads; t++) {
        cs.scenes[t] = lrt_scene_create((unsigned)total, c11_bounds_cb, c11_intersect_cb, &cs);
        if (cs.scenes[t]) lrt_scene_build(cs.scenes[t]);
    }
}

// Helper: load scene and rebuild C11 BVH
static void LoadAndRebuildC11(const std::string& path) {
    std::cout << "Loading " << path << "...\n";
    scene::Scene newScene;
    if (!LoadModel(path, newScene)) {
        std::cerr << "Failed to load: " << path << "\n";
        return;
    }
    if (sceneTriangleCount(newScene) == 0) {
        std::cerr << "No triangles in: " << path << "\n";
        return;
    }
    g_state.scene = std::move(newScene);
    int num_threads = std::max(1, (int)std::thread::hardware_concurrency());
    buildC11Scene(g_c11scene, g_state.scene, num_threads);
    FitToScene(g_state);
    std::cout << "Scene: " << g_state.scene.meshes.size() << " meshes, "
              << g_c11scene.num_tris << " triangles.\n";
    size_t sep = path.find_last_of("/\\");
    std::string fname = (sep != std::string::npos) ? path.substr(sep + 1) : path;
    std::string title = "LightRT Viewer (X11) - " + fname;
    if (g_dpy && g_win) XStoreName(g_dpy, g_win, title.c_str());
}

// --- Timing helpers ---

static uint64_t GetTimeNs() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

// --- X11-specific path tracing using C11 API ---

// Inline helpers (mirror the ones in viewer_common.cc)
static uint32_t pcg_hash_impl(uint32_t input) {
    uint32_t state = input * 747796405u + 2891336453u;
    uint32_t word = ((state >> ((state >> 28u) + 4u)) ^ state) * 277803737u;
    return (word >> 22u) ^ word;
}

static float rand_float_impl(uint32_t& seed) {
    seed = pcg_hash_impl(seed);
    return (float)(seed & 0xFFFFFFu) / (float)0x1000000u;
}

static Vec3 cosine_hemisphere_impl(float u1, float u2, const Vec3& normal) {
    return lightrt_common::shading::cosineHemisphere(u1, u2, normal);
}

static Vec3 vmul_impl(const Vec3& a, const Vec3& b) {
    return Vec3(a.x * b.x, a.y * b.y, a.z * b.z);
}

static Vec3 jitter_direction_impl(const Vec3& dir, float half_angle, uint32_t& seed) {
    float u1 = rand_float_impl(seed);
    float u2 = rand_float_impl(seed);
    float cos_max = cosf(half_angle);
    float cos_theta = 1.0f - u1 * (1.0f - cos_max);
    float sin_theta = sqrtf(std::max(0.0f, 1.0f - cos_theta * cos_theta));
    float phi = 2.0f * (float)lightrt_common::shading::kPi * u2;

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

static void PathTraceX11(ViewerState& state, C11Scene& cs) {
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
    float scale = tanf(state.camera.fov * 0.5f * (float)lightrt_common::shading::kPi / 180.0f);

    uint32_t sampleIdx = state.sampleCount;
    Vec3 sunDir = state.sunDirection;
    ShadowMode shadowMode = state.shadowMode;

    float shadowConeAngle = 0.0f;
    if (shadowMode == SHADOW_SOFT) shadowConeAngle = 0.035f;
    else if (shadowMode == SHADOW_STRONG_SOFT) shadowConeAngle = 0.087f;

    int num_threads = cs.num_threads;
    std::vector<std::thread> threads;

    for (int t = 0; t < num_threads; ++t) {
        threads.emplace_back([&, t, sampleIdx, sunDir, shadowMode, shadowConeAngle]() {
            lrt_scene* local_scene = cs.scenes[t];
            int start_y = t * (height / num_threads);
            int end_y = (t == num_threads - 1) ? height : (t + 1) * (height / num_threads);

            for (int y = start_y; y < end_y; ++y) {
                for (int x = 0; x < width; ++x) {
                    uint32_t seed = pcg_hash_impl((uint32_t)x + (uint32_t)y * 65537u + sampleIdx * 1000003u);

                    float jx = rand_float_impl(seed);
                    float jy = rand_float_impl(seed);

                    float px = (2.0f * (x + jx) * invWidth - 1.0f) * aspectRatio * scale;
                    float py = (1.0f - 2.0f * (y + jy) * invHeight) * scale;

                    Vec3 dir = (state.camera.forward + state.camera.right * px + state.camera.up * py).normalize();
                    Vec3 origin = state.camera.position;

                    double org[3] = {origin.x, origin.y, origin.z};
                    double ddir[3] = {dir.x, dir.y, dir.z};

                    double hit_t, hit_u, hit_v;
                    unsigned prim = lrt_scene_intersect(local_scene, org, ddir,
                                                        1e-6, 1e30, &hit_t, &hit_u, &hit_v);

                    Vec3 color(0, 0, 0);

                    if (prim == LRT_NO_HIT) {
                        color = SampleSky(dir, sunDir);
                    } else {
                        // Compute face normal from world-space triangle vertices
                        float* verts = &cs.vertices[prim * 9];
                        Vec3 v0(verts[0], verts[1], verts[2]);
                        Vec3 v1(verts[3], verts[4], verts[5]);
                        Vec3 v2(verts[6], verts[7], verts[8]);
                        Vec3 normal = (v1 - v0).cross(v2 - v0).normalize();

                        if (normal.dot(dir) > 0.0f) normal = normal * -1.0f;

                        Vec3 hitPos(origin + dir * (float)hit_t);
                        Vec3 albedo(cs.colors[prim * 3], cs.colors[prim * 3 + 1], cs.colors[prim * 3 + 2]);

                        // Direct lighting with optional soft shadow
                        Vec3 shadowDir = sunDir;
                        if (shadowConeAngle > 0.0f)
                            shadowDir = jitter_direction_impl(sunDir, shadowConeAngle, seed);

                        float NdotL = std::max(0.0f, normal.dot(shadowDir));
                        float directLight = 0.0f;
                        if (NdotL > 0.0f) {
                            bool occluded = false;
                            if (shadowMode != SHADOW_OFF) {
                                double s_org[3] = {hitPos.x + normal.x * 0.001f,
                                                   hitPos.y + normal.y * 0.001f,
                                                   hitPos.z + normal.z * 0.001f};
                                double s_dir[3] = {shadowDir.x, shadowDir.y, shadowDir.z};
                                double s_t;
                                unsigned s_hit = lrt_scene_intersect(local_scene, s_org, s_dir,
                                                                      0.0, 1e10, &s_t, nullptr, nullptr);
                                occluded = (s_hit != LRT_NO_HIT);
                            }
                            if (!occluded) directLight = NdotL;
                        }

                        Vec3 sunColor(1.5f, 1.4f, 1.2f);
                        Vec3 direct = sunColor * directLight;
                        Vec3 ambient = SampleSky(normal, sunDir) * 0.15f;

                        // Indirect (1 bounce)
                        Vec3 indirect(0, 0, 0);
                        {
                            float u1 = rand_float_impl(seed);
                            float u2 = rand_float_impl(seed);
                            Vec3 bounceDir = cosine_hemisphere_impl(u1, u2, normal);
                            Vec3 bOrg = hitPos + normal * 0.001f;

                            double b_org[3] = {bOrg.x, bOrg.y, bOrg.z};
                            double b_dir[3] = {bounceDir.x, bounceDir.y, bounceDir.z};

                            double b_t, b_u, b_v;
                            unsigned b_prim = lrt_scene_intersect(local_scene, b_org, b_dir,
                                                                   1e-6, 1e30, &b_t, &b_u, &b_v);

                            if (b_prim == LRT_NO_HIT) {
                                indirect = SampleSky(bounceDir, sunDir);
                            } else {
                                float* b_verts = &cs.vertices[b_prim * 9];
                                Vec3 bv0(b_verts[0], b_verts[1], b_verts[2]);
                                Vec3 bv1(b_verts[3], b_verts[4], b_verts[5]);
                                Vec3 bv2(b_verts[6], b_verts[7], b_verts[8]);
                                Vec3 bnorm = (bv1 - bv0).cross(bv2 - bv0).normalize();
                                if (bnorm.dot(bounceDir) > 0.0f) bnorm = bnorm * -1.0f;

                                Vec3 bHitPos(bOrg + bounceDir * (float)b_t);

                                Vec3 bShadowDir = sunDir;
                                if (shadowConeAngle > 0.0f)
                                    bShadowDir = jitter_direction_impl(sunDir, shadowConeAngle, seed);

                                float bNdotL = std::max(0.0f, bnorm.dot(bShadowDir));
                                float bDirect = 0.0f;
                                if (bNdotL > 0.0f) {
                                    bool bOcc = false;
                                    if (shadowMode != SHADOW_OFF) {
                                        double bs_org[3] = {bHitPos.x + bnorm.x * 0.001f,
                                                            bHitPos.y + bnorm.y * 0.001f,
                                                            bHitPos.z + bnorm.z * 0.001f};
                                        double bs_dir[3] = {bShadowDir.x, bShadowDir.y, bShadowDir.z};
                                        double bs_t;
                                        unsigned bs_hit = lrt_scene_intersect(local_scene, bs_org, bs_dir,
                                                                               0.0, 1e10, &bs_t, nullptr, nullptr);
                                        bOcc = (bs_hit != LRT_NO_HIT);
                                    }
                                    if (!bOcc) bDirect = bNdotL;
                                }
                                Vec3 bAlbedo(cs.colors[b_prim * 3], cs.colors[b_prim * 3 + 1], cs.colors[b_prim * 3 + 2]);
                                Vec3 bAmbient = SampleSky(bnorm, sunDir) * 0.15f;
                                indirect = vmul_impl(sunColor * bDirect + bAmbient, bAlbedo);
                            }
                        }

                        color = vmul_impl(direct + ambient + indirect, albedo);
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

static void RenderFrameX11(ViewerState& state, C11Scene& cs) {
    int w = (int)state.width;
    int h = (int)state.height;

    PathTraceX11(state, cs);

    int fs = state.fontScale;
    int lineH = 10 * fs;

    std::string stats = "FPS: " + std::to_string((int)state.fps);
    DrawString(10, 10, stats.c_str(), 0xFFFFFFFF, state.pixels.data(), w, h, fs);

    std::string tris = "Tris: " + std::to_string(cs.num_tris);
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

// --- Entry Point ---

int main(int argc, char* argv[]) {
    // Parse command line
    if (argc < 2) {
        std::cout << "No model specified, using default scene.\n";
        CreateDefaultScene(g_state.scene);
    } else {
        std::string path = argv[1];
        std::cout << "Loading " << path << "...\n";

        if (!LoadModel(path, g_state.scene)) {
            std::cerr << "Failed to load model.\n";
            return 1;
        }
    }

    if (sceneTriangleCount(g_state.scene) == 0) {
        std::cerr << "No triangles in scene.\n";
        return 1;
    }

    std::cout << "Scene: " << g_state.scene.meshes.size() << " meshes, "
              << sceneTriangleCount(g_state.scene) << " triangles.\n";

    // Build C11 scene (flat BVH over world-space triangles, one lrt_scene per thread)
    int num_threads = std::max(1, (int)std::thread::hardware_concurrency());
    buildC11Scene(g_c11scene, g_state.scene, num_threads);

    // Initialize sun direction and accumulation buffer
    g_state.sunDirection = Vec3(1, 1, -0.5f).normalize();
    g_state.pixels.resize(g_state.width * g_state.height);
    g_state.accumBuffer.resize((size_t)g_state.width * g_state.height * 3, 0.0f);
    FitToScene(g_state);

    // Load X11 at runtime
    if (lightrt_x11_load(&g_x11_) != 0) {
        std::cerr << "Failed to load libX11.so.6 — is X11 installed?\n";
        return 1;
    }

    // Open X11 display
    Display* dpy = XOpenDisplay(nullptr);
    if (!dpy) {
        std::cerr << "Cannot open X display.\n";
        lightrt_x11_unload(&g_x11_);
        return 1;
    }

    int screen = DefaultScreen(dpy);
    Window root = RootWindow(dpy, screen);
    Visual* visual = DefaultVisual(dpy, screen);
    int depth = DefaultDepth(dpy, screen);

    // Require 24/32-bit TrueColor for direct pixel blitting
    if (depth < 24) {
        std::cerr << "Need 24-bit or 32-bit display depth, got " << depth << ".\n";
        XCloseDisplay(dpy);
        return 1;
    }

    // HiDPI detection: scale window and font for high-DPI displays (4K+)
    {
        Screen* xscreen = ScreenOfDisplay(dpy, screen);
        int w_px = WidthOfScreen(xscreen);
        int h_px = HeightOfScreen(xscreen);
        int w_mm = WidthMMOfScreen(xscreen);
        double dpi = (w_mm > 0) ? (double)w_px * 25.4 / (double)w_mm : 96.0;

        if (dpi > 150.0) {
            // Scale window to ~80% of screen for high-DPI displays
            uint32_t new_w = std::max(g_state.width, (uint32_t)((double)w_px * 0.8));
            uint32_t new_h = std::max(g_state.height, (uint32_t)((double)h_px * 0.8));
            ResizeFramebuffer(g_state, new_w, new_h);
            // 2x font for 150-250 DPI, 3x for 250+
            g_state.fontScale = (dpi > 250.0) ? 3 : 2;
        }
    }

    // Create window
    XSetWindowAttributes attrs;
    attrs.background_pixel = BlackPixel(dpy, screen);
    attrs.event_mask = ExposureMask | StructureNotifyMask |
                       KeyPressMask | KeyReleaseMask |
                       ButtonPressMask | ButtonReleaseMask |
                       PointerMotionMask;

    Window win = XCreateWindow(
        dpy, root,
        0, 0, g_state.width, g_state.height,
        0, depth, InputOutput, visual,
        CWBackPixel | CWEventMask, &attrs);

    XStoreName(dpy, win, "LightRT Viewer (X11)");

    // Handle WM_DELETE_WINDOW
    Atom wm_delete = XInternAtom(dpy, "WM_DELETE_WINDOW", False);
    XSetWMProtocols(dpy, win, &wm_delete, 1);

    XMapWindow(dpy, win);
    g_dpy = dpy;
    g_win = win;

    // Create GC for drawing
    GC gc = XCreateGC(dpy, win, 0, nullptr);

    // Create XImage for pixel blitting
    XImage* ximg = XCreateImage(
        dpy, visual, depth, ZPixmap, 0,
        (char*)g_state.pixels.data(),
        g_state.width, g_state.height,
        32, 0);
    // XImage does NOT own the pixel data — we manage it
    ximg->byte_order = LSBFirst;

    uint64_t lastTime = GetTimeNs();
    uint64_t fpsTimer = lastTime;
    int fpsFrameCount = 0;

    std::cout << "Controls: Alt+LMB/Shift+LMB Orbit, Alt+MMB/Ctrl+LMB Pan, Alt+RMB/Ctrl+Shift+LMB/Tab+LMB Dolly\n";
    std::cout << "          F: Fit, S: Shadow, +: Font 2x, O: Open File (zenity/kdialog)\n";

    // Main loop
    while (g_running) {
        // Process all pending events
        while (XPending(dpy)) {
            XEvent ev;
            XNextEvent(dpy, &ev);

            switch (ev.type) {
            case ClientMessage:
                if ((Atom)ev.xclient.data.l[0] == wm_delete) {
                    g_running = false;
                }
                break;

            case ConfigureNotify: {
                uint32_t w = (uint32_t)ev.xconfigure.width;
                uint32_t h = (uint32_t)ev.xconfigure.height;
                if (w > 0 && h > 0 && (w != g_state.width || h != g_state.height)) {
                    ResizeFramebuffer(g_state, w, h);

                    // Recreate XImage for new size
                    // Set data to null so XDestroyImage doesn't free our buffer
                    ximg->data = nullptr;
                    XDestroyImage(ximg);

                    ximg = XCreateImage(
                        dpy, visual, depth, ZPixmap, 0,
                        (char*)g_state.pixels.data(),
                        g_state.width, g_state.height,
                        32, 0);
                    ximg->byte_order = LSBFirst;
                }
                break;
            }

            case KeyPress: {
                KeySym ks = XLookupKeysym(&ev.xkey, 0);
                switch (ks) {
                case XK_f: case XK_F:
                    g_state.keys[KEY_F] = true; break;
                case XK_s: case XK_S:
                    g_state.keys[KEY_S] = true; break;
                case XK_plus: case XK_equal:
                    g_state.keys[KEY_PLUS] = true; break;
                case XK_o: case XK_O:
                    ShowOpenFileDialog(); break;
                case XK_Escape:
                    g_state.keys[KEY_ESCAPE] = true; break;
                case XK_Shift_L: case XK_Shift_R:
                    g_state.shiftPressed = true; break;
                case XK_Control_L: case XK_Control_R:
                    g_state.ctrlPressed = true; break;
                case XK_Alt_L: case XK_Alt_R:
                    g_state.altPressed = true; break;
                case XK_Tab:
                    g_state.tabPressed = true; break;
                }
                break;
            }

            case KeyRelease: {
                // Filter out auto-repeat: if next event is KeyPress of same key, skip both
                if (XEventsQueued(dpy, QueuedAfterReading)) {
                    XEvent next;
                    XPeekEvent(dpy, &next);
                    if (next.type == KeyPress &&
                        next.xkey.time == ev.xkey.time &&
                        next.xkey.keycode == ev.xkey.keycode) {
                        // Auto-repeat pair — consume the KeyPress and ignore both
                        XNextEvent(dpy, &next);
                        break;
                    }
                }

                KeySym ks = XLookupKeysym(&ev.xkey, 0);
                switch (ks) {
                case XK_f: case XK_F:
                    g_state.keys[KEY_F] = false; break;
                case XK_s: case XK_S:
                    g_state.keys[KEY_S] = false; break;
                case XK_plus: case XK_equal:
                    g_state.keys[KEY_PLUS] = false; break;
                case XK_Escape:
                    g_state.keys[KEY_ESCAPE] = false; break;
                case XK_Shift_L: case XK_Shift_R:
                    g_state.shiftPressed = false; break;
                case XK_Control_L: case XK_Control_R:
                    g_state.ctrlPressed = false; break;
                case XK_Alt_L: case XK_Alt_R:
                    g_state.altPressed = false; break;
                case XK_Tab:
                    g_state.tabPressed = false; break;
                }
                break;
            }

            case ButtonPress: {
                double x = (double)ev.xbutton.x;
                double y = (double)ev.xbutton.y;
                switch (ev.xbutton.button) {
                case Button1:
                    g_state.lmbPressed = true;
                    OnMouseDown(g_state, x, y);
                    break;
                case Button2:
                    g_state.mmbPressed = true;
                    OnMouseDown(g_state, x, y);
                    break;
                case Button3:
                    g_state.rmbPressed = true;
                    OnMouseDown(g_state, x, y);
                    break;
                case Button4: // Scroll up
                    DollyCamera(g_state, -0.3f);
                    break;
                case Button5: // Scroll down
                    DollyCamera(g_state, 0.3f);
                    break;
                }
                break;
            }

            case ButtonRelease: {
                switch (ev.xbutton.button) {
                case Button1:
                    g_state.lmbPressed = false;
                    if (!g_state.mmbPressed && !g_state.rmbPressed)
                        g_state.dragging = false;
                    break;
                case Button2:
                    g_state.mmbPressed = false;
                    if (!g_state.lmbPressed && !g_state.rmbPressed)
                        g_state.dragging = false;
                    break;
                case Button3:
                    g_state.rmbPressed = false;
                    if (!g_state.lmbPressed && !g_state.mmbPressed)
                        g_state.dragging = false;
                    break;
                }
                break;
            }

            case MotionNotify: {
                double x = (double)ev.xmotion.x;
                double y = (double)ev.xmotion.y;
                OnMouseDrag(g_state, x, y);
                break;
            }
            } // switch
        } // while XPending

        if (!g_running) break;

        // Timing
        uint64_t now = GetTimeNs();
        float dt = (float)(now - lastTime) / 1e9f;
        lastTime = now;

        // FPS counter
        fpsFrameCount++;
        float fpsElapsed = (float)(now - fpsTimer) / 1e9f;
        if (fpsElapsed >= 1.0f) {
            g_state.fps = fpsFrameCount / fpsElapsed;
            fpsFrameCount = 0;
            fpsTimer = now;
        }

        // Process input
        if (ProcessInput(g_state, dt)) {
            g_running = false;
            break;
        }

        // Render (using C11 API for ray intersection)
        RenderFrameX11(g_state, g_c11scene);

        // Blit to window via XPutImage
        // g_state.pixels is BGRA (uint32_t) which matches X11 ZPixmap on little-endian
        XPutImage(dpy, win, gc, ximg,
                  0, 0, 0, 0, g_state.width, g_state.height);
        XFlush(dpy);
    }

    // Cleanup — set data to null so XDestroyImage doesn't free our buffer
    ximg->data = nullptr;
    XDestroyImage(ximg);
    XFreeGC(dpy, gc);
    XDestroyWindow(dpy, win);
    XCloseDisplay(dpy);
    lightrt_x11_unload(&g_x11_);

    return 0;
}
