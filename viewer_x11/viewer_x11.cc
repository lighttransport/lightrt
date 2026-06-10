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

// --- Benchmark mode: procedural mandelbulb + rays/sec measurement ---

// Direct C11 scene build from raw triangles (no scene::Scene needed)
static void buildC11SceneFromTriangles(C11Scene& cs,
                                       const float* verts, int num_tris,
                                       const float* colors,
                                       int num_threads) {
    for (auto* s : cs.scenes) lrt_scene_free(s);
    cs.scenes.clear();
    cs.vertices.clear();
    cs.colors.clear();
    cs.instance_ids.clear();
    cs.num_tris = 0;
    cs.num_threads = num_threads;
    if (num_tris == 0) return;

    cs.vertices.assign(verts, verts + num_tris * 9);
    cs.colors.assign(colors, colors + num_tris * 3);
    cs.instance_ids.resize(num_tris, 0);
    cs.num_tris = num_tris;

    cs.scenes.resize(num_threads);
    for (int t = 0; t < num_threads; t++) {
        cs.scenes[t] = lrt_scene_create((unsigned)num_tris,
                                        c11_bounds_cb, c11_intersect_cb, &cs);
        if (cs.scenes[t]) lrt_scene_build(cs.scenes[t]);
    }
}

// --- Marching Cubes (mandelbulb mesh generation) ---

static const int kMcEdgeTable[256] = {
    0x0, 0x109, 0x203, 0x30a, 0x406, 0x50f, 0x605, 0x70c, 0x80c, 0x905, 0xa0f, 0xb06, 0xc0a, 0xd03, 0xe09, 0xf00,
    0x190, 0x99, 0x393, 0x29a, 0x596, 0x49f, 0x795, 0x69c, 0x99c, 0x895, 0xb9f, 0xa96, 0xd9a, 0xc93, 0xf99, 0xe90,
    0x230, 0x339, 0x33, 0x13a, 0x636, 0x73f, 0x435, 0x53c, 0xa3c, 0xb35, 0x83f, 0x936, 0xe3a, 0xf33, 0xc39, 0xd30,
    0x3a0, 0x2a9, 0x1a3, 0xaa, 0x7a6, 0x6af, 0x5a5, 0x4ac, 0xbac, 0xaa5, 0x9af, 0x8a6, 0xfaa, 0xea3, 0xda9, 0xca0,
    0x460, 0x569, 0x663, 0x76a, 0x66, 0x16f, 0x265, 0x36c, 0xc6c, 0xd65, 0xe6f, 0xf66, 0x86a, 0x963, 0xa69, 0xb60,
    0x5f0, 0x4f9, 0x7f3, 0x6fa, 0x1f6, 0xff, 0x3f5, 0x2fc, 0xdfc, 0xcf5, 0xfff, 0xef6, 0x9fa, 0x8f3, 0xbf9, 0xaf0,
    0x650, 0x759, 0x453, 0x55a, 0x256, 0x35f, 0x55, 0x15c, 0xe5c, 0xf55, 0xc5f, 0xd56, 0xa5a, 0xb53, 0x859, 0x950,
    0x7c0, 0x6c9, 0x5c3, 0x4ca, 0x3c6, 0x2cf, 0x1c5, 0xcc, 0xfcc, 0xec5, 0xdcf, 0xcc6, 0xbca, 0xac3, 0x9c9, 0x8c0,
    0x8c0, 0x9c9, 0xac3, 0xbca, 0xcc6, 0xdcf, 0xec5, 0xfcc, 0xcc, 0x1c5, 0x2cf, 0x3c6, 0x4ca, 0x5c3, 0x6c9, 0x7c0,
    0x950, 0x859, 0xb53, 0xa5a, 0xd56, 0xc5f, 0xf55, 0xe5c, 0x15c, 0x55, 0x35f, 0x256, 0x55a, 0x453, 0x759, 0x650,
    0xaf0, 0xbf9, 0x8f3, 0x9fa, 0xef6, 0xfff, 0xcf5, 0xdfc, 0x2fc, 0x3f5, 0xff, 0x1f6, 0x6fa, 0x7f3, 0x4f9, 0x5f0,
    0xb60, 0xa69, 0x963, 0x86a, 0xf66, 0xe6f, 0xd65, 0xc6c, 0x36c, 0x265, 0x16f, 0x66, 0x76a, 0x663, 0x569, 0x460,
    0xca0, 0xda9, 0xea3, 0xfaa, 0x8a6, 0x9af, 0xaa5, 0xbac, 0x4ac, 0x5a5, 0x6af, 0x7a6, 0xaa, 0x1a3, 0x2a9, 0x3a0,
    0xd30, 0xc39, 0xf33, 0xe3a, 0x936, 0x83f, 0xb35, 0xa3c, 0x53c, 0x435, 0x73f, 0x636, 0x13a, 0x33, 0x339, 0x230,
    0xe90, 0xf99, 0xc93, 0xd9a, 0xa96, 0xb9f, 0x895, 0x99c, 0x69c, 0x795, 0x49f, 0x596, 0x29a, 0x393, 0x99, 0x190,
    0xf00, 0xe09, 0xd03, 0xc0a, 0xb06, 0xa0f, 0x905, 0x80c, 0x70c, 0x605, 0x50f, 0x406, 0x30a, 0x203, 0x109, 0x0
};

static const int kMcTriTable[256][16] = {
    {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,1,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,8,3,9,8,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {9,2,10,0,2,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {2,8,3,2,10,8,10,9,8,-1,-1,-1,-1,-1,-1,-1},
    {3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,11,2,8,11,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,9,0,2,3,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,11,2,1,9,11,9,8,11,-1,-1,-1,-1,-1,-1,-1},
    {3,10,1,11,10,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,10,1,0,8,10,8,11,10,-1,-1,-1,-1,-1,-1,-1},
    {3,9,0,3,11,9,11,10,9,-1,-1,-1,-1,-1,-1,-1},
    {9,8,10,10,8,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {4,7,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {4,3,0,7,3,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,1,9,8,4,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {4,1,9,4,7,1,7,3,1,-1,-1,-1,-1,-1,-1,-1},
    {1,2,10,8,4,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {3,4,7,3,0,4,1,2,10,-1,-1,-1,-1,-1,-1,-1},
    {9,2,10,9,0,2,8,4,7,-1,-1,-1,-1,-1,-1,-1},
    {2,10,9,2,9,7,2,7,3,7,9,4,-1,-1,-1,-1},
    {8,4,7,3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {11,4,7,11,2,4,2,0,4,-1,-1,-1,-1,-1,-1,-1},
    {9,0,1,8,4,7,2,3,11,-1,-1,-1,-1,-1,-1,-1},
    {4,7,11,9,4,11,9,11,2,9,2,1,-1,-1,-1,-1},
    {3,10,1,3,11,10,7,8,4,-1,-1,-1,-1,-1,-1,-1},
    {1,11,10,1,4,11,1,0,4,7,11,4,-1,-1,-1,-1},
    {4,7,8,9,0,11,9,11,10,11,0,3,-1,-1,-1,-1},
    {4,7,11,4,11,9,9,11,10,-1,-1,-1,-1,-1,-1,-1},
    {9,5,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {9,5,4,0,8,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,5,4,1,5,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {8,5,4,8,3,5,3,1,5,-1,-1,-1,-1,-1,-1,-1},
    {1,2,10,9,5,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {3,0,8,1,2,10,4,9,5,-1,-1,-1,-1,-1,-1,-1},
    {5,2,10,5,4,2,4,0,2,-1,-1,-1,-1,-1,-1,-1},
    {2,10,5,3,2,5,3,5,4,3,4,8,-1,-1,-1,-1},
    {9,5,4,2,3,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,11,2,0,8,11,4,9,5,-1,-1,-1,-1,-1,-1,-1},
    {0,5,4,0,1,5,2,3,11,-1,-1,-1,-1,-1,-1,-1},
    {2,1,5,2,5,8,2,8,11,4,8,5,-1,-1,-1,-1},
    {10,3,11,10,1,3,9,5,4,-1,-1,-1,-1,-1,-1,-1},
    {4,9,5,0,8,1,8,10,1,8,11,10,-1,-1,-1,-1},
    {5,4,0,5,0,11,5,11,10,11,0,3,-1,-1,-1,-1},
    {5,4,8,5,8,10,10,8,11,-1,-1,-1,-1,-1,-1,-1},
    {9,7,8,5,7,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {9,3,0,9,5,3,5,7,3,-1,-1,-1,-1,-1,-1,-1},
    {0,7,8,0,1,7,1,5,7,-1,-1,-1,-1,-1,-1,-1},
    {1,5,3,3,5,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {9,7,8,9,5,7,10,1,2,-1,-1,-1,-1,-1,-1,-1},
    {10,1,2,9,5,0,5,3,0,5,7,3,-1,-1,-1,-1},
    {8,0,2,8,2,5,8,5,7,10,5,2,-1,-1,-1,-1},
    {2,10,5,2,5,3,3,5,7,-1,-1,-1,-1,-1,-1,-1},
    {7,9,5,7,8,9,3,11,2,-1,-1,-1,-1,-1,-1,-1},
    {9,5,7,9,7,2,9,2,0,2,7,11,-1,-1,-1,-1},
    {2,3,11,0,1,8,1,7,8,1,5,7,-1,-1,-1,-1},
    {11,2,1,11,1,7,7,1,5,-1,-1,-1,-1,-1,-1,-1},
    {9,5,8,8,5,7,10,1,3,10,3,11,-1,-1,-1,-1},
    {5,7,0,5,0,9,7,11,0,1,0,10,11,10,0,-1},
    {11,10,0,11,0,3,10,5,0,8,0,7,5,7,0,-1},
    {11,10,5,7,11,5,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {10,6,5,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,5,10,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {9,0,1,5,10,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,8,3,1,9,8,5,10,6,-1,-1,-1,-1,-1,-1,-1},
    {1,6,5,2,6,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,6,5,1,2,6,3,0,8,-1,-1,-1,-1,-1,-1,-1},
    {9,6,5,9,0,6,0,2,6,-1,-1,-1,-1,-1,-1,-1},
    {5,9,8,5,8,2,5,2,6,3,2,8,-1,-1,-1,-1},
    {2,3,11,10,6,5,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {11,0,8,11,2,0,10,6,5,-1,-1,-1,-1,-1,-1,-1},
    {0,1,9,2,3,11,5,10,6,-1,-1,-1,-1,-1,-1,-1},
    {5,10,6,1,9,2,9,11,2,9,8,11,-1,-1,-1,-1},
    {6,3,11,6,5,3,5,1,3,-1,-1,-1,-1,-1,-1,-1},
    {0,8,11,0,11,5,0,5,1,5,11,6,-1,-1,-1,-1},
    {3,11,6,0,3,6,0,6,5,0,5,9,-1,-1,-1,-1},
    {6,5,9,6,9,11,11,9,8,-1,-1,-1,-1,-1,-1,-1},
    {5,10,6,4,7,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {4,3,0,4,7,3,6,5,10,-1,-1,-1,-1,-1,-1,-1},
    {1,9,0,5,10,6,8,4,7,-1,-1,-1,-1,-1,-1,-1},
    {10,6,5,1,9,7,1,7,3,7,9,4,-1,-1,-1,-1},
    {6,1,2,6,5,1,4,7,8,-1,-1,-1,-1,-1,-1,-1},
    {1,2,5,5,2,6,3,0,4,3,4,7,-1,-1,-1,-1},
    {8,4,7,9,0,5,0,6,5,0,2,6,-1,-1,-1,-1},
    {7,3,4,5,9,2,5,2,6,2,9,4,-1,-1,-1,-1},
    {3,11,2,7,8,4,10,6,5,-1,-1,-1,-1,-1,-1,-1},
    {5,10,6,4,7,2,4,7,11,4,11,2,4,2,0,-1},
    {0,1,9,4,7,8,2,3,11,5,10,6,-1,-1,-1,-1},
    {9,2,1,9,11,2,9,4,11,7,11,4,5,10,6,-1},
    {8,4,7,3,11,5,3,5,1,5,11,6,-1,-1,-1,-1},
    {5,1,11,5,11,6,1,0,11,7,11,4,0,4,11,-1},
    {0,5,9,0,3,5,3,11,5,4,7,8,6,5,11,-1},
    {5,11,6,5,9,11,9,4,11,7,11,4,-1,-1,-1,-1},
    {9,5,4,10,6,5,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,5,4,9,10,6,5,-1,-1,-1,-1,-1,-1,-1},
    {0,5,4,0,1,5,10,6,5,-1,-1,-1,-1,-1,-1,-1},
    {8,3,1,8,1,6,8,6,5,8,5,4,6,1,10,-1},
    {1,6,5,1,2,6,9,5,4,-1,-1,-1,-1,-1,-1,-1},
    {9,5,4,0,8,1,8,6,1,8,2,6,1,2,8,-1},
    {0,2,6,0,6,4,4,6,5,-1,-1,-1,-1,-1,-1,-1},
    {8,3,2,8,2,4,4,2,6,6,2,5,-1,-1,-1,-1},
    {10,6,5,9,5,4,2,3,11,-1,-1,-1,-1,-1,-1,-1},
    {4,9,5,0,8,11,0,11,2,11,8,3,10,6,5,-1},
    {5,4,0,5,0,10,10,0,1,2,3,11,6,5,10,-1},
    {10,6,5,1,9,2,9,11,2,9,8,11,4,8,9,-1},
    {6,5,1,6,1,11,11,1,3,9,5,4,-1,-1,-1,-1},
    {0,8,11,0,11,5,0,5,1,5,11,6,4,9,5,-1},
    {5,4,0,5,0,6,6,0,3,6,3,11,-1,-1,-1,-1},
    {5,4,8,5,8,6,6,8,11,-1,-1,-1,-1,-1,-1,-1},
    {7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,1,9,7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,8,3,1,9,8,7,6,11,-1,-1,-1,-1,-1,-1,-1},
    {10,1,2,6,11,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,2,10,3,0,8,6,11,7,-1,-1,-1,-1,-1,-1,-1},
    {2,9,0,2,10,9,6,11,7,-1,-1,-1,-1,-1,-1,-1},
    {6,11,7,2,10,3,10,8,3,10,9,8,-1,-1,-1,-1},
    {7,2,3,6,2,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {7,0,8,7,6,0,6,2,0,-1,-1,-1,-1,-1,-1,-1},
    {2,7,6,2,3,7,0,1,9,-1,-1,-1,-1,-1,-1,-1},
    {1,6,2,1,8,6,1,9,8,8,7,6,-1,-1,-1,-1},
    {10,7,6,10,1,7,1,3,7,-1,-1,-1,-1,-1,-1,-1},
    {10,7,6,1,7,10,1,8,7,1,0,8,-1,-1,-1,-1},
    {0,3,7,0,7,10,0,10,9,6,10,7,-1,-1,-1,-1},
    {7,6,10,7,10,8,8,10,9,-1,-1,-1,-1,-1,-1,-1},
    {6,8,4,11,8,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {3,6,11,3,0,6,0,4,6,-1,-1,-1,-1,-1,-1,-1},
    {8,6,11,8,4,6,9,0,1,-1,-1,-1,-1,-1,-1,-1},
    {9,4,6,9,6,3,9,3,1,11,3,6,-1,-1,-1,-1},
    {6,8,4,6,11,8,2,10,1,-1,-1,-1,-1,-1,-1,-1},
    {1,2,10,3,0,11,0,6,11,0,4,6,-1,-1,-1,-1},
    {4,11,8,4,6,11,0,2,9,2,10,9,-1,-1,-1,-1},
    {10,9,3,10,3,2,9,4,3,11,3,6,4,6,3,-1},
    {8,2,3,8,4,2,4,6,2,-1,-1,-1,-1,-1,-1,-1},
    {0,4,2,4,6,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,9,0,2,3,4,2,3,8,4,3,2,4,6,2,-1},
    {1,9,4,1,4,2,2,4,6,-1,-1,-1,-1,-1,-1,-1},
    {8,1,3,8,6,1,8,4,6,6,10,1,-1,-1,-1,-1},
    {10,1,0,10,0,6,6,0,4,-1,-1,-1,-1,-1,-1,-1},
    {4,6,3,4,3,8,6,10,3,0,3,9,10,9,3,-1},
    {10,9,4,6,10,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {4,9,5,7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,4,9,5,11,7,6,-1,-1,-1,-1,-1,-1,-1},
    {5,0,1,5,4,0,7,6,11,-1,-1,-1,-1,-1,-1,-1},
    {11,7,6,8,3,4,3,5,4,3,1,5,-1,-1,-1,-1},
    {9,5,4,10,1,2,7,6,11,-1,-1,-1,-1,-1,-1,-1},
    {6,11,7,1,2,10,0,8,3,4,9,5,-1,-1,-1,-1},
    {7,6,11,5,4,10,4,2,10,4,0,2,-1,-1,-1,-1},
    {3,4,8,3,5,4,3,2,5,10,5,2,11,7,6,-1},
    {7,2,3,7,6,2,5,4,9,-1,-1,-1,-1,-1,-1,-1},
    {9,5,4,0,8,6,0,6,2,6,8,7,-1,-1,-1,-1},
    {3,7,6,3,6,2,5,4,0,5,0,1,-1,-1,-1,-1},
    {1,5,4,1,4,9,2,1,9,6,2,9,4,5,6,2},
    {5,4,9,7,6,1,7,1,3,1,6,10,-1,-1,-1,-1},
    {1,0,8,1,8,10,10,8,7,10,7,6,4,9,5,-1},
    {3,7,0,7,6,0,5,4,0,6,10,0,10,1,0,-1},
    {7,6,10,7,10,8,8,10,1,8,1,0,5,4,9,-1},
    {6,9,5,6,11,9,11,8,9,-1,-1,-1,-1,-1,-1,-1},
    {3,6,11,0,6,3,0,5,6,0,9,5,-1,-1,-1,-1},
    {0,11,8,0,5,11,0,1,5,5,6,11,-1,-1,-1,-1},
    {6,11,3,6,3,5,5,3,1,-1,-1,-1,-1,-1,-1,-1},
    {1,2,10,9,5,11,9,5,6,11,5,9,11,8,9,-1},
    {0,9,5,0,5,3,3,5,6,3,6,11,1,2,10,-1},
    {8,0,2,8,2,11,11,2,10,11,10,6,9,5,4,-1},
    {2,10,6,2,6,3,3,6,11,-1,-1,-1,-1,-1,-1,-1},
    {8,4,9,8,9,2,8,2,3,2,9,5,6,11,7,-1},
    {0,9,5,0,5,2,2,5,6,2,6,11,7,6,2,-1},
    {1,5,0,1,8,0,3,8,1,4,9,5,2,3,7,-1},
    {1,5,6,1,6,2,5,4,6,7,6,4,-1,-1,-1,-1},
    {8,4,9,8,9,3,3,9,1,5,4,9,6,10,1,3},
    {9,5,4,1,0,10,10,0,6,6,0,4,6,4,5,3},
    {4,9,5,0,3,8,8,3,7,8,7,6,8,6,10,8},
    {5,6,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,2,10,7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,7,6,11,1,2,10,-1,-1,-1,-1,-1,-1,-1},
    {0,1,9,10,1,2,6,11,7,-1,-1,-1,-1,-1,-1,-1},
    {1,9,8,10,9,1,6,11,7,10,1,6,-1,-1,-1,-1},
    {7,6,11,1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,1,2,10,7,6,11,-1,-1,-1,-1,-1,-1,-1},
    {9,0,2,9,2,10,6,11,7,9,10,6,-1,-1,-1,-1},
    {6,11,7,2,10,3,10,8,3,10,9,8,-1,-1,-1,-1},
    {3,1,10,11,3,10,7,6,11,10,7,11,-1,-1,-1,-1},
    {0,8,10,0,10,1,11,10,8,7,11,8,10,7,8,-1},
    {0,1,9,2,3,7,2,7,6,7,3,11,2,6,7,-1},
    {1,9,8,1,8,6,1,6,2,8,7,6,11,6,7,-1},
    {7,6,1,7,1,3,11,1,6,10,1,11,7,11,6,-1},
    {0,8,1,8,10,1,6,11,7,8,6,10,6,8,7,-1},
    {0,3,7,0,7,9,7,6,9,10,9,6,0,9,7,-1},
    {7,6,10,7,10,8,8,10,9,-1,-1,-1,-1,-1,-1,-1},
    {6,8,4,11,8,6,1,2,10,-1,-1,-1,-1,-1,-1,-1},
    {3,0,4,3,4,6,11,4,0,6,5,10,4,11,6,3},
    {8,4,6,8,6,11,0,1,9,8,11,6,-1,-1,-1,-1},
    {9,4,6,9,6,1,6,11,1,10,1,11,9,1,6,-1},
    {6,8,4,6,11,8,2,10,1,-1,-1,-1,-1,-1,-1,-1},
    {1,2,10,3,0,11,0,6,11,0,4,6,-1,-1,-1,-1},
    {4,11,8,4,6,11,0,2,9,2,10,9,-1,-1,-1,-1},
    {10,9,3,10,3,2,9,4,3,11,3,6,4,6,3,-1},
    {8,2,3,8,4,2,4,6,2,1,2,10,-1,-1,-1,-1},
    {0,4,2,4,6,2,1,2,10,-1,-1,-1,-1,-1,-1,-1},
    {1,9,0,2,3,4,2,3,8,4,3,2,4,6,2,-1},
    {1,9,4,1,4,2,2,4,6,-1,-1,-1,-1,-1,-1,-1},
    {8,1,3,8,6,1,8,4,6,6,10,1,-1,-1,-1,-1},
    {10,1,0,10,0,6,6,0,4,-1,-1,-1,-1,-1,-1,-1},
    {4,6,3,4,3,8,6,10,3,0,3,9,10,9,3,-1},
    {10,9,4,6,10,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {4,9,5,7,6,11,1,2,10,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,4,9,5,11,7,6,1,2,10,-1,-1,-1,-1},
    {5,0,1,5,4,0,7,6,11,1,2,10,-1,-1,-1,-1},
    {11,7,6,8,3,4,3,5,4,3,1,5,1,2,10,-1},
    {9,5,4,10,1,2,7,6,11,-1,-1,-1,-1,-1,-1,-1},
    {6,11,7,1,2,10,0,8,3,4,9,5,-1,-1,-1,-1},
    {7,6,11,5,4,10,4,2,10,4,0,2,-1,-1,-1,-1},
    {3,4,8,3,5,4,3,2,5,10,5,2,11,7,6,-1},
    {7,2,3,7,6,2,5,4,9,1,2,10,-1,-1,-1,-1},
    {9,5,4,0,8,6,0,6,2,6,8,7,1,2,10,-1},
    {3,7,6,3,6,2,5,4,0,5,0,1,1,2,10,-1},
    {1,5,4,1,4,9,2,1,9,6,2,9,4,5,6,2},
    {5,4,9,7,6,1,7,1,3,1,6,10,-1,-1,-1,-1},
    {1,0,8,1,8,10,10,8,7,10,7,6,4,9,5,-1},
    {3,7,0,7,6,0,5,4,0,6,10,0,10,1,0,-1},
    {7,6,10,7,10,8,8,10,1,8,1,0,5,4,9,-1},
    {6,9,5,6,11,9,11,8,9,1,2,10,-1,-1,-1,-1},
    {3,6,11,0,6,3,0,5,6,0,9,5,1,2,10,-1},
    {0,11,8,0,5,11,0,1,5,5,6,11,1,2,10,-1},
    {6,11,3,6,3,5,5,3,1,1,2,10,-1,-1,-1,-1},
    {10,1,2,9,5,11,9,5,6,11,5,9,11,8,9,-1},
    {0,9,5,0,5,3,3,5,6,3,6,11,1,2,10,-1},
    {8,0,2,8,2,11,11,2,10,11,10,6,9,5,4,-1},
    {2,10,6,2,6,3,3,6,11,-1,-1,-1,-1,-1,-1,-1},
    {8,4,9,8,9,2,8,2,3,2,9,5,6,11,7,-1},
    {0,9,5,0,5,2,2,5,6,2,6,11,7,6,2,-1},
    {1,5,0,1,8,0,3,8,1,4,9,5,2,3,7,-1},
    {1,5,6,1,6,2,5,4,6,7,6,4,-1,-1,-1,-1},
    {8,4,9,8,9,3,3,9,1,5,4,9,6,10,1,3},
    {9,5,4,1,0,10,10,0,6,6,0,4,6,4,5,3},
    {4,9,5,0,3,8,8,3,7,8,7,6,8,6,10,8},
    {5,6,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {1,2,10,5,6,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,5,10,6,1,2,10,-1,-1,-1,-1,-1,-1,-1},
    {0,1,10,0,10,6,5,10,1,5,6,10,9,0,6,5},
    {8,3,1,8,1,6,8,6,5,8,5,4,6,1,10,-1},
    {5,6,10,1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,3,1,2,10,5,6,10,-1,-1,-1,-1,-1,-1,-1},
    {9,0,2,9,2,10,5,6,10,9,10,6,-1,-1,-1,-1},
    {5,6,10,2,10,3,10,8,3,10,9,8,-1,-1,-1,-1},
    {5,6,10,3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
    {0,8,11,0,11,2,10,6,5,0,2,10,-1,-1,-1,-1},
    {0,1,9,2,3,11,5,6,10,-1,-1,-1,-1,-1,-1,-1},
    {5,10,6,1,9,2,9,11,2,9,8,11,-1,-1,-1,-1},
    {5,6,10,3,11,6,11,1,3,11,5,1,11,6,5,-1},
    {0,8,11,0,11,5,0,5,1,5,11,6,-1,-1,-1,-1},
    {3,11,6,0,3,6,0,6,5,0,5,9,-1,-1,-1,-1},
    {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1}
};

static const int kMcCorner[8][3] = {
    {0,0,0},{1,0,0},{1,0,1},{0,0,1},
    {0,1,0},{1,1,0},{1,1,1},{0,1,1}
};
static const int kMcEdge[12][2] = {
    {0,1},{1,2},{2,3},{3,0},{4,5},{5,6},{6,7},{7,4},{0,4},{1,5},{2,6},{3,7}
};

static float lerp(float a, float b, float t) { return a + (b - a) * t; }

static int marchingCubes(float (*de)(float,float,float,void*), void* de_user,
                         const AABB& bounds, int res,
                         std::vector<float>& out_verts) {
    out_verts.clear();
    int n = res;
    Vec3 sz = bounds.extents();
    Vec3 org = bounds.min;
    float step_x = sz.x / n, step_y = sz.y / n, step_z = sz.z / n;
    int grid_n = n + 1;
    int grid_slice = grid_n * grid_n;

    // Allocate grid
    std::vector<float> grid(grid_n * grid_n * grid_n);
    for (int k = 0; k <= n; k++)
        for (int j = 0; j <= n; j++)
            for (int i = 0; i <= n; i++) {
                float px = org.x + i * step_x, py = org.y + j * step_y, pz = org.z + k * step_z;
                grid[k * grid_slice + j * grid_n + i] = de(px, py, pz, de_user);
            }

    int tri_count = 0;
    for (int k = 0; k < n; k++)
        for (int j = 0; j < n; j++)
            for (int i = 0; i < n; i++) {
                int idx[8];
                for (int c = 0; c < 8; c++)
                    idx[c] = (k + kMcCorner[c][2]) * grid_slice +
                             (j + kMcCorner[c][1]) * grid_n +
                             (i + kMcCorner[c][0]);

                int cube_idx = 0;
                for (int c = 0; c < 8; c++)
                    if (grid[idx[c]] < 0) cube_idx |= (1 << c);

                if (cube_idx == 0 || cube_idx == 255) continue;

                int edge_mask = kMcEdgeTable[cube_idx];
                float vert_list[12][3];
                for (int e = 0; e < 12; e++) {
                    if (edge_mask & (1 << e)) {
                        int c0 = kMcEdge[e][0], c1 = kMcEdge[e][1];
                        float v0 = grid[idx[c0]], v1 = grid[idx[c1]];
                        float t = v0 / (v0 - v1);
                        float x0 = org.x + (i + kMcCorner[c0][0]) * step_x;
                        float y0 = org.y + (j + kMcCorner[c0][1]) * step_y;
                        float z0 = org.z + (k + kMcCorner[c0][2]) * step_z;
                        float x1 = org.x + (i + kMcCorner[c1][0]) * step_x;
                        float y1 = org.y + (j + kMcCorner[c1][1]) * step_y;
                        float z1 = org.z + (k + kMcCorner[c1][2]) * step_z;
                        vert_list[e][0] = lerp(x0, x1, t);
                        vert_list[e][1] = lerp(y0, y1, t);
                        vert_list[e][2] = lerp(z0, z1, t);
                    }
                }

                for (int t = 0; t + 2 < 16; t += 3) {
                    int i0 = kMcTriTable[cube_idx][t];
                    if (i0 == -1) break;
                    int i1 = kMcTriTable[cube_idx][t+1];
                    int i2 = kMcTriTable[cube_idx][t+2];
                    if (i1 == -1 || i2 == -1) break;
                    out_verts.push_back(vert_list[i0][0]); out_verts.push_back(vert_list[i0][1]); out_verts.push_back(vert_list[i0][2]);
                    out_verts.push_back(vert_list[i1][0]); out_verts.push_back(vert_list[i1][1]); out_verts.push_back(vert_list[i1][2]);
                    out_verts.push_back(vert_list[i2][0]); out_verts.push_back(vert_list[i2][1]); out_verts.push_back(vert_list[i2][2]);
                    tri_count++;
                }
            }

    return tri_count;
}

// Mandelbulb distance estimator
struct MandelbulbParams { int power; int iterations; float bailout; };

static float mandelbulbDE(float x, float y, float z, void* user) {
    MandelbulbParams* p = (MandelbulbParams*)user;
    float wx = x, wy = y, wz = z;
    float dr = 1.0f;
    float r = 0.0f;
    for (int i = 0; i < p->iterations; i++) {
        r = sqrtf(wx*wx + wy*wy + wz*wz);
        if (r > p->bailout) break;
        float theta = acosf(wz / r);
        float phi = atan2f(wy, wx);
        float pow_r = powf(r, (float)p->power);
        dr = powf(r, (float)(p->power - 1)) * (float)p->power * dr + 1.0f;
        theta *= (float)p->power;
        phi *= (float)p->power;
        float st = sinf(theta);
        wx = st * cosf(phi) * pow_r + x;
        wy = st * sinf(phi) * pow_r + y;
        wz = cosf(theta) * pow_r + z;
    }
    return 0.5f * logf(r) * r / dr;
}

static int generateMandelbulb(int fineness, std::vector<float>& out_verts,
                              std::vector<float>& out_colors) {
    MandelbulbParams params;
    params.power = 8;
    params.iterations = 10;
    params.bailout = 2.0f;

    AABB bounds(Vec3(-1.6f, -1.6f, -1.6f), Vec3(1.6f, 1.6f, 1.6f));
    int ntri = marchingCubes(mandelbulbDE, &params, bounds, fineness, out_verts);

    // Colors based on vertex position (gradient)
    out_colors.clear();
    out_colors.reserve(ntri * 3);
    for (int i = 0; i < ntri; i++) {
        float* v = &out_verts[i * 9];
        float cx = (v[0] + v[3] + v[6]) / 3.0f;
        float cy = (v[1] + v[4] + v[7]) / 3.0f;
        float cz = (v[2] + v[5] + v[8]) / 3.0f;
        float r = sqrtf(cx*cx + cy*cy + cz*cz);
        float hue = atan2f(cz, cx) / 3.14159f * 0.5f + 0.5f;
        float val = (1.0f - r * 0.4f);
        // Simple HSV-like coloring
        out_colors.push_back(fabsf(sinf(hue * 6.2832f)) * val);
        out_colors.push_back(fabsf(sinf((hue + 0.333f) * 6.2832f)) * val);
        out_colors.push_back(fabsf(sinf((hue + 0.667f) * 6.2832f)) * val);
    }
    return ntri;
}

// Benchmark mode state
static struct {
    bool active = false;
    int fineness = 64;
    double rays_per_sec = 0;
    float build_time_ms = 0;
    int num_tris = 0;
    int num_rays = 0;
    C11Scene c11scene;
    bool c11scene_valid = false;
} g_bench;

static void regenerateBenchmark();
static void runBenchmarkMeasurement();

static void enterBenchmarkMode(C11Scene& main_cs) {
    g_bench.active = true;
    g_bench.num_rays = 0;
    // Build a fresh C11 scene for the mandelbulb
    regenerateBenchmark();
    // Clear the accumulation buffer so the viewer starts fresh
    std::fill(g_state.accumBuffer.begin(), g_state.accumBuffer.end(), 0.0f);
    g_state.sampleCount = 0;
    g_state.cameraDirty = true;
    // Fit camera to the mandelbulb
    g_state.camera.orbitCenter = Vec3(0, 0, 0);
    g_state.camera.orbitDistance = 3.5f;
    g_state.camera.yaw = 90.0f;
    g_state.camera.pitch = 25.0f;
    UpdateCameraFromOrbit(g_state.camera);
}

static void exitBenchmarkMode() {
    g_bench.active = false;
    // Free the benchmark C11 scene
    for (auto* s : g_bench.c11scene.scenes) lrt_scene_free(s);
    g_bench.c11scene.scenes.clear();
    g_bench.c11scene.vertices.clear();
    g_bench.c11scene.colors.clear();
    g_bench.c11scene.num_tris = 0;
    g_bench.c11scene_valid = false;
}

static void regenerateBenchmark() {
    // Free old scene
    for (auto* s : g_bench.c11scene.scenes) lrt_scene_free(s);
    g_bench.c11scene.scenes.clear();

    std::vector<float> verts, colors;
    uint64_t t0 = GetTimeNs();
    g_bench.num_tris = generateMandelbulb(g_bench.fineness, verts, colors);
    uint64_t t1 = GetTimeNs();

    int num_threads = std::max(1, (int)std::thread::hardware_concurrency());
    buildC11SceneFromTriangles(g_bench.c11scene, verts.data(), g_bench.num_tris,
                               colors.data(), num_threads);
    uint64_t t2 = GetTimeNs();

    g_bench.build_time_ms = (float)(t2 - t0) / 1e6f;
    g_bench.c11scene_valid = true;
    g_bench.num_rays = 0;

    runBenchmarkMeasurement();
}

static void runBenchmarkMeasurement() {
    if (!g_bench.c11scene_valid || g_bench.c11scene.num_tris == 0) return;
    if (g_bench.c11scene.scenes.empty()) return;
    lrt_scene* scene = g_bench.c11scene.scenes[0];
    if (!scene) return;

    // Cast random rays through the bounding box from random origins on a sphere
    int total_rays = std::max(100000, g_bench.c11scene.num_tris * 50);
    if (total_rays > 5000000) total_rays = 5000000;

    uint64_t t0 = GetTimeNs();
    uint32_t hits = 0;

    for (int i = 0; i < total_rays; i++) {
        uint32_t seed = (uint32_t)(i * 2654435761u);
        // Random direction on unit sphere
        float theta = 2.0f * 3.14159f * (float)(seed & 0xFFFFFF) / 16777216.0f; seed = pcg_hash_impl(seed);
        float phi = acosf(2.0f * (float)(seed & 0xFFFFFF) / 16777216.0f - 1.0f); seed = pcg_hash_impl(seed);
        float sx = sinf(phi) * cosf(theta);
        float sy = sinf(phi) * sinf(theta);
        float sz = cosf(phi);
        double org[3] = {sx * 5.0, sy * 5.0, sz * 5.0};
        // Direction toward center with some spread
        seed = pcg_hash_impl(seed);
        float spread = (float)(seed & 0xFFFF) / 65536.0f * 0.5f;
        double tx = (double)((float)((seed >> 16) & 0xFF) / 256.0f * 2.0f - 1.0f) * spread;
        double ty = (double)((float)((seed >> 8) & 0xFF) / 256.0f * 2.0f - 1.0f) * spread;
        double tz = (double)((float)(seed & 0xFF) / 256.0f * 2.0f - 1.0f) * spread;
        double dir[3] = {-org[0] + tx, -org[1] + ty, -org[2] + tz};
        double dlen = sqrt(dir[0]*dir[0] + dir[1]*dir[1] + dir[2]*dir[2]);
        if (dlen > 1e-12) { dir[0] /= dlen; dir[1] /= dlen; dir[2] /= dlen; }
        double ht;
        unsigned hit = lrt_scene_intersect(scene, org, dir, 1e-6, 1e10, &ht, 0, 0);
        if (hit != LRT_NO_HIT) hits++;
    }

    uint64_t t1 = GetTimeNs();
    double elapsed = (double)(t1 - t0) / 1e9;
    g_bench.rays_per_sec = (elapsed > 0) ? (double)total_rays / elapsed : 0;
    g_bench.num_rays = total_rays;
}

// Overlay for benchmark mode (called from main loop after rendering)
static void drawBenchmarkOverlay(ViewerState& state) {
    int w = (int)state.width;
    int h = (int)state.height;
    int fs = state.fontScale;
    int lineH = 12 * fs;
    int x = 10;
    int y = h - lineH * 8;
    if (y < 10) y = 10;

    uint32_t color = 0xFF00FF00; // green text

    DrawString(x, y, "[BENCHMARK MODE]", color, state.pixels.data(), w, h, fs);
    y += lineH;
    std::string fstr = "Fineness: " + std::to_string(g_bench.fineness) + "x" + std::to_string(g_bench.fineness) + "x" + std::to_string(g_bench.fineness);
    DrawString(x, y, fstr.c_str(), color, state.pixels.data(), w, h, fs);
    y += lineH;
    std::string tstr = "Triangles: " + std::to_string(g_bench.num_tris);
    DrawString(x, y, tstr.c_str(), color, state.pixels.data(), w, h, fs);
    y += lineH;
    char btbuf[64];
    snprintf(btbuf, sizeof(btbuf), "Build time: %.2f ms", g_bench.build_time_ms);
    DrawString(x, y, btbuf, color, state.pixels.data(), w, h, fs);
    y += lineH;
    char rpsbuf[64];
    snprintf(rpsbuf, sizeof(rpsbuf), "Throughput: %.1f M rays/sec", g_bench.rays_per_sec / 1e6);
    DrawString(x, y, rpsbuf, color, state.pixels.data(), w, h, fs);
    y += lineH;
    char nrbuf[64];
    snprintf(nrbuf, sizeof(nrbuf), "Rays traced: %d", g_bench.num_rays);
    DrawString(x, y, nrbuf, color, state.pixels.data(), w, h, fs);
    y += lineH;
    DrawString(x, y, "B: Exit benchmark   [ ]: Fineness", color, state.pixels.data(), w, h, fs);
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
                case XK_b: case XK_B:
                    if (g_bench.active) {
                        exitBenchmarkMode();
                    } else {
                        enterBenchmarkMode(g_c11scene);
                    }
                    break;
                case XK_bracketleft:
                    if (g_bench.active && g_bench.fineness > 16) {
                        g_bench.fineness = std::max(16, g_bench.fineness / 2);
                        regenerateBenchmark();
                    }
                    break;
                case XK_bracketright:
                    if (g_bench.active && g_bench.fineness < 256) {
                        g_bench.fineness = std::min(256, g_bench.fineness * 2);
                        regenerateBenchmark();
                    }
                    break;
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
        if (g_bench.active) {
            RenderFrameX11(g_state, g_bench.c11scene);
            drawBenchmarkOverlay(g_state);
        } else {
            RenderFrameX11(g_state, g_c11scene);
        }

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
