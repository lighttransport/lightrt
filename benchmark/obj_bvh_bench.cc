// Copyright (c) 2026 Light Transport Entertainment, Inc.
// SPDX-License-Identifier: MIT
//
// obj_bvh_bench.cc - Standalone OBJ loading + BVH build benchmark with rendering
//
// Usage: obj_bvh_bench <model.obj> [--lbvh] [--no-parallel] [--rays N]
//                      [--width W] [--height H] [--no-render]

#define TINYOBJLOADER_IMPLEMENTATION
#include "../viewer/third_party/tiny_obj_loader.h"

#include "../lightrt.hh"

#include <iostream>
#include <iomanip>
#include <chrono>
#include <string>
#include <cmath>
#include <cstring>
#include <thread>
#include <vector>
#include <algorithm>

using namespace lightrt;

// ============================================================================
// Timer utility
// ============================================================================

struct Timer {
  std::chrono::high_resolution_clock::time_point start;

  Timer() : start(std::chrono::high_resolution_clock::now()) {}

  double elapsedMs() const {
    auto now = std::chrono::high_resolution_clock::now();
    return std::chrono::duration<double, std::milli>(now - start).count();
  }

  void reset() { start = std::chrono::high_resolution_clock::now(); }
};

// ============================================================================
// Simple xorshift64 RNG
// ============================================================================

class RNG {
public:
  explicit RNG(uint64_t seed = 12345) : state_(seed ? seed : 1) {}

  float uniform() {
    state_ ^= state_ >> 12;
    state_ ^= state_ << 25;
    state_ ^= state_ >> 27;
    return static_cast<float>(state_ * 0x2545F4914F6CDD1DULL) /
           static_cast<float>(UINT64_MAX);
  }

  float uniform(float lo, float hi) { return lo + uniform() * (hi - lo); }

private:
  uint64_t state_;
};

// ============================================================================
// OBJ Loader
// ============================================================================

bool LoadOBJ(const std::string& filename, std::vector<Triangle>& triangles) {
  tinyobj::attrib_t attrib;
  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string warn, err;

  Timer t;
  if (!tinyobj::LoadObj(&attrib, &shapes, &materials, &warn, &err,
                        filename.c_str())) {
    std::cerr << "TinyObj Error: " << warn << err << "\n";
    return false;
  }
  double load_ms = t.elapsedMs();

  for (const auto& shape : shapes) {
    size_t index_offset = 0;
    for (size_t f = 0; f < shape.mesh.num_face_vertices.size(); f++) {
      int fv = shape.mesh.num_face_vertices[f];
      if (fv >= 3) {
        // Triangulate: fan from vertex 0
        tinyobj::index_t idx0 = shape.mesh.indices[index_offset];
        Vec3 v0(attrib.vertices[3 * idx0.vertex_index + 0],
                attrib.vertices[3 * idx0.vertex_index + 1],
                attrib.vertices[3 * idx0.vertex_index + 2]);

        for (int t = 1; t < fv - 1; t++) {
          tinyobj::index_t idx1 = shape.mesh.indices[index_offset + t];
          tinyobj::index_t idx2 = shape.mesh.indices[index_offset + t + 1];

          Vec3 v1(attrib.vertices[3 * idx1.vertex_index + 0],
                  attrib.vertices[3 * idx1.vertex_index + 1],
                  attrib.vertices[3 * idx1.vertex_index + 2]);
          Vec3 v2(attrib.vertices[3 * idx2.vertex_index + 0],
                  attrib.vertices[3 * idx2.vertex_index + 1],
                  attrib.vertices[3 * idx2.vertex_index + 2]);

          Triangle tri;
          tri.v0 = v0;
          tri.v1 = v1;
          tri.v2 = v2;
          triangles.push_back(tri);
        }
      }
      index_offset += fv;
    }
  }

  std::cout << "  OBJ load:      " << std::fixed << std::setprecision(1)
            << load_ms << " ms (" << attrib.vertices.size() / 3 << " vertices)\n";
  std::cout << "  Triangulation: " << triangles.size() << " triangles\n";
  return true;
}

// ============================================================================
// Benchmark helpers
// ============================================================================

void benchBVHBuild(const std::vector<Triangle>& triangles,
                   const std::string& label, const BVHBuildConfig& config,
                   TriangleBVH& bvh_out) {
  Timer t;
  bvh_out.build(triangles, config);
  double ms = t.elapsedMs();

  std::cout << "  " << std::left << std::setw(24) << label << std::right
            << std::fixed << std::setprecision(1) << std::setw(10) << ms
            << " ms  (nodes: " << bvh_out.getBVH().getNodes().size() << ")\n";
}

void benchTraversal(const TriangleBVH& bvh, const AABB& scene_bounds,
                    uint32_t num_rays) {
  RNG rng(42);
  Vec3 extent = scene_bounds.max - scene_bounds.min;
  Vec3 center = (scene_bounds.min + scene_bounds.max) * 0.5f;
  float radius = std::max({extent.x, extent.y, extent.z}) * 0.5f;

  // Generate random rays from outside the bounding sphere looking inward
  std::vector<Ray> rays;
  rays.reserve(num_rays);
  for (uint32_t i = 0; i < num_rays; i++) {
    // Random point on sphere
    float theta = rng.uniform(0.0f, 2.0f * 3.14159265f);
    float phi = rng.uniform(0.0f, 3.14159265f);
    Vec3 on_sphere(radius * 2.0f * sinf(phi) * cosf(theta),
                   radius * 2.0f * sinf(phi) * sinf(theta),
                   radius * 2.0f * cosf(phi));
    Vec3 origin = center + on_sphere;

    // Aim toward a random point inside the bbox
    Vec3 target(rng.uniform(scene_bounds.min.x, scene_bounds.max.x),
                rng.uniform(scene_bounds.min.y, scene_bounds.max.y),
                rng.uniform(scene_bounds.min.z, scene_bounds.max.z));
    Vec3 dir = (target - origin).normalize();
    rays.emplace_back(origin, dir);
  }

  // Warm up
  {
    float t_hit, u, v;
    for (uint32_t i = 0; i < std::min(num_rays, 1000u); i++) {
      bvh.traverse(rays[i], t_hit, u, v);
    }
  }

  uint32_t hits = 0;
  Timer t;
  float t_hit, u, v;
  for (uint32_t i = 0; i < num_rays; i++) {
    uint32_t idx = bvh.traverse(rays[i], t_hit, u, v);
    if (idx != kInvalidIndex) hits++;
  }
  double ms = t.elapsedMs();

  double mrays = num_rays / (ms * 1000.0);
  std::cout << "  Traversal (" << num_rays << " rays): " << std::fixed
            << std::setprecision(1) << ms << " ms  (" << std::setprecision(2)
            << mrays << " Mrays/s, " << hits << " hits)\n";
}

// ============================================================================
// Rendering
// ============================================================================

static constexpr float kPi = 3.14159265358979323846f;

// Shade a hit point: clay-like material with two directional lights
RGB8 shadeHit(const Triangle& tri, uint32_t /*prim_id*/) {
  Vec3 e1 = tri.v1 - tri.v0;
  Vec3 e2 = tri.v2 - tri.v0;
  Vec3 normal = e1.cross(e2).normalize();

  // Two directional lights (key + fill)
  Vec3 light1 = Vec3(0.5f, 0.8f, 0.3f).normalize();
  Vec3 light2 = Vec3(-0.3f, 0.4f, -0.7f).normalize();
  float ndl1 = std::max(0.0f, std::abs(normal.dot(light1)));
  float ndl2 = std::max(0.0f, std::abs(normal.dot(light2)));

  // Clay material: warm neutral base
  float ambient = 0.12f;
  float diffuse = 0.55f * ndl1 + 0.33f * ndl2;
  float intensity = ambient + diffuse;

  // Warm clay tint (slightly orange-gray)
  float r = std::min(1.0f, intensity * 0.85f + 0.05f);
  float g = std::min(1.0f, intensity * 0.78f + 0.04f);
  float b = std::min(1.0f, intensity * 0.70f + 0.03f);

  return RGB8(static_cast<uint8_t>(r * 255.0f),
              static_cast<uint8_t>(g * 255.0f),
              static_cast<uint8_t>(b * 255.0f));
}

// Render perspective image (multi-threaded)
void renderPerspective(const TriangleBVH& bvh,
                       const std::vector<Triangle>& triangles,
                       std::vector<RGB8>& image,
                       uint32_t width, uint32_t height,
                       const Vec3& eye, const Vec3& target, const Vec3& up_hint,
                       float fov_deg) {
  image.resize(width * height);

  Vec3 forward = (target - eye).normalize();
  Vec3 right = forward.cross(up_hint).normalize();
  Vec3 up = right.cross(forward).normalize();
  float scale = tanf(fov_deg * 0.5f * kPi / 180.0f);
  float aspect = static_cast<float>(width) / height;

  int nthreads = static_cast<int>(std::thread::hardware_concurrency());
  std::vector<std::thread> threads;
  int rows_per = static_cast<int>(height) / nthreads;

  for (int tid = 0; tid < nthreads; tid++) {
    threads.emplace_back([&, tid]() {
      int y0 = tid * rows_per;
      int y1 = (tid == nthreads - 1) ? static_cast<int>(height) : (tid + 1) * rows_per;
      for (int y = y0; y < y1; y++) {
        for (uint32_t x = 0; x < width; x++) {
          float px = (2.0f * (x + 0.5f) / width - 1.0f) * aspect * scale;
          float py = (1.0f - 2.0f * (y + 0.5f) / height) * scale;
          Vec3 dir = (forward + right * px + up * py).normalize();
          Ray ray(eye, dir);

          float t_hit, u, v;
          uint32_t hit = bvh.traverse(ray, t_hit, u, v);
          if (hit != kInvalidIndex) {
            image[y * width + x] = shadeHit(triangles[hit], hit);
          } else {
            // Sky gradient
            float t_sky = 0.5f * (dir.dot(up) + 1.0f);
            uint8_t r = static_cast<uint8_t>(30 + 40 * t_sky);
            uint8_t g = static_cast<uint8_t>(30 + 50 * t_sky);
            uint8_t b = static_cast<uint8_t>(40 + 70 * t_sky);
            image[y * width + x] = RGB8(r, g, b);
          }
        }
      }
    });
  }
  for (auto& th : threads) th.join();
}

// Render orthographic image (multi-threaded)
void renderOrtho(const TriangleBVH& bvh,
                 const std::vector<Triangle>& triangles,
                 std::vector<RGB8>& image,
                 uint32_t width, uint32_t height,
                 const Vec3& dir, const Vec3& up_hint,
                 const AABB& bounds, float padding) {
  image.resize(width * height);

  Vec3 forward = dir.normalize();
  Vec3 right = forward.cross(up_hint).normalize();
  Vec3 up = right.cross(forward).normalize();

  // Compute the extent of the bounding box projected onto the view plane
  Vec3 center = (bounds.min + bounds.max) * 0.5f;
  Vec3 ext = bounds.max - bounds.min;

  // Project bbox corners to find view-plane extent
  float half_w = 0.0f, half_h = 0.0f;
  for (int i = 0; i < 8; i++) {
    Vec3 corner(
      (i & 1) ? bounds.max.x : bounds.min.x,
      (i & 2) ? bounds.max.y : bounds.min.y,
      (i & 4) ? bounds.max.z : bounds.min.z);
    Vec3 d = corner - center;
    half_w = std::max(half_w, std::abs(d.dot(right)));
    half_h = std::max(half_h, std::abs(d.dot(up)));
  }

  // Apply padding and match aspect ratio
  half_w *= (1.0f + padding);
  half_h *= (1.0f + padding);
  float aspect = static_cast<float>(width) / height;
  if (half_w / half_h < aspect) {
    half_w = half_h * aspect;
  } else {
    half_h = half_w / aspect;
  }

  // Ray origin distance: far behind the scene
  float depth = std::max({ext.x, ext.y, ext.z}) * 2.0f;
  Vec3 origin_base = center - forward * depth;

  int nthreads = static_cast<int>(std::thread::hardware_concurrency());
  std::vector<std::thread> threads;
  int rows_per = static_cast<int>(height) / nthreads;

  for (int tid = 0; tid < nthreads; tid++) {
    threads.emplace_back([&, tid]() {
      int y0 = tid * rows_per;
      int y1 = (tid == nthreads - 1) ? static_cast<int>(height) : (tid + 1) * rows_per;
      for (int y = y0; y < y1; y++) {
        for (uint32_t x = 0; x < width; x++) {
          float u_coord = (2.0f * (x + 0.5f) / width - 1.0f) * half_w;
          float v_coord = (1.0f - 2.0f * (y + 0.5f) / height) * half_h;
          Vec3 origin = origin_base + right * u_coord + up * v_coord;
          Ray ray(origin, forward);

          float t_hit, u_bary, v_bary;
          uint32_t hit = bvh.traverse(ray, t_hit, u_bary, v_bary);
          if (hit != kInvalidIndex) {
            image[y * width + x] = shadeHit(triangles[hit], hit);
          } else {
            image[y * width + x] = RGB8(35, 35, 45);
          }
        }
      }
    });
  }
  for (auto& th : threads) th.join();
}

void renderAllViews(const TriangleBVH& bvh,
                    const std::vector<Triangle>& triangles,
                    const AABB& bounds,
                    uint32_t width, uint32_t height,
                    const std::string& prefix) {
  std::vector<RGB8> image;

  Vec3 center = (bounds.min + bounds.max) * 0.5f;
  Vec3 ext = bounds.max - bounds.min;
  float max_ext = std::max({ext.x, ext.y, ext.z});

  // --- 1. Perspective from +Y (looking down at a 45-degree angle) ---
  {
    float dist = max_ext * 2.0f;
    Vec3 eye = center + Vec3(0.0f, dist, dist * 0.7f);
    float fov = 45.0f;
    std::string filename = prefix + "_persp_y.bmp";

    Timer t;
    renderPerspective(bvh, triangles, image, width, height,
                      eye, center, Vec3(0, 1, 0), fov);
    double ms = t.elapsedMs();

    HeatmapWriter::writeImage(filename.c_str(), image.data(), width, height, ImageFormat::BMP);
    std::cout << "  " << std::left << std::setw(30) << filename << std::right
              << std::fixed << std::setprecision(1) << ms << " ms\n";
  }

  // --- 2. Ortho top (looking down -Y) ---
  {
    std::string filename = prefix + "_ortho_top.bmp";
    Timer t;
    renderOrtho(bvh, triangles, image, width, height,
                Vec3(0, -1, 0), Vec3(0, 0, -1), bounds, 0.1f);
    double ms = t.elapsedMs();

    HeatmapWriter::writeImage(filename.c_str(), image.data(), width, height, ImageFormat::BMP);
    std::cout << "  " << std::left << std::setw(30) << filename << std::right
              << std::fixed << std::setprecision(1) << ms << " ms\n";
  }

  // --- 3. Ortho front (looking -Z) ---
  {
    std::string filename = prefix + "_ortho_front.bmp";
    Timer t;
    renderOrtho(bvh, triangles, image, width, height,
                Vec3(0, 0, -1), Vec3(0, 1, 0), bounds, 0.1f);
    double ms = t.elapsedMs();

    HeatmapWriter::writeImage(filename.c_str(), image.data(), width, height, ImageFormat::BMP);
    std::cout << "  " << std::left << std::setw(30) << filename << std::right
              << std::fixed << std::setprecision(1) << ms << " ms\n";
  }

  // --- 4. Ortho left (looking +X, i.e. from -X side) ---
  {
    std::string filename = prefix + "_ortho_left.bmp";
    Timer t;
    renderOrtho(bvh, triangles, image, width, height,
                Vec3(1, 0, 0), Vec3(0, 1, 0), bounds, 0.1f);
    double ms = t.elapsedMs();

    HeatmapWriter::writeImage(filename.c_str(), image.data(), width, height, ImageFormat::BMP);
    std::cout << "  " << std::left << std::setw(30) << filename << std::right
              << std::fixed << std::setprecision(1) << ms << " ms\n";
  }
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char** argv) {
  if (argc < 2) {
    std::cerr << "Usage: " << argv[0]
              << " <model.obj> [--lbvh] [--no-parallel] [--rays N]"
              << " [--width W] [--height H] [--no-render]\n";
    return 1;
  }

  std::string obj_path = argv[1];
  bool use_lbvh = false;
  bool use_parallel = true;
  uint32_t num_rays = 100000;
  uint32_t render_width = 800;
  uint32_t render_height = 600;
  bool do_render = true;

  for (int i = 2; i < argc; i++) {
    if (strcmp(argv[i], "--lbvh") == 0) use_lbvh = true;
    else if (strcmp(argv[i], "--no-parallel") == 0) use_parallel = false;
    else if (strcmp(argv[i], "--no-render") == 0) do_render = false;
    else if (strcmp(argv[i], "--rays") == 0 && i + 1 < argc)
      num_rays = static_cast<uint32_t>(atoi(argv[++i]));
    else if (strcmp(argv[i], "--width") == 0 && i + 1 < argc)
      render_width = static_cast<uint32_t>(atoi(argv[++i]));
    else if (strcmp(argv[i], "--height") == 0 && i + 1 < argc)
      render_height = static_cast<uint32_t>(atoi(argv[++i]));
  }

  std::cout << "=== OBJ BVH Benchmark ===\n";
  std::cout << "File: " << obj_path << "\n\n";

  // Load OBJ
  std::vector<Triangle> triangles;
  std::cout << "[Load]\n";
  if (!LoadOBJ(obj_path, triangles) || triangles.empty()) {
    std::cerr << "Failed to load model.\n";
    return 1;
  }

  // Compute scene bounds
  AABB scene_bounds;
  for (const auto& tri : triangles) {
    scene_bounds.expand(tri.bounds());
  }
  Vec3 ext = scene_bounds.max - scene_bounds.min;
  std::cout << "  Scene bounds:  (" << scene_bounds.min.x << ", "
            << scene_bounds.min.y << ", " << scene_bounds.min.z << ") - ("
            << scene_bounds.max.x << ", " << scene_bounds.max.y << ", "
            << scene_bounds.max.z << ")\n";
  std::cout << "  Extent:        " << ext.x << " x " << ext.y << " x "
            << ext.z << "\n\n";

  // BVH Build Benchmarks
  std::cout << "[BVH Build] (" << triangles.size() << " triangles)\n";
  std::cout << "  " << std::left << std::setw(24) << "Method" << std::right
            << std::setw(10) << "Time" << "      Info\n";
  std::cout << "  " << std::string(50, '-') << "\n";

  // 1. Default SAH (binned, parallel)
  {
    BVHBuildConfig cfg;
    cfg.use_parallel_build = use_parallel;
    TriangleBVH bvh;
    benchBVHBuild(triangles, "SAH binned (parallel)", cfg, bvh);

    // Traversal benchmark with default build
    std::cout << "\n[Traversal] (SAH binned)\n";
    benchTraversal(bvh, scene_bounds, num_rays);
  }

  // 2. LBVH (fast build)
  {
    BVHBuildConfig cfg = BVHBuildConfig::fast();
    cfg.use_parallel_build = use_parallel;
    TriangleBVH bvh;
    benchBVHBuild(triangles, "LBVH (parallel)", cfg, bvh);

    std::cout << "\n[Traversal] (LBVH)\n";
    benchTraversal(bvh, scene_bounds, num_rays);
  }

  // 3. SAH binned, single-threaded
  {
    BVHBuildConfig cfg;
    cfg.use_parallel_build = false;
    TriangleBVH bvh;
    benchBVHBuild(triangles, "SAH binned (single)", cfg, bvh);
  }

  // 4. LBVH, single-threaded
  {
    BVHBuildConfig cfg = BVHBuildConfig::fast();
    cfg.use_parallel_build = false;
    TriangleBVH bvh;
    benchBVHBuild(triangles, "LBVH (single)", cfg, bvh);
  }

  // If user requested specific mode, run that too
  if (use_lbvh) {
    std::cout << "\n[User-requested LBVH build]\n";
    BVHBuildConfig cfg = BVHBuildConfig::fast();
    cfg.use_parallel_build = use_parallel;
    TriangleBVH bvh;
    benchBVHBuild(triangles, "LBVH", cfg, bvh);
  }

  // Rendering
  if (do_render) {
    std::cout << "\n[Render] " << render_width << "x" << render_height << "\n";
    std::cout << "  " << std::left << std::setw(30) << "Output" << std::right
              << "Render time\n";
    std::cout << "  " << std::string(45, '-') << "\n";

    // Build a fresh BVH for rendering (SAH, parallel)
    TriangleBVH render_bvh;
    {
      BVHBuildConfig cfg;
      cfg.use_parallel_build = use_parallel;
      render_bvh.build(triangles, cfg);
    }

    // Derive output prefix from input filename (strip directory and extension)
    std::string prefix = obj_path;
    {
      auto slash = prefix.find_last_of("/\\");
      if (slash != std::string::npos) prefix = prefix.substr(slash + 1);
      auto dot = prefix.rfind('.');
      if (dot != std::string::npos) prefix = prefix.substr(0, dot);
    }

    renderAllViews(render_bvh, triangles, scene_bounds,
                   render_width, render_height, prefix);
  }

  std::cout << "\nDone.\n";
  return 0;
}
