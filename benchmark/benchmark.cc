// Copyright (c) 2026 Light Transport Entertainment, Inc.
// SPDX-License-Identifier: MIT
//
// benchmark.cc - Comprehensive BVH benchmarks for LightRT

#include "../lightrt.hh"
#include <iostream>
#include <iomanip>
#include <chrono>
#include <cmath>
#include <numeric>

using namespace lightrt;

// ============================================================================
// Random Number Generator (xorshift64)
// ============================================================================

class RNG {
public:
  explicit RNG(uint64_t seed = 12345) : state_(seed ? seed : 1) {}

  uint64_t next() {
    state_ ^= state_ >> 12;
    state_ ^= state_ << 25;
    state_ ^= state_ >> 27;
    return state_ * 0x2545F4914F6CDD1DULL;
  }

  float uniform() {
    return static_cast<float>(next()) / static_cast<float>(UINT64_MAX);
  }

  float uniform(float min_val, float max_val) {
    return min_val + uniform() * (max_val - min_val);
  }

  Vec3 uniformVec3(float min_val, float max_val) {
    return Vec3(uniform(min_val, max_val),
                uniform(min_val, max_val),
                uniform(min_val, max_val));
  }

  Vec3 uniformDirection() {
    // Uniform on sphere
    float z = uniform(-1.0f, 1.0f);
    float phi = uniform(0.0f, 2.0f * 3.14159265f);
    float r = std::sqrt(1.0f - z * z);
    return Vec3(r * std::cos(phi), r * std::sin(phi), z);
  }

private:
  uint64_t state_;
};

// ============================================================================
// Scene Generators
// ============================================================================

// Random triangles uniformly distributed in a cube
std::vector<Triangle> generateRandomTriangles(uint32_t count, float scene_size, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(count);

  for (uint32_t i = 0; i < count; i++) {
    Vec3 center = rng.uniformVec3(-scene_size, scene_size);
    float tri_size = rng.uniform(0.1f, 1.0f);

    Vec3 v0 = center + rng.uniformVec3(-tri_size, tri_size);
    Vec3 v1 = center + rng.uniformVec3(-tri_size, tri_size);
    Vec3 v2 = center + rng.uniformVec3(-tri_size, tri_size);

    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// Triangles in a uniform grid (spatially coherent)
std::vector<Triangle> generateUniformTriangles(uint32_t grid_size, float scene_size) {
  std::vector<Triangle> triangles;
  float cell_size = (2.0f * scene_size) / grid_size;

  for (uint32_t x = 0; x < grid_size; x++) {
    for (uint32_t y = 0; y < grid_size; y++) {
      for (uint32_t z = 0; z < grid_size; z++) {
        Vec3 corner(-scene_size + x * cell_size,
                    -scene_size + y * cell_size,
                    -scene_size + z * cell_size);

        // Two triangles per cell (quad face)
        Vec3 v0 = corner;
        Vec3 v1 = corner + Vec3(cell_size * 0.9f, 0.0f, 0.0f);
        Vec3 v2 = corner + Vec3(0.0f, cell_size * 0.9f, 0.0f);
        Vec3 v3 = corner + Vec3(cell_size * 0.9f, cell_size * 0.9f, 0.0f);

        triangles.emplace_back(v0, v1, v2);
        triangles.emplace_back(v1, v3, v2);
      }
    }
  }

  return triangles;
}

// Overlapping triangles at same location (worst case for BVH)
// All triangles have the same centroid, testing O(K) vs O(N)
std::vector<Triangle> generateOverlappingTriangles(uint32_t count, Vec3 center, float size, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(count);

  for (uint32_t i = 0; i < count; i++) {
    // All triangles share the same center but have different orientations/sizes
    float angle = rng.uniform(0.0f, 2.0f * 3.14159265f);
    float s = rng.uniform(size * 0.5f, size);

    Vec3 v0 = center + Vec3(s * std::cos(angle), s * std::sin(angle), 0.0f);
    Vec3 v1 = center + Vec3(s * std::cos(angle + 2.094f), s * std::sin(angle + 2.094f), 0.0f);
    Vec3 v2 = center + Vec3(s * std::cos(angle + 4.189f), s * std::sin(angle + 4.189f), 0.0f);

    // Small random offset to create slightly different AABBs
    float offset = rng.uniform(-0.001f, 0.001f);
    v0.z += offset;
    v1.z += offset;
    v2.z += offset;

    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// ============================================================================
// Ray Generators
// ============================================================================

// Random rays in all directions from random origins
std::vector<Ray> generateRandomRays(uint32_t count, float scene_size, RNG& rng) {
  std::vector<Ray> rays;
  rays.reserve(count);

  for (uint32_t i = 0; i < count; i++) {
    Vec3 origin = rng.uniformVec3(-scene_size * 2.0f, scene_size * 2.0f);
    Vec3 dir = rng.uniformDirection();
    rays.emplace_back(origin, dir);
  }

  return rays;
}

// Coherent rays: parallel rays in a grid pattern (like rasterization)
std::vector<Ray> generateCoherentRays(uint32_t res_x, uint32_t res_y, float scene_size) {
  std::vector<Ray> rays;
  rays.reserve(res_x * res_y);

  Vec3 origin(0.0f, 0.0f, -scene_size * 3.0f);

  for (uint32_t y = 0; y < res_y; y++) {
    for (uint32_t x = 0; x < res_x; x++) {
      float px = -scene_size + (2.0f * scene_size * x) / res_x;
      float py = -scene_size + (2.0f * scene_size * y) / res_y;

      Vec3 target(px, py, 0.0f);
      Vec3 dir = (target - origin).normalize();

      rays.emplace_back(origin, dir);
    }
  }

  return rays;
}

// ============================================================================
// Benchmark Utilities
// ============================================================================

struct BenchmarkResult {
  double build_time_ms;
  double traverse_time_ms;
  uint32_t num_primitives;
  uint32_t num_rays;
  uint32_t num_hits;
  double rays_per_second;
  BVH::Stats bvh_stats;
};

template<typename F>
double measureTime(F&& func) {
  auto start = std::chrono::high_resolution_clock::now();
  func();
  auto end = std::chrono::high_resolution_clock::now();
  return std::chrono::duration<double, std::milli>(end - start).count();
}

void printResult(const char* name, const BenchmarkResult& r) {
  std::cout << "\n--- " << name << " ---\n";
  std::cout << "  Primitives: " << r.num_primitives << "\n";
  std::cout << "  Build time: " << std::fixed << std::setprecision(2) << r.build_time_ms << " ms\n";
  std::cout << "  BVH nodes: " << r.bvh_stats.num_nodes << " (leaves: " << r.bvh_stats.num_leaves << ")\n";
  std::cout << "  Max depth: " << r.bvh_stats.max_depth << "\n";
  std::cout << "  Avg leaf size: " << std::setprecision(1) << r.bvh_stats.avg_leaf_size << "\n";
  std::cout << "  Rays traced: " << r.num_rays << "\n";
  std::cout << "  Traverse time: " << std::setprecision(2) << r.traverse_time_ms << " ms\n";
  std::cout << "  Hit rate: " << std::setprecision(1) << (100.0 * r.num_hits / r.num_rays) << "%\n";
  std::cout << "  Rays/second: " << std::scientific << std::setprecision(2) << r.rays_per_second << "\n";
}

// ============================================================================
// Benchmarks
// ============================================================================

BenchmarkResult benchmarkRandomTriangles(uint32_t num_triangles, uint32_t num_rays) {
  BenchmarkResult result = {};
  RNG rng(42);

  std::vector<Triangle> triangles = generateRandomTriangles(num_triangles, 10.0f, rng);
  std::vector<Ray> rays = generateRandomRays(num_rays, 10.0f, rng);

  result.num_primitives = num_triangles;
  result.num_rays = num_rays;

  TriangleBVH bvh;
  BVHBuildConfig config;
  config.use_sah = true;
  config.use_binning = true;
  config.max_leaf_size = 4;

  result.build_time_ms = measureTime([&]() {
    bvh.build(triangles, config);
  });

  result.bvh_stats = bvh.getStats();

  result.traverse_time_ms = measureTime([&]() {
    for (const auto& ray : rays) {
      float t, u, v;
      uint32_t hit = bvh.traverse(ray, t, u, v);
      if (hit != kInvalidIndex) {
        result.num_hits++;
      }
    }
  });

  result.rays_per_second = (num_rays / result.traverse_time_ms) * 1000.0;
  return result;
}

BenchmarkResult benchmarkUniformTriangles(uint32_t grid_size, uint32_t num_rays) {
  BenchmarkResult result = {};
  RNG rng(42);

  std::vector<Triangle> triangles = generateUniformTriangles(grid_size, 10.0f);
  std::vector<Ray> rays = generateRandomRays(num_rays, 10.0f, rng);

  result.num_primitives = static_cast<uint32_t>(triangles.size());
  result.num_rays = num_rays;

  TriangleBVH bvh;
  BVHBuildConfig config;
  config.use_sah = true;
  config.use_binning = true;
  config.max_leaf_size = 4;

  result.build_time_ms = measureTime([&]() {
    bvh.build(triangles, config);
  });

  result.bvh_stats = bvh.getStats();

  result.traverse_time_ms = measureTime([&]() {
    for (const auto& ray : rays) {
      float t, u, v;
      uint32_t hit = bvh.traverse(ray, t, u, v);
      if (hit != kInvalidIndex) {
        result.num_hits++;
      }
    }
  });

  result.rays_per_second = (num_rays / result.traverse_time_ms) * 1000.0;
  return result;
}

BenchmarkResult benchmarkCoherentRays(uint32_t num_triangles, uint32_t res) {
  BenchmarkResult result = {};
  RNG rng(42);

  std::vector<Triangle> triangles = generateRandomTriangles(num_triangles, 10.0f, rng);
  std::vector<Ray> rays = generateCoherentRays(res, res, 10.0f);

  result.num_primitives = num_triangles;
  result.num_rays = static_cast<uint32_t>(rays.size());

  TriangleBVH bvh;
  BVHBuildConfig config;
  config.use_sah = true;
  config.use_binning = true;
  config.max_leaf_size = 4;

  result.build_time_ms = measureTime([&]() {
    bvh.build(triangles, config);
  });

  result.bvh_stats = bvh.getStats();

  result.traverse_time_ms = measureTime([&]() {
    for (const auto& ray : rays) {
      float t, u, v;
      uint32_t hit = bvh.traverse(ray, t, u, v);
      if (hit != kInvalidIndex) {
        result.num_hits++;
      }
    }
  });

  result.rays_per_second = (result.num_rays / result.traverse_time_ms) * 1000.0;
  return result;
}

// ============================================================================
// Overlapping Triangles Test (O(K) vs O(N) verification)
// ============================================================================

void benchmarkOverlappingTriangles() {
  std::cout << "\n========================================\n";
  std::cout << "Overlapping Triangles Test (O(K) vs O(N))\n";
  std::cout << "========================================\n";
  std::cout << "\nAll triangles share the same centroid.\n";
  std::cout << "BVH cannot spatially separate them.\n\n";

  RNG rng(42);
  const uint32_t num_rays = 10000;
  std::vector<Ray> rays = generateRandomRays(num_rays, 5.0f, rng);

  std::vector<uint32_t> leaf_sizes = {4, 8, 16, 32};
  std::vector<uint32_t> prim_counts = {1000, 10000, 100000};

  // Test 1: SAH mode (allows large leaves when split doesn't help)
  std::cout << "=== Mode 1: SAH (default) ===\n";
  std::cout << "SAH may create large leaves when splitting doesn't improve cost.\n";
  std::cout << "Time scales with num_primitives (O(N) for overlapping).\n\n";

  std::cout << std::setw(12) << "Primitives"
            << std::setw(12) << "LeafSize"
            << std::setw(12) << "AvgLeaf"
            << std::setw(12) << "Time(ms)"
            << std::setw(14) << "Rays/sec\n";
  std::cout << std::string(62, '-') << "\n";

  for (uint32_t num_prims : prim_counts) {
    std::vector<Triangle> triangles = generateOverlappingTriangles(
        num_prims, Vec3(0.0f, 0.0f, 0.0f), 1.0f, rng);

    TriangleBVH bvh;
    BVHBuildConfig config;
    config.use_sah = true;
    config.use_binning = true;
    config.max_leaf_size = 4;
    config.force_max_leaf_size = false;  // SAH can override

    bvh.build(triangles, config);
    BVH::Stats stats = bvh.getStats();

    double traverse_time = measureTime([&]() {
      for (const auto& ray : rays) {
        float t, u, v;
        bvh.traverse(ray, t, u, v);
      }
    });

    double rays_per_sec = (num_rays / traverse_time) * 1000.0;

    std::cout << std::fixed
              << std::setw(12) << num_prims
              << std::setw(12) << 4
              << std::setw(12) << std::setprecision(1) << stats.avg_leaf_size
              << std::setw(12) << std::setprecision(2) << traverse_time
              << std::setw(14) << std::scientific << std::setprecision(2) << rays_per_sec << "\n";
  }

  // Test 2: Force max_leaf_size mode (guarantees O(K))
  std::cout << "\n=== Mode 2: force_max_leaf_size (O(K) guaranteed) ===\n";
  std::cout << "Always splits until max_leaf_size, even without SAH benefit.\n";
  std::cout << "Time scales with leaf_size (O(K)), NOT with num_primitives.\n\n";

  std::cout << std::setw(12) << "Primitives"
            << std::setw(12) << "LeafSize"
            << std::setw(12) << "AvgLeaf"
            << std::setw(12) << "Time(ms)"
            << std::setw(14) << "Rays/sec\n";
  std::cout << std::string(62, '-') << "\n";

  for (uint32_t num_prims : prim_counts) {
    std::vector<Triangle> triangles = generateOverlappingTriangles(
        num_prims, Vec3(0.0f, 0.0f, 0.0f), 1.0f, rng);

    for (uint32_t leaf_size : leaf_sizes) {
      TriangleBVH bvh;
      BVHBuildConfig config;
      config.use_sah = true;
      config.use_binning = true;
      config.max_leaf_size = leaf_size;
      config.force_max_leaf_size = true;  // Guarantee O(K)

      bvh.build(triangles, config);
      BVH::Stats stats = bvh.getStats();

      double traverse_time = measureTime([&]() {
        for (const auto& ray : rays) {
          float t, u, v;
          bvh.traverse(ray, t, u, v);
        }
      });

      double rays_per_sec = (num_rays / traverse_time) * 1000.0;

      std::cout << std::fixed
                << std::setw(12) << num_prims
                << std::setw(12) << leaf_size
                << std::setw(12) << std::setprecision(1) << stats.avg_leaf_size
                << std::setw(12) << std::setprecision(2) << traverse_time
                << std::setw(14) << std::scientific << std::setprecision(2) << rays_per_sec << "\n";
    }
    std::cout << "\n";
  }

  std::cout << "Analysis:\n";
  std::cout << "- For perfectly overlapping primitives, ALL leaves share the same AABB\n";
  std::cout << "- A ray intersecting this region must test ALL primitives regardless of BVH structure\n";
  std::cout << "- SAH mode: 1 large leaf with N primitives -> O(N) tests\n";
  std::cout << "- force_max_leaf_size: N/K leaves with K primitives each -> still O(N) total tests\n";
  std::cout << "- True O(K) per ray is only achievable when primitives can be spatially separated\n";
  std::cout << "- The force_max_leaf_size bounds per-leaf work to K, but cannot reduce total work\n";
}

// ============================================================================
// SBVH vs BVH Comparison
// ============================================================================

struct SBVHBenchmarkResult {
  double build_time_ms;
  double traverse_time_ms;
  uint32_t num_primitives;
  uint32_t num_references;
  uint32_t num_rays;
  uint32_t num_hits;
  double rays_per_second;
  SBVH::Stats sbvh_stats;
};

void printSBVHResult(const char* name, const SBVHBenchmarkResult& r) {
  std::cout << "\n--- " << name << " ---\n";
  std::cout << "  Primitives: " << r.num_primitives << "\n";
  std::cout << "  References: " << r.num_references
            << " (split ratio: " << std::fixed << std::setprecision(2)
            << r.sbvh_stats.split_ratio << "x)\n";
  std::cout << "  Build time: " << std::setprecision(2) << r.build_time_ms << " ms\n";
  std::cout << "  BVH nodes: " << r.sbvh_stats.num_nodes << " (leaves: " << r.sbvh_stats.num_leaves << ")\n";
  std::cout << "  Max depth: " << r.sbvh_stats.max_depth << "\n";
  std::cout << "  Avg leaf size: " << std::setprecision(1) << r.sbvh_stats.avg_leaf_size << "\n";
  std::cout << "  SAH cost: " << std::scientific << std::setprecision(2) << r.sbvh_stats.sah_cost << "\n";
  std::cout << "  Rays traced: " << r.num_rays << "\n";
  std::cout << "  Traverse time: " << std::fixed << std::setprecision(2) << r.traverse_time_ms << " ms\n";
  std::cout << "  Hit rate: " << std::setprecision(1) << (100.0 * r.num_hits / r.num_rays) << "%\n";
  std::cout << "  Rays/second: " << std::scientific << std::setprecision(2) << r.rays_per_second << "\n";
}

// ============================================================================
// Co-planar Triangle Generators
// ============================================================================

// Generate co-planar triangles on XY plane (worst case for Z-axis BVH splits)
std::vector<Triangle> generateCoplanarTrianglesXY(uint32_t count, float scene_size, float z_pos, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(count);

  for (uint32_t i = 0; i < count; i++) {
    float cx = rng.uniform(-scene_size, scene_size);
    float cy = rng.uniform(-scene_size, scene_size);
    float size = rng.uniform(0.1f, 0.5f);
    float angle = rng.uniform(0.0f, 6.28318f);

    Vec3 v0(cx + size * std::cos(angle), cy + size * std::sin(angle), z_pos);
    Vec3 v1(cx + size * std::cos(angle + 2.094f), cy + size * std::sin(angle + 2.094f), z_pos);
    Vec3 v2(cx + size * std::cos(angle + 4.189f), cy + size * std::sin(angle + 4.189f), z_pos);

    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// Generate co-planar triangles on XZ plane (floor-like geometry)
std::vector<Triangle> generateCoplanarTrianglesXZ(uint32_t count, float scene_size, float y_pos, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(count);

  for (uint32_t i = 0; i < count; i++) {
    float cx = rng.uniform(-scene_size, scene_size);
    float cz = rng.uniform(-scene_size, scene_size);
    float size = rng.uniform(0.1f, 0.5f);
    float angle = rng.uniform(0.0f, 6.28318f);

    Vec3 v0(cx + size * std::cos(angle), y_pos, cz + size * std::sin(angle));
    Vec3 v1(cx + size * std::cos(angle + 2.094f), y_pos, cz + size * std::sin(angle + 2.094f));
    Vec3 v2(cx + size * std::cos(angle + 4.189f), y_pos, cz + size * std::sin(angle + 4.189f));

    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// Generate multiple co-planar layers (like building floors)
std::vector<Triangle> generateMultipleCoplanarLayers(uint32_t tris_per_layer, uint32_t num_layers,
                                                      float scene_size, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(tris_per_layer * num_layers);

  float layer_spacing = (2.0f * scene_size) / (num_layers + 1);

  for (uint32_t layer = 0; layer < num_layers; layer++) {
    float y_pos = -scene_size + (layer + 1) * layer_spacing;
    auto layer_tris = generateCoplanarTrianglesXZ(tris_per_layer, scene_size, y_pos, rng);
    triangles.insert(triangles.end(), layer_tris.begin(), layer_tris.end());
  }

  return triangles;
}

// Generate tightly packed co-planar triangles (tessellated plane)
std::vector<Triangle> generateTessellatedPlane(uint32_t grid_res, float scene_size, float y_pos) {
  std::vector<Triangle> triangles;
  triangles.reserve(grid_res * grid_res * 2);

  float cell_size = (2.0f * scene_size) / grid_res;

  for (uint32_t x = 0; x < grid_res; x++) {
    for (uint32_t z = 0; z < grid_res; z++) {
      float x0 = -scene_size + x * cell_size;
      float x1 = x0 + cell_size;
      float z0 = -scene_size + z * cell_size;
      float z1 = z0 + cell_size;

      Vec3 v00(x0, y_pos, z0);
      Vec3 v10(x1, y_pos, z0);
      Vec3 v01(x0, y_pos, z1);
      Vec3 v11(x1, y_pos, z1);

      triangles.emplace_back(v00, v10, v11);
      triangles.emplace_back(v00, v11, v01);
    }
  }

  return triangles;
}

// Generate overlapping co-planar triangles at exact same height (worst case)
std::vector<Triangle> generateOverlappingCoplanar(uint32_t count, float scene_size, float y_pos, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(count);

  for (uint32_t i = 0; i < count; i++) {
    // Large triangles that overlap significantly
    float cx = rng.uniform(-scene_size * 0.5f, scene_size * 0.5f);
    float cz = rng.uniform(-scene_size * 0.5f, scene_size * 0.5f);
    float size = rng.uniform(scene_size * 0.3f, scene_size * 0.8f);
    float angle = rng.uniform(0.0f, 6.28318f);

    Vec3 v0(cx + size * std::cos(angle), y_pos, cz + size * std::sin(angle));
    Vec3 v1(cx + size * std::cos(angle + 2.094f), y_pos, cz + size * std::sin(angle + 2.094f));
    Vec3 v2(cx + size * std::cos(angle + 4.189f), y_pos, cz + size * std::sin(angle + 4.189f));

    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// Generate thin triangles spanning the scene (pathological for standard BVH)
// These triangles have long edges that span most of the scene but are very thin
std::vector<Triangle> generateThinSpanningTriangles(uint32_t count, float scene_size, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(count);

  for (uint32_t i = 0; i < count; i++) {
    // Random axis to span (0=X, 1=Y, 2=Z)
    int span_axis = static_cast<int>(rng.next() % 3);

    // Triangle spans most of the scene along span_axis
    float span_start = -scene_size * rng.uniform(0.8f, 1.0f);
    float span_end = scene_size * rng.uniform(0.8f, 1.0f);

    // Very thin perpendicular to span axis
    float thickness = rng.uniform(0.001f, 0.01f) * scene_size;

    // Random position along other axes
    float pos1 = rng.uniform(-scene_size * 0.8f, scene_size * 0.8f);
    float pos2 = rng.uniform(-scene_size * 0.8f, scene_size * 0.8f);

    Vec3 v0, v1, v2;
    if (span_axis == 0) {
      // Spans X axis
      v0 = Vec3(span_start, pos1, pos2);
      v1 = Vec3(span_end, pos1, pos2);
      v2 = Vec3((span_start + span_end) * 0.5f, pos1 + thickness, pos2);
    } else if (span_axis == 1) {
      // Spans Y axis
      v0 = Vec3(pos1, span_start, pos2);
      v1 = Vec3(pos1, span_end, pos2);
      v2 = Vec3(pos1 + thickness, (span_start + span_end) * 0.5f, pos2);
    } else {
      // Spans Z axis
      v0 = Vec3(pos1, pos2, span_start);
      v1 = Vec3(pos1, pos2, span_end);
      v2 = Vec3(pos1 + thickness, pos2, (span_start + span_end) * 0.5f);
    }

    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// Generate diagonal triangles (worst case: spans all 3 axes)
std::vector<Triangle> generateDiagonalTriangles(uint32_t count, float scene_size, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(count);

  for (uint32_t i = 0; i < count; i++) {
    // Diagonal from one corner toward opposite corner
    float t0 = rng.uniform(0.0f, 0.3f);
    float t1 = rng.uniform(0.7f, 1.0f);

    Vec3 corner0(-scene_size, -scene_size, -scene_size);
    Vec3 corner1(scene_size, scene_size, scene_size);
    Vec3 dir = corner1 - corner0;

    Vec3 v0 = corner0 + dir * t0;
    Vec3 v1 = corner0 + dir * t1;

    // Small offset perpendicular to diagonal
    float thickness = rng.uniform(0.001f, 0.02f) * scene_size;
    Vec3 perp(rng.uniform(-1.0f, 1.0f), rng.uniform(-1.0f, 1.0f), rng.uniform(-1.0f, 1.0f));
    perp = perp - dir * (perp.x * dir.x + perp.y * dir.y + perp.z * dir.z) /
                        (dir.x * dir.x + dir.y * dir.y + dir.z * dir.z);
    float len = std::sqrt(perp.x * perp.x + perp.y * perp.y + perp.z * perp.z);
    if (len > 0.0001f) {
      perp = perp * (thickness / len);
    } else {
      perp = Vec3(thickness, 0.0f, 0.0f);
    }

    Vec3 v2 = (v0 + v1) * 0.5f + perp;

    // Random offset to spread triangles
    Vec3 offset = rng.uniformVec3(-scene_size * 0.5f, scene_size * 0.5f);
    v0 = v0 + offset;
    v1 = v1 + offset;
    v2 = v2 + offset;

    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// Generate hair-like triangles (very thin, elongated)
std::vector<Triangle> generateHairTriangles(uint32_t count, float scene_size, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(count);

  for (uint32_t i = 0; i < count; i++) {
    // Hair root position
    Vec3 root = rng.uniformVec3(-scene_size * 0.8f, scene_size * 0.8f);

    // Hair direction (mostly upward with some randomness)
    Vec3 dir = Vec3(rng.uniform(-0.3f, 0.3f), 1.0f, rng.uniform(-0.3f, 0.3f));
    float len = std::sqrt(dir.x * dir.x + dir.y * dir.y + dir.z * dir.z);
    dir = dir * (1.0f / len);

    // Hair length (can be quite long relative to scene)
    float hair_length = rng.uniform(scene_size * 0.3f, scene_size * 0.9f);

    // Hair thickness (very thin)
    float thickness = rng.uniform(0.001f, 0.005f) * scene_size;

    Vec3 tip = root + dir * hair_length;

    // Perpendicular vector for width
    Vec3 perp;
    if (std::abs(dir.y) < 0.9f) {
      perp = Vec3(-dir.z, 0.0f, dir.x);
    } else {
      perp = Vec3(1.0f, 0.0f, 0.0f);
    }
    float perp_len = std::sqrt(perp.x * perp.x + perp.y * perp.y + perp.z * perp.z);
    perp = perp * (thickness / perp_len);

    Vec3 v0 = root - perp;
    Vec3 v1 = root + perp;
    Vec3 v2 = tip;

    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// Generate large triangles that span significant scene area (good for SBVH)
std::vector<Triangle> generateLargeTriangles(uint32_t count, float scene_size, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(count);

  for (uint32_t i = 0; i < count; i++) {
    // Large triangles spanning multiple regions
    float tri_size = rng.uniform(scene_size * 0.3f, scene_size * 0.8f);
    Vec3 center = rng.uniformVec3(-scene_size * 0.5f, scene_size * 0.5f);

    Vec3 v0 = center + Vec3(tri_size, 0.0f, 0.0f);
    Vec3 v1 = center + Vec3(-tri_size * 0.5f, tri_size * 0.866f, 0.0f);
    Vec3 v2 = center + Vec3(-tri_size * 0.5f, -tri_size * 0.866f, 0.0f);

    // Random rotation
    float angle = rng.uniform(0.0f, 3.14159265f);
    float ca = std::cos(angle), sa = std::sin(angle);
    auto rotate = [&](Vec3& v) {
      float x = v.x, y = v.y;
      v.x = x * ca - y * sa;
      v.y = x * sa + y * ca;
    };
    rotate(v0); rotate(v1); rotate(v2);

    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// ============================================================================
// Spanning Polygon Scene Generators
// ============================================================================

// Ground plane (1 large quad as 2 tris) + small random triangles above it
std::vector<Triangle> generateGroundPlaneScene(uint32_t small_count, float scene_size, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(small_count + 2);

  // Large ground quad at y=0 spanning [-scene_size, scene_size] in XZ
  Vec3 g0(-scene_size, 0.0f, -scene_size);
  Vec3 g1( scene_size, 0.0f, -scene_size);
  Vec3 g2( scene_size, 0.0f,  scene_size);
  Vec3 g3(-scene_size, 0.0f,  scene_size);
  triangles.emplace_back(g0, g1, g2);
  triangles.emplace_back(g0, g2, g3);

  // Small random triangles scattered above the plane
  for (uint32_t i = 0; i < small_count; i++) {
    Vec3 center(rng.uniform(-scene_size, scene_size),
                rng.uniform(0.1f, scene_size),
                rng.uniform(-scene_size, scene_size));
    float tri_size = rng.uniform(0.05f, 0.3f);
    Vec3 v0 = center + rng.uniformVec3(-tri_size, tri_size);
    Vec3 v1 = center + rng.uniformVec3(-tri_size, tri_size);
    Vec3 v2 = center + rng.uniformVec3(-tri_size, tri_size);
    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// Room enclosure (floor + ceiling + 4 walls = 12 tris) + small triangles inside
std::vector<Triangle> generateRoomScene(uint32_t small_count, float room_size, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(small_count + 12);

  float s = room_size;
  // Helper: add a quad as 2 triangles
  auto addQuad = [&](Vec3 a, Vec3 b, Vec3 c, Vec3 d) {
    triangles.emplace_back(a, b, c);
    triangles.emplace_back(a, c, d);
  };

  // Floor (y = 0)
  addQuad(Vec3(-s, 0, -s), Vec3( s, 0, -s), Vec3( s, 0,  s), Vec3(-s, 0,  s));
  // Ceiling (y = 2*s)
  addQuad(Vec3(-s, 2*s, -s), Vec3(-s, 2*s,  s), Vec3( s, 2*s,  s), Vec3( s, 2*s, -s));
  // Back wall (z = -s)
  addQuad(Vec3(-s, 0, -s), Vec3(-s, 2*s, -s), Vec3( s, 2*s, -s), Vec3( s, 0, -s));
  // Front wall (z = s)
  addQuad(Vec3(-s, 0,  s), Vec3( s, 0,  s), Vec3( s, 2*s,  s), Vec3(-s, 2*s,  s));
  // Left wall (x = -s)
  addQuad(Vec3(-s, 0, -s), Vec3(-s, 0,  s), Vec3(-s, 2*s,  s), Vec3(-s, 2*s, -s));
  // Right wall (x = s)
  addQuad(Vec3( s, 0, -s), Vec3( s, 2*s, -s), Vec3( s, 2*s,  s), Vec3( s, 0,  s));

  // Small random triangles inside the room
  for (uint32_t i = 0; i < small_count; i++) {
    Vec3 center(rng.uniform(-s * 0.9f, s * 0.9f),
                rng.uniform(0.1f, 2.0f * s * 0.9f),
                rng.uniform(-s * 0.9f, s * 0.9f));
    float tri_size = rng.uniform(0.05f, 0.3f);
    Vec3 v0 = center + rng.uniformVec3(-tri_size, tri_size);
    Vec3 v1 = center + rng.uniformVec3(-tri_size, tri_size);
    Vec3 v2 = center + rng.uniformVec3(-tri_size, tri_size);
    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// Large partition-like triangles spanning 50-100% of scene + small triangles
std::vector<Triangle> generateMixedSpanningScene(uint32_t num_large, uint32_t num_small,
                                                   float scene_size, RNG& rng) {
  std::vector<Triangle> triangles;
  triangles.reserve(num_large + num_small);

  // Large triangles spanning significant portion of scene
  for (uint32_t i = 0; i < num_large; i++) {
    float span_fraction = rng.uniform(0.5f, 1.0f);
    float span = scene_size * span_fraction;

    // Random axis-aligned orientation
    int axis = static_cast<int>(rng.next() % 3);
    float pos = rng.uniform(-scene_size * 0.5f, scene_size * 0.5f);

    Vec3 v0, v1, v2;
    if (axis == 0) {
      // Spans YZ plane
      v0 = Vec3(pos, -span, -span);
      v1 = Vec3(pos,  span, -span);
      v2 = Vec3(pos,  0.0f,  span);
    } else if (axis == 1) {
      // Spans XZ plane
      v0 = Vec3(-span, pos, -span);
      v1 = Vec3( span, pos, -span);
      v2 = Vec3( 0.0f, pos,  span);
    } else {
      // Spans XY plane
      v0 = Vec3(-span, -span, pos);
      v1 = Vec3( span, -span, pos);
      v2 = Vec3( 0.0f,  span, pos);
    }

    triangles.emplace_back(v0, v1, v2);
  }

  // Small random triangles scattered throughout
  for (uint32_t i = 0; i < num_small; i++) {
    Vec3 center = rng.uniformVec3(-scene_size, scene_size);
    float tri_size = rng.uniform(0.05f, 0.3f);
    Vec3 v0 = center + rng.uniformVec3(-tri_size, tri_size);
    Vec3 v1 = center + rng.uniformVec3(-tri_size, tri_size);
    Vec3 v2 = center + rng.uniformVec3(-tri_size, tri_size);
    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// ============================================================================
// Spanning Polygon Benchmark (TriangleBVH vs SBVH)
// ============================================================================

void benchmarkSpanningPolygons(uint32_t num_triangles, uint32_t num_rays) {
  std::cout << "\n========================================\n";
  std::cout << "Spanning Polygon Scenes (TriangleBVH vs SBVH)\n";
  std::cout << "========================================\n";
  std::cout << "\nLarge spanning polygons cause BVH AABB overlap at every split.\n";
  std::cout << "SBVH spatial splits clip these into tighter sub-references.\n";

  RNG rng(42);
  const float scene_size = 10.0f;

  // Generate downward camera rays (hits ground plane / floor)
  auto generateDownwardCameraRays = [&](uint32_t count, float sz) {
    std::vector<Ray> rays;
    rays.reserve(count);
    for (uint32_t i = 0; i < count; i++) {
      float x = rng.uniform(-sz, sz);
      float z = rng.uniform(-sz, sz);
      Vec3 origin(x, sz * 2.0f, z);
      Vec3 dir(rng.uniform(-0.1f, 0.1f), -1.0f, rng.uniform(-0.1f, 0.1f));
      float len = std::sqrt(dir.x * dir.x + dir.y * dir.y + dir.z * dir.z);
      dir = dir * (1.0f / len);
      rays.emplace_back(origin, dir);
    }
    return rays;
  };

  // Helper lambda to run TriangleBVH vs SBVH comparison on a scene
  auto runComparison = [&](const char* scene_name, const std::vector<Triangle>& triangles,
                            const std::vector<Ray>& rays) {
    std::cout << "\n--- " << scene_name << " ---\n";
    std::cout << "  Triangles: " << triangles.size() << ", Rays: " << rays.size() << "\n";

    // TriangleBVH
    double bvh_build_ms, bvh_traverse_ms;
    uint32_t bvh_hits = 0;
    uint64_t bvh_total_nodes = 0, bvh_total_prims = 0;
    BVH::Stats bvh_stats;
    {
      TriangleBVH bvh;
      BVHBuildConfig config;
      config.use_sah = true;
      config.use_binning = true;
      config.max_leaf_size = 4;

      bvh_build_ms = measureTime([&]() {
        bvh.build(triangles, config);
      });
      bvh_stats = bvh.getStats();

      bvh_traverse_ms = measureTime([&]() {
        for (const auto& ray : rays) {
          float t, u, v;
          TraversalStats stats;
          TraversalConfig cfg;
          if (bvh.traverseWithConfig(ray, t, u, v, cfg, &stats) != kInvalidIndex) {
            bvh_hits++;
          }
          bvh_total_nodes += stats.nodes_visited;
          bvh_total_prims += stats.prims_tested;
        }
      });
    }

    double bvh_mrays = (rays.size() / 1e6) / (bvh_traverse_ms / 1000.0);
    double bvh_avg_nodes = static_cast<double>(bvh_total_nodes) / rays.size();
    double bvh_avg_prims = static_cast<double>(bvh_total_prims) / rays.size();

    std::cout << "  TriangleBVH:\n";
    std::cout << std::fixed << std::setprecision(2);
    std::cout << "    Build: " << bvh_build_ms << " ms, Traverse: " << bvh_traverse_ms
              << " ms (" << bvh_mrays << " Mrays/s)\n";
    std::cout << "    SAH: " << std::scientific << bvh_stats.sah_cost << std::fixed
              << ", Nodes: " << bvh_stats.num_nodes << "\n";
    std::cout << "    Avg nodes/ray: " << std::setprecision(1) << bvh_avg_nodes
              << ", Avg prims/ray: " << bvh_avg_prims << "\n";
    std::cout << "    Hits: " << bvh_hits << "\n";

    // SBVH with default config (split_factor=1.5)
    auto runSBVH = [&](const char* label, float max_split_factor, float alpha) {
      double sbvh_build_ms, sbvh_traverse_ms;
      uint32_t sbvh_hits = 0;
      uint64_t sbvh_total_nodes = 0, sbvh_total_prims = 0;
      SBVH::Stats sbvh_stats;
      {
        SBVH sbvh;
        SBVHBuildConfig config;
        config.max_leaf_size = 4;
        config.num_spatial_bins = 256;
        config.num_object_bins = 32;
        config.alpha = alpha;
        config.max_split_factor = max_split_factor;

        sbvh_build_ms = measureTime([&]() {
          sbvh.build(triangles, config);
        });
        sbvh_stats = sbvh.getStats();

        sbvh_traverse_ms = measureTime([&]() {
          for (const auto& ray : rays) {
            float t, u, v;
            TraversalStats stats;
            TraversalConfig cfg;
            cfg.use_mailboxing = true;
            if (sbvh.traverseWithConfig(ray, t, u, v, cfg, &stats) != kInvalidIndex) {
              sbvh_hits++;
            }
            sbvh_total_nodes += stats.nodes_visited;
            sbvh_total_prims += stats.prims_tested;
          }
        });
      }

      double sbvh_mrays = (rays.size() / 1e6) / (sbvh_traverse_ms / 1000.0);
      double sbvh_avg_nodes = static_cast<double>(sbvh_total_nodes) / rays.size();
      double sbvh_avg_prims = static_cast<double>(sbvh_total_prims) / rays.size();
      double speedup = bvh_traverse_ms / sbvh_traverse_ms;

      std::cout << "  " << label << ":\n";
      std::cout << std::fixed << std::setprecision(2);
      std::cout << "    Build: " << sbvh_build_ms << " ms, Traverse: " << sbvh_traverse_ms
                << " ms (" << sbvh_mrays << " Mrays/s)\n";
      std::cout << "    SAH: " << std::scientific << sbvh_stats.sah_cost << std::fixed
                << ", Split ratio: " << std::setprecision(2) << sbvh_stats.split_ratio << "x\n";
      std::cout << "    Avg nodes/ray: " << std::setprecision(1) << sbvh_avg_nodes
                << ", Avg prims/ray: " << sbvh_avg_prims << "\n";
      std::cout << "    Hits: " << sbvh_hits
                << ", Speedup: " << std::setprecision(2) << speedup << "x"
                << (speedup > 1.0 ? " (SBVH faster)" : " (TriangleBVH faster)") << "\n";

      if (sbvh_hits != bvh_hits) {
        std::cout << "    WARNING: Hit count mismatch! (BVH=" << bvh_hits << " vs SBVH=" << sbvh_hits << ")\n";
      }
    };

    runSBVH("SBVH (split_factor=1.5)", 1.5f, 1e-5f);
    runSBVH("SBVH (split_factor=3.0, aggressive)", 3.0f, 1e-7f);
  };

  // ---- Scene A: Ground plane + small triangles ----
  uint32_t small_count = num_triangles > 2 ? num_triangles - 2 : 1000;
  {
    auto triangles = generateGroundPlaneScene(small_count, scene_size, rng);
    auto random_rays = generateRandomRays(num_rays, scene_size, rng);
    runComparison("Ground Plane + random rays", triangles, random_rays);

    auto downward_rays = generateDownwardCameraRays(num_rays, scene_size);
    runComparison("Ground Plane + downward camera rays", triangles, downward_rays);
  }

  // ---- Scene B: Room enclosure + small triangles ----
  {
    auto triangles = generateRoomScene(small_count, scene_size, rng);
    auto random_rays = generateRandomRays(num_rays, scene_size, rng);
    runComparison("Room Enclosure + random rays", triangles, random_rays);
  }

  // ---- Scene C: Mixed spanning partitions ----
  {
    uint32_t num_large = 20;
    uint32_t num_small = num_triangles > num_large ? num_triangles - num_large : 1000;
    auto triangles = generateMixedSpanningScene(num_large, num_small, scene_size, rng);
    auto random_rays = generateRandomRays(num_rays, scene_size, rng);
    runComparison("Mixed Spanning (20 large + small)", triangles, random_rays);
  }

  // ---- Scaling test: Ground plane with varying small triangle counts ----
  std::cout << "\n--- Scaling Test (Ground Plane) ---\n";
  std::cout << std::setw(12) << "SmallTris"
            << std::setw(14) << "BVH(ms)"
            << std::setw(14) << "SBVH(ms)"
            << std::setw(10) << "Speedup"
            << std::setw(14) << "BVH nodes/r"
            << std::setw(14) << "SBVH nodes/r" << "\n";
  std::cout << std::string(78, '-') << "\n";

  for (uint32_t sc : {1000u, 10000u, 100000u}) {
    RNG scale_rng(123);
    auto triangles = generateGroundPlaneScene(sc, scene_size, scale_rng);
    auto rays = generateRandomRays(num_rays, scene_size, scale_rng);

    // TriangleBVH
    double bvh_ms;
    uint64_t bvh_nodes_total = 0;
    {
      TriangleBVH bvh;
      bvh.build(triangles);
      bvh_ms = measureTime([&]() {
        for (const auto& ray : rays) {
          float t, u, v;
          TraversalStats stats;
          TraversalConfig cfg;
          bvh.traverseWithConfig(ray, t, u, v, cfg, &stats);
          bvh_nodes_total += stats.nodes_visited;
        }
      });
    }

    // SBVH
    double sbvh_ms;
    uint64_t sbvh_nodes_total = 0;
    {
      SBVH sbvh;
      SBVHBuildConfig config;
      config.max_split_factor = 2.0f;
      sbvh.build(triangles, config);
      sbvh_ms = measureTime([&]() {
        for (const auto& ray : rays) {
          float t, u, v;
          TraversalStats stats;
          TraversalConfig cfg;
          cfg.use_mailboxing = true;
          sbvh.traverseWithConfig(ray, t, u, v, cfg, &stats);
          sbvh_nodes_total += stats.nodes_visited;
        }
      });
    }

    double speedup = bvh_ms / sbvh_ms;
    double bvh_avg_nodes = static_cast<double>(bvh_nodes_total) / rays.size();
    double sbvh_avg_nodes = static_cast<double>(sbvh_nodes_total) / rays.size();

    std::cout << std::fixed << std::setprecision(2)
              << std::setw(12) << sc
              << std::setw(14) << bvh_ms
              << std::setw(14) << sbvh_ms
              << std::setw(10) << speedup << "x"
              << std::setw(13) << std::setprecision(1) << bvh_avg_nodes
              << std::setw(14) << sbvh_avg_nodes << "\n";
  }

  std::cout << "\n--- Analysis ---\n";
  std::cout << "Large spanning polygons (ground planes, walls) have AABBs that\n";
  std::cout << "overlap all children at every BVH split, degrading traversal.\n";
  std::cout << "SBVH spatial splits clip these into tighter sub-references,\n";
  std::cout << "reducing avg nodes/ray and prims/ray for better traversal.\n";
  std::cout << "Aggressive split_factor=3.0 allows more duplication for\n";
  std::cout << "potentially tighter bounds at the cost of longer build time.\n";
}

void benchmarkSBVHvsTriangleBVH(uint32_t num_triangles, uint32_t num_rays) {
  std::cout << "\n========================================\n";
  std::cout << "SBVH vs TriangleBVH Comparison\n";
  std::cout << "========================================\n";

  RNG rng(42);

  // Test with large triangles (where SBVH excels)
  std::cout << "\n=== Large Triangles (SBVH-favorable) ===\n";
  std::vector<Triangle> large_triangles = generateLargeTriangles(num_triangles, 10.0f, rng);
  std::vector<Ray> rays = generateRandomRays(num_rays, 10.0f, rng);

  // TriangleBVH
  {
    TriangleBVH bvh;
    BVHBuildConfig config;
    config.use_sah = true;
    config.use_binning = true;
    config.max_leaf_size = 4;

    BenchmarkResult result = {};
    result.num_primitives = num_triangles;
    result.num_rays = num_rays;

    result.build_time_ms = measureTime([&]() {
      bvh.build(large_triangles, config);
    });
    result.bvh_stats = bvh.getStats();

    result.traverse_time_ms = measureTime([&]() {
      for (const auto& ray : rays) {
        float t, u, v;
        if (bvh.traverse(ray, t, u, v) != kInvalidIndex) {
          result.num_hits++;
        }
      }
    });
    result.rays_per_second = (num_rays / result.traverse_time_ms) * 1000.0;
    printResult("TriangleBVH (large triangles)", result);
  }

  // SBVH
  {
    SBVH sbvh;
    SBVHBuildConfig config;
    config.max_leaf_size = 4;
    config.num_spatial_bins = 256;
    config.num_object_bins = 32;
    config.alpha = 1e-5f;
    config.max_split_factor = 1.5f;

    SBVHBenchmarkResult result = {};
    result.num_primitives = num_triangles;
    result.num_rays = num_rays;

    result.build_time_ms = measureTime([&]() {
      sbvh.build(large_triangles, config);
    });
    result.sbvh_stats = sbvh.getStats();
    result.num_references = result.sbvh_stats.num_references;

    result.traverse_time_ms = measureTime([&]() {
      for (const auto& ray : rays) {
        float t, u, v;
        if (sbvh.traverse(ray, t, u, v) != kInvalidIndex) {
          result.num_hits++;
        }
      }
    });
    result.rays_per_second = (num_rays / result.traverse_time_ms) * 1000.0;
    printSBVHResult("SBVH (large triangles)", result);
  }

  // Test with random triangles
  std::cout << "\n=== Random Triangles (baseline) ===\n";
  std::vector<Triangle> random_triangles = generateRandomTriangles(num_triangles, 10.0f, rng);
  rays = generateRandomRays(num_rays, 10.0f, rng);

  // TriangleBVH
  {
    TriangleBVH bvh;
    BVHBuildConfig config;
    config.use_sah = true;
    config.use_binning = true;
    config.max_leaf_size = 4;

    BenchmarkResult result = {};
    result.num_primitives = num_triangles;
    result.num_rays = num_rays;

    result.build_time_ms = measureTime([&]() {
      bvh.build(random_triangles, config);
    });
    result.bvh_stats = bvh.getStats();

    result.traverse_time_ms = measureTime([&]() {
      for (const auto& ray : rays) {
        float t, u, v;
        if (bvh.traverse(ray, t, u, v) != kInvalidIndex) {
          result.num_hits++;
        }
      }
    });
    result.rays_per_second = (num_rays / result.traverse_time_ms) * 1000.0;
    printResult("TriangleBVH (random triangles)", result);
  }

  // SBVH
  {
    SBVH sbvh;
    SBVHBuildConfig config;
    config.max_leaf_size = 4;
    config.num_spatial_bins = 256;
    config.num_object_bins = 32;
    config.alpha = 1e-5f;
    config.max_split_factor = 1.5f;

    SBVHBenchmarkResult result = {};
    result.num_primitives = num_triangles;
    result.num_rays = num_rays;

    result.build_time_ms = measureTime([&]() {
      sbvh.build(random_triangles, config);
    });
    result.sbvh_stats = sbvh.getStats();
    result.num_references = result.sbvh_stats.num_references;

    result.traverse_time_ms = measureTime([&]() {
      for (const auto& ray : rays) {
        float t, u, v;
        if (sbvh.traverse(ray, t, u, v) != kInvalidIndex) {
          result.num_hits++;
        }
      }
    });
    result.rays_per_second = (num_rays / result.traverse_time_ms) * 1000.0;
    printSBVHResult("SBVH (random triangles)", result);
  }

  std::cout << "\nSBVH Analysis:\n";
  std::cout << "- SBVH allows primitives to be split across nodes (spatial splits)\n";
  std::cout << "- Benefits large triangles that span multiple spatial regions\n";
  std::cout << "- Split ratio > 1.0 means primitives were duplicated\n";
  std::cout << "- Lower SAH cost generally correlates with faster traversal\n";
  std::cout << "- Trade-off: longer build time for potentially faster traversal\n";
}

// ============================================================================
// Pathological Scenes for SBVH
// ============================================================================

void benchmarkPathologicalScenes(uint32_t num_triangles, uint32_t num_rays) {
  std::cout << "\n========================================\n";
  std::cout << "Pathological Scenes (SBVH vs TriangleBVH)\n";
  std::cout << "========================================\n";
  std::cout << "\nThese scenes are designed to stress standard BVH\n";
  std::cout << "and demonstrate SBVH's spatial split benefits.\n";

  RNG rng(42);
  std::vector<Ray> rays = generateRandomRays(num_rays, 10.0f, rng);

  // Helper lambda for running benchmark on a scene
  auto runBenchmark = [&](const char* scene_name, const std::vector<Triangle>& triangles) {
    std::cout << "\n=== " << scene_name << " ===\n";
    std::cout << "Triangles: " << triangles.size() << "\n";

    // TriangleBVH
    double bvh_build_time, bvh_traverse_time;
    uint32_t bvh_hits = 0;
    BVH::Stats bvh_stats;
    {
      TriangleBVH bvh;
      BVHBuildConfig config;
      config.use_sah = true;
      config.use_binning = true;
      config.max_leaf_size = 4;

      bvh_build_time = measureTime([&]() {
        bvh.build(triangles, config);
      });
      bvh_stats = bvh.getStats();

      bvh_traverse_time = measureTime([&]() {
        for (const auto& ray : rays) {
          float t, u, v;
          if (bvh.traverse(ray, t, u, v) != kInvalidIndex) {
            bvh_hits++;
          }
        }
      });
    }

    // SBVH
    double sbvh_build_time, sbvh_traverse_time;
    uint32_t sbvh_hits = 0;
    SBVH::Stats sbvh_stats;
    {
      SBVH sbvh;
      SBVHBuildConfig config;
      config.max_leaf_size = 4;
      config.num_spatial_bins = 256;
      config.num_object_bins = 32;
      config.alpha = 1e-5f;
      config.max_split_factor = 2.0f;  // Allow more splits for pathological cases

      sbvh_build_time = measureTime([&]() {
        sbvh.build(triangles, config);
      });
      sbvh_stats = sbvh.getStats();

      sbvh_traverse_time = measureTime([&]() {
        for (const auto& ray : rays) {
          float t, u, v;
          if (sbvh.traverse(ray, t, u, v) != kInvalidIndex) {
            sbvh_hits++;
          }
        }
      });
    }

    // Print comparison
    double bvh_rays_per_sec = (num_rays / bvh_traverse_time) * 1000.0;
    double sbvh_rays_per_sec = (num_rays / sbvh_traverse_time) * 1000.0;
    double speedup = bvh_traverse_time / sbvh_traverse_time;

    std::cout << std::fixed << std::setprecision(2);
    std::cout << "\n  TriangleBVH:\n";
    std::cout << "    Build: " << bvh_build_time << " ms\n";
    std::cout << "    Traverse: " << bvh_traverse_time << " ms\n";
    std::cout << "    Rays/sec: " << std::scientific << bvh_rays_per_sec << "\n";
    std::cout << std::fixed;
    std::cout << "    Nodes: " << bvh_stats.num_nodes << ", Depth: " << bvh_stats.max_depth << "\n";
    std::cout << "    Hits: " << bvh_hits << " (" << (100.0 * bvh_hits / num_rays) << "%)\n";

    std::cout << "\n  SBVH:\n";
    std::cout << "    Build: " << sbvh_build_time << " ms\n";
    std::cout << "    Traverse: " << sbvh_traverse_time << " ms\n";
    std::cout << "    Rays/sec: " << std::scientific << sbvh_rays_per_sec << "\n";
    std::cout << std::fixed;
    std::cout << "    Nodes: " << sbvh_stats.num_nodes << ", Depth: " << sbvh_stats.max_depth << "\n";
    std::cout << "    References: " << sbvh_stats.num_references
              << " (split ratio: " << sbvh_stats.split_ratio << "x)\n";
    std::cout << "    Hits: " << sbvh_hits << " (" << (100.0 * sbvh_hits / num_rays) << "%)\n";

    std::cout << "\n  Speedup: " << speedup << "x";
    if (speedup > 1.0) {
      std::cout << " (SBVH faster)";
    } else if (speedup < 1.0) {
      std::cout << " (TriangleBVH faster)";
    }
    std::cout << "\n";
  };

  // Test 1: Thin spanning triangles (long edges across scene)
  {
    std::vector<Triangle> triangles = generateThinSpanningTriangles(num_triangles, 10.0f, rng);
    runBenchmark("Thin Spanning Triangles (long edges across bbox)", triangles);
  }

  // Test 2: Diagonal triangles (span all 3 axes)
  {
    std::vector<Triangle> triangles = generateDiagonalTriangles(num_triangles, 10.0f, rng);
    runBenchmark("Diagonal Triangles (span all 3 axes)", triangles);
  }

  // Test 3: Hair-like triangles (thin and elongated)
  {
    std::vector<Triangle> triangles = generateHairTriangles(num_triangles, 10.0f, rng);
    runBenchmark("Hair-like Triangles (thin elongated)", triangles);
  }

  // Test 4: Mixed scene (some large, some small)
  {
    std::vector<Triangle> triangles;
    triangles.reserve(num_triangles);

    // 30% thin spanning
    auto thin = generateThinSpanningTriangles(num_triangles * 3 / 10, 10.0f, rng);
    triangles.insert(triangles.end(), thin.begin(), thin.end());

    // 30% hair-like
    auto hair = generateHairTriangles(num_triangles * 3 / 10, 10.0f, rng);
    triangles.insert(triangles.end(), hair.begin(), hair.end());

    // 40% small random (normal)
    auto small = generateRandomTriangles(num_triangles * 4 / 10, 10.0f, rng);
    triangles.insert(triangles.end(), small.begin(), small.end());

    runBenchmark("Mixed Scene (30% thin + 30% hair + 40% small)", triangles);
  }

  std::cout << "\n--- Analysis ---\n";
  std::cout << "Thin spanning triangles: AABB covers large area but actual geometry is thin.\n";
  std::cout << "  Standard BVH cannot separate them well -> many false positive AABB hits.\n";
  std::cout << "  SBVH splits them spatially -> tighter bounds, fewer false positives.\n";
  std::cout << "\nDiagonal triangles: Span all 3 axes, worst case for axis-aligned BVH.\n";
  std::cout << "  Any split plane intersects most triangles.\n";
  std::cout << "  SBVH can clip triangles to create tighter local bounds.\n";
  std::cout << "\nHair-like triangles: Common in production scenes (fur, grass, cables).\n";
  std::cout << "  High aspect ratio causes AABB bloat.\n";
  std::cout << "  SBVH's spatial splits help significantly.\n";
}

// ============================================================================
// Co-planar Triangle Benchmark with Max Prim Test Limits
// ============================================================================

void benchmarkCoplanarTriangles(uint32_t num_triangles, uint32_t num_rays) {
  std::cout << "\n========================================\n";
  std::cout << "Co-planar Triangle Scenes\n";
  std::cout << "========================================\n";
  std::cout << "\nCo-planar triangles stress BVH construction because\n";
  std::cout << "they have zero extent in one axis, making splits difficult.\n";

  RNG rng(42);

  // Generate rays from above looking down (hits co-planar triangles)
  auto generateDownwardRays = [&](uint32_t count, float scene_size) {
    std::vector<Ray> rays;
    rays.reserve(count);
    for (uint32_t i = 0; i < count; i++) {
      float x = rng.uniform(-scene_size, scene_size);
      float z = rng.uniform(-scene_size, scene_size);
      Vec3 origin(x, scene_size * 2.0f, z);
      Vec3 dir(0.0f, -1.0f, 0.0f);
      rays.emplace_back(origin, dir);
    }
    return rays;
  };

  // Helper for running benchmark
  auto runCoplanarBenchmark = [&](const char* name, const std::vector<Triangle>& triangles,
                                   const std::vector<Ray>& rays) {
    std::cout << "\n=== " << name << " ===\n";
    std::cout << "Triangles: " << triangles.size() << ", Rays: " << rays.size() << "\n";

    // Build TriangleBVH
    TriangleBVH bvh;
    BVHBuildConfig config;
    config.use_sah = true;
    config.use_binning = true;
    config.max_leaf_size = 4;
    bvh.build(triangles, config);

    BVH::Stats bvh_stats = bvh.getStats();
    std::cout << "BVH: " << bvh_stats.num_nodes << " nodes, depth=" << bvh_stats.max_depth
              << ", avg_leaf=" << std::fixed << std::setprecision(1) << bvh_stats.avg_leaf_size << "\n";

    // Test with different max_prim_tests limits
    std::vector<uint32_t> limits = {0, 32, 64, 128, 256, 512};

    std::cout << "\nMax Prim Tests Impact (K << N):\n";
    std::cout << std::setw(12) << "Limit"
              << std::setw(12) << "Time(ms)"
              << std::setw(14) << "Rays/sec"
              << std::setw(10) << "Hits"
              << std::setw(12) << "AvgTests"
              << std::setw(10) << "Trunc%\n";
    std::cout << std::string(70, '-') << "\n";

    for (uint32_t limit : limits) {
      TraversalConfig trav_config;
      trav_config.max_prim_tests = limit;

      uint32_t total_hits = 0;
      uint64_t total_prim_tests = 0;
      uint32_t truncated_rays = 0;

      double traverse_time = measureTime([&]() {
        for (const auto& ray : rays) {
          float t, u, v;
          TraversalStats stats;
          if (bvh.traverseWithConfig(ray, t, u, v, trav_config, &stats) != kInvalidIndex) {
            total_hits++;
          }
          total_prim_tests += stats.prims_tested;
          if (stats.terminated_early) {
            truncated_rays++;
          }
        }
      });

      double rays_per_sec = (rays.size() / traverse_time) * 1000.0;
      double avg_tests = static_cast<double>(total_prim_tests) / rays.size();
      double trunc_pct = 100.0 * truncated_rays / rays.size();

      std::cout << std::fixed
                << std::setw(12) << (limit == 0 ? "unlimited" : std::to_string(limit))
                << std::setw(12) << std::setprecision(2) << traverse_time
                << std::setw(14) << std::scientific << std::setprecision(2) << rays_per_sec
                << std::setw(10) << std::fixed << total_hits
                << std::setw(12) << std::setprecision(1) << avg_tests
                << std::setw(10) << std::setprecision(1) << trunc_pct << "%\n";
    }
  };

  // Test 1: Single co-planar layer
  {
    auto triangles = generateCoplanarTrianglesXZ(num_triangles, 10.0f, 0.0f, rng);
    auto rays = generateDownwardRays(num_rays, 10.0f);
    runCoplanarBenchmark("Single Co-planar Layer (XZ plane, y=0)", triangles, rays);
  }

  // Test 2: Tessellated plane (no gaps, worst case for overlapping AABBs)
  {
    uint32_t grid_res = static_cast<uint32_t>(std::sqrt(num_triangles / 2.0));
    auto triangles = generateTessellatedPlane(grid_res, 10.0f, 0.0f);
    auto rays = generateDownwardRays(num_rays, 10.0f);
    runCoplanarBenchmark("Tessellated Plane (grid, no gaps)", triangles, rays);
  }

  // Test 3: Overlapping co-planar (large triangles, many overlaps)
  {
    auto triangles = generateOverlappingCoplanar(num_triangles / 10, 10.0f, 0.0f, rng);
    auto rays = generateDownwardRays(num_rays, 10.0f);
    runCoplanarBenchmark("Overlapping Co-planar (large, overlapping)", triangles, rays);
  }

  // Test 4: Multiple layers
  {
    uint32_t num_layers = 10;
    uint32_t tris_per_layer = num_triangles / num_layers;
    auto triangles = generateMultipleCoplanarLayers(tris_per_layer, num_layers, 10.0f, rng);
    auto rays = generateDownwardRays(num_rays, 10.0f);
    runCoplanarBenchmark("Multiple Co-planar Layers (10 floors)", triangles, rays);
  }

  // Test 5: SBVH comparison on co-planar scene
  std::cout << "\n=== SBVH vs TriangleBVH on Co-planar Scene ===\n";
  {
    auto triangles = generateOverlappingCoplanar(num_triangles / 10, 10.0f, 0.0f, rng);
    auto rays = generateDownwardRays(num_rays, 10.0f);

    std::cout << "Triangles: " << triangles.size() << "\n";

    // TriangleBVH
    {
      TriangleBVH bvh;
      BVHBuildConfig config;
      config.use_sah = true;
      config.use_binning = true;
      config.max_leaf_size = 4;
      bvh.build(triangles, config);

      uint32_t hits = 0;
      uint64_t total_tests = 0;

      double time = measureTime([&]() {
        for (const auto& ray : rays) {
          float t, u, v;
          TraversalStats stats;
          TraversalConfig cfg;
          if (bvh.traverseWithConfig(ray, t, u, v, cfg, &stats) != kInvalidIndex) {
            hits++;
          }
          total_tests += stats.prims_tested;
        }
      });

      std::cout << "\nTriangleBVH:\n";
      std::cout << "  Time: " << std::fixed << std::setprecision(2) << time << " ms\n";
      std::cout << "  Rays/sec: " << std::scientific << (rays.size() / time * 1000.0) << "\n";
      std::cout << std::fixed << "  Avg prim tests: " << std::setprecision(1)
                << (static_cast<double>(total_tests) / rays.size()) << "\n";
      std::cout << "  Hits: " << hits << "\n";
    }

    // SBVH with mailboxing
    {
      SBVH sbvh;
      SBVHBuildConfig config;
      config.max_leaf_size = 4;
      config.max_split_factor = 2.0f;
      sbvh.build(triangles, config);

      auto sbvh_stats = sbvh.getStats();
      std::cout << "\nSBVH (split ratio: " << std::setprecision(2) << sbvh_stats.split_ratio << "x):\n";

      // Without mailboxing
      {
        uint32_t hits = 0;
        uint64_t total_tests = 0;

        double time = measureTime([&]() {
          for (const auto& ray : rays) {
            float t, u, v;
            TraversalStats stats;
            TraversalConfig cfg;
            cfg.use_mailboxing = false;
            if (sbvh.traverseWithConfig(ray, t, u, v, cfg, &stats) != kInvalidIndex) {
              hits++;
            }
            total_tests += stats.prims_tested;
          }
        });

        std::cout << "  Without mailboxing:\n";
        std::cout << "    Time: " << std::setprecision(2) << time << " ms\n";
        std::cout << "    Avg prim tests: " << std::setprecision(1)
                  << (static_cast<double>(total_tests) / rays.size()) << "\n";
      }

      // With mailboxing
      {
        uint32_t hits = 0;
        uint64_t total_tests = 0;

        double time = measureTime([&]() {
          for (const auto& ray : rays) {
            float t, u, v;
            TraversalStats stats;
            TraversalConfig cfg;
            cfg.use_mailboxing = true;
            if (sbvh.traverseWithConfig(ray, t, u, v, cfg, &stats) != kInvalidIndex) {
              hits++;
            }
            total_tests += stats.prims_tested;
          }
        });

        std::cout << "  With mailboxing:\n";
        std::cout << "    Time: " << std::setprecision(2) << time << " ms\n";
        std::cout << "    Avg prim tests: " << std::setprecision(1)
                  << (static_cast<double>(total_tests) / rays.size()) << "\n";
      }

      // With max_prim_tests limit
      {
        uint32_t hits = 0;
        uint64_t total_tests = 0;
        uint32_t truncated = 0;

        double time = measureTime([&]() {
          for (const auto& ray : rays) {
            float t, u, v;
            TraversalStats stats;
            TraversalConfig cfg = TraversalConfig::fast(64);
            if (sbvh.traverseWithConfig(ray, t, u, v, cfg, &stats) != kInvalidIndex) {
              hits++;
            }
            total_tests += stats.prims_tested;
            if (stats.terminated_early) truncated++;
          }
        });

        std::cout << "  With max_prim_tests=64 + mailboxing:\n";
        std::cout << "    Time: " << std::setprecision(2) << time << " ms\n";
        std::cout << "    Avg prim tests: " << std::setprecision(1)
                  << (static_cast<double>(total_tests) / rays.size()) << "\n";
        std::cout << "    Hits: " << hits << " (truncated: " << truncated << ")\n";
      }
    }
  }

  std::cout << "\n--- Analysis ---\n";
  std::cout << "Co-planar triangles have zero extent in one axis (e.g., all y=0).\n";
  std::cout << "BVH cannot split along that axis, leading to large leaves or deep trees.\n";
  std::cout << "\nMax prim tests (K << N) limits worst-case behavior:\n";
  std::cout << "  - K=0 (unlimited): Full accuracy but O(N) worst case\n";
  std::cout << "  - K=64-256: Good balance of speed and accuracy\n";
  std::cout << "  - Truncation % shows how often K limit was hit\n";
  std::cout << "\nMailboxing in SBVH avoids duplicate tests when same primitive\n";
  std::cout << "appears in multiple leaves due to spatial splits.\n";
}

// ============================================================================
// Main
// ============================================================================

// ============================================================================
// Auto-Tuning Benchmark
// ============================================================================

void benchmarkAutoTuning(uint32_t num_triangles, uint32_t num_rays) {
  std::cout << "\n========================================\n";
  std::cout << "Auto-Tuning Benchmark\n";
  std::cout << "========================================\n";

  RNG rng(42);

  // Test different scene types
  struct SceneType {
    std::string name;
    std::vector<Triangle> (*generator)(uint32_t, float, RNG&);
    bool needs_rng;
  };

  // Generate different scenes to test auto-tuning
  std::cout << "\n1. Random Triangles Scene\n";
  std::cout << "-------------------------\n";
  {
    auto triangles = generateRandomTriangles(num_triangles, 10.0f, rng);

    std::cout << "Scene: " << triangles.size() << " random triangles\n";

    // Quick tune
    auto start = std::chrono::high_resolution_clock::now();
    auto result = AutoTuner::tune(triangles, AutoTuneConfig::quick());
    auto end = std::chrono::high_resolution_clock::now();
    double tune_time_ms = std::chrono::duration<double, std::milli>(end - start).count();

    std::cout << "Quick tune time: " << std::fixed << std::setprecision(2)
              << tune_time_ms << " ms\n";

    std::cout << "Best method: "
              << (result.best_method == BVHBuildMethod::TriangleBVH ? "TriangleBVH" : "SBVH") << "\n";
    std::cout << "Best max_leaf_size: " << result.best_bvh_config.max_leaf_size << "\n";
    std::cout << "Build time: " << result.build_time_us_per_prim << " us/prim\n";
    std::cout << "Traversal time: " << result.traversal_time_ns_per_ray << " ns/ray\n";
    std::cout << "Memory: " << result.memory_bytes_per_prim << " bytes/prim\n";

    // Scene characteristics
    std::cout << "\nScene analysis:\n";
    std::cout << "  Avg triangle area: " << result.scene_info.avg_triangle_area << "\n";
    std::cout << "  Triangle density: " << result.scene_info.triangle_density << "\n";
    std::cout << "  Overlap ratio: " << result.scene_info.overlap_ratio << "\n";
    std::cout << "  Has thin triangles: " << (result.scene_info.has_thin_triangles ? "yes" : "no") << "\n";
    std::cout << "  Has clustered distribution: " << (result.scene_info.has_clustered_distribution ? "yes" : "no") << "\n";
    std::cout << "  Has coplanar regions: " << (result.scene_info.has_coplanar_regions ? "yes" : "no") << "\n";
  }

  std::cout << "\n2. Hair-like Triangles Scene\n";
  std::cout << "----------------------------\n";
  {
    auto triangles = generateHairTriangles(num_triangles, 10.0f, rng);

    std::cout << "Scene: " << triangles.size() << " hair-like triangles\n";

    // Full tune with SBVH
    AutoTuneConfig cfg;
    cfg.test_sbvh = true;
    cfg.sample_prim_count = 2000;  // More samples for complex scene

    auto start = std::chrono::high_resolution_clock::now();
    auto result = AutoTuner::tune(triangles, cfg);
    auto end = std::chrono::high_resolution_clock::now();
    double tune_time_ms = std::chrono::duration<double, std::milli>(end - start).count();

    std::cout << "Full tune time: " << std::fixed << std::setprecision(2)
              << tune_time_ms << " ms\n";

    std::cout << "Best method: "
              << (result.best_method == BVHBuildMethod::TriangleBVH ? "TriangleBVH" : "SBVH") << "\n";
    if (result.best_method == BVHBuildMethod::SBVH) {
      std::cout << "SBVH alpha: " << result.best_sbvh_config.alpha << "\n";
      std::cout << "SBVH max_leaf_size: " << result.best_sbvh_config.max_leaf_size << "\n";
    } else {
      std::cout << "BVH max_leaf_size: " << result.best_bvh_config.max_leaf_size << "\n";
    }

    std::cout << "Best traversal config:\n";
    std::cout << "  max_prim_tests: " << result.best_traversal_config.max_prim_tests << "\n";
    std::cout << "  use_mailboxing: " << (result.best_traversal_config.use_mailboxing ? "yes" : "no") << "\n";

    // Scene characteristics
    std::cout << "\nScene analysis:\n";
    std::cout << "  Has thin triangles: " << (result.scene_info.has_thin_triangles ? "yes" : "no") << "\n";
    std::cout << "  Overlap ratio: " << result.scene_info.overlap_ratio << "\n";

    // Show all tested configurations
    std::cout << "\nAll tested configurations:\n";
    std::cout << std::setw(12) << "Method" << std::setw(10) << "LeafSz"
              << std::setw(12) << "Build(us)" << std::setw(12) << "Trav(ns)"
              << std::setw(12) << "Mem(B)" << std::setw(10) << "Cost" << "\n";
    for (const auto& m : result.all_metrics) {
      std::cout << std::setw(12) << (m.method == BVHBuildMethod::TriangleBVH ? "TriBVH" : "SBVH")
                << std::setw(10) << m.max_leaf_size
                << std::setw(12) << std::setprecision(3) << m.build_time_us_per_prim
                << std::setw(12) << std::setprecision(2) << m.traversal_time_ns_per_ray
                << std::setw(12) << std::setprecision(1) << m.memory_bytes_per_prim
                << std::setw(10) << std::setprecision(4) << m.combined_cost << "\n";
    }
  }

  std::cout << "\n3. Co-planar Triangles Scene\n";
  std::cout << "----------------------------\n";
  {
    auto triangles = generateOverlappingCoplanar(num_triangles, 10.0f, 0.0f, rng);

    std::cout << "Scene: " << triangles.size() << " overlapping co-planar triangles\n";

    // Throughput-optimized tuning
    auto start = std::chrono::high_resolution_clock::now();
    auto result = AutoTuner::tune(triangles, AutoTuneConfig::throughput());
    auto end = std::chrono::high_resolution_clock::now();
    double tune_time_ms = std::chrono::duration<double, std::milli>(end - start).count();

    std::cout << "Throughput-optimized tune time: " << std::fixed << std::setprecision(2)
              << tune_time_ms << " ms\n";

    std::cout << "Best method: "
              << (result.best_method == BVHBuildMethod::TriangleBVH ? "TriangleBVH" : "SBVH") << "\n";

    std::cout << "Best traversal config:\n";
    std::cout << "  max_prim_tests: " << result.best_traversal_config.max_prim_tests << "\n";
    std::cout << "  use_mailboxing: " << (result.best_traversal_config.use_mailboxing ? "yes" : "no") << "\n";

    std::cout << "\nScene analysis:\n";
    std::cout << "  Has coplanar regions: " << (result.scene_info.has_coplanar_regions ? "yes" : "no") << "\n";
    std::cout << "  Overlap ratio: " << result.scene_info.overlap_ratio << "\n";
  }

  std::cout << "\n4. Verify Auto-Tuned Build\n";
  std::cout << "--------------------------\n";
  {
    auto triangles = generateRandomTriangles(num_triangles, 10.0f, rng);

    // Use buildOptimal for convenience
    TriangleBVH auto_bvh;
    auto start = std::chrono::high_resolution_clock::now();
    AutoTuner::buildOptimal(triangles, auto_bvh, AutoTuneConfig::quick());
    auto end = std::chrono::high_resolution_clock::now();
    double build_time_ms = std::chrono::duration<double, std::milli>(end - start).count();

    std::cout << "buildOptimal() time (tune + build): " << std::fixed << std::setprecision(2)
              << build_time_ms << " ms\n";

    // Compare with default build
    TriangleBVH default_bvh;
    start = std::chrono::high_resolution_clock::now();
    default_bvh.build(triangles);
    end = std::chrono::high_resolution_clock::now();
    double default_build_ms = std::chrono::duration<double, std::milli>(end - start).count();

    std::cout << "Default build() time: " << default_build_ms << " ms\n";

    // Measure traversal performance
    AABB scene_bounds;
    for (const auto& tri : triangles) {
      scene_bounds.expand(tri.bounds());
    }

    std::vector<Ray> rays;
    rays.reserve(num_rays);
    for (uint32_t i = 0; i < num_rays; i++) {
      Vec3 origin = rng.uniformVec3(-20.0f, 20.0f);
      Vec3 target = rng.uniformVec3(-10.0f, 10.0f);
      rays.emplace_back(origin, (target - origin).normalize());
    }

    // Benchmark auto-tuned BVH
    uint32_t auto_hits = 0;
    start = std::chrono::high_resolution_clock::now();
    for (const auto& ray : rays) {
      float t, u, v;
      if (auto_bvh.traverse(ray, t, u, v) != kInvalidIndex) {
        auto_hits++;
      }
    }
    end = std::chrono::high_resolution_clock::now();
    double auto_trav_ms = std::chrono::duration<double, std::milli>(end - start).count();

    // Benchmark default BVH
    uint32_t default_hits = 0;
    start = std::chrono::high_resolution_clock::now();
    for (const auto& ray : rays) {
      float t, u, v;
      if (default_bvh.traverse(ray, t, u, v) != kInvalidIndex) {
        default_hits++;
      }
    }
    end = std::chrono::high_resolution_clock::now();
    double default_trav_ms = std::chrono::duration<double, std::milli>(end - start).count();

    std::cout << "\nTraversal comparison:\n";
    std::cout << "  Auto-tuned: " << auto_trav_ms << " ms (" << auto_hits << " hits)\n";
    std::cout << "  Default:    " << default_trav_ms << " ms (" << default_hits << " hits)\n";
    std::cout << "  Speedup:    " << (default_trav_ms / auto_trav_ms) << "x\n";

    // Verify hits match
    if (auto_hits != default_hits) {
      std::cout << "  WARNING: Hit counts differ!\n";
    }
  }

  std::cout << "\n5. Traversal Config Tuning (Existing BVH)\n";
  std::cout << "-----------------------------------------\n";
  {
    auto triangles = generateOverlappingCoplanar(num_triangles / 2, 10.0f, 0.0f, rng);

    // Build BVH first
    TriangleBVH bvh;
    bvh.build(triangles);

    AABB scene_bounds;
    for (const auto& tri : triangles) {
      scene_bounds.expand(tri.bounds());
    }

    std::cout << "Scene: " << triangles.size() << " overlapping triangles\n";

    // Tune traversal config
    auto start = std::chrono::high_resolution_clock::now();
    auto best_trav = AutoTuner::tuneTraversal(bvh, scene_bounds, 2000, 5);
    auto end = std::chrono::high_resolution_clock::now();
    double tune_time_ms = std::chrono::duration<double, std::milli>(end - start).count();

    std::cout << "Traversal tune time: " << std::fixed << std::setprecision(2)
              << tune_time_ms << " ms\n";
    std::cout << "Best traversal config:\n";
    std::cout << "  max_prim_tests: " << best_trav.max_prim_tests << "\n";
    std::cout << "  use_mailboxing: " << (best_trav.use_mailboxing ? "yes" : "no") << "\n";
    std::cout << "  early_termination: " << (best_trav.early_termination ? "yes" : "no") << "\n";
  }
}

int main(int argc, char** argv) {
  std::cout << "============================================\n";
  std::cout << "LightRT BVH Benchmark Suite\n";
  std::cout << "============================================\n";

  // Parse arguments
  uint32_t num_triangles = 100000;
  uint32_t num_rays = 100000;

  if (argc > 1) {
    num_triangles = static_cast<uint32_t>(std::atoi(argv[1]));
  }
  if (argc > 2) {
    num_rays = static_cast<uint32_t>(std::atoi(argv[2]));
  }

  std::cout << "\nConfiguration:\n";
  std::cout << "  Triangles: " << num_triangles << "\n";
  std::cout << "  Rays: " << num_rays << "\n";

  // Run benchmarks
  std::cout << "\n========================================\n";
  std::cout << "1. Random Triangles + Random Rays\n";
  std::cout << "========================================\n";
  printResult("Random/Random", benchmarkRandomTriangles(num_triangles, num_rays));

  std::cout << "\n========================================\n";
  std::cout << "2. Uniform Grid Triangles + Random Rays\n";
  std::cout << "========================================\n";
  uint32_t grid_size = static_cast<uint32_t>(std::cbrt(num_triangles / 2.0));
  printResult("Uniform/Random", benchmarkUniformTriangles(grid_size, num_rays));

  std::cout << "\n========================================\n";
  std::cout << "3. Random Triangles + Coherent Rays\n";
  std::cout << "========================================\n";
  uint32_t res = static_cast<uint32_t>(std::sqrt(num_rays));
  printResult("Random/Coherent", benchmarkCoherentRays(num_triangles, res));

  // Overlapping triangles test
  benchmarkOverlappingTriangles();

  // SBVH comparison
  benchmarkSBVHvsTriangleBVH(num_triangles, num_rays);

  // Pathological scenes for SBVH
  benchmarkPathologicalScenes(num_triangles, num_rays);

  // Co-planar triangle scenes with max prim test limits
  benchmarkCoplanarTriangles(num_triangles, num_rays);

  // Spanning polygon scenes (ground planes, rooms, partitions)
  benchmarkSpanningPolygons(num_triangles, num_rays);

  // Auto-tuning benchmark
  benchmarkAutoTuning(num_triangles, num_rays);

  // MMap BVH benchmark
  std::cout << "\n========================================\n";
  std::cout << "MMap BVH Benchmark (Zero-Copy)\n";
  std::cout << "========================================\n";
  {
    RNG rng(42);
    auto triangles = generateRandomTriangles(num_triangles, 10.0f, rng);

    std::cout << "\nScene: " << triangles.size() << " triangles\n";

    // Standard TriangleBVH (copies data)
    TriangleBVH standard_bvh;
    auto start = std::chrono::high_resolution_clock::now();
    standard_bvh.build(triangles);
    auto end = std::chrono::high_resolution_clock::now();
    double standard_build_ms = std::chrono::duration<double, std::milli>(end - start).count();

    auto standard_stats = standard_bvh.getStats();
    size_t standard_memory = standard_stats.num_nodes * sizeof(BVHNode) +
                             triangles.size() * sizeof(Triangle);

    // MMap BVH with compact nodes (references external data)
    MMapTriangleBVH mmap_compact_bvh;
    start = std::chrono::high_resolution_clock::now();
    mmap_compact_bvh.build(triangles.data(), static_cast<uint32_t>(triangles.size()),
                           MMapBVHConfig::minMemory());
    end = std::chrono::high_resolution_clock::now();
    double mmap_compact_build_ms = std::chrono::duration<double, std::milli>(end - start).count();

    auto mmap_compact_stats = mmap_compact_bvh.getStats();

    // MMap BVH with full precision nodes
    MMapTriangleBVH mmap_full_bvh;
    start = std::chrono::high_resolution_clock::now();
    mmap_full_bvh.build(triangles.data(), static_cast<uint32_t>(triangles.size()),
                        MMapBVHConfig::maxSpeed());
    end = std::chrono::high_resolution_clock::now();
    double mmap_full_build_ms = std::chrono::duration<double, std::milli>(end - start).count();

    auto mmap_full_stats = mmap_full_bvh.getStats();

    std::cout << "\n=== Build Time ===\n";
    std::cout << "  Standard TriangleBVH:  " << std::fixed << std::setprecision(2)
              << standard_build_ms << " ms\n";
    std::cout << "  MMap Compact (16-bit): " << mmap_compact_build_ms << " ms\n";
    std::cout << "  MMap Full (32-bit):    " << mmap_full_build_ms << " ms\n";

    std::cout << "\n=== BVH Memory Usage ===\n";
    std::cout << "  Standard TriangleBVH:  " << (standard_memory / 1024.0) << " KB"
              << " (includes triangle copy)\n";
    std::cout << "  MMap Compact (16-bit): " << (mmap_compact_stats.bvh_memory_bytes / 1024.0) << " KB"
              << " (BVH only, triangles external)\n";
    std::cout << "  MMap Full (32-bit):    " << (mmap_full_stats.bvh_memory_bytes / 1024.0) << " KB"
              << " (BVH only, triangles external)\n";

    float savings_compact = 100.0f * (1.0f - static_cast<float>(mmap_compact_stats.bvh_memory_bytes) / standard_memory);
    float savings_full = 100.0f * (1.0f - static_cast<float>(mmap_full_stats.bvh_memory_bytes) / standard_memory);
    std::cout << "\n  Memory savings (vs standard with copy):\n";
    std::cout << "    MMap Compact: " << std::setprecision(1) << savings_compact << "%\n";
    std::cout << "    MMap Full:    " << savings_full << "%\n";

    std::cout << "\n=== Index Precision ===\n";
    std::cout << "  MMap Compact: " << static_cast<int>(mmap_compact_stats.index_bytes) << " bytes/index";
    if (mmap_compact_stats.index_bytes == 1) std::cout << " (uint8)";
    else if (mmap_compact_stats.index_bytes == 2) std::cout << " (uint16)";
    else std::cout << " (uint32)";
    std::cout << "\n";
    std::cout << "  MMap Full:    " << static_cast<int>(mmap_full_stats.index_bytes) << " bytes/index";
    if (mmap_full_stats.index_bytes == 1) std::cout << " (uint8)";
    else if (mmap_full_stats.index_bytes == 2) std::cout << " (uint16)";
    else std::cout << " (uint32)";
    std::cout << "\n";

    // Generate test rays
    std::vector<Ray> rays;
    rays.reserve(num_rays);
    for (uint32_t i = 0; i < num_rays; i++) {
      Vec3 origin = rng.uniformVec3(-20.0f, 20.0f);
      Vec3 target = rng.uniformVec3(-10.0f, 10.0f);
      rays.emplace_back(origin, (target - origin).normalize());
    }

    // Benchmark traversal
    uint32_t standard_hits = 0;
    start = std::chrono::high_resolution_clock::now();
    for (const auto& ray : rays) {
      float t, u, v;
      if (standard_bvh.traverse(ray, t, u, v) != kInvalidIndex) {
        standard_hits++;
      }
    }
    end = std::chrono::high_resolution_clock::now();
    double standard_trav_ms = std::chrono::duration<double, std::milli>(end - start).count();

    uint32_t mmap_compact_hits = 0;
    start = std::chrono::high_resolution_clock::now();
    for (const auto& ray : rays) {
      float t, u, v;
      if (mmap_compact_bvh.traverse(ray, t, u, v) != kInvalidIndex) {
        mmap_compact_hits++;
      }
    }
    end = std::chrono::high_resolution_clock::now();
    double mmap_compact_trav_ms = std::chrono::duration<double, std::milli>(end - start).count();

    uint32_t mmap_full_hits = 0;
    start = std::chrono::high_resolution_clock::now();
    for (const auto& ray : rays) {
      float t, u, v;
      if (mmap_full_bvh.traverse(ray, t, u, v) != kInvalidIndex) {
        mmap_full_hits++;
      }
    }
    end = std::chrono::high_resolution_clock::now();
    double mmap_full_trav_ms = std::chrono::duration<double, std::milli>(end - start).count();

    std::cout << "\n=== Traversal Performance ===\n";
    std::cout << "  Standard TriangleBVH:  " << standard_trav_ms << " ms ("
              << standard_hits << " hits, " << std::scientific << std::setprecision(2)
              << (num_rays / standard_trav_ms * 1000) << " rays/sec)\n";
    std::cout << "  MMap Compact (16-bit): " << std::fixed << std::setprecision(2)
              << mmap_compact_trav_ms << " ms ("
              << mmap_compact_hits << " hits, " << std::scientific << std::setprecision(2)
              << (num_rays / mmap_compact_trav_ms * 1000) << " rays/sec)\n";
    std::cout << "  MMap Full (32-bit):    " << std::fixed << std::setprecision(2)
              << mmap_full_trav_ms << " ms ("
              << mmap_full_hits << " hits, " << std::scientific << std::setprecision(2)
              << (num_rays / mmap_full_trav_ms * 1000) << " rays/sec)\n";

    // Verify correctness
    if (standard_hits != mmap_compact_hits || standard_hits != mmap_full_hits) {
      std::cout << "\n  WARNING: Hit counts differ!\n";
    } else {
      std::cout << "\n  All implementations produce same results.\n";
    }

    // Test with small primitive count to show uint8 index
    std::cout << "\n=== Small Scene (uint8 indices) ===\n";
    auto small_triangles = generateRandomTriangles(200, 10.0f, rng);
    MMapTriangleBVH small_bvh;
    small_bvh.build(small_triangles.data(), static_cast<uint32_t>(small_triangles.size()));
    auto small_stats = small_bvh.getStats();
    std::cout << "  Triangles: " << small_stats.num_primitives << "\n";
    std::cout << "  Index precision: " << static_cast<int>(small_stats.index_bytes)
              << " bytes (uint8)\n";
    std::cout << "  BVH memory: " << small_stats.bvh_memory_bytes << " bytes\n";

    // Test with medium scene for uint16 index
    std::cout << "\n=== Medium Scene (uint16 indices) ===\n";
    auto medium_triangles = generateRandomTriangles(30000, 10.0f, rng);
    MMapTriangleBVH medium_bvh;
    medium_bvh.build(medium_triangles.data(), static_cast<uint32_t>(medium_triangles.size()));
    auto medium_stats = medium_bvh.getStats();
    std::cout << "  Triangles: " << medium_stats.num_primitives << "\n";
    std::cout << "  Index precision: " << static_cast<int>(medium_stats.index_bytes)
              << " bytes (uint16)\n";
    std::cout << "  BVH memory: " << (medium_stats.bvh_memory_bytes / 1024.0) << " KB\n";
  }

  // ========================================
  // Profiling and Heatmap Benchmark
  // ========================================
  {
    std::cout << "\n========================================\n";
    std::cout << "Profiling and Heatmap Benchmark\n";
    std::cout << "========================================\n\n";

    RNG profile_rng(99);

    // Create a simple scene
    auto profile_triangles = generateRandomTriangles(10000, 10.0f, profile_rng);
    TriangleBVH profile_bvh;
    profile_bvh.build(profile_triangles);

    AABB scene_bounds;
    for (const auto& tri : profile_triangles) {
      scene_bounds.expand(tri.bounds());
    }

    // Test profiled traversal vs normal traversal
    std::cout << "=== Profiled vs Non-Profiled Traversal ===\n";
    std::cout << "Testing 10000 rays...\n\n";

    std::vector<Ray> profile_rays;
    for (uint32_t i = 0; i < 10000; i++) {
      Vec3 origin = profile_rng.uniformVec3(-20.0f, 20.0f);
      Vec3 target = profile_rng.uniformVec3(-10.0f, 10.0f);
      profile_rays.emplace_back(origin, (target - origin).normalize());
    }

    // Non-profiled (template NoProfiler - should have zero overhead)
    auto start = std::chrono::high_resolution_clock::now();
    uint32_t hits_noprofile = 0;
    for (const auto& ray : profile_rays) {
      float t, u, v;
      uint32_t hit = traverseProfiled<NoProfiler>(profile_bvh, ray, t, u, v, nullptr);
      if (hit != kInvalidIndex) hits_noprofile++;
    }
    auto end = std::chrono::high_resolution_clock::now();
    double time_noprofile = std::chrono::duration<double, std::milli>(end - start).count();

    // Profiled (template WithProfiler - collects stats)
    start = std::chrono::high_resolution_clock::now();
    uint32_t hits_profile = 0;
    TraversalProfile total_profile;
    for (const auto& ray : profile_rays) {
      float t, u, v;
      TraversalProfile profile;
      uint32_t hit = traverseProfiled<WithProfiler>(profile_bvh, ray, t, u, v, &profile);
      if (hit != kInvalidIndex) hits_profile++;
      total_profile.add(profile);
    }
    end = std::chrono::high_resolution_clock::now();
    double time_profile = std::chrono::duration<double, std::milli>(end - start).count();

    std::cout << "  Non-profiled: " << std::fixed << std::setprecision(2)
              << time_noprofile << " ms (" << hits_noprofile << " hits)\n";
    std::cout << "  Profiled:     " << time_profile << " ms (" << hits_profile << " hits)\n";
    std::cout << "  Overhead:     " << ((time_profile / time_noprofile - 1.0) * 100.0) << "%\n";

    std::cout << "\n=== Aggregate Profile Statistics ===\n";
    std::cout << "  Total nodes visited: " << total_profile.nodes_visited << "\n";
    std::cout << "  Total leaf visits:   " << total_profile.leaf_visits << "\n";
    std::cout << "  Total prims tested:  " << total_profile.prims_tested << "\n";
    std::cout << "  Max depth reached:   " << total_profile.max_depth << "\n";
    std::cout << "  Avg nodes/ray:       " << (float)total_profile.nodes_visited / profile_rays.size() << "\n";
    std::cout << "  Avg prims/ray:       " << (float)total_profile.prims_tested / profile_rays.size() << "\n";

    // Test heatmap writing
    std::cout << "\n=== Heatmap Image Writing ===\n";
    const uint32_t img_width = 128;
    const uint32_t img_height = 128;

    // Render a small image with profiling
    Vec3 camera_pos(0.0f, 0.0f, 30.0f);
    Vec3 camera_dir(0.0f, 0.0f, -1.0f);
    Vec3 camera_up(0.0f, 1.0f, 0.0f);
    float fov_y = 60.0f * 3.14159265f / 180.0f;  // 60 degrees

    TraversalProfile* image_profiles = renderImageProfiled(
        profile_bvh, img_width, img_height,
        camera_pos, camera_dir, camera_up, fov_y, nullptr);

    // Write heatmaps in different formats and colormaps
    bool ok = HeatmapWriter::writeHeatmap("heatmap_nodes.bmp", image_profiles,
                                           img_width, img_height,
                                           HeatmapWriter::Metric::NodesVisited,
                                           Colormap::Viridis, ImageFormat::BMP);
    std::cout << "  heatmap_nodes.bmp (Viridis):    " << (ok ? "OK" : "FAILED") << "\n";

    ok = HeatmapWriter::writeHeatmap("heatmap_prims.bmp", image_profiles,
                                      img_width, img_height,
                                      HeatmapWriter::Metric::PrimsTested,
                                      Colormap::Hot, ImageFormat::BMP);
    std::cout << "  heatmap_prims.bmp (Hot):        " << (ok ? "OK" : "FAILED") << "\n";

    ok = HeatmapWriter::writeHeatmap("heatmap_depth.tga", image_profiles,
                                      img_width, img_height,
                                      HeatmapWriter::Metric::MaxDepth,
                                      Colormap::Jet, ImageFormat::TGA);
    std::cout << "  heatmap_depth.tga (Jet):        " << (ok ? "OK" : "FAILED") << "\n";

    ok = HeatmapWriter::writeHeatmap("heatmap_leaves.ppm", image_profiles,
                                      img_width, img_height,
                                      HeatmapWriter::Metric::LeafVisits,
                                      Colormap::Turbo, ImageFormat::PPM);
    std::cout << "  heatmap_leaves.ppm (Turbo):     " << (ok ? "OK" : "FAILED") << "\n";

    // Test direct colormap API
    std::vector<float> test_values(img_width * img_height);
    for (uint32_t i = 0; i < img_width * img_height; i++) {
      test_values[i] = static_cast<float>(i) / (img_width * img_height);
    }
    ok = HeatmapWriter::writeImage("colormap_test.bmp", test_values.data(),
                                    img_width, img_height,
                                    Colormap::Plasma, ImageFormat::BMP);
    std::cout << "  colormap_test.bmp (Plasma):     " << (ok ? "OK" : "FAILED") << "\n";

    // Test PNG format
    ok = HeatmapWriter::writeHeatmap("heatmap_prims.png", image_profiles,
                                      img_width, img_height,
                                      HeatmapWriter::Metric::PrimsTested,
                                      Colormap::Viridis, ImageFormat::PNG);
    std::cout << "  heatmap_prims.png (Viridis):    " << (ok ? "OK" : "FAILED") << "\n";

    ok = HeatmapWriter::writeImage("colormap_test.png", test_values.data(),
                                    img_width, img_height,
                                    Colormap::Inferno, ImageFormat::PNG);
    std::cout << "  colormap_test.png (Inferno):    " << (ok ? "OK" : "FAILED") << "\n";

    // Cleanup
    delete[] image_profiles;

    // Show statistics about generated heatmaps
    std::cout << "\n=== Heatmap Statistics ===\n";
    std::cout << "  Image size: " << img_width << "x" << img_height << " pixels\n";
    std::cout << "  Files written: 7\n";
    std::cout << "  Formats tested: BMP, TGA, PPM, PNG\n";
    std::cout << "  Colormaps tested: Viridis, Hot, Jet, Turbo, Plasma, Inferno\n";
  }

  // ============================================================================
  // Path Tracing Features (any-hit, self-intersection, packet traversal)
  // ============================================================================
  {
    std::cout << "\n=== Path Tracing Features ===\n";

    const uint32_t num_triangles = 10000;
    const uint32_t num_rays = 10000;

    RNG pt_rng(77);

    // Create random triangles
    std::vector<Triangle> triangles;
    triangles.reserve(num_triangles);
    for (uint32_t i = 0; i < num_triangles; i++) {
      Vec3 center = pt_rng.uniformVec3(-10.0f, 10.0f);
      Vec3 v0 = center + pt_rng.uniformVec3(-0.3f, 0.3f);
      Vec3 v1 = center + pt_rng.uniformVec3(-0.3f, 0.3f);
      Vec3 v2 = center + pt_rng.uniformVec3(-0.3f, 0.3f);
      triangles.push_back(Triangle(v0, v1, v2));
    }

    TriangleBVH bvh;
    bvh.build(triangles);

    // Create random rays
    std::vector<Ray> rays;
    rays.reserve(num_rays);
    for (uint32_t i = 0; i < num_rays; i++) {
      Vec3 origin = pt_rng.uniformVec3(-15.0f, 15.0f);
      Vec3 dir = pt_rng.uniformDirection();
      rays.push_back(Ray(origin, dir));
    }

    // 1. Any-hit traversal (shadow rays)
    std::cout << "  Any-hit traversal (shadow rays):\n";
    {
      uint32_t hits = 0;
      auto start = std::chrono::high_resolution_clock::now();
      for (const auto& ray : rays) {
        if (bvh.traverseAnyHit(ray)) {
          hits++;
        }
      }
      auto end = std::chrono::high_resolution_clock::now();
      double ms = std::chrono::duration<double, std::milli>(end - start).count();
      double mrps = (num_rays / 1e6) / (ms / 1000.0);
      std::cout << "    Time: " << std::fixed << std::setprecision(2) << ms << " ms";
      std::cout << " (" << std::setprecision(2) << mrps << " Mrays/s)";
      std::cout << " - " << hits << " hits\n";
    }

    // Compare with TraversalConfig::anyHit()
    {
      uint32_t hits = 0;
      auto start = std::chrono::high_resolution_clock::now();
      for (const auto& ray : rays) {
        float t, u, v;
        if (bvh.traverseWithConfig(ray, t, u, v, TraversalConfig::anyHit()) != kInvalidIndex) {
          hits++;
        }
      }
      auto end = std::chrono::high_resolution_clock::now();
      double ms = std::chrono::duration<double, std::milli>(end - start).count();
      double mrps = (num_rays / 1e6) / (ms / 1000.0);
      std::cout << "    Config:anyHit(): " << std::fixed << std::setprecision(2) << ms << " ms";
      std::cout << " (" << std::setprecision(2) << mrps << " Mrays/s)";
      std::cout << " - " << hits << " hits\n";
    }

    // 2. Self-intersection avoidance
    std::cout << "  Self-intersection avoidance:\n";
    {
      // First find hits, then trace secondary rays
      uint32_t secondary_hits = 0;
      uint32_t total_secondary = 0;
      auto start = std::chrono::high_resolution_clock::now();
      for (const auto& ray : rays) {
        float t, u, v;
        uint32_t hit_idx = bvh.traverse(ray, t, u, v);
        if (hit_idx != kInvalidIndex) {
          // Spawn secondary ray from hit point
          Vec3 hit_pos = ray.origin + ray.direction * t;
          Vec3 new_dir = pt_rng.uniformDirection();
          Ray secondary(hit_pos + new_dir * 0.001f, new_dir);

          // Trace with self-intersection avoidance
          float t2, u2, v2;
          uint32_t hit2 = bvh.traverseWithConfig(secondary, t2, u2, v2,
                                                  TraversalConfig::secondaryRay(hit_idx));
          if (hit2 != kInvalidIndex) {
            secondary_hits++;
          }
          total_secondary++;
        }
      }
      auto end = std::chrono::high_resolution_clock::now();
      double ms = std::chrono::duration<double, std::milli>(end - start).count();
      std::cout << "    Time: " << std::fixed << std::setprecision(2) << ms << " ms";
      std::cout << " - " << secondary_hits << "/" << total_secondary << " secondary hits\n";
    }

    // 3. Shadow ray with self-intersection avoidance
    std::cout << "  Shadow rays with exclude_prim_id:\n";
    {
      uint32_t shadow_tests = 0;
      uint32_t occluded = 0;
      Vec3 light_pos(0.0f, 20.0f, 0.0f);

      auto start = std::chrono::high_resolution_clock::now();
      for (const auto& ray : rays) {
        float t, u, v;
        uint32_t hit_idx = bvh.traverse(ray, t, u, v);
        if (hit_idx != kInvalidIndex) {
          Vec3 hit_pos = ray.origin + ray.direction * t;
          Vec3 to_light = light_pos - hit_pos;
          float light_dist = to_light.length();
          to_light = to_light * (1.0f / light_dist);

          Ray shadow_ray(hit_pos + to_light * 0.001f, to_light, kEpsilon, light_dist);
          if (bvh.traverseAnyHit(shadow_ray, hit_idx)) {
            occluded++;
          }
          shadow_tests++;
        }
      }
      auto end = std::chrono::high_resolution_clock::now();
      double ms = std::chrono::duration<double, std::milli>(end - start).count();
      std::cout << "    Time: " << std::fixed << std::setprecision(2) << ms << " ms";
      std::cout << " - " << occluded << "/" << shadow_tests << " occluded\n";
    }

    // 4. Packet traversal (4 rays)
    std::cout << "  Packet traversal (4 rays at a time):\n";
    {
      uint32_t total_hits = 0;
      auto start = std::chrono::high_resolution_clock::now();
      for (uint32_t i = 0; i + 4 <= num_rays; i += 4) {
        Ray4 packet = Ray4::fromRays(&rays[i], 4);
        HitResult4 results;
        bvh.traverse4(packet, results);
        for (int j = 0; j < 4; j++) {
          if (results.prim_id[j] != kInvalidIndex) {
            total_hits++;
          }
        }
      }
      auto end = std::chrono::high_resolution_clock::now();
      double ms = std::chrono::duration<double, std::milli>(end - start).count();
      double mrps = (num_rays / 1e6) / (ms / 1000.0);
      std::cout << "    Time: " << std::fixed << std::setprecision(2) << ms << " ms";
      std::cout << " (" << std::setprecision(2) << mrps << " Mrays/s)";
      std::cout << " - " << total_hits << " hits\n";
    }

    // Compare with single-ray traversal
    {
      uint32_t total_hits = 0;
      auto start = std::chrono::high_resolution_clock::now();
      for (const auto& ray : rays) {
        float t, u, v;
        if (bvh.traverse(ray, t, u, v) != kInvalidIndex) {
          total_hits++;
        }
      }
      auto end = std::chrono::high_resolution_clock::now();
      double ms = std::chrono::duration<double, std::milli>(end - start).count();
      double mrps = (num_rays / 1e6) / (ms / 1000.0);
      std::cout << "    Single-ray: " << std::fixed << std::setprecision(2) << ms << " ms";
      std::cout << " (" << std::setprecision(2) << mrps << " Mrays/s)";
      std::cout << " - " << total_hits << " hits\n";
    }

    // 5. Packet any-hit traversal (4 rays)
    std::cout << "  Packet any-hit (4 rays at a time):\n";
    {
      uint32_t total_hits = 0;
      auto start = std::chrono::high_resolution_clock::now();
      for (uint32_t i = 0; i + 4 <= num_rays; i += 4) {
        Ray4 packet = Ray4::fromRays(&rays[i], 4);
        uint32_t hit_mask = bvh.traverse4AnyHit(packet);
        for (int j = 0; j < 4; j++) {
          if (hit_mask & (1u << j)) {
            total_hits++;
          }
        }
      }
      auto end = std::chrono::high_resolution_clock::now();
      double ms = std::chrono::duration<double, std::milli>(end - start).count();
      double mrps = (num_rays / 1e6) / (ms / 1000.0);
      std::cout << "    Time: " << std::fixed << std::setprecision(2) << ms << " ms";
      std::cout << " (" << std::setprecision(2) << mrps << " Mrays/s)";
      std::cout << " - " << total_hits << " hits\n";
    }

    // 6. Packet traversal (8 rays)
    std::cout << "  Packet traversal (8 rays at a time):\n";
    {
      uint32_t total_hits = 0;
      auto start = std::chrono::high_resolution_clock::now();
      for (uint32_t i = 0; i + 8 <= num_rays; i += 8) {
        Ray8 packet = Ray8::fromRays(&rays[i], 8);
        HitResult8 results;
        bvh.traverse8(packet, results);
        for (int j = 0; j < 8; j++) {
          if (results.prim_id[j] != kInvalidIndex) {
            total_hits++;
          }
        }
      }
      auto end = std::chrono::high_resolution_clock::now();
      double ms = std::chrono::duration<double, std::milli>(end - start).count();
      double mrps = (num_rays / 1e6) / (ms / 1000.0);
      std::cout << "    Time: " << std::fixed << std::setprecision(2) << ms << " ms";
      std::cout << " (" << std::setprecision(2) << mrps << " Mrays/s)";
      std::cout << " - " << total_hits << " hits\n";
    }

    // 7. Coherent rays (camera-like pattern)
    std::cout << "  Coherent ray packets (camera rays):\n";
    {
      // Generate coherent camera rays
      std::vector<Ray> camera_rays;
      camera_rays.reserve(num_rays);
      Vec3 cam_pos(-20.0f, 0.0f, 0.0f);
      Vec3 cam_dir(1.0f, 0.0f, 0.0f);
      Vec3 cam_up(0.0f, 1.0f, 0.0f);
      Vec3 cam_right = cam_dir.cross(cam_up);
      float fov_scale = 0.5f;

      uint32_t img_w = 100, img_h = 100;
      for (uint32_t y = 0; y < img_h; y++) {
        for (uint32_t x = 0; x < img_w; x++) {
          float u = (2.0f * x / img_w - 1.0f) * fov_scale;
          float v = (2.0f * y / img_h - 1.0f) * fov_scale;
          Vec3 dir = cam_dir + cam_right * u + cam_up * v;
          dir = dir.normalize();
          camera_rays.push_back(Ray(cam_pos, dir));
        }
      }

      // Packet traversal
      uint32_t packet_hits = 0;
      auto start = std::chrono::high_resolution_clock::now();
      for (uint32_t i = 0; i + 4 <= camera_rays.size(); i += 4) {
        Ray4 packet = Ray4::fromRays(&camera_rays[i], 4);
        HitResult4 results;
        bvh.traverse4(packet, results);
        for (int j = 0; j < 4; j++) {
          if (results.prim_id[j] != kInvalidIndex) {
            packet_hits++;
          }
        }
      }
      auto end = std::chrono::high_resolution_clock::now();
      double packet_ms = std::chrono::duration<double, std::milli>(end - start).count();

      // Single-ray traversal
      uint32_t single_hits = 0;
      start = std::chrono::high_resolution_clock::now();
      for (const auto& ray : camera_rays) {
        float t, u, v;
        if (bvh.traverse(ray, t, u, v) != kInvalidIndex) {
          single_hits++;
        }
      }
      end = std::chrono::high_resolution_clock::now();
      double single_ms = std::chrono::duration<double, std::milli>(end - start).count();

      double speedup = single_ms / packet_ms;
      std::cout << "    Packet (4-ray): " << std::fixed << std::setprecision(2) << packet_ms << " ms";
      std::cout << " - " << packet_hits << " hits\n";
      std::cout << "    Single-ray:     " << std::setprecision(2) << single_ms << " ms";
      std::cout << " - " << single_hits << " hits\n";
      std::cout << "    Speedup: " << std::setprecision(2) << speedup << "x\n";
    }
  }

  std::cout << "\n============================================\n";
  std::cout << "Benchmark Complete\n";
  std::cout << "============================================\n";

  return 0;
}
