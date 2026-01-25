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
// Main
// ============================================================================

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

  std::cout << "\n============================================\n";
  std::cout << "Benchmark Complete\n";
  std::cout << "============================================\n";

  return 0;
}
