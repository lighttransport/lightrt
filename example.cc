// Copyright (c) 2026 Light Transport Entertainment, Inc.
// SPDX-License-Identifier: MIT
//
// example.cc - Example usage of LightRT BVH framework

#include "lightrt.hh"
#include <iostream>
#include <chrono>
#include <cmath>

using namespace lightrt;

// Simple scene generator
std::vector<AABB> createRandomScene(uint32_t num_boxes) {
  std::vector<AABB> boxes;
  boxes.reserve(num_boxes);
  
  // Use simple pseudo-random generation
  auto rand_float = [](float min_val, float max_val) -> float {
    static uint32_t seed = 12345;
    seed = seed * 1103515245 + 12345;
    float normalized = static_cast<float>(seed) / static_cast<float>(0xFFFFFFFF);
    return min_val + normalized * (max_val - min_val);
  };
  
  for (uint32_t i = 0; i < num_boxes; i++) {
    Vec3 center(rand_float(-10.0f, 10.0f),
                rand_float(-10.0f, 10.0f),
                rand_float(-10.0f, 10.0f));
    
    Vec3 size(rand_float(0.1f, 0.5f),
              rand_float(0.1f, 0.5f),
              rand_float(0.1f, 0.5f));
    
    AABB box(center - size * 0.5f, center + size * 0.5f);
    boxes.push_back(box);
  }
  
  return boxes;
}

// Test BVH construction and traversal
void testSingleLevelBVH() {
  std::cout << "\n=== Single-Level BVH Test ===\n";
  
  // Create scene with random boxes
  const uint32_t num_primitives = 10000;
  std::cout << "Creating scene with " << num_primitives << " primitives...\n";
  
  std::vector<AABB> primitives = createRandomScene(num_primitives);
  
  // Build BVH
  std::cout << "Building BVH...\n";
  auto start = std::chrono::high_resolution_clock::now();
  
  BVH bvh;
  BVHBuildConfig config;
  config.use_sah = true;
  config.use_binning = true;
  
  bool success = bvh.build(primitives, config);
  
  auto end = std::chrono::high_resolution_clock::now();
  auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
  
  if (success) {
    std::cout << "BVH built successfully in " << duration.count() << " ms\n";
    
    // Print statistics
    BVH::Stats stats = bvh.getStats();
    std::cout << "\nBVH Statistics:\n";
    std::cout << "  Total nodes: " << stats.num_nodes << "\n";
    std::cout << "  Leaf nodes: " << stats.num_leaves << "\n";
    std::cout << "  Max depth: " << stats.max_depth << "\n";
    std::cout << "  Average leaf size: " << stats.avg_leaf_size << "\n";
    std::cout << "  SAH cost: " << stats.sah_cost << "\n";
  } else {
    std::cout << "BVH build failed!\n";
    return;
  }
  
  // Test ray traversal
  std::cout << "\nTesting ray traversal...\n";
  
  Ray ray(Vec3(0.0f, 0.0f, -20.0f), Vec3(0.0f, 0.0f, 1.0f));
  
  // Scalar traversal
  start = std::chrono::high_resolution_clock::now();
  float hit_t = 0.0f;
  uint32_t hit_prim = bvh.traverse(ray, hit_t);
  end = std::chrono::high_resolution_clock::now();
  auto scalar_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start);
  
  if (hit_prim != kInvalidIndex) {
    std::cout << "  Scalar traversal: Hit primitive " << hit_prim << " at t=" << hit_t 
              << " (" << scalar_duration.count() << " ns)\n";
  } else {
    std::cout << "  Scalar traversal: No hit (" << scalar_duration.count() << " ns)\n";
  }
  
  // SIMD traversal
  start = std::chrono::high_resolution_clock::now();
  hit_t = 0.0f;
  hit_prim = bvh.traverseSIMD(ray, hit_t);
  end = std::chrono::high_resolution_clock::now();
  auto simd_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start);
  
  if (hit_prim != kInvalidIndex) {
    std::cout << "  SIMD traversal: Hit primitive " << hit_prim << " at t=" << hit_t 
              << " (" << simd_duration.count() << " ns)\n";
  } else {
    std::cout << "  SIMD traversal: No hit (" << simd_duration.count() << " ns)\n";
  }
  
  // Performance test with many rays
  const uint32_t num_rays = 10000;
  std::cout << "\nPerformance test with " << num_rays << " rays...\n";
  
  start = std::chrono::high_resolution_clock::now();
  uint32_t hits = 0;
  for (uint32_t i = 0; i < num_rays; i++) {
    float angle = static_cast<float>(i) / num_rays * 2.0f * 3.14159265f;
    Vec3 dir(std::sin(angle), std::cos(angle), 1.0f);
    dir = dir.normalize();
    
    Ray test_ray(Vec3(0.0f, 0.0f, -20.0f), dir);
    float t;
    uint32_t prim = bvh.traverseSIMD(test_ray, t);
    if (prim != kInvalidIndex) {
      hits++;
    }
  }
  end = std::chrono::high_resolution_clock::now();
  duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
  
  std::cout << "  Traced " << num_rays << " rays in " << duration.count() << " ms\n";
  std::cout << "  Hit rate: " << (hits * 100.0f / num_rays) << "%\n";
  std::cout << "  Rays/second: " << (num_rays * 1000.0f / duration.count()) << "\n";
}

// Test two-level BVH
void testTwoLevelBVH() {
  std::cout << "\n=== Two-Level BVH (TLAS/BLAS) Test ===\n";
  
  // Create multiple bottom-level BVHs
  const uint32_t num_blas = 3;
  const uint32_t prims_per_blas = 100;
  
  std::cout << "Creating " << num_blas << " BLAS with " << prims_per_blas << " primitives each...\n";
  
  std::vector<BLAS> blas_array;
  blas_array.resize(num_blas);
  
  for (uint32_t i = 0; i < num_blas; i++) {
    std::vector<AABB> primitives = createRandomScene(prims_per_blas);
    blas_array[i].build(primitives);
    std::cout << "  BLAS " << i << " built with " << primitives.size() << " primitives\n";
  }
  
  // Create instances of BLASes
  std::cout << "\nCreating TLAS with instances...\n";
  
  std::vector<BLASInstance> instances;
  
  // Instance 0: BLAS 0 at position (0, 0, 0)
  BLASInstance inst0;
  inst0.blas_id = 0;
  inst0.bounds = AABB(Vec3(-10.0f, -10.0f, -10.0f), Vec3(10.0f, 10.0f, 10.0f));
  instances.push_back(inst0);
  
  // Instance 1: BLAS 1 at position (15, 0, 0)
  BLASInstance inst1;
  inst1.blas_id = 1;
  inst1.transform[3] = 15.0f;  // Translation X
  inst1.bounds = AABB(Vec3(5.0f, -10.0f, -10.0f), Vec3(25.0f, 10.0f, 10.0f));
  instances.push_back(inst1);
  
  // Instance 2: BLAS 2 at position (-15, 0, 0)
  BLASInstance inst2;
  inst2.blas_id = 2;
  inst2.transform[3] = -15.0f;  // Translation X
  inst2.bounds = AABB(Vec3(-25.0f, -10.0f, -10.0f), Vec3(-5.0f, 10.0f, 10.0f));
  instances.push_back(inst2);
  
  // Build TLAS
  TLAS tlas;
  bool success = tlas.build(instances);
  
  if (success) {
    std::cout << "TLAS built successfully\n";
    
    // Test ray tracing
    std::cout << "\nTesting two-level ray tracing...\n";
    
    Ray ray(Vec3(0.0f, 0.0f, -20.0f), Vec3(0.0f, 0.0f, 1.0f));
    TLAS::TraceResult result = tlas.trace(ray, blas_array);
    
    if (result.instance_id != kInvalidIndex) {
      std::cout << "  Hit instance " << result.instance_id 
                << ", primitive " << result.primitive_id 
                << " at t=" << result.t << "\n";
    } else {
      std::cout << "  No hit\n";
    }
  } else {
    std::cout << "TLAS build failed!\n";
  }
}

// Test quantization
void testQuantization() {
  std::cout << "\n=== Quantization Test ===\n";
  
  AABB original(Vec3(-10.0f, -5.0f, -2.0f), Vec3(10.0f, 5.0f, 2.0f));
  Vec3 global_min(-20.0f, -20.0f, -20.0f);
  Vec3 global_max(20.0f, 20.0f, 20.0f);
  
  std::cout << "Original AABB:\n";
  std::cout << "  Min: (" << original.min.x << ", " << original.min.y << ", " << original.min.z << ")\n";
  std::cout << "  Max: (" << original.max.x << ", " << original.max.y << ", " << original.max.z << ")\n";
  
  QuantizedAABB quantized;
  quantized.quantize(original, global_min, global_max);
  
  std::cout << "\nQuantized (16-bit):\n";
  std::cout << "  Min: (" << quantized.min[0] << ", " << quantized.min[1] << ", " << quantized.min[2] << ")\n";
  std::cout << "  Max: (" << quantized.max[0] << ", " << quantized.max[1] << ", " << quantized.max[2] << ")\n";
  
  AABB dequantized = quantized.dequantize(global_min, global_max);
  
  std::cout << "\nDequantized:\n";
  std::cout << "  Min: (" << dequantized.min.x << ", " << dequantized.min.y << ", " << dequantized.min.z << ")\n";
  std::cout << "  Max: (" << dequantized.max.x << ", " << dequantized.max.y << ", " << dequantized.max.z << ")\n";
  
  Vec3 error_min = original.min - dequantized.min;
  Vec3 error_max = original.max - dequantized.max;
  
  std::cout << "\nQuantization error:\n";
  std::cout << "  Min: (" << error_min.x << ", " << error_min.y << ", " << error_min.z << ")\n";
  std::cout << "  Max: (" << error_max.x << ", " << error_max.y << ", " << error_max.z << ")\n";
}

// Test FP16
void testFP16() {
  std::cout << "\n=== FP16 Test ===\n";
  
#ifdef LIGHTRT_HAS_FP16
  std::cout << "FP16 support: ENABLED\n";
  
  float test_values[] = {0.0f, 1.0f, -1.0f, 0.5f, 3.14159f, 100.0f, 0.001f};
  
  std::cout << "\nFP32 -> FP16 -> FP32 conversion test:\n";
  for (float original : test_values) {
    uint16_t fp16 = floatToFP16(original);
    float converted = fp16ToFloat(fp16);
    float error = original - converted;
    
    std::cout << "  " << original << " -> 0x" << std::hex << fp16 << std::dec 
              << " -> " << converted << " (error: " << error << ")\n";
  }
#else
  std::cout << "FP16 support: NOT AVAILABLE\n";
  std::cout << "  FP16 requires F16C (x86) or FP16 vector arithmetic (ARM)\n";
#endif
}

// Display SIMD capabilities
void displayCapabilities() {
  std::cout << "\n=== LightRT Capabilities ===\n";
  
#ifdef LIGHTRT_HAS_SSE2
  std::cout << "  SSE2: YES\n";
#else
  std::cout << "  SSE2: NO\n";
#endif

#ifdef LIGHTRT_HAS_AVX
  std::cout << "  AVX: YES\n";
#else
  std::cout << "  AVX: NO\n";
#endif

#ifdef LIGHTRT_HAS_NEON
  std::cout << "  NEON: YES\n";
#else
  std::cout << "  NEON: NO\n";
#endif

#ifdef LIGHTRT_HAS_SVE
  std::cout << "  SVE: YES\n";
#else
  std::cout << "  SVE: NO\n";
#endif

#ifdef LIGHTRT_HAS_FP16
  std::cout << "  FP16: YES\n";
#else
  std::cout << "  FP16: NO\n";
#endif

  std::cout << "\n  C++ Standard: " << __cplusplus << "\n";
  
#ifdef __EXCEPTIONS
  std::cout << "  Exceptions: ENABLED\n";
#else
  std::cout << "  Exceptions: DISABLED\n";
#endif

#ifdef __GXX_RTTI
  std::cout << "  RTTI: ENABLED\n";
#else
  std::cout << "  RTTI: DISABLED\n";
#endif
}

void testBVH4() {
  std::cout << "\n=== Wide BVH (BVH4) Test ===\n";
  
  const uint32_t num_primitives = 10000;
  std::vector<AABB> primitives = createRandomScene(num_primitives);
  
  BVH binary_bvh;
  binary_bvh.build(primitives);
  
  BVH4Precision precisions[] = {
    BVH4Precision::FP32,
    BVH4Precision::FP16,
    BVH4Precision::Int16,
    BVH4Precision::Int8
  };
  const char* names[] = {"FP32", "FP16", "Int16", "Int8"};

  Ray ray(Vec3(0.0f, 0.0f, -20.0f), Vec3(0.0f, 0.0f, 1.0f).normalize());

  for (int i = 0; i < 4; i++) {
    std::cout << "\nTesting BVH4 with " << names[i] << " precision:\n";
    BVH4 bvh4;
    auto start = std::chrono::high_resolution_clock::now();
    bvh4.build(binary_bvh, primitives, precisions[i]);
    auto end = std::chrono::high_resolution_clock::now();
    auto build_duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
    
    std::cout << "  Build time (collapse + quantize): " << build_duration.count() << " ms\n";
    
    // Warmup
    float hit_t = 0.0f;
    bvh4.traverse(ray, hit_t);

    start = std::chrono::high_resolution_clock::now();
    hit_t = 0.0f;
    uint32_t hit_prim = bvh4.traverse(ray, hit_t);
    end = std::chrono::high_resolution_clock::now();
    auto traverse_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start);
    
    if (hit_prim != kInvalidIndex) {
      std::cout << "  Hit primitive " << hit_prim << " at t=" << hit_t 
                << " (" << traverse_duration.count() << " ns)\n";
    } else {
      std::cout << "  No hit (" << traverse_duration.count() << " ns)\n";
    }
  }
}

int main() {
  std::cout << "==============================================\n";
  std::cout << "LightRT - Lightweight Ray Tracing BVH Example\n";
  std::cout << "==============================================\n";
  
  displayCapabilities();
  testSingleLevelBVH();
  testTwoLevelBVH();
  testBVH4();
  testQuantization();
  testFP16();
  
  std::cout << "\n==============================================\n";
  std::cout << "All tests completed!\n";
  std::cout << "==============================================\n";
  
  return 0;
}
