// Copyright (c) 2026 Light Transport Entertainment, Inc.
// SPDX-License-Identifier: MIT
//
// lightrt.hh - Lightweight ray tracing and BVH kernel
//
// Features:
// - Two-level BVH construction and traversal
// - SIMD optimized (SSE2, AVX, NEON, SVE)
// - Quantization and FP16 support
// - C++17, no RTTI, no exceptions

#ifndef LIGHTRT_HH_
#define LIGHTRT_HH_

#include <cstdint>
#include <cstring>
#include <algorithm>
#include <vector>
#include <limits>
#include <cmath>

// SIMD detection
#if defined(__x86_64__) || defined(_M_X64) || defined(__i386__) || defined(_M_IX86)
  #if defined(__AVX__)
    #define LIGHTRT_HAS_AVX 1
    #include <immintrin.h>
  #elif defined(__SSE2__)
    #define LIGHTRT_HAS_SSE2 1
    #include <emmintrin.h>
  #endif
#endif

#if defined(__ARM_NEON) || defined(__ARM_NEON__)
  #define LIGHTRT_HAS_NEON 1
  #include <arm_neon.h>
#endif

#if defined(__ARM_FEATURE_SVE)
  #define LIGHTRT_HAS_SVE 1
  #include <arm_sve.h>
#endif

// FP16 support detection
#if defined(__F16C__) || defined(__ARM_FEATURE_FP16_VECTOR_ARITHMETIC)
  #define LIGHTRT_HAS_FP16 1
#endif

namespace lightrt {

// ============================================================================
// Constants and Configuration
// ============================================================================

constexpr float kInfinity = std::numeric_limits<float>::infinity();
constexpr float kEpsilon = 1e-6f;
constexpr uint32_t kInvalidIndex = 0xFFFFFFFF;

// ============================================================================
// Vector Math
// ============================================================================

struct alignas(16) Vec3 {
  float x, y, z;
  
  Vec3() noexcept : x(0.0f), y(0.0f), z(0.0f) {}
  Vec3(float x_, float y_, float z_) noexcept : x(x_), y(y_), z(z_) {}
  
  Vec3 operator+(const Vec3& v) const noexcept {
    return Vec3(x + v.x, y + v.y, z + v.z);
  }
  
  Vec3 operator-(const Vec3& v) const noexcept {
    return Vec3(x - v.x, y - v.y, z - v.z);
  }
  
  Vec3 operator*(float s) const noexcept {
    return Vec3(x * s, y * s, z * s);
  }
  
  Vec3 operator/(float s) const noexcept {
    float inv = 1.0f / s;
    return Vec3(x * inv, y * inv, z * inv);
  }
  
  float dot(const Vec3& v) const noexcept {
    return x * v.x + y * v.y + z * v.z;
  }
  
  Vec3 cross(const Vec3& v) const noexcept {
    return Vec3(y * v.z - z * v.y,
                z * v.x - x * v.z,
                x * v.y - y * v.x);
  }
  
  float length() const noexcept {
    return std::sqrt(x * x + y * y + z * z);
  }
  
  Vec3 normalize() const noexcept {
    float len = length();
    if (len > 0.0f) {
      return *this / len;
    }
    return *this;
  }
};

// ============================================================================
// Ray
// ============================================================================

struct alignas(16) Ray {
  Vec3 origin;
  Vec3 direction;
  float tmin;
  float tmax;
  
  Ray() noexcept : tmin(kEpsilon), tmax(kInfinity) {}
  
  Ray(const Vec3& o, const Vec3& d, float tmin_ = kEpsilon, float tmax_ = kInfinity) noexcept
    : origin(o), direction(d), tmin(tmin_), tmax(tmax_) {}
  
  Vec3 at(float t) const noexcept {
    return origin + direction * t;
  }
};

// ============================================================================
// AABB (Axis-Aligned Bounding Box)
// ============================================================================

struct alignas(16) AABB {
  Vec3 min;
  Vec3 max;
  
  AABB() noexcept {
    min = Vec3(kInfinity, kInfinity, kInfinity);
    max = Vec3(-kInfinity, -kInfinity, -kInfinity);
  }
  
  AABB(const Vec3& min_, const Vec3& max_) noexcept : min(min_), max(max_) {}
  
  void expand(const Vec3& p) noexcept {
    min.x = std::min(min.x, p.x);
    min.y = std::min(min.y, p.y);
    min.z = std::min(min.z, p.z);
    max.x = std::max(max.x, p.x);
    max.y = std::max(max.y, p.y);
    max.z = std::max(max.z, p.z);
  }
  
  void expand(const AABB& b) noexcept {
    min.x = std::min(min.x, b.min.x);
    min.y = std::min(min.y, b.min.y);
    min.z = std::min(min.z, b.min.z);
    max.x = std::max(max.x, b.max.x);
    max.y = std::max(max.y, b.max.y);
    max.z = std::max(max.z, b.max.z);
  }
  
  Vec3 center() const noexcept {
    return (min + max) * 0.5f;
  }
  
  Vec3 extents() const noexcept {
    return max - min;
  }
  
  float surfaceArea() const noexcept {
    Vec3 d = extents();
    return 2.0f * (d.x * d.y + d.y * d.z + d.z * d.x);
  }
  
  int longestAxis() const noexcept {
    Vec3 d = extents();
    if (d.x > d.y && d.x > d.z) return 0;
    if (d.y > d.z) return 1;
    return 2;
  }
  
  // Ray-AABB intersection test
  bool intersect(const Ray& ray, float& tmin_out, float& tmax_out) const noexcept;
  
  // SIMD optimized intersection
  bool intersectSIMD(const Ray& ray, float& tmin_out, float& tmax_out) const noexcept;
};

// ============================================================================
// Triangle
// ============================================================================

struct alignas(16) Triangle {
  Vec3 v0, v1, v2;

  Triangle() noexcept = default;
  Triangle(const Vec3& a, const Vec3& b, const Vec3& c) noexcept : v0(a), v1(b), v2(c) {}

  Vec3 centroid() const noexcept {
    return (v0 + v1 + v2) * (1.0f / 3.0f);
  }

  Vec3 normal() const noexcept {
    Vec3 e1 = v1 - v0;
    Vec3 e2 = v2 - v0;
    return e1.cross(e2).normalize();
  }

  AABB bounds() const noexcept;

  // Moller-Trumbore ray-triangle intersection
  // Returns true if hit, sets t, u, v (barycentric coordinates)
  bool intersect(const Ray& ray, float& t, float& u, float& v) const noexcept;
};

// ============================================================================
// Quantization Support
// ============================================================================

// Quantize float to 16-bit unsigned integer in range [min, max]
inline uint16_t quantizeFloat(float value, float min_val, float max_val) noexcept {
  float normalized = (value - min_val) / (max_val - min_val);
  normalized = std::max(0.0f, std::min(1.0f, normalized));
  return static_cast<uint16_t>(normalized * 65535.0f);
}

// Dequantize 16-bit unsigned integer to float in range [min, max]
inline float dequantizeFloat(uint16_t value, float min_val, float max_val) noexcept {
  float normalized = static_cast<float>(value) / 65535.0f;
  return min_val + normalized * (max_val - min_val);
}

// Quantized AABB using 16-bit integers
struct QuantizedAABB {
  uint16_t min[3];
  uint16_t max[3];
  
  void quantize(const AABB& aabb, const Vec3& global_min, const Vec3& global_max) noexcept {
    min[0] = quantizeFloat(aabb.min.x, global_min.x, global_max.x);
    min[1] = quantizeFloat(aabb.min.y, global_min.y, global_max.y);
    min[2] = quantizeFloat(aabb.min.z, global_min.z, global_max.z);
    max[0] = quantizeFloat(aabb.max.x, global_min.x, global_max.x);
    max[1] = quantizeFloat(aabb.max.y, global_min.y, global_max.y);
    max[2] = quantizeFloat(aabb.max.z, global_min.z, global_max.z);
  }
  
  AABB dequantize(const Vec3& global_min, const Vec3& global_max) const noexcept {
    AABB result;
    result.min.x = dequantizeFloat(min[0], global_min.x, global_max.x);
    result.min.y = dequantizeFloat(min[1], global_min.y, global_max.y);
    result.min.z = dequantizeFloat(min[2], global_min.z, global_max.z);
    result.max.x = dequantizeFloat(max[0], global_min.x, global_max.x);
    result.max.y = dequantizeFloat(max[1], global_min.y, global_max.y);
    result.max.z = dequantizeFloat(max[2], global_min.z, global_max.z);
    return result;
  }
};

// ============================================================================
// FP16 Support
// ============================================================================

#ifdef LIGHTRT_HAS_FP16

// Convert float to FP16
inline uint16_t floatToFP16(float value) noexcept {
#if defined(__F16C__)
  __m128 v = _mm_set_ss(value);
  __m128i h = _mm_cvtps_ph(v, 0);
  return static_cast<uint16_t>(_mm_extract_epi16(h, 0));
#else
  // Software fallback for ARM NEON
  uint32_t bits;
  std::memcpy(&bits, &value, sizeof(float));
  
  uint32_t sign = (bits >> 16) & 0x8000;
  int32_t exponent = ((bits >> 23) & 0xFF) - 127 + 15;
  uint32_t mantissa = bits & 0x7FFFFF;
  
  if (exponent <= 0) {
    // Denormal or zero
    return static_cast<uint16_t>(sign);
  } else if (exponent >= 31) {
    // Infinity or overflow
    return static_cast<uint16_t>(sign | 0x7C00);
  }
  
  return static_cast<uint16_t>(sign | (exponent << 10) | (mantissa >> 13));
#endif
}

// Convert FP16 to float
inline float fp16ToFloat(uint16_t value) noexcept {
#if defined(__F16C__)
  __m128i h = _mm_cvtsi32_si128(value);
  __m128 v = _mm_cvtph_ps(h);
  return _mm_cvtss_f32(v);
#else
  // Software fallback for ARM NEON
  uint32_t sign = (value & 0x8000) << 16;
  int32_t exponent = (value >> 10) & 0x1F;
  uint32_t mantissa = value & 0x3FF;
  
  if (exponent == 0) {
    // Denormal or zero
    if (mantissa == 0) {
      uint32_t bits = sign;
      float result;
      std::memcpy(&result, &bits, sizeof(float));
      return result;
    }
    // Denormal
    exponent = 1;
    while ((mantissa & 0x400) == 0) {
      mantissa <<= 1;
      exponent--;
    }
    mantissa &= 0x3FF;
  } else if (exponent == 31) {
    // Infinity or NaN
    uint32_t bits = sign | 0x7F800000 | (mantissa << 13);
    float result;
    std::memcpy(&result, &bits, sizeof(float));
    return result;
  }
  
  uint32_t bits = sign | ((exponent + 127 - 15) << 23) | (mantissa << 13);
  float result;
  std::memcpy(&result, &bits, sizeof(float));
  return result;
#endif
}

#endif // LIGHTRT_HAS_FP16

// ============================================================================
// BVH Node
// ============================================================================

struct BVHNode {
  AABB bounds;
  
  union {
    // Interior node
    struct {
      uint32_t left_child;   // Index to left child
      uint32_t right_child;  // Index to right child
    };
    
    // Leaf node
    struct {
      uint32_t prim_offset;  // Offset into primitive indices
      uint32_t prim_count;   // Number of primitives
    };
  };
  
  // Flags: bit 0 = is_leaf
  uint32_t flags;
  uint32_t padding; // Ensure alignment
  
  BVHNode() noexcept : left_child(0), right_child(0), flags(0), padding(0) {}
  
  bool isLeaf() const noexcept {
    return (flags & 0x1) != 0;
  }
  
  void setLeaf(uint32_t offset, uint32_t count) noexcept {
    prim_offset = offset;
    prim_count = count;
    flags |= 0x1;
  }
  
  void setInterior(uint32_t left, uint32_t right) noexcept {
    left_child = left;
    right_child = right;
    flags &= ~0x1;
  }
};

// ============================================================================
// Build Configuration
// ============================================================================

struct BVHBuildConfig {
  uint32_t max_leaf_size;      // Maximum primitives per leaf
  uint32_t min_leaf_size;      // Minimum primitives to create leaf
  float traversal_cost;        // Cost of traversing interior node
  float intersection_cost;     // Cost of primitive intersection
  bool use_sah;                // Use Surface Area Heuristic
  bool use_binning;            // Use binned SAH for large nodes
  uint32_t num_bins;           // Number of bins for binned SAH
  bool force_max_leaf_size;    // Always enforce max_leaf_size (ignore SAH cost)

  BVHBuildConfig() noexcept
    : max_leaf_size(4)
    , min_leaf_size(1)
    , traversal_cost(1.0f)
    , intersection_cost(1.0f)
    , use_sah(true)
    , use_binning(true)
    , num_bins(16)
    , force_max_leaf_size(false) {}
};

// ============================================================================
// BVH Builder
// ============================================================================

class BVH {
public:
  BVH() noexcept = default;
  ~BVH() noexcept = default;
  
  // Build BVH from primitives (AABBs)
  // prim_aabbs: Bounding boxes of primitives
  // Returns true on success
  bool build(const std::vector<AABB>& prim_aabbs, const BVHBuildConfig& config = BVHBuildConfig()) noexcept;
  
  // Traverse BVH and find closest intersection
  // Returns primitive index or kInvalidIndex if no hit
  uint32_t traverse(const Ray& ray, float& hit_t) const noexcept;
  
  // Traverse BVH using SIMD optimizations
  uint32_t traverseSIMD(const Ray& ray, float& hit_t) const noexcept;
  
  // Get BVH statistics
  struct Stats {
    uint32_t num_nodes;
    uint32_t num_leaves;
    uint32_t max_depth;
    float avg_leaf_size;
    float sah_cost;
  };
  
  Stats getStats() const noexcept;
  
  // Access to nodes (for serialization, etc.)
  const std::vector<BVHNode>& getNodes() const noexcept { return nodes_; }
  const std::vector<uint32_t>& getPrimitiveIndices() const noexcept { return prim_indices_; }
  
private:
  std::vector<BVHNode> nodes_;
  std::vector<uint32_t> prim_indices_;
  std::vector<AABB> prim_aabbs_;
  BVHBuildConfig config_;
  
  // Recursive build
  uint32_t buildRecursive(
    uint32_t* indices,
    uint32_t num_prims,
    uint32_t depth) noexcept;
  
  // Split methods
  struct SplitResult {
    int axis;
    float pos;
    float cost;
  };
  
  SplitResult findBestSplit(
    const uint32_t* indices,
    uint32_t num_prims,
    const AABB& centroid_bounds,
    float parent_area) noexcept;

  SplitResult findBestSplitBinned(
    const uint32_t* indices,
    uint32_t num_prims,
    const AABB& centroid_bounds,
    float parent_area) noexcept;
};

// ============================================================================
// Two-Level BVH (TLAS + BLAS)
// ============================================================================

// Bottom-Level Acceleration Structure
struct BLAS {
  BVH bvh;
  std::vector<AABB> primitives;  // Primitive AABBs
  
  bool build(const std::vector<AABB>& prim_aabbs, const BVHBuildConfig& config = BVHBuildConfig()) noexcept {
    primitives = prim_aabbs;
    return bvh.build(prim_aabbs, config);
  }
};

// Instance of a BLAS with transformation
struct BLASInstance {
  uint32_t blas_id;        // Index into BLAS array
  float transform[12];     // 3x4 transformation matrix (row-major)
  float inv_transform[12]; // Inverse transformation
  AABB bounds;             // Transformed world-space bounds
  
  BLASInstance() noexcept : blas_id(kInvalidIndex) {
    // Identity transform
    std::memset(transform, 0, sizeof(transform));
    std::memset(inv_transform, 0, sizeof(inv_transform));
    transform[0] = transform[5] = transform[10] = 1.0f;
    inv_transform[0] = inv_transform[5] = inv_transform[10] = 1.0f;
  }
  
  // Transform point from world to local space
  Vec3 worldToLocal(const Vec3& p) const noexcept {
    return Vec3(
      inv_transform[0] * p.x + inv_transform[1] * p.y + inv_transform[2] * p.z + inv_transform[3],
      inv_transform[4] * p.x + inv_transform[5] * p.y + inv_transform[6] * p.z + inv_transform[7],
      inv_transform[8] * p.x + inv_transform[9] * p.y + inv_transform[10] * p.z + inv_transform[11]
    );
  }
  
  // Transform direction from world to local space
  Vec3 worldToLocalDir(const Vec3& d) const noexcept {
    return Vec3(
      inv_transform[0] * d.x + inv_transform[1] * d.y + inv_transform[2] * d.z,
      inv_transform[4] * d.x + inv_transform[5] * d.y + inv_transform[6] * d.z,
      inv_transform[8] * d.x + inv_transform[9] * d.y + inv_transform[10] * d.z
    );
  }
};

// Top-Level Acceleration Structure
class TLAS {
public:
  TLAS() noexcept = default;
  ~TLAS() noexcept = default;
  
  // Build TLAS from BLAS instances
  bool build(const std::vector<BLASInstance>& instances, const BVHBuildConfig& config = BVHBuildConfig()) noexcept;
  
  // Traverse TLAS and find closest intersection
  // Returns instance index and primitive index, or kInvalidIndex if no hit
  struct TraceResult {
    uint32_t instance_id;
    uint32_t primitive_id;
    float t;
  };
  
  TraceResult trace(const Ray& ray, const std::vector<BLAS>& blas_array) const noexcept;
  
  const BVH& getBVH() const noexcept { return bvh_; }
  const std::vector<BLASInstance>& getInstances() const noexcept { return instances_; }
  
private:
  BVH bvh_;
  std::vector<BLASInstance> instances_;
};

// ============================================================================
// Triangle BVH - BVH over triangles with proper ray-triangle intersection
// ============================================================================

class TriangleBVH {
public:
  TriangleBVH() noexcept = default;
  ~TriangleBVH() noexcept = default;

  // Build BVH from triangles
  bool build(const std::vector<Triangle>& triangles, const BVHBuildConfig& config = BVHBuildConfig()) noexcept;

  // Traverse and find closest triangle intersection
  // Returns triangle index or kInvalidIndex if no hit
  // hit_t: distance to hit, hit_u/hit_v: barycentric coordinates
  uint32_t traverse(const Ray& ray, float& hit_t, float& hit_u, float& hit_v) const noexcept;

  // Get statistics
  BVH::Stats getStats() const noexcept { return bvh_.getStats(); }

  // Access internals
  const BVH& getBVH() const noexcept { return bvh_; }
  const std::vector<Triangle>& getTriangles() const noexcept { return triangles_; }

private:
  BVH bvh_;
  std::vector<Triangle> triangles_;
};

} // namespace lightrt

#endif // LIGHTRT_HH_
