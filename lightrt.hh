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
// Quad (Bilinear Patch)
// ============================================================================

struct alignas(16) Quad {
  Vec3 v0, v1, v2, v3;  // Counter-clockwise: v0-v1-v2-v3

  Quad() noexcept = default;
  Quad(const Vec3& a, const Vec3& b, const Vec3& c, const Vec3& d) noexcept
    : v0(a), v1(b), v2(c), v3(d) {}

  Vec3 centroid() const noexcept {
    return (v0 + v1 + v2 + v3) * 0.25f;
  }

  AABB bounds() const noexcept;

  // Ray-quad intersection (bilinear patch)
  // Returns true if hit, sets t, u, v (parametric coordinates)
  bool intersect(const Ray& ray, float& t, float& u, float& v) const noexcept;
};

// ============================================================================
// NGon (Convex Polygon with N vertices)
// ============================================================================

struct NGon {
  std::vector<Vec3> vertices;  // Counter-clockwise vertices
  Vec3 normal;                 // Precomputed normal (for planar ngons)

  NGon() noexcept = default;
  NGon(const std::vector<Vec3>& verts) noexcept;

  void computeNormal() noexcept;
  Vec3 centroid() const noexcept;
  AABB bounds() const noexcept;

  // Ray-ngon intersection (assumes convex, planar polygon)
  bool intersect(const Ray& ray, float& t) const noexcept;
};

// ============================================================================
// Sphere
// ============================================================================

struct alignas(16) Sphere {
  Vec3 center;
  float radius;

  Sphere() noexcept : radius(1.0f) {}
  Sphere(const Vec3& c, float r) noexcept : center(c), radius(r) {}

  Vec3 centroid() const noexcept { return center; }
  AABB bounds() const noexcept;

  // Ray-sphere intersection
  // Returns true if hit, sets t (nearest hit), and optionally normal at hit
  bool intersect(const Ray& ray, float& t) const noexcept;
  bool intersect(const Ray& ray, float& t, Vec3& hit_normal) const noexcept;
};

// ============================================================================
// Disk
// ============================================================================

struct alignas(16) Disk {
  Vec3 center;
  Vec3 normal;
  float radius;

  Disk() noexcept : normal(0, 1, 0), radius(1.0f) {}
  Disk(const Vec3& c, const Vec3& n, float r) noexcept
    : center(c), normal(n.normalize()), radius(r) {}

  Vec3 centroid() const noexcept { return center; }
  AABB bounds() const noexcept;

  // Ray-disk intersection
  bool intersect(const Ray& ray, float& t) const noexcept;
};

// ============================================================================
// OrientedDisk (Screen-oriented / Billboard)
// Always faces toward a reference point (typically camera/ray origin)
// ============================================================================

struct alignas(16) OrientedDisk {
  Vec3 center;
  float radius;

  OrientedDisk() noexcept : radius(1.0f) {}
  OrientedDisk(const Vec3& c, float r) noexcept : center(c), radius(r) {}

  Vec3 centroid() const noexcept { return center; }
  AABB bounds() const noexcept;

  // Ray-oriented disk intersection (disk faces ray origin)
  bool intersect(const Ray& ray, float& t) const noexcept;
};

// ============================================================================
// Curve Types
// ============================================================================

enum class CurveType : uint8_t {
  Linear,       // Linear segments (fast, simple)
  Bezier,       // Cubic Bezier (smooth, uses Phantom algorithm)
  CatmullRom,   // Catmull-Rom spline
  BSpline       // B-spline
};

// ============================================================================
// Curve (Hair/Fiber primitive)
// Implements Phantom Ray-Hair Intersector for robust Bezier curves
// Reference: Reshetov & Luebke, HPG 2018
// ============================================================================

struct Curve {
  std::vector<Vec3> control_points;  // Control points
  std::vector<float> radii;          // Radius at each control point (for varying width)
  CurveType type;

  Curve() noexcept : type(CurveType::Bezier) {}
  Curve(const std::vector<Vec3>& points, float radius, CurveType t = CurveType::Bezier) noexcept;
  Curve(const std::vector<Vec3>& points, const std::vector<float>& r, CurveType t = CurveType::Bezier) noexcept;

  Vec3 centroid() const noexcept;
  AABB bounds() const noexcept;

  // Evaluate curve position at parameter t [0,1]
  Vec3 evaluate(float t) const noexcept;

  // Evaluate curve tangent at parameter t
  Vec3 evaluateTangent(float t) const noexcept;

  // Interpolate radius at parameter t
  float radiusAt(float t) const noexcept;

  // Ray-curve intersection
  // Returns true if hit, sets t_hit (ray parameter), u_hit (curve parameter)
  bool intersect(const Ray& ray, float& t_hit, float& u_hit) const noexcept;

private:
  // Phantom Ray-Hair algorithm for Bezier curves
  bool intersectPhantom(const Ray& ray, float& t_hit, float& u_hit) const noexcept;

  // Simple linear segment intersection (fast approximation)
  bool intersectLinear(const Ray& ray, float& t_hit, float& u_hit) const noexcept;
};

// ============================================================================
// Custom Geometry (AABB + Callback)
// For user-defined intersection routines
// ============================================================================

// Intersection callback function type
// Parameters: ray, user_data, out_t, out_u, out_v
// Returns: true if hit
using IntersectCallback = bool (*)(const Ray&, void*, float&, float&, float&);

// Bounds callback function type (optional, for dynamic bounds)
// Parameters: user_data
// Returns: AABB
using BoundsCallback = AABB (*)(void*);

struct CustomGeometry {
  AABB bounds_cache;           // Cached/static bounds
  void* user_data;             // User-provided data pointer
  IntersectCallback intersect_fn;
  BoundsCallback bounds_fn;    // Optional: for dynamic bounds

  CustomGeometry() noexcept
    : user_data(nullptr), intersect_fn(nullptr), bounds_fn(nullptr) {}

  CustomGeometry(const AABB& b, IntersectCallback fn, void* data = nullptr) noexcept
    : bounds_cache(b), user_data(data), intersect_fn(fn), bounds_fn(nullptr) {}

  Vec3 centroid() const noexcept { return bounds_cache.center(); }

  AABB bounds() const noexcept {
    if (bounds_fn) {
      return bounds_fn(user_data);
    }
    return bounds_cache;
  }

  bool intersect(const Ray& ray, float& t, float& u, float& v) const noexcept {
    if (intersect_fn) {
      return intersect_fn(ray, user_data, t, u, v);
    }
    return false;
  }
};

// ============================================================================
// Quantized Triangle (Low Memory)
// Uses 16-bit quantized coordinates relative to a global bounding box
// Memory: 18 bytes vs 36 bytes for full-precision Triangle
// ============================================================================

struct QuantizedTriangle {
  uint16_t v0[3];  // Quantized vertex 0
  uint16_t v1[3];  // Quantized vertex 1
  uint16_t v2[3];  // Quantized vertex 2

  QuantizedTriangle() noexcept = default;

  // Quantize from full-precision triangle
  void quantize(const Triangle& tri, const Vec3& global_min, const Vec3& global_max) noexcept;

  // Dequantize to full-precision triangle
  Triangle dequantize(const Vec3& global_min, const Vec3& global_max) const noexcept;

  // Direct intersection (dequantizes internally)
  bool intersect(const Ray& ray, const Vec3& global_min, const Vec3& global_max,
                 float& t, float& u, float& v) const noexcept;
};

// ============================================================================
// Gaussian Splat Primitive
// For 3D Gaussian Splatting (3DGS) ray tracing
// Reference: "3D Gaussian Ray Tracing" (SIGGRAPH Asia 2024)
// ============================================================================

// Spherical Harmonics degree for color (0=DC only, 1=4 coeffs, 2=9, 3=16)
enum class SHDegree : uint8_t {
  DC = 0,      // 1 coefficient per channel (3 total)
  Degree1 = 1, // 4 coefficients per channel (12 total)
  Degree2 = 2, // 9 coefficients per channel (27 total)
  Degree3 = 3  // 16 coefficients per channel (48 total)
};

struct GaussianSplat {
  Vec3 position;           // Center position
  Vec3 scale;              // Scale along each axis (before rotation)
  float rotation[4];       // Quaternion (w, x, y, z)
  float opacity;           // Opacity [0, 1]
  float sh_coeffs[48];     // Spherical harmonics (up to degree 3)
  SHDegree sh_degree;      // Active SH degree

  GaussianSplat() noexcept;

  // Compute covariance matrix from scale and rotation
  void getCovariance(float cov[6]) const noexcept;  // Upper triangle: xx, xy, xz, yy, yz, zz

  // Compute world-space 3x3 covariance matrix
  void getCovarianceMatrix(float mat[9]) const noexcept;

  Vec3 centroid() const noexcept { return position; }

  // Conservative AABB bounds (3-sigma ellipsoid)
  AABB bounds() const noexcept;

  // Ray-Gaussian intersection (ellipsoid approximation)
  // Returns true if ray intersects the 3-sigma confidence ellipsoid
  // t_hit: ray parameter at intersection
  // density: Gaussian density at hit point (for alpha compositing)
  bool intersect(const Ray& ray, float& t_hit, float& density) const noexcept;

  // Evaluate Gaussian density at a point
  float evaluate(const Vec3& point) const noexcept;

  // Get color from SH coefficients for a given view direction
  Vec3 getColor(const Vec3& view_dir) const noexcept;
};

// ============================================================================
// Quantized Gaussian Splat (Low Memory)
// Quantized version for large-scale scenes
// Memory: ~32 bytes vs ~220 bytes for full GaussianSplat
// ============================================================================

struct QuantizedGaussianSplat {
  uint16_t position[3];    // Quantized position (relative to scene bounds)
  uint16_t scale[3];       // Quantized log-scale
  int8_t rotation[4];      // Quantized quaternion (normalized, -127 to 127)
  uint8_t opacity;         // Quantized opacity (0-255)
  uint8_t color_dc[3];     // DC color (RGB, 0-255)
  // Optional: additional SH stored separately in SoA layout

  QuantizedGaussianSplat() noexcept = default;

  // Quantize from full-precision Gaussian
  void quantize(const GaussianSplat& gs, const Vec3& pos_min, const Vec3& pos_max,
                float scale_min, float scale_max) noexcept;

  // Dequantize to full-precision Gaussian
  GaussianSplat dequantize(const Vec3& pos_min, const Vec3& pos_max,
                           float scale_min, float scale_max) const noexcept;

  // Direct intersection (dequantizes internally for accuracy)
  bool intersect(const Ray& ray, const Vec3& pos_min, const Vec3& pos_max,
                 float scale_min, float scale_max,
                 float& t_hit, float& density) const noexcept;
};

// ============================================================================
// Primitive Variant (Type-safe union for mixed primitive BVH)
// ============================================================================

enum class PrimitiveType : uint8_t {
  Triangle,
  Quad,
  Sphere,
  Disk,
  OrientedDisk,
  Curve,
  Custom,
  QuantizedTriangle,
  GaussianSplat,
  QuantizedGaussianSplat
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
// SBVH Build Configuration
// ============================================================================

struct SBVHBuildConfig {
  uint32_t max_leaf_size;        // Maximum primitives per leaf
  float traversal_cost;          // Cost of traversing interior node
  float intersection_cost;       // Cost of primitive intersection
  uint32_t num_spatial_bins;     // Number of bins for spatial splits
  uint32_t num_object_bins;      // Number of bins for object splits
  float alpha;                   // Spatial split threshold (overlap ratio)
  float max_split_factor;        // Max reference count increase (e.g., 1.5 = 50% more)

  SBVHBuildConfig() noexcept
    : max_leaf_size(4)
    , traversal_cost(1.0f)
    , intersection_cost(1.0f)
    , num_spatial_bins(256)
    , num_object_bins(32)
    , alpha(1e-5f)
    , max_split_factor(1.5f) {}
};

// ============================================================================
// Traversal Configuration (for limiting primitive tests)
// ============================================================================

struct TraversalConfig {
  uint32_t max_prim_tests;       // Maximum primitive intersection tests (0 = unlimited)
  bool use_mailboxing;           // Use mailboxing to avoid duplicate tests (for SBVH)
  bool early_termination;        // Stop on first hit (any-hit query)

  TraversalConfig() noexcept
    : max_prim_tests(0)
    , use_mailboxing(false)
    , early_termination(false) {}

  // Preset for fast approximate traversal
  static TraversalConfig fast(uint32_t max_tests = 64) noexcept {
    TraversalConfig cfg;
    cfg.max_prim_tests = max_tests;
    cfg.use_mailboxing = true;
    return cfg;
  }

  // Preset for any-hit (shadow rays)
  static TraversalConfig anyHit() noexcept {
    TraversalConfig cfg;
    cfg.early_termination = true;
    return cfg;
  }
};

// Traversal statistics
struct TraversalStats {
  uint32_t nodes_visited;
  uint32_t prims_tested;
  uint32_t prims_hit;
  bool terminated_early;         // Hit max_prim_tests limit

  TraversalStats() noexcept
    : nodes_visited(0)
    , prims_tested(0)
    , prims_hit(0)
    , terminated_early(false) {}
};

// Simple mailbox using bitset for small primitive counts, or hash set for large
class Mailbox {
public:
  explicit Mailbox(uint32_t num_prims) noexcept : num_prims_(num_prims) {
    if (num_prims <= kBitsetThreshold) {
      bitset_.resize((num_prims + 63) / 64, 0);
    } else {
      // Use simple hash table for large primitive counts
      hash_table_.resize(std::max(num_prims / 4, 256u), kInvalidIndex);
    }
  }

  // Returns true if primitive was already tested, marks it as tested
  bool testAndMark(uint32_t prim_id) noexcept {
    if (num_prims_ <= kBitsetThreshold) {
      uint32_t word = prim_id / 64;
      uint64_t bit = 1ULL << (prim_id % 64);
      if (bitset_[word] & bit) {
        return true;  // Already tested
      }
      bitset_[word] |= bit;
      return false;
    } else {
      // Linear probing hash table
      uint32_t idx = prim_id % hash_table_.size();
      for (uint32_t i = 0; i < hash_table_.size(); i++) {
        uint32_t probe = (idx + i) % hash_table_.size();
        if (hash_table_[probe] == prim_id) {
          return true;  // Already tested
        }
        if (hash_table_[probe] == kInvalidIndex) {
          hash_table_[probe] = prim_id;
          return false;
        }
      }
      return false;  // Table full, test anyway
    }
  }

  void clear() noexcept {
    if (num_prims_ <= kBitsetThreshold) {
      std::fill(bitset_.begin(), bitset_.end(), 0);
    } else {
      std::fill(hash_table_.begin(), hash_table_.end(), kInvalidIndex);
    }
  }

private:
  static constexpr uint32_t kBitsetThreshold = 65536;
  uint32_t num_prims_;
  std::vector<uint64_t> bitset_;
  std::vector<uint32_t> hash_table_;
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

  // Traverse with configuration (max prim tests, early termination)
  uint32_t traverseWithConfig(const Ray& ray, float& hit_t, float& hit_u, float& hit_v,
                              const TraversalConfig& config,
                              TraversalStats* stats = nullptr) const noexcept;

  // Get statistics
  BVH::Stats getStats() const noexcept { return bvh_.getStats(); }
  uint32_t getNumPrimitives() const noexcept { return static_cast<uint32_t>(triangles_.size()); }

  // Access internals
  const BVH& getBVH() const noexcept { return bvh_; }
  const std::vector<Triangle>& getTriangles() const noexcept { return triangles_; }

private:
  BVH bvh_;
  std::vector<Triangle> triangles_;
};

// ============================================================================
// SBVH (Split BVH) - BVH with Spatial Splits
// Reference: "Spatial Splits in Bounding Volume Hierarchies" (Stich et al., HPG 2009)
// ============================================================================

class SBVH {
public:
  // Primitive reference with clipped bounds
  struct PrimRef {
    uint32_t prim_id;    // Original primitive index
    AABB bounds;         // Clipped bounding box (may be smaller than original)

    PrimRef() noexcept : prim_id(kInvalidIndex) {}
    PrimRef(uint32_t id, const AABB& b) noexcept : prim_id(id), bounds(b) {}
  };

  SBVH() noexcept = default;
  ~SBVH() noexcept = default;

  // Build SBVH from triangles
  bool build(const std::vector<Triangle>& triangles,
             const SBVHBuildConfig& config = SBVHBuildConfig()) noexcept;

  // Traverse and find closest triangle intersection
  uint32_t traverse(const Ray& ray, float& hit_t, float& hit_u, float& hit_v) const noexcept;

  // Traverse with configuration (max prim tests, mailboxing, early termination)
  // Mailboxing avoids testing same primitive multiple times (important for SBVH)
  uint32_t traverseWithConfig(const Ray& ray, float& hit_t, float& hit_u, float& hit_v,
                              const TraversalConfig& config,
                              TraversalStats* stats = nullptr) const noexcept;

  // Get statistics
  struct Stats {
    uint32_t num_nodes;
    uint32_t num_leaves;
    uint32_t max_depth;
    float avg_leaf_size;
    float sah_cost;
    uint32_t num_references;     // Total references (>= num_primitives due to splits)
    uint32_t num_primitives;     // Original primitive count
    float split_ratio;           // num_references / num_primitives
  };

  Stats getStats() const noexcept;
  uint32_t getNumPrimitives() const noexcept { return static_cast<uint32_t>(triangles_.size()); }

  // Access internals
  const std::vector<BVHNode>& getNodes() const noexcept { return nodes_; }
  const std::vector<PrimRef>& getReferences() const noexcept { return refs_; }
  const std::vector<Triangle>& getTriangles() const noexcept { return triangles_; }

private:
  std::vector<BVHNode> nodes_;
  std::vector<PrimRef> refs_;          // Leaf references (may have duplicates)
  std::vector<Triangle> triangles_;    // Original triangles
  SBVHBuildConfig config_;
  AABB scene_bounds_;

  // Split result types
  enum class SplitType { Object, Spatial };

  struct SplitResult {
    SplitType type;
    int axis;
    float pos;
    float cost;
    AABB left_bounds;
    AABB right_bounds;
    uint32_t left_count;
    uint32_t right_count;
  };

  // Spatial bin for binned split finding
  struct SpatialBin {
    AABB bounds;
    uint32_t enter;   // Primitives entering this bin
    uint32_t exit;    // Primitives exiting this bin

    SpatialBin() noexcept : enter(0), exit(0) {}
  };

  // Object bin
  struct ObjectBin {
    AABB bounds;
    uint32_t count;

    ObjectBin() noexcept : count(0) {}
  };

  // Build methods
  uint32_t buildRecursive(std::vector<PrimRef>& refs, uint32_t depth) noexcept;

  // Split finding
  SplitResult findObjectSplit(const std::vector<PrimRef>& refs,
                              const AABB& node_bounds,
                              const AABB& centroid_bounds) noexcept;

  SplitResult findSpatialSplit(const std::vector<PrimRef>& refs,
                               const AABB& node_bounds) noexcept;

  // Perform the split
  void performObjectSplit(std::vector<PrimRef>& refs,
                          const SplitResult& split,
                          std::vector<PrimRef>& left_refs,
                          std::vector<PrimRef>& right_refs) noexcept;

  void performSpatialSplit(std::vector<PrimRef>& refs,
                           const SplitResult& split,
                           std::vector<PrimRef>& left_refs,
                           std::vector<PrimRef>& right_refs) noexcept;

  // Clip triangle AABB to a half-space
  AABB clipTriangleToPlane(const Triangle& tri, int axis, float pos, bool left) const noexcept;

  // Compute overlap between two AABBs
  float computeOverlap(const AABB& a, const AABB& b) const noexcept;
};

// ============================================================================
// SBVH for generic primitives (AABB-based)
// ============================================================================

class SBVHGeneric {
public:
  // Primitive reference with clipped bounds
  struct PrimRef {
    uint32_t prim_id;
    AABB bounds;

    PrimRef() noexcept : prim_id(kInvalidIndex) {}
    PrimRef(uint32_t id, const AABB& b) noexcept : prim_id(id), bounds(b) {}
  };

  SBVHGeneric() noexcept = default;
  ~SBVHGeneric() noexcept = default;

  // Build SBVH from primitive AABBs
  // prim_aabbs: Bounding boxes of primitives (used for both bounds and spatial clipping)
  bool build(const std::vector<AABB>& prim_aabbs,
             const SBVHBuildConfig& config = SBVHBuildConfig()) noexcept;

  // Traverse and find closest intersection (returns primitive index)
  uint32_t traverse(const Ray& ray, float& hit_t) const noexcept;

  // Get statistics
  struct Stats {
    uint32_t num_nodes;
    uint32_t num_leaves;
    uint32_t max_depth;
    float avg_leaf_size;
    float sah_cost;
    uint32_t num_references;
    uint32_t num_primitives;
    float split_ratio;
  };

  Stats getStats() const noexcept;

  const std::vector<BVHNode>& getNodes() const noexcept { return nodes_; }
  const std::vector<PrimRef>& getReferences() const noexcept { return refs_; }

private:
  std::vector<BVHNode> nodes_;
  std::vector<PrimRef> refs_;
  std::vector<AABB> prim_aabbs_;
  SBVHBuildConfig config_;
  AABB scene_bounds_;

  enum class SplitType { Object, Spatial };

  struct SplitResult {
    SplitType type;
    int axis;
    float pos;
    float cost;
    AABB left_bounds;
    AABB right_bounds;
    uint32_t left_count;
    uint32_t right_count;
  };

  struct SpatialBin {
    AABB bounds;
    uint32_t enter;
    uint32_t exit;
    SpatialBin() noexcept : enter(0), exit(0) {}
  };

  struct ObjectBin {
    AABB bounds;
    uint32_t count;
    ObjectBin() noexcept : count(0) {}
  };

  uint32_t buildRecursive(std::vector<PrimRef>& refs, uint32_t depth) noexcept;

  SplitResult findObjectSplit(const std::vector<PrimRef>& refs,
                              const AABB& node_bounds,
                              const AABB& centroid_bounds) noexcept;

  SplitResult findSpatialSplit(const std::vector<PrimRef>& refs,
                               const AABB& node_bounds) noexcept;

  void performObjectSplit(std::vector<PrimRef>& refs,
                          const SplitResult& split,
                          std::vector<PrimRef>& left_refs,
                          std::vector<PrimRef>& right_refs) noexcept;

  void performSpatialSplit(std::vector<PrimRef>& refs,
                           const SplitResult& split,
                           std::vector<PrimRef>& left_refs,
                           std::vector<PrimRef>& right_refs) noexcept;

  AABB clipAABBToPlane(const AABB& aabb, int axis, float pos, bool left) const noexcept;
  float computeOverlap(const AABB& a, const AABB& b) const noexcept;
};

// ============================================================================
// Auto-Tuning for BVH Construction and Traversal
// Samples M primitives from N input, measures costs, selects best algorithms
// ============================================================================

// BVH build method
enum class BVHBuildMethod : uint8_t {
  TriangleBVH,    // Standard BVH with object splits only
  SBVH            // Split BVH with spatial splits
};

// Auto-tune configuration
struct AutoTuneConfig {
  uint32_t sample_prim_count;      // Number of primitives to sample (M), 0 = auto (sqrt(N))
  uint32_t sample_ray_count;       // Number of rays to test for traversal
  uint32_t warmup_iterations;      // Warmup iterations before timing
  uint32_t timing_iterations;      // Iterations for timing measurement
  bool test_sbvh;                  // Test SBVH in addition to TriangleBVH
  bool test_traversal_configs;     // Test different traversal configs
  float build_weight;              // Weight for build time in cost (0-1)
  float traversal_weight;          // Weight for traversal time in cost (0-1)
  float memory_weight;             // Weight for memory usage in cost (0-1)

  AutoTuneConfig() noexcept
    : sample_prim_count(0)         // 0 = auto
    , sample_ray_count(1000)
    , warmup_iterations(3)
    , timing_iterations(10)
    , test_sbvh(true)
    , test_traversal_configs(true)
    , build_weight(0.1f)           // Build time typically matters less
    , traversal_weight(0.8f)       // Traversal performance is most important
    , memory_weight(0.1f) {}       // Memory matters for large scenes

  // Preset: optimize for throughput (many rays)
  static AutoTuneConfig throughput() noexcept {
    AutoTuneConfig cfg;
    cfg.build_weight = 0.05f;
    cfg.traversal_weight = 0.9f;
    cfg.memory_weight = 0.05f;
    return cfg;
  }

  // Preset: optimize for interactive (frequent rebuilds)
  static AutoTuneConfig interactive() noexcept {
    AutoTuneConfig cfg;
    cfg.build_weight = 0.4f;
    cfg.traversal_weight = 0.5f;
    cfg.memory_weight = 0.1f;
    return cfg;
  }

  // Preset: optimize for memory (large scenes)
  static AutoTuneConfig memory() noexcept {
    AutoTuneConfig cfg;
    cfg.build_weight = 0.1f;
    cfg.traversal_weight = 0.5f;
    cfg.memory_weight = 0.4f;
    cfg.test_sbvh = false;  // SBVH uses more memory due to reference duplication
    return cfg;
  }

  // Preset: quick tuning (fewer samples)
  static AutoTuneConfig quick() noexcept {
    AutoTuneConfig cfg;
    cfg.sample_ray_count = 500;
    cfg.warmup_iterations = 1;
    cfg.timing_iterations = 5;
    cfg.test_sbvh = false;
    cfg.test_traversal_configs = false;
    return cfg;
  }
};

// Auto-tune result
struct AutoTuneResult {
  BVHBuildMethod best_method;
  BVHBuildConfig best_bvh_config;        // Used if method == TriangleBVH
  SBVHBuildConfig best_sbvh_config;      // Used if method == SBVH
  TraversalConfig best_traversal_config;

  // Measured metrics (normalized to per-primitive or per-ray)
  float build_time_us_per_prim;          // Build time in microseconds per primitive
  float traversal_time_ns_per_ray;       // Traversal time in nanoseconds per ray
  float memory_bytes_per_prim;           // Memory usage in bytes per primitive

  // Detailed metrics for each tested configuration
  struct ConfigMetrics {
    BVHBuildMethod method;
    float build_time_us_per_prim;
    float traversal_time_ns_per_ray;
    float memory_bytes_per_prim;
    float combined_cost;                 // Weighted cost used for selection
    uint32_t max_leaf_size;
    float sbvh_alpha;                    // Only for SBVH
  };
  std::vector<ConfigMetrics> all_metrics;

  // Scene characteristics detected during tuning
  struct SceneCharacteristics {
    float avg_triangle_area;
    float scene_volume;
    float triangle_density;              // Triangles per unit volume
    float overlap_ratio;                 // Estimated AABB overlap
    bool has_thin_triangles;             // Long thin triangles detected
    bool has_clustered_distribution;     // Spatial clustering detected
    bool has_coplanar_regions;           // Co-planar triangles detected
  };
  SceneCharacteristics scene_info;

  AutoTuneResult() noexcept
    : best_method(BVHBuildMethod::TriangleBVH)
    , build_time_us_per_prim(0)
    , traversal_time_ns_per_ray(0)
    , memory_bytes_per_prim(0) {}
};

// Simple timer for benchmarking (platform-independent)
class SimpleTimer {
public:
  void start() noexcept;
  void stop() noexcept;
  double elapsedMicroseconds() const noexcept;
  double elapsedMilliseconds() const noexcept { return elapsedMicroseconds() / 1000.0; }

private:
  uint64_t start_time_;
  uint64_t end_time_;
};

// Simple RNG for sampling (Xorshift64)
class SimpleRNG {
public:
  explicit SimpleRNG(uint64_t seed = 12345) noexcept : state_(seed ? seed : 1) {}

  uint64_t next() noexcept {
    state_ ^= state_ >> 12;
    state_ ^= state_ << 25;
    state_ ^= state_ >> 27;
    return state_ * 0x2545F4914F6CDD1DULL;
  }

  float nextFloat() noexcept {
    return static_cast<float>(next() & 0xFFFFFF) / static_cast<float>(0x1000000);
  }

  // Generate random float in range [min, max]
  float nextFloat(float min_val, float max_val) noexcept {
    return min_val + nextFloat() * (max_val - min_val);
  }

  // Shuffle array using Fisher-Yates
  template<typename T>
  void shuffle(std::vector<T>& arr) noexcept {
    for (size_t i = arr.size() - 1; i > 0; i--) {
      size_t j = next() % (i + 1);
      std::swap(arr[i], arr[j]);
    }
  }

private:
  uint64_t state_;
};

// AutoTuner class
class AutoTuner {
public:
  // Auto-tune BVH construction for triangles
  // Returns the best configuration based on sampling and measurement
  static AutoTuneResult tune(const std::vector<Triangle>& triangles,
                             const AutoTuneConfig& config = AutoTuneConfig()) noexcept;

  // Tune traversal configuration for an existing TriangleBVH
  // Useful when you already have a BVH and want optimal traversal settings
  static TraversalConfig tuneTraversal(const TriangleBVH& bvh,
                                        const AABB& scene_bounds,
                                        uint32_t sample_ray_count = 1000,
                                        uint32_t timing_iterations = 10) noexcept;

  // Tune traversal configuration for an existing SBVH
  static TraversalConfig tuneTraversal(const SBVH& sbvh,
                                        const AABB& scene_bounds,
                                        uint32_t sample_ray_count = 1000,
                                        uint32_t timing_iterations = 10) noexcept;

  // Analyze scene characteristics (useful for manual tuning decisions)
  static AutoTuneResult::SceneCharacteristics analyzeScene(
      const std::vector<Triangle>& triangles) noexcept;

  // Build BVH using auto-tuned configuration
  // Convenience function that combines tune() and build()
  static bool buildOptimal(const std::vector<Triangle>& triangles,
                           TriangleBVH& out_bvh,
                           const AutoTuneConfig& config = AutoTuneConfig()) noexcept;

  static bool buildOptimal(const std::vector<Triangle>& triangles,
                           SBVH& out_sbvh,
                           const AutoTuneConfig& config = AutoTuneConfig()) noexcept;

private:
  // Sample M primitives from N using stratified sampling
  static std::vector<Triangle> samplePrimitives(
      const std::vector<Triangle>& triangles,
      uint32_t sample_count,
      SimpleRNG& rng) noexcept;

  // Generate test rays covering the scene
  static std::vector<Ray> generateTestRays(
      const AABB& scene_bounds,
      uint32_t ray_count,
      SimpleRNG& rng) noexcept;

  // Measure build time for TriangleBVH
  static double measureBuildTime(
      const std::vector<Triangle>& triangles,
      const BVHBuildConfig& config,
      uint32_t iterations,
      TriangleBVH& out_bvh) noexcept;

  // Measure build time for SBVH
  static double measureBuildTime(
      const std::vector<Triangle>& triangles,
      const SBVHBuildConfig& config,
      uint32_t iterations,
      SBVH& out_sbvh) noexcept;

  // Measure traversal time for TriangleBVH
  static double measureTraversalTime(
      const TriangleBVH& bvh,
      const std::vector<Ray>& rays,
      const TraversalConfig& trav_config,
      uint32_t iterations) noexcept;

  // Measure traversal time for SBVH
  static double measureTraversalTime(
      const SBVH& sbvh,
      const std::vector<Ray>& rays,
      const TraversalConfig& trav_config,
      uint32_t iterations) noexcept;

  // Estimate memory usage
  static size_t estimateMemory(const TriangleBVH& bvh) noexcept;
  static size_t estimateMemory(const SBVH& sbvh) noexcept;
};

} // namespace lightrt

#endif // LIGHTRT_HH_
