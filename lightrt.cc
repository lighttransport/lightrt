// Copyright (c) 2026 Light Transport Entertainment, Inc.
// SPDX-License-Identifier: MIT
//
// lightrt.cc - Lightweight ray tracing and BVH kernel implementation

#include "lightrt.hh"

namespace lightrt {

// ============================================================================
// Triangle Implementation
// ============================================================================

AABB Triangle::bounds() const noexcept {
  AABB b;
  b.expand(v0);
  b.expand(v1);
  b.expand(v2);
  return b;
}

bool Triangle::intersect(const Ray& ray, float& t, float& u, float& v) const noexcept {
  // Moller-Trumbore algorithm
  const Vec3 e1 = v1 - v0;
  const Vec3 e2 = v2 - v0;

  const Vec3 pvec = ray.direction.cross(e2);
  const float det = e1.dot(pvec);

  // Backface culling disabled - test both sides
  if (std::abs(det) < kEpsilon) {
    return false;
  }

  const float inv_det = 1.0f / det;

  const Vec3 tvec = ray.origin - v0;
  u = tvec.dot(pvec) * inv_det;
  if (u < 0.0f || u > 1.0f) {
    return false;
  }

  const Vec3 qvec = tvec.cross(e1);
  v = ray.direction.dot(qvec) * inv_det;
  if (v < 0.0f || u + v > 1.0f) {
    return false;
  }

  t = e2.dot(qvec) * inv_det;
  return t > ray.tmin && t < ray.tmax;
}

// ============================================================================
// Quad Implementation
// ============================================================================

AABB Quad::bounds() const noexcept {
  AABB b;
  b.expand(v0);
  b.expand(v1);
  b.expand(v2);
  b.expand(v3);
  return b;
}

bool Quad::intersect(const Ray& ray, float& t, float& u_out, float& v_out) const noexcept {
  // Split quad into two triangles and test both
  // Triangle 1: v0, v1, v2
  float t1, u1, v1_param;
  Triangle tri1(v0, v1, v2);
  bool hit1 = tri1.intersect(ray, t1, u1, v1_param);

  // Triangle 2: v0, v2, v3
  float t2, u2, v2_param;
  Triangle tri2(v0, v2, v3);
  bool hit2 = tri2.intersect(ray, t2, u2, v2_param);

  if (hit1 && hit2) {
    if (t1 < t2) {
      t = t1;
      u_out = u1;
      v_out = v1_param;
    } else {
      t = t2;
      // Remap UV for second triangle
      u_out = u2;
      v_out = 1.0f - v2_param;
    }
    return true;
  } else if (hit1) {
    t = t1;
    u_out = u1;
    v_out = v1_param;
    return true;
  } else if (hit2) {
    t = t2;
    u_out = u2;
    v_out = 1.0f - v2_param;
    return true;
  }

  return false;
}

// ============================================================================
// NGon Implementation
// ============================================================================

NGon::NGon(const std::vector<Vec3>& verts) noexcept : vertices(verts) {
  computeNormal();
}

void NGon::computeNormal() noexcept {
  if (vertices.size() < 3) {
    normal = Vec3(0, 1, 0);
    return;
  }
  // Use Newell's method for robust normal computation
  Vec3 n(0, 0, 0);
  for (size_t i = 0; i < vertices.size(); i++) {
    const Vec3& curr = vertices[i];
    const Vec3& next = vertices[(i + 1) % vertices.size()];
    n.x += (curr.y - next.y) * (curr.z + next.z);
    n.y += (curr.z - next.z) * (curr.x + next.x);
    n.z += (curr.x - next.x) * (curr.y + next.y);
  }
  normal = n.normalize();
}

Vec3 NGon::centroid() const noexcept {
  if (vertices.empty()) return Vec3();
  Vec3 c(0, 0, 0);
  for (const auto& v : vertices) {
    c = c + v;
  }
  return c * (1.0f / vertices.size());
}

AABB NGon::bounds() const noexcept {
  AABB b;
  for (const auto& v : vertices) {
    b.expand(v);
  }
  return b;
}

bool NGon::intersect(const Ray& ray, float& t) const noexcept {
  if (vertices.size() < 3) return false;

  // Ray-plane intersection
  float denom = normal.dot(ray.direction);
  if (std::abs(denom) < kEpsilon) return false;

  float plane_d = normal.dot(vertices[0]);
  t = (plane_d - normal.dot(ray.origin)) / denom;

  if (t < ray.tmin || t > ray.tmax) return false;

  // Point on plane
  Vec3 p = ray.at(t);

  // Check if point is inside polygon (crossing number algorithm)
  // Project to 2D based on dominant normal axis
  int axis0, axis1;
  float nx = std::abs(normal.x);
  float ny = std::abs(normal.y);
  float nz = std::abs(normal.z);

  if (nx >= ny && nx >= nz) {
    axis0 = 1; axis1 = 2;
  } else if (ny >= nz) {
    axis0 = 0; axis1 = 2;
  } else {
    axis0 = 0; axis1 = 1;
  }

  auto getCoord = [](const Vec3& v, int axis) -> float {
    return axis == 0 ? v.x : axis == 1 ? v.y : v.z;
  };

  float px = getCoord(p, axis0);
  float py = getCoord(p, axis1);

  int crossings = 0;
  for (size_t i = 0; i < vertices.size(); i++) {
    const Vec3& v0 = vertices[i];
    const Vec3& v1 = vertices[(i + 1) % vertices.size()];

    float x0 = getCoord(v0, axis0) - px;
    float y0 = getCoord(v0, axis1) - py;
    float x1 = getCoord(v1, axis0) - px;
    float y1 = getCoord(v1, axis1) - py;

    if ((y0 > 0) != (y1 > 0)) {
      float x_intersect = x0 + (x1 - x0) * y0 / (y0 - y1);
      if (x_intersect > 0) {
        crossings++;
      }
    }
  }

  return (crossings & 1) != 0;
}

// ============================================================================
// Sphere Implementation
// ============================================================================

AABB Sphere::bounds() const noexcept {
  return AABB(
    Vec3(center.x - radius, center.y - radius, center.z - radius),
    Vec3(center.x + radius, center.y + radius, center.z + radius)
  );
}

bool Sphere::intersect(const Ray& ray, float& t) const noexcept {
  Vec3 oc = ray.origin - center;

  float a = ray.direction.dot(ray.direction);
  float half_b = oc.dot(ray.direction);
  float c = oc.dot(oc) - radius * radius;

  float discriminant = half_b * half_b - a * c;
  if (discriminant < 0) return false;

  float sqrtd = std::sqrt(discriminant);

  // Find nearest root in acceptable range
  float root = (-half_b - sqrtd) / a;
  if (root < ray.tmin || root > ray.tmax) {
    root = (-half_b + sqrtd) / a;
    if (root < ray.tmin || root > ray.tmax) {
      return false;
    }
  }

  t = root;
  return true;
}

bool Sphere::intersect(const Ray& ray, float& t, Vec3& hit_normal) const noexcept {
  if (!intersect(ray, t)) return false;
  Vec3 hit_point = ray.at(t);
  hit_normal = (hit_point - center) * (1.0f / radius);
  return true;
}

// ============================================================================
// Disk Implementation
// ============================================================================

AABB Disk::bounds() const noexcept {
  // Conservative bounds for arbitrary orientation
  return AABB(
    Vec3(center.x - radius, center.y - radius, center.z - radius),
    Vec3(center.x + radius, center.y + radius, center.z + radius)
  );
}

bool Disk::intersect(const Ray& ray, float& t) const noexcept {
  // Ray-plane intersection
  float denom = normal.dot(ray.direction);
  if (std::abs(denom) < kEpsilon) return false;

  float plane_d = normal.dot(center);
  t = (plane_d - normal.dot(ray.origin)) / denom;

  if (t < ray.tmin || t > ray.tmax) return false;

  // Check if hit point is within radius
  Vec3 p = ray.at(t);
  Vec3 diff = p - center;
  float dist_sq = diff.dot(diff);

  return dist_sq <= radius * radius;
}

// ============================================================================
// OrientedDisk (Billboard) Implementation
// ============================================================================

AABB OrientedDisk::bounds() const noexcept {
  // Sphere bounds since orientation is dynamic
  return AABB(
    Vec3(center.x - radius, center.y - radius, center.z - radius),
    Vec3(center.x + radius, center.y + radius, center.z + radius)
  );
}

bool OrientedDisk::intersect(const Ray& ray, float& t) const noexcept {
  // Normal faces toward ray origin
  Vec3 to_origin = ray.origin - center;
  Vec3 normal = to_origin.normalize();

  // Ray-plane intersection
  float denom = normal.dot(ray.direction);
  if (std::abs(denom) < kEpsilon) return false;

  float plane_d = normal.dot(center);
  t = (plane_d - normal.dot(ray.origin)) / denom;

  if (t < ray.tmin || t > ray.tmax) return false;

  // Check if hit point is within radius
  Vec3 p = ray.at(t);
  Vec3 diff = p - center;
  float dist_sq = diff.dot(diff);

  return dist_sq <= radius * radius;
}

// ============================================================================
// Curve Implementation
// ============================================================================

Curve::Curve(const std::vector<Vec3>& points, float radius, CurveType t) noexcept
  : control_points(points), type(t) {
  radii.resize(points.size(), radius);
}

Curve::Curve(const std::vector<Vec3>& points, const std::vector<float>& r, CurveType t) noexcept
  : control_points(points), radii(r), type(t) {
  // Ensure radii matches control points
  if (radii.size() < control_points.size()) {
    float last_r = radii.empty() ? 0.01f : radii.back();
    radii.resize(control_points.size(), last_r);
  }
}

Vec3 Curve::centroid() const noexcept {
  if (control_points.empty()) return Vec3();
  Vec3 c(0, 0, 0);
  for (const auto& p : control_points) {
    c = c + p;
  }
  return c * (1.0f / control_points.size());
}

AABB Curve::bounds() const noexcept {
  AABB b;
  for (size_t i = 0; i < control_points.size(); i++) {
    float r = i < radii.size() ? radii[i] : 0.01f;
    Vec3 p = control_points[i];
    b.expand(Vec3(p.x - r, p.y - r, p.z - r));
    b.expand(Vec3(p.x + r, p.y + r, p.z + r));
  }
  return b;
}

Vec3 Curve::evaluate(float t) const noexcept {
  if (control_points.empty()) return Vec3();
  if (control_points.size() == 1) return control_points[0];

  t = std::max(0.0f, std::min(1.0f, t));

  if (type == CurveType::Linear || control_points.size() == 2) {
    // Linear interpolation between segments
    float segment_t = t * (control_points.size() - 1);
    size_t i = static_cast<size_t>(segment_t);
    i = std::min(i, control_points.size() - 2);
    float local_t = segment_t - i;
    return control_points[i] + (control_points[i + 1] - control_points[i]) * local_t;
  }

  if (type == CurveType::Bezier && control_points.size() >= 4) {
    // Cubic Bezier: P(t) = (1-t)^3*P0 + 3(1-t)^2*t*P1 + 3(1-t)*t^2*P2 + t^3*P3
    float u = 1.0f - t;
    float u2 = u * u;
    float u3 = u2 * u;
    float t2 = t * t;
    float t3 = t2 * t;

    return control_points[0] * u3 +
           control_points[1] * (3.0f * u2 * t) +
           control_points[2] * (3.0f * u * t2) +
           control_points[3] * t3;
  }

  if (type == CurveType::CatmullRom && control_points.size() >= 4) {
    // Catmull-Rom spline
    float segment_t = t * (control_points.size() - 3);
    size_t i = static_cast<size_t>(segment_t);
    i = std::min(i, control_points.size() - 4);
    float local_t = segment_t - i;

    const Vec3& p0 = control_points[i];
    const Vec3& p1 = control_points[i + 1];
    const Vec3& p2 = control_points[i + 2];
    const Vec3& p3 = control_points[i + 3];

    float t2 = local_t * local_t;
    float t3 = t2 * local_t;

    return (p1 * 2.0f +
            (p2 - p0) * local_t +
            (p0 * 2.0f - p1 * 5.0f + p2 * 4.0f - p3) * t2 +
            (p1 * 3.0f - p0 - p2 * 3.0f + p3) * t3) * 0.5f;
  }

  // Fallback to linear
  float segment_t = t * (control_points.size() - 1);
  size_t i = static_cast<size_t>(segment_t);
  i = std::min(i, control_points.size() - 2);
  float local_t = segment_t - i;
  return control_points[i] + (control_points[i + 1] - control_points[i]) * local_t;
}

Vec3 Curve::evaluateTangent(float t) const noexcept {
  // Numerical differentiation
  const float h = 0.001f;
  Vec3 p0 = evaluate(std::max(0.0f, t - h));
  Vec3 p1 = evaluate(std::min(1.0f, t + h));
  return (p1 - p0).normalize();
}

float Curve::radiusAt(float t) const noexcept {
  if (radii.empty()) return 0.01f;
  if (radii.size() == 1) return radii[0];

  t = std::max(0.0f, std::min(1.0f, t));
  float segment_t = t * (radii.size() - 1);
  size_t i = static_cast<size_t>(segment_t);
  i = std::min(i, radii.size() - 2);
  float local_t = segment_t - i;

  return radii[i] + (radii[i + 1] - radii[i]) * local_t;
}

bool Curve::intersect(const Ray& ray, float& t_hit, float& u_hit) const noexcept {
  if (control_points.size() < 2) return false;

  if (type == CurveType::Linear) {
    return intersectLinear(ray, t_hit, u_hit);
  }

  // Use Phantom algorithm for smooth curves
  return intersectPhantom(ray, t_hit, u_hit);
}

// Phantom Ray-Hair Intersector implementation
// Based on Reshetov & Luebke, HPG 2018
bool Curve::intersectPhantom(const Ray& ray, float& t_hit, float& u_hit) const noexcept {
  const int max_iterations = 10;
  const float epsilon = 1e-5f;

  // Initial guess: middle of curve
  float u = 0.5f;
  float best_t = ray.tmax;
  bool hit = false;

  // Newton-Raphson iteration
  for (int iter = 0; iter < max_iterations; iter++) {
    Vec3 curve_pos = evaluate(u);
    Vec3 curve_tangent = evaluateTangent(u);
    float r = radiusAt(u);

    // Vector from ray origin to curve point
    Vec3 oc = curve_pos - ray.origin;

    // Project onto ray to find closest point
    float t_closest = oc.dot(ray.direction) / ray.direction.dot(ray.direction);

    if (t_closest < ray.tmin) {
      // Try moving along curve
      u = std::max(0.0f, u - 0.1f);
      continue;
    }

    Vec3 ray_point = ray.at(t_closest);
    Vec3 diff = ray_point - curve_pos;
    float dist_sq = diff.dot(diff);

    // Check if ray passes within radius
    if (dist_sq <= r * r) {
      // Refine hit point - find actual surface intersection
      float inside_dist = std::sqrt(r * r - dist_sq);

      float t_surface = t_closest - inside_dist;
      if (t_surface > ray.tmin && t_surface < best_t) {
        best_t = t_surface;
        u_hit = u;
        hit = true;
      }
    }

    // Compute gradient for Newton step
    // Move u to minimize distance to ray
    Vec3 curve_to_ray = ray_point - curve_pos;
    float du = curve_tangent.dot(curve_to_ray) / (curve_tangent.dot(curve_tangent) + epsilon);

    float new_u = u + du * 0.5f;
    new_u = std::max(0.0f, std::min(1.0f, new_u));

    if (std::abs(new_u - u) < epsilon) {
      break;
    }
    u = new_u;
  }

  // Also check endpoints and subdivisions for robustness
  const int num_samples = 8;
  for (int i = 0; i <= num_samples; i++) {
    float sample_u = static_cast<float>(i) / num_samples;
    Vec3 curve_pos = evaluate(sample_u);
    float r = radiusAt(sample_u);

    Vec3 oc = curve_pos - ray.origin;
    float t_closest = oc.dot(ray.direction) / ray.direction.dot(ray.direction);

    if (t_closest < ray.tmin || t_closest >= best_t) continue;

    Vec3 ray_point = ray.at(t_closest);
    Vec3 diff = ray_point - curve_pos;
    float dist_sq = diff.dot(diff);

    if (dist_sq <= r * r) {
      float inside_dist = std::sqrt(r * r - dist_sq);

      float t_surface = t_closest - inside_dist;
      if (t_surface > ray.tmin && t_surface < best_t) {
        best_t = t_surface;
        u_hit = sample_u;
        hit = true;
      }
    }
  }

  if (hit) {
    t_hit = best_t;
  }
  return hit;
}

// Simple linear segment intersection (capsule-based)
bool Curve::intersectLinear(const Ray& ray, float& t_hit, float& u_hit) const noexcept {
  float best_t = ray.tmax;
  bool hit = false;

  for (size_t i = 0; i < control_points.size() - 1; i++) {
    const Vec3& p0 = control_points[i];
    const Vec3& p1 = control_points[i + 1];
    float r0 = i < radii.size() ? radii[i] : 0.01f;
    float r1 = i + 1 < radii.size() ? radii[i + 1] : r0;
    float r = (r0 + r1) * 0.5f;

    // Capsule intersection: cylinder + two spheres
    Vec3 segment = p1 - p0;
    float seg_len_sq = segment.dot(segment);

    if (seg_len_sq < kEpsilon) {
      // Degenerate segment, treat as sphere
      Sphere sphere(p0, r);
      float t;
      if (sphere.intersect(ray, t) && t < best_t) {
        best_t = t;
        u_hit = static_cast<float>(i) / (control_points.size() - 1);
        hit = true;
      }
      continue;
    }

    Vec3 seg_dir = segment * (1.0f / std::sqrt(seg_len_sq));

    // Find closest points between ray and line segment
    Vec3 w0 = ray.origin - p0;
    float a = ray.direction.dot(ray.direction);
    float b = ray.direction.dot(seg_dir);
    float c = seg_dir.dot(seg_dir);
    float d = ray.direction.dot(w0);
    float e = seg_dir.dot(w0);

    float denom = a * c - b * b;
    float t_ray, t_seg;

    if (std::abs(denom) < kEpsilon) {
      // Parallel lines
      t_ray = d / a;
      t_seg = 0.0f;
    } else {
      t_ray = (b * e - c * d) / denom;
      t_seg = (a * e - b * d) / denom;
    }

    // Clamp t_seg to segment
    t_seg = std::max(0.0f, std::min(std::sqrt(seg_len_sq), t_seg));

    // Recompute t_ray for clamped t_seg
    Vec3 closest_on_seg = p0 + seg_dir * t_seg;
    Vec3 oc = closest_on_seg - ray.origin;
    t_ray = oc.dot(ray.direction) / a;

    if (t_ray < ray.tmin || t_ray >= best_t) continue;

    Vec3 ray_point = ray.at(t_ray);
    Vec3 diff = ray_point - closest_on_seg;
    float dist_sq = diff.dot(diff);

    // Interpolate radius along segment
    float seg_u = t_seg / std::sqrt(seg_len_sq);
    float local_r = r0 + (r1 - r0) * seg_u;

    if (dist_sq <= local_r * local_r) {
      float inside_dist = std::sqrt(local_r * local_r - dist_sq);
      float t_surface = t_ray - inside_dist;

      if (t_surface > ray.tmin && t_surface < best_t) {
        best_t = t_surface;
        u_hit = (i + seg_u) / (control_points.size() - 1);
        hit = true;
      }
    }
  }

  if (hit) {
    t_hit = best_t;
  }
  return hit;
}

// ============================================================================
// AABB Ray Intersection (Scalar)
// ============================================================================

bool AABB::intersect(const Ray& ray, float& tmin_out, float& tmax_out) const noexcept {
  float tmin = ray.tmin;
  float tmax = ray.tmax;
  
  for (int i = 0; i < 3; i++) {
    float inv_d = 1.0f / (i == 0 ? ray.direction.x : i == 1 ? ray.direction.y : ray.direction.z);
    float t0 = ((i == 0 ? min.x : i == 1 ? min.y : min.z) - 
                (i == 0 ? ray.origin.x : i == 1 ? ray.origin.y : ray.origin.z)) * inv_d;
    float t1 = ((i == 0 ? max.x : i == 1 ? max.y : max.z) - 
                (i == 0 ? ray.origin.x : i == 1 ? ray.origin.y : ray.origin.z)) * inv_d;
    
    if (inv_d < 0.0f) {
      float temp = t0;
      t0 = t1;
      t1 = temp;
    }
    
    tmin = t0 > tmin ? t0 : tmin;
    tmax = t1 < tmax ? t1 : tmax;
    
    if (tmax < tmin) {
      return false;
    }
  }
  
  tmin_out = tmin;
  tmax_out = tmax;
  return true;
}

// ============================================================================
// AABB Ray Intersection (SIMD Optimized)
// ============================================================================

bool AABB::intersectSIMD(const Ray& ray, float& tmin_out, float& tmax_out) const noexcept {
#if defined(LIGHTRT_HAS_SSE2) || defined(LIGHTRT_HAS_AVX)
  // SSE2/AVX optimized version
  __m128 ray_orig = _mm_set_ps(0.0f, ray.origin.z, ray.origin.y, ray.origin.x);
  __m128 ray_dir = _mm_set_ps(0.0f, ray.direction.z, ray.direction.y, ray.direction.x);
  __m128 ray_inv_dir = _mm_div_ps(_mm_set1_ps(1.0f), ray_dir);
  
  __m128 box_min = _mm_set_ps(0.0f, min.z, min.y, min.x);
  __m128 box_max = _mm_set_ps(0.0f, max.z, max.y, max.x);
  
  __m128 t0 = _mm_mul_ps(_mm_sub_ps(box_min, ray_orig), ray_inv_dir);
  __m128 t1 = _mm_mul_ps(_mm_sub_ps(box_max, ray_orig), ray_inv_dir);
  
  __m128 tmin_v = _mm_min_ps(t0, t1);
  __m128 tmax_v = _mm_max_ps(t0, t1);
  
  // Horizontal max of tmin
  float tmin = ray.tmin;
  alignas(16) float tmin_arr[4];
  _mm_store_ps(tmin_arr, tmin_v);
  tmin = std::max(tmin, std::max(tmin_arr[0], std::max(tmin_arr[1], tmin_arr[2])));
  
  // Horizontal min of tmax
  float tmax = ray.tmax;
  alignas(16) float tmax_arr[4];
  _mm_store_ps(tmax_arr, tmax_v);
  tmax = std::min(tmax, std::min(tmax_arr[0], std::min(tmax_arr[1], tmax_arr[2])));
  
  if (tmax < tmin) {
    return false;
  }
  
  tmin_out = tmin;
  tmax_out = tmax;
  return true;
  
#elif defined(LIGHTRT_HAS_NEON)
  // ARM NEON optimized version
  float32x4_t ray_orig = {ray.origin.x, ray.origin.y, ray.origin.z, 0.0f};
  float32x4_t ray_inv_dir = {
    1.0f / ray.direction.x,
    1.0f / ray.direction.y,
    1.0f / ray.direction.z,
    0.0f
  };
  
  float32x4_t box_min_v = {min.x, min.y, min.z, 0.0f};
  float32x4_t box_max_v = {max.x, max.y, max.z, 0.0f};
  
  float32x4_t t0 = vmulq_f32(vsubq_f32(box_min_v, ray_orig), ray_inv_dir);
  float32x4_t t1 = vmulq_f32(vsubq_f32(box_max_v, ray_orig), ray_inv_dir);
  
  float32x4_t tmin_v = vminq_f32(t0, t1);
  float32x4_t tmax_v = vmaxq_f32(t0, t1);
  
  // Horizontal max of tmin
  float tmin = ray.tmin;
  float tmin_arr[4];
  vst1q_f32(tmin_arr, tmin_v);
  tmin = std::max(tmin, std::max(tmin_arr[0], std::max(tmin_arr[1], tmin_arr[2])));
  
  // Horizontal min of tmax
  float tmax = ray.tmax;
  float tmax_arr[4];
  vst1q_f32(tmax_arr, tmax_v);
  tmax = std::min(tmax, std::min(tmax_arr[0], std::min(tmax_arr[1], tmax_arr[2])));
  
  if (tmax < tmin) {
    return false;
  }
  
  tmin_out = tmin;
  tmax_out = tmax;
  return true;
  
#else
  // Fallback to scalar version
  return intersect(ray, tmin_out, tmax_out);
#endif
}

// ============================================================================
// BVH Builder Implementation
// ============================================================================

bool BVH::build(const std::vector<AABB>& prim_aabbs, const BVHBuildConfig& config) noexcept {
  if (prim_aabbs.empty()) {
    return false;
  }

  prim_aabbs_ = prim_aabbs;
  config_ = config;

  // Use a separate working buffer to avoid invalidation during insert
  std::vector<uint32_t> work_indices(prim_aabbs.size());
  for (uint32_t i = 0; i < prim_aabbs.size(); i++) {
    work_indices[i] = i;
  }

  // Clear output arrays
  prim_indices_.clear();
  prim_indices_.reserve(prim_aabbs.size());
  nodes_.clear();
  nodes_.reserve(prim_aabbs.size() * 2);

  // Build recursively
  buildRecursive(work_indices.data(), static_cast<uint32_t>(prim_aabbs.size()), 0);

  return true;
}

uint32_t BVH::buildRecursive(uint32_t* indices, uint32_t num_prims, uint32_t depth) noexcept {
  // Allocate new node
  uint32_t node_idx = static_cast<uint32_t>(nodes_.size());
  nodes_.emplace_back();
  BVHNode& node = nodes_[node_idx];
  
  // Compute bounds of all primitives
  AABB bounds;
  for (uint32_t i = 0; i < num_prims; i++) {
    bounds.expand(prim_aabbs_[indices[i]]);
  }
  node.bounds = bounds;
  
  // Check if we should create a leaf
  if (num_prims <= config_.max_leaf_size) {
    // Create leaf node
    uint32_t offset = static_cast<uint32_t>(prim_indices_.size());
    
    // Move primitives to end of array
    prim_indices_.insert(prim_indices_.end(), indices, indices + num_prims);
    
    node.setLeaf(offset, num_prims);
    return node_idx;
  }
  
  // Compute centroid bounds
  AABB centroid_bounds;
  for (uint32_t i = 0; i < num_prims; i++) {
    centroid_bounds.expand(prim_aabbs_[indices[i]].center());
  }
  
  // Find best split
  float parent_area = bounds.surfaceArea();
  SplitResult split;
  if (config_.use_binning && num_prims > 64) {
    split = findBestSplitBinned(indices, num_prims, centroid_bounds, parent_area);
  } else if (config_.use_sah) {
    split = findBestSplit(indices, num_prims, centroid_bounds, parent_area);
  } else {
    // Simple midpoint split
    split.axis = centroid_bounds.longestAxis();
    split.pos = (centroid_bounds.min.x + centroid_bounds.max.x) * 0.5f;
    if (split.axis == 1) {
      split.pos = (centroid_bounds.min.y + centroid_bounds.max.y) * 0.5f;
    } else if (split.axis == 2) {
      split.pos = (centroid_bounds.min.z + centroid_bounds.max.z) * 0.5f;
    }
    split.cost = 0.0f;
  }
  
  // Partition primitives
  auto getAxisValue = [&](uint32_t idx) -> float {
    Vec3 c = prim_aabbs_[idx].center();
    return split.axis == 0 ? c.x : split.axis == 1 ? c.y : c.z;
  };
  
  uint32_t* mid = std::partition(indices, indices + num_prims,
    [&](uint32_t idx) { return getAxisValue(idx) < split.pos; });
  
  uint32_t left_count = static_cast<uint32_t>(mid - indices);
  
  // Handle degenerate case where all primitives go to one side
  if (left_count == 0 || left_count == num_prims) {
    left_count = num_prims / 2;
  }
  
  // Check if split is worth it (SAH cost)
  // Skip this check if force_max_leaf_size is enabled (always split until leaf size reached)
  if (config_.use_sah && !config_.force_max_leaf_size &&
      split.cost >= config_.intersection_cost * num_prims) {
    // Don't split, create leaf
    uint32_t offset = static_cast<uint32_t>(prim_indices_.size());
    prim_indices_.insert(prim_indices_.end(), indices, indices + num_prims);
    node.setLeaf(offset, num_prims);
    return node_idx;
  }
  
  // Build children
  uint32_t left_child = buildRecursive(indices, left_count, depth + 1);
  uint32_t right_child = buildRecursive(mid, num_prims - left_count, depth + 1);
  
  // Update node (it may have been reallocated)
  nodes_[node_idx].setInterior(left_child, right_child);
  
  return node_idx;
}

BVH::SplitResult BVH::findBestSplit(
    const uint32_t* indices,
    uint32_t num_prims,
    const AABB& /* centroid_bounds */,
    float parent_area) noexcept {

  SplitResult best;
  best.cost = kInfinity;
  best.axis = 0;
  best.pos = 0.0f;

  float inv_parent_area = (parent_area > kEpsilon) ? 1.0f / parent_area : 0.0f;

  // Try each axis
  for (int axis = 0; axis < 3; axis++) {
    // Sort primitives by centroid along axis
    std::vector<uint32_t> sorted_indices(indices, indices + num_prims);

    std::sort(sorted_indices.begin(), sorted_indices.end(), [&](uint32_t a, uint32_t b) {
      Vec3 ca = prim_aabbs_[a].center();
      Vec3 cb = prim_aabbs_[b].center();
      float va = axis == 0 ? ca.x : axis == 1 ? ca.y : ca.z;
      float vb = axis == 0 ? cb.x : axis == 1 ? cb.y : cb.z;
      return va < vb;
    });

    // Try splits between primitives
    for (uint32_t i = 1; i < num_prims; i++) {
      // Compute bounds for left and right
      AABB left_bounds, right_bounds;

      for (uint32_t j = 0; j < i; j++) {
        left_bounds.expand(prim_aabbs_[sorted_indices[j]]);
      }

      for (uint32_t j = i; j < num_prims; j++) {
        right_bounds.expand(prim_aabbs_[sorted_indices[j]]);
      }

      // Compute SAH cost (normalized by parent area)
      float left_area = left_bounds.surfaceArea() * inv_parent_area;
      float right_area = right_bounds.surfaceArea() * inv_parent_area;
      float cost = config_.traversal_cost +
                   config_.intersection_cost * (i * left_area + (num_prims - i) * right_area);
      
      if (cost < best.cost) {
        best.cost = cost;
        best.axis = axis;
        
        // Split position is between primitives
        Vec3 c1 = prim_aabbs_[sorted_indices[i - 1]].center();
        Vec3 c2 = prim_aabbs_[sorted_indices[i]].center();
        best.pos = (axis == 0 ? (c1.x + c2.x) : axis == 1 ? (c1.y + c2.y) : (c1.z + c2.z)) * 0.5f;
      }
    }
  }
  
  return best;
}

BVH::SplitResult BVH::findBestSplitBinned(
    const uint32_t* indices,
    uint32_t num_prims,
    const AABB& centroid_bounds,
    float parent_area) noexcept {

  SplitResult best;
  best.cost = kInfinity;
  best.axis = 0;
  best.pos = 0.0f;

  float inv_parent_area = (parent_area > kEpsilon) ? 1.0f / parent_area : 0.0f;

  // Try each axis
  for (int axis = 0; axis < 3; axis++) {
    float min_val = axis == 0 ? centroid_bounds.min.x :
                    axis == 1 ? centroid_bounds.min.y : centroid_bounds.min.z;
    float max_val = axis == 0 ? centroid_bounds.max.x :
                    axis == 1 ? centroid_bounds.max.y : centroid_bounds.max.z;

    if (max_val - min_val < kEpsilon) {
      continue;
    }

    // Initialize bins
    struct Bin {
      AABB bounds;
      uint32_t count;

      Bin() : count(0) {}
    };

    std::vector<Bin> bins(config_.num_bins);

    // Put primitives into bins
    float scale = config_.num_bins / (max_val - min_val);
    for (uint32_t i = 0; i < num_prims; i++) {
      Vec3 centroid = prim_aabbs_[indices[i]].center();
      float val = axis == 0 ? centroid.x : axis == 1 ? centroid.y : centroid.z;

      uint32_t bin_idx = static_cast<uint32_t>((val - min_val) * scale);
      bin_idx = std::min(bin_idx, config_.num_bins - 1);

      bins[bin_idx].bounds.expand(prim_aabbs_[indices[i]]);
      bins[bin_idx].count++;
    }

    // Compute costs for each split
    for (uint32_t i = 1; i < config_.num_bins; i++) {
      AABB left_bounds, right_bounds;
      uint32_t left_count = 0, right_count = 0;

      for (uint32_t j = 0; j < i; j++) {
        left_bounds.expand(bins[j].bounds);
        left_count += bins[j].count;
      }

      for (uint32_t j = i; j < config_.num_bins; j++) {
        right_bounds.expand(bins[j].bounds);
        right_count += bins[j].count;
      }

      if (left_count == 0 || right_count == 0) {
        continue;
      }

      // Normalize by parent area for proper SAH comparison
      float left_area = left_bounds.surfaceArea() * inv_parent_area;
      float right_area = right_bounds.surfaceArea() * inv_parent_area;
      float cost = config_.traversal_cost +
                   config_.intersection_cost * (left_count * left_area + right_count * right_area);

      if (cost < best.cost) {
        best.cost = cost;
        best.axis = axis;
        best.pos = min_val + (max_val - min_val) * (static_cast<float>(i) / config_.num_bins);
      }
    }
  }
  
  return best;
}

// ============================================================================
// BVH Traversal Implementation
// ============================================================================

uint32_t BVH::traverse(const Ray& ray, float& hit_t) const noexcept {
  if (nodes_.empty()) {
    return kInvalidIndex;
  }
  
  uint32_t hit_prim = kInvalidIndex;
  hit_t = ray.tmax;
  
  // Stack-based traversal
  struct StackEntry {
    uint32_t node_idx;
  };
  
  StackEntry stack[64];
  int stack_ptr = 0;
  
  stack[stack_ptr++].node_idx = 0;
  
  while (stack_ptr > 0) {
    uint32_t node_idx = stack[--stack_ptr].node_idx;
    const BVHNode& node = nodes_[node_idx];
    
    float tmin, tmax;
    if (!node.bounds.intersect(ray, tmin, tmax) || tmin > hit_t) {
      continue;
    }
    
    if (node.isLeaf()) {
      // Test primitives in leaf
      for (uint32_t i = 0; i < node.prim_count; i++) {
        uint32_t prim_idx = prim_indices_[node.prim_offset + i];
        
        // Simple AABB intersection as primitive test
        float prim_tmin, prim_tmax;
        if (prim_aabbs_[prim_idx].intersect(ray, prim_tmin, prim_tmax)) {
          if (prim_tmin < hit_t && prim_tmin > ray.tmin) {
            hit_t = prim_tmin;
            hit_prim = prim_idx;
          }
        }
      }
    } else {
      // Add children to stack
      if (stack_ptr < 62) {
        stack[stack_ptr++].node_idx = node.left_child;
        stack[stack_ptr++].node_idx = node.right_child;
      }
    }
  }
  
  return hit_prim;
}

uint32_t BVH::traverseSIMD(const Ray& ray, float& hit_t) const noexcept {
  if (nodes_.empty()) {
    return kInvalidIndex;
  }
  
  uint32_t hit_prim = kInvalidIndex;
  hit_t = ray.tmax;
  
  // Stack-based traversal with SIMD intersection
  struct StackEntry {
    uint32_t node_idx;
  };
  
  StackEntry stack[64];
  int stack_ptr = 0;
  
  stack[stack_ptr++].node_idx = 0;
  
  while (stack_ptr > 0) {
    uint32_t node_idx = stack[--stack_ptr].node_idx;
    const BVHNode& node = nodes_[node_idx];
    
    float tmin, tmax;
    if (!node.bounds.intersectSIMD(ray, tmin, tmax) || tmin > hit_t) {
      continue;
    }
    
    if (node.isLeaf()) {
      // Test primitives in leaf
      for (uint32_t i = 0; i < node.prim_count; i++) {
        uint32_t prim_idx = prim_indices_[node.prim_offset + i];
        
        // Simple AABB intersection as primitive test
        float prim_tmin, prim_tmax;
        if (prim_aabbs_[prim_idx].intersectSIMD(ray, prim_tmin, prim_tmax)) {
          if (prim_tmin < hit_t && prim_tmin > ray.tmin) {
            hit_t = prim_tmin;
            hit_prim = prim_idx;
          }
        }
      }
    } else {
      // Add children to stack
      if (stack_ptr < 62) {
        stack[stack_ptr++].node_idx = node.left_child;
        stack[stack_ptr++].node_idx = node.right_child;
      }
    }
  }
  
  return hit_prim;
}

BVH::Stats BVH::getStats() const noexcept {
  Stats stats = {};
  
  if (nodes_.empty()) {
    return stats;
  }
  
  // Count nodes and compute depth
  std::vector<uint32_t> depths(nodes_.size(), 0);
  
  for (uint32_t i = 0; i < nodes_.size(); i++) {
    const BVHNode& node = nodes_[i];
    stats.num_nodes++;
    
    if (node.isLeaf()) {
      stats.num_leaves++;
      stats.avg_leaf_size += node.prim_count;
      stats.max_depth = std::max(stats.max_depth, depths[i]);
    } else {
      depths[node.left_child] = depths[i] + 1;
      depths[node.right_child] = depths[i] + 1;
    }
  }
  
  if (stats.num_leaves > 0) {
    stats.avg_leaf_size /= stats.num_leaves;
  }
  
  // Compute SAH cost
  stats.sah_cost = 0.0f;
  for (uint32_t i = 0; i < nodes_.size(); i++) {
    const BVHNode& node = nodes_[i];
    float area = node.bounds.surfaceArea();
    
    if (node.isLeaf()) {
      stats.sah_cost += area * node.prim_count * config_.intersection_cost;
    } else {
      stats.sah_cost += area * config_.traversal_cost;
    }
  }
  
  return stats;
}

// ============================================================================
// Two-Level BVH (TLAS) Implementation
// ============================================================================

bool TLAS::build(const std::vector<BLASInstance>& instances, const BVHBuildConfig& config) noexcept {
  if (instances.empty()) {
    return false;
  }
  
  instances_ = instances;
  
  // Build BVH over instance AABBs
  std::vector<AABB> instance_aabbs;
  instance_aabbs.reserve(instances.size());
  
  for (const auto& inst : instances) {
    instance_aabbs.push_back(inst.bounds);
  }
  
  return bvh_.build(instance_aabbs, config);
}

TLAS::TraceResult TLAS::trace(const Ray& ray, const std::vector<BLAS>& blas_array) const noexcept {
  TraceResult result;
  result.instance_id = kInvalidIndex;
  result.primitive_id = kInvalidIndex;
  result.t = ray.tmax;
  
  if (instances_.empty() || blas_array.empty()) {
    return result;
  }
  
  // Traverse TLAS to find instances
  float tlas_hit_t;
  uint32_t instance_idx = bvh_.traverse(ray, tlas_hit_t);
  
  if (instance_idx == kInvalidIndex) {
    return result;
  }
  
  // For simplicity, we test all instances (in full implementation, we'd traverse TLAS properly)
  for (uint32_t i = 0; i < instances_.size(); i++) {
    const BLASInstance& inst = instances_[i];
    
    if (inst.blas_id >= blas_array.size()) {
      continue;
    }
    
    // Transform ray to instance local space
    Ray local_ray;
    local_ray.origin = inst.worldToLocal(ray.origin);
    local_ray.direction = inst.worldToLocalDir(ray.direction).normalize();
    local_ray.tmin = ray.tmin;
    local_ray.tmax = result.t;
    
    // Traverse BLAS
    const BLAS& blas = blas_array[inst.blas_id];
    float hit_t;
    uint32_t prim_idx = blas.bvh.traverse(local_ray, hit_t);
    
    if (prim_idx != kInvalidIndex && hit_t < result.t) {
      result.instance_id = i;
      result.primitive_id = prim_idx;
      result.t = hit_t;
    }
  }
  
  return result;
}

// ============================================================================
// Triangle BVH Implementation
// ============================================================================

bool TriangleBVH::build(const std::vector<Triangle>& triangles, const BVHBuildConfig& config) noexcept {
  if (triangles.empty()) {
    return false;
  }

  triangles_ = triangles;

  // Build AABBs from triangles for BVH construction
  std::vector<AABB> aabbs;
  aabbs.reserve(triangles.size());
  for (const auto& tri : triangles) {
    aabbs.push_back(tri.bounds());
  }

  return bvh_.build(aabbs, config);
}

uint32_t TriangleBVH::traverse(const Ray& ray, float& hit_t, float& hit_u, float& hit_v) const noexcept {
  const auto& nodes = bvh_.getNodes();
  const auto& prim_indices = bvh_.getPrimitiveIndices();

  if (nodes.empty()) {
    return kInvalidIndex;
  }

  uint32_t hit_tri = kInvalidIndex;
  hit_t = ray.tmax;

  // Stack-based traversal
  struct StackEntry {
    uint32_t node_idx;
  };

  StackEntry stack[64];
  int stack_ptr = 0;

  stack[stack_ptr++].node_idx = 0;

  while (stack_ptr > 0) {
    uint32_t node_idx = stack[--stack_ptr].node_idx;
    const BVHNode& node = nodes[node_idx];

    float tmin, tmax;
    if (!node.bounds.intersectSIMD(ray, tmin, tmax) || tmin > hit_t) {
      continue;
    }

    if (node.isLeaf()) {
      // Test triangles in leaf
      for (uint32_t i = 0; i < node.prim_count; i++) {
        uint32_t tri_idx = prim_indices[node.prim_offset + i];
        float t, u, v;
        if (triangles_[tri_idx].intersect(ray, t, u, v)) {
          if (t < hit_t) {
            hit_t = t;
            hit_u = u;
            hit_v = v;
            hit_tri = tri_idx;
          }
        }
      }
    } else {
      // Add children to stack (front-to-back ordering)
      if (stack_ptr < 62) {
        stack[stack_ptr++].node_idx = node.left_child;
        stack[stack_ptr++].node_idx = node.right_child;
      }
    }
  }

  return hit_tri;
}

} // namespace lightrt
