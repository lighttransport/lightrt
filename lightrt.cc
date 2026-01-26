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
// Quantized Triangle Implementation
// ============================================================================

void QuantizedTriangle::quantize(const Triangle& tri, const Vec3& global_min, const Vec3& global_max) noexcept {
  v0[0] = quantizeFloat(tri.v0.x, global_min.x, global_max.x);
  v0[1] = quantizeFloat(tri.v0.y, global_min.y, global_max.y);
  v0[2] = quantizeFloat(tri.v0.z, global_min.z, global_max.z);

  v1[0] = quantizeFloat(tri.v1.x, global_min.x, global_max.x);
  v1[1] = quantizeFloat(tri.v1.y, global_min.y, global_max.y);
  v1[2] = quantizeFloat(tri.v1.z, global_min.z, global_max.z);

  v2[0] = quantizeFloat(tri.v2.x, global_min.x, global_max.x);
  v2[1] = quantizeFloat(tri.v2.y, global_min.y, global_max.y);
  v2[2] = quantizeFloat(tri.v2.z, global_min.z, global_max.z);
}

Triangle QuantizedTriangle::dequantize(const Vec3& global_min, const Vec3& global_max) const noexcept {
  Triangle tri;
  tri.v0.x = dequantizeFloat(v0[0], global_min.x, global_max.x);
  tri.v0.y = dequantizeFloat(v0[1], global_min.y, global_max.y);
  tri.v0.z = dequantizeFloat(v0[2], global_min.z, global_max.z);

  tri.v1.x = dequantizeFloat(v1[0], global_min.x, global_max.x);
  tri.v1.y = dequantizeFloat(v1[1], global_min.y, global_max.y);
  tri.v1.z = dequantizeFloat(v1[2], global_min.z, global_max.z);

  tri.v2.x = dequantizeFloat(v2[0], global_min.x, global_max.x);
  tri.v2.y = dequantizeFloat(v2[1], global_min.y, global_max.y);
  tri.v2.z = dequantizeFloat(v2[2], global_min.z, global_max.z);

  return tri;
}

bool QuantizedTriangle::intersect(const Ray& ray, const Vec3& global_min, const Vec3& global_max,
                                   float& t, float& u, float& v) const noexcept {
  Triangle tri = dequantize(global_min, global_max);
  return tri.intersect(ray, t, u, v);
}

// ============================================================================
// Gaussian Splat Implementation
// ============================================================================

GaussianSplat::GaussianSplat() noexcept
  : scale(1.0f, 1.0f, 1.0f), opacity(1.0f), sh_degree(SHDegree::DC) {
  rotation[0] = 1.0f;  // w
  rotation[1] = 0.0f;  // x
  rotation[2] = 0.0f;  // y
  rotation[3] = 0.0f;  // z
  std::memset(sh_coeffs, 0, sizeof(sh_coeffs));
}

void GaussianSplat::getCovariance(float cov[6]) const noexcept {
  // Build rotation matrix from quaternion
  float w = rotation[0], x = rotation[1], y = rotation[2], z = rotation[3];

  float R[9];
  R[0] = 1.0f - 2.0f * (y * y + z * z);
  R[1] = 2.0f * (x * y - w * z);
  R[2] = 2.0f * (x * z + w * y);
  R[3] = 2.0f * (x * y + w * z);
  R[4] = 1.0f - 2.0f * (x * x + z * z);
  R[5] = 2.0f * (y * z - w * x);
  R[6] = 2.0f * (x * z - w * y);
  R[7] = 2.0f * (y * z + w * x);
  R[8] = 1.0f - 2.0f * (x * x + y * y);

  // Scale matrix S = diag(scale)
  float sx2 = scale.x * scale.x;
  float sy2 = scale.y * scale.y;
  float sz2 = scale.z * scale.z;

  // Covariance = R * S^2 * R^T
  // Since S is diagonal, S^2 is also diagonal
  // Compute RS first, then RS * R^T
  float RS[9];
  RS[0] = R[0] * sx2; RS[1] = R[1] * sy2; RS[2] = R[2] * sz2;
  RS[3] = R[3] * sx2; RS[4] = R[4] * sy2; RS[5] = R[5] * sz2;
  RS[6] = R[6] * sx2; RS[7] = R[7] * sy2; RS[8] = R[8] * sz2;

  // Cov = RS * R^T (symmetric, store upper triangle)
  cov[0] = RS[0] * R[0] + RS[1] * R[1] + RS[2] * R[2];  // xx
  cov[1] = RS[0] * R[3] + RS[1] * R[4] + RS[2] * R[5];  // xy
  cov[2] = RS[0] * R[6] + RS[1] * R[7] + RS[2] * R[8];  // xz
  cov[3] = RS[3] * R[3] + RS[4] * R[4] + RS[5] * R[5];  // yy
  cov[4] = RS[3] * R[6] + RS[4] * R[7] + RS[5] * R[8];  // yz
  cov[5] = RS[6] * R[6] + RS[7] * R[7] + RS[8] * R[8];  // zz
}

void GaussianSplat::getCovarianceMatrix(float mat[9]) const noexcept {
  float cov[6];
  getCovariance(cov);
  mat[0] = cov[0]; mat[1] = cov[1]; mat[2] = cov[2];
  mat[3] = cov[1]; mat[4] = cov[3]; mat[5] = cov[4];
  mat[6] = cov[2]; mat[7] = cov[4]; mat[8] = cov[5];
}

AABB GaussianSplat::bounds() const noexcept {
  // Conservative 3-sigma bounds
  // For an axis-aligned ellipsoid, the extent along each axis is 3*sigma
  // For a rotated Gaussian, we compute the diagonal of the covariance
  float cov[6];
  getCovariance(cov);

  // 3-sigma extent along each axis
  float extent_x = 3.0f * std::sqrt(cov[0]);
  float extent_y = 3.0f * std::sqrt(cov[3]);
  float extent_z = 3.0f * std::sqrt(cov[5]);

  return AABB(
    Vec3(position.x - extent_x, position.y - extent_y, position.z - extent_z),
    Vec3(position.x + extent_x, position.y + extent_y, position.z + extent_z)
  );
}

bool GaussianSplat::intersect(const Ray& ray, float& t_hit, float& density) const noexcept {
  // Ray-ellipsoid intersection using quadric form
  // The 3-sigma confidence ellipsoid is defined by:
  // (p - center)^T * Cov^(-1) * (p - center) = 9  (for 3-sigma)

  float cov[6];
  getCovariance(cov);

  // Invert the 3x3 symmetric covariance matrix
  // For symmetric matrix: [a b c; b d e; c e f]
  float a = cov[0], b = cov[1], c = cov[2];
  float d = cov[3], e = cov[4], f = cov[5];

  float det = a * (d * f - e * e) - b * (b * f - c * e) + c * (b * e - c * d);
  if (std::abs(det) < kEpsilon) {
    return false;  // Degenerate Gaussian
  }

  float inv_det = 1.0f / det;

  // Inverse covariance (also symmetric)
  float inv_cov[6];
  inv_cov[0] = (d * f - e * e) * inv_det;
  inv_cov[1] = (c * e - b * f) * inv_det;
  inv_cov[2] = (b * e - c * d) * inv_det;
  inv_cov[3] = (a * f - c * c) * inv_det;
  inv_cov[4] = (b * c - a * e) * inv_det;
  inv_cov[5] = (a * d - b * b) * inv_det;

  // Ray: P(t) = O + t*D
  // Ellipsoid: (P - C)^T * M * (P - C) = 9
  // Let V = P - C = O - C + t*D
  // V^T * M * V = 9
  // Expanding: (O-C)^T*M*(O-C) + 2*t*(O-C)^T*M*D + t^2*D^T*M*D = 9

  Vec3 oc = ray.origin - position;

  // Compute quadratic coefficients
  // A = D^T * M * D
  float A = inv_cov[0] * ray.direction.x * ray.direction.x +
            inv_cov[3] * ray.direction.y * ray.direction.y +
            inv_cov[5] * ray.direction.z * ray.direction.z +
            2.0f * inv_cov[1] * ray.direction.x * ray.direction.y +
            2.0f * inv_cov[2] * ray.direction.x * ray.direction.z +
            2.0f * inv_cov[4] * ray.direction.y * ray.direction.z;

  // B = 2 * (O-C)^T * M * D
  float B = 2.0f * (inv_cov[0] * oc.x * ray.direction.x +
                    inv_cov[3] * oc.y * ray.direction.y +
                    inv_cov[5] * oc.z * ray.direction.z +
                    inv_cov[1] * (oc.x * ray.direction.y + oc.y * ray.direction.x) +
                    inv_cov[2] * (oc.x * ray.direction.z + oc.z * ray.direction.x) +
                    inv_cov[4] * (oc.y * ray.direction.z + oc.z * ray.direction.y));

  // C = (O-C)^T * M * (O-C) - 9
  float C = inv_cov[0] * oc.x * oc.x +
            inv_cov[3] * oc.y * oc.y +
            inv_cov[5] * oc.z * oc.z +
            2.0f * inv_cov[1] * oc.x * oc.y +
            2.0f * inv_cov[2] * oc.x * oc.z +
            2.0f * inv_cov[4] * oc.y * oc.z - 9.0f;

  // Solve quadratic
  float discriminant = B * B - 4.0f * A * C;
  if (discriminant < 0) {
    return false;
  }

  float sqrt_disc = std::sqrt(discriminant);
  float t0 = (-B - sqrt_disc) / (2.0f * A);
  float t1 = (-B + sqrt_disc) / (2.0f * A);

  // Find nearest valid intersection
  float t = t0;
  if (t < ray.tmin || t > ray.tmax) {
    t = t1;
    if (t < ray.tmin || t > ray.tmax) {
      return false;
    }
  }

  t_hit = t;

  // Compute density at hit point
  Vec3 hit_point = ray.at(t);
  density = evaluate(hit_point) * opacity;

  return true;
}

float GaussianSplat::evaluate(const Vec3& point) const noexcept {
  // Evaluate Gaussian: exp(-0.5 * (p-c)^T * Cov^(-1) * (p-c))
  float cov[6];
  getCovariance(cov);

  // Invert covariance
  float a = cov[0], b = cov[1], c = cov[2];
  float d = cov[3], e = cov[4], f = cov[5];

  float det = a * (d * f - e * e) - b * (b * f - c * e) + c * (b * e - c * d);
  if (std::abs(det) < kEpsilon) {
    return 0.0f;
  }

  float inv_det = 1.0f / det;

  float inv_cov[6];
  inv_cov[0] = (d * f - e * e) * inv_det;
  inv_cov[1] = (c * e - b * f) * inv_det;
  inv_cov[2] = (b * e - c * d) * inv_det;
  inv_cov[3] = (a * f - c * c) * inv_det;
  inv_cov[4] = (b * c - a * e) * inv_det;
  inv_cov[5] = (a * d - b * b) * inv_det;

  Vec3 diff = point - position;

  float mahal_sq = inv_cov[0] * diff.x * diff.x +
                   inv_cov[3] * diff.y * diff.y +
                   inv_cov[5] * diff.z * diff.z +
                   2.0f * inv_cov[1] * diff.x * diff.y +
                   2.0f * inv_cov[2] * diff.x * diff.z +
                   2.0f * inv_cov[4] * diff.y * diff.z;

  return std::exp(-0.5f * mahal_sq);
}

Vec3 GaussianSplat::getColor(const Vec3& view_dir) const noexcept {
  // Evaluate spherical harmonics for view-dependent color
  Vec3 color(0.0f, 0.0f, 0.0f);

  // DC term (degree 0)
  color.x = sh_coeffs[0];
  color.y = sh_coeffs[1];
  color.z = sh_coeffs[2];

  if (sh_degree >= SHDegree::Degree1) {
    // Degree 1 terms
    float x = view_dir.x, y = view_dir.y, z = view_dir.z;
    color.x += sh_coeffs[3] * y + sh_coeffs[6] * z + sh_coeffs[9] * x;
    color.y += sh_coeffs[4] * y + sh_coeffs[7] * z + sh_coeffs[10] * x;
    color.z += sh_coeffs[5] * y + sh_coeffs[8] * z + sh_coeffs[11] * x;
  }

  if (sh_degree >= SHDegree::Degree2) {
    // Degree 2 terms
    float x = view_dir.x, y = view_dir.y, z = view_dir.z;
    float xy = x * y, yz = y * z, xz = x * z;
    float x2 = x * x, y2 = y * y, z2 = z * z;

    color.x += sh_coeffs[12] * xy + sh_coeffs[15] * yz +
               sh_coeffs[18] * (2.0f * z2 - x2 - y2) +
               sh_coeffs[21] * xz + sh_coeffs[24] * (x2 - y2);
    color.y += sh_coeffs[13] * xy + sh_coeffs[16] * yz +
               sh_coeffs[19] * (2.0f * z2 - x2 - y2) +
               sh_coeffs[22] * xz + sh_coeffs[25] * (x2 - y2);
    color.z += sh_coeffs[14] * xy + sh_coeffs[17] * yz +
               sh_coeffs[20] * (2.0f * z2 - x2 - y2) +
               sh_coeffs[23] * xz + sh_coeffs[26] * (x2 - y2);
  }

  // Clamp to valid range
  color.x = std::max(0.0f, color.x);
  color.y = std::max(0.0f, color.y);
  color.z = std::max(0.0f, color.z);

  return color;
}

// ============================================================================
// Quantized Gaussian Splat Implementation
// ============================================================================

void QuantizedGaussianSplat::quantize(const GaussianSplat& gs, const Vec3& pos_min, const Vec3& pos_max,
                                       float scale_min, float scale_max) noexcept {
  // Quantize position
  position[0] = quantizeFloat(gs.position.x, pos_min.x, pos_max.x);
  position[1] = quantizeFloat(gs.position.y, pos_min.y, pos_max.y);
  position[2] = quantizeFloat(gs.position.z, pos_min.z, pos_max.z);

  // Quantize scale (in log space for better precision)
  float log_scale_min = std::log(scale_min + kEpsilon);
  float log_scale_max = std::log(scale_max + kEpsilon);
  scale[0] = quantizeFloat(std::log(gs.scale.x + kEpsilon), log_scale_min, log_scale_max);
  scale[1] = quantizeFloat(std::log(gs.scale.y + kEpsilon), log_scale_min, log_scale_max);
  scale[2] = quantizeFloat(std::log(gs.scale.z + kEpsilon), log_scale_min, log_scale_max);

  // Quantize quaternion (normalize first)
  float qlen = std::sqrt(gs.rotation[0] * gs.rotation[0] +
                         gs.rotation[1] * gs.rotation[1] +
                         gs.rotation[2] * gs.rotation[2] +
                         gs.rotation[3] * gs.rotation[3]);
  if (qlen > kEpsilon) {
    float inv_qlen = 1.0f / qlen;
    rotation[0] = static_cast<int8_t>(std::max(-127.0f, std::min(127.0f, gs.rotation[0] * inv_qlen * 127.0f)));
    rotation[1] = static_cast<int8_t>(std::max(-127.0f, std::min(127.0f, gs.rotation[1] * inv_qlen * 127.0f)));
    rotation[2] = static_cast<int8_t>(std::max(-127.0f, std::min(127.0f, gs.rotation[2] * inv_qlen * 127.0f)));
    rotation[3] = static_cast<int8_t>(std::max(-127.0f, std::min(127.0f, gs.rotation[3] * inv_qlen * 127.0f)));
  } else {
    rotation[0] = 127;  // Identity quaternion
    rotation[1] = rotation[2] = rotation[3] = 0;
  }

  // Quantize opacity
  opacity = static_cast<uint8_t>(std::max(0.0f, std::min(255.0f, gs.opacity * 255.0f)));

  // Quantize DC color
  color_dc[0] = static_cast<uint8_t>(std::max(0.0f, std::min(255.0f, gs.sh_coeffs[0] * 255.0f)));
  color_dc[1] = static_cast<uint8_t>(std::max(0.0f, std::min(255.0f, gs.sh_coeffs[1] * 255.0f)));
  color_dc[2] = static_cast<uint8_t>(std::max(0.0f, std::min(255.0f, gs.sh_coeffs[2] * 255.0f)));
}

GaussianSplat QuantizedGaussianSplat::dequantize(const Vec3& pos_min, const Vec3& pos_max,
                                                  float scale_min, float scale_max) const noexcept {
  GaussianSplat gs;

  // Dequantize position
  gs.position.x = dequantizeFloat(position[0], pos_min.x, pos_max.x);
  gs.position.y = dequantizeFloat(position[1], pos_min.y, pos_max.y);
  gs.position.z = dequantizeFloat(position[2], pos_min.z, pos_max.z);

  // Dequantize scale (from log space)
  float log_scale_min = std::log(scale_min + kEpsilon);
  float log_scale_max = std::log(scale_max + kEpsilon);
  gs.scale.x = std::exp(dequantizeFloat(scale[0], log_scale_min, log_scale_max));
  gs.scale.y = std::exp(dequantizeFloat(scale[1], log_scale_min, log_scale_max));
  gs.scale.z = std::exp(dequantizeFloat(scale[2], log_scale_min, log_scale_max));

  // Dequantize quaternion and normalize
  gs.rotation[0] = static_cast<float>(rotation[0]) / 127.0f;
  gs.rotation[1] = static_cast<float>(rotation[1]) / 127.0f;
  gs.rotation[2] = static_cast<float>(rotation[2]) / 127.0f;
  gs.rotation[3] = static_cast<float>(rotation[3]) / 127.0f;

  float qlen = std::sqrt(gs.rotation[0] * gs.rotation[0] +
                         gs.rotation[1] * gs.rotation[1] +
                         gs.rotation[2] * gs.rotation[2] +
                         gs.rotation[3] * gs.rotation[3]);
  if (qlen > kEpsilon) {
    float inv_qlen = 1.0f / qlen;
    gs.rotation[0] *= inv_qlen;
    gs.rotation[1] *= inv_qlen;
    gs.rotation[2] *= inv_qlen;
    gs.rotation[3] *= inv_qlen;
  }

  // Dequantize opacity
  gs.opacity = static_cast<float>(opacity) / 255.0f;

  // Dequantize DC color
  gs.sh_coeffs[0] = static_cast<float>(color_dc[0]) / 255.0f;
  gs.sh_coeffs[1] = static_cast<float>(color_dc[1]) / 255.0f;
  gs.sh_coeffs[2] = static_cast<float>(color_dc[2]) / 255.0f;
  gs.sh_degree = SHDegree::DC;

  return gs;
}

bool QuantizedGaussianSplat::intersect(const Ray& ray, const Vec3& pos_min, const Vec3& pos_max,
                                        float scale_min, float scale_max,
                                        float& t_hit, float& density) const noexcept {
  GaussianSplat gs = dequantize(pos_min, pos_max, scale_min, scale_max);
  return gs.intersect(ray, t_hit, density);
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

uint32_t TriangleBVH::traverseWithConfig(const Ray& ray, float& hit_t, float& hit_u, float& hit_v,
                                          const TraversalConfig& config,
                                          TraversalStats* stats) const noexcept {
  const auto& nodes = bvh_.getNodes();
  const auto& prim_indices = bvh_.getPrimitiveIndices();

  if (nodes.empty()) {
    return kInvalidIndex;
  }

  uint32_t hit_tri = kInvalidIndex;
  hit_t = ray.tmax;

  TraversalStats local_stats;
  uint32_t prim_tests = 0;
  const uint32_t max_tests = config.max_prim_tests;

  // Stack-based traversal
  struct StackEntry {
    uint32_t node_idx;
  };

  StackEntry stack[64];
  int stack_ptr = 0;

  stack[stack_ptr++].node_idx = 0;

  while (stack_ptr > 0) {
    // Check if we've hit the primitive test limit
    if (max_tests > 0 && prim_tests >= max_tests) {
      local_stats.terminated_early = true;
      break;
    }

    uint32_t node_idx = stack[--stack_ptr].node_idx;
    const BVHNode& node = nodes[node_idx];
    local_stats.nodes_visited++;

    float tmin, tmax;
    if (!node.bounds.intersectSIMD(ray, tmin, tmax) || tmin > hit_t) {
      continue;
    }

    if (node.isLeaf()) {
      // Test triangles in leaf
      for (uint32_t i = 0; i < node.prim_count; i++) {
        // Check limit before each test
        if (max_tests > 0 && prim_tests >= max_tests) {
          local_stats.terminated_early = true;
          break;
        }

        uint32_t tri_idx = prim_indices[node.prim_offset + i];
        prim_tests++;
        local_stats.prims_tested++;

        float t, u, v;
        if (triangles_[tri_idx].intersect(ray, t, u, v)) {
          if (t < hit_t) {
            hit_t = t;
            hit_u = u;
            hit_v = v;
            hit_tri = tri_idx;
            local_stats.prims_hit++;

            // Early termination for any-hit queries
            if (config.early_termination) {
              if (stats) *stats = local_stats;
              return hit_tri;
            }
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

  if (stats) *stats = local_stats;
  return hit_tri;
}

// ============================================================================
// SBVH Implementation
// Reference: "Spatial Splits in Bounding Volume Hierarchies" (Stich et al., HPG 2009)
// ============================================================================

bool SBVH::build(const std::vector<Triangle>& triangles, const SBVHBuildConfig& config) noexcept {
  if (triangles.empty()) {
    return false;
  }

  triangles_ = triangles;
  config_ = config;

  // Compute scene bounds and create initial references
  scene_bounds_ = AABB();
  std::vector<PrimRef> initial_refs;
  initial_refs.reserve(triangles.size());

  for (uint32_t i = 0; i < triangles.size(); i++) {
    AABB bounds = triangles[i].bounds();
    scene_bounds_.expand(bounds);
    initial_refs.emplace_back(i, bounds);
  }

  // Clear output arrays
  nodes_.clear();
  nodes_.reserve(triangles.size() * 2);
  refs_.clear();
  refs_.reserve(static_cast<size_t>(triangles.size() * config_.max_split_factor));

  // Build recursively
  buildRecursive(initial_refs, 0);

  return true;
}

uint32_t SBVH::buildRecursive(std::vector<PrimRef>& refs, uint32_t depth) noexcept {
  uint32_t num_refs = static_cast<uint32_t>(refs.size());

  // Allocate new node
  uint32_t node_idx = static_cast<uint32_t>(nodes_.size());
  nodes_.emplace_back();

  // Compute node bounds and centroid bounds
  AABB node_bounds;
  AABB centroid_bounds;
  for (const auto& ref : refs) {
    node_bounds.expand(ref.bounds);
    centroid_bounds.expand(ref.bounds.center());
  }
  nodes_[node_idx].bounds = node_bounds;

  // Check if we should create a leaf
  if (num_refs <= config_.max_leaf_size) {
    uint32_t offset = static_cast<uint32_t>(refs_.size());
    refs_.insert(refs_.end(), refs.begin(), refs.end());
    nodes_[node_idx].setLeaf(offset, num_refs);
    return node_idx;
  }

  // Find best object split
  SplitResult object_split = findObjectSplit(refs, node_bounds, centroid_bounds);

  // Compute overlap ratio to decide if we should try spatial splits
  float overlap_area = computeOverlap(object_split.left_bounds, object_split.right_bounds);
  float scene_area = scene_bounds_.surfaceArea();
  float overlap_ratio = scene_area > kEpsilon ? overlap_area / scene_area : 0.0f;

  // Check reference count limit
  bool can_split_spatially = refs_.size() + refs.size() * 2 <
                              static_cast<size_t>(triangles_.size() * config_.max_split_factor);

  // Find best spatial split if overlap is significant and we haven't hit the limit
  SplitResult best_split = object_split;
  if (overlap_ratio > config_.alpha && can_split_spatially) {
    SplitResult spatial_split = findSpatialSplit(refs, node_bounds);
    if (spatial_split.cost < object_split.cost) {
      best_split = spatial_split;
    }
  }

  // Check if split is worth it
  float leaf_cost = config_.intersection_cost * num_refs;
  if (best_split.cost >= leaf_cost || best_split.left_count == 0 || best_split.right_count == 0) {
    // Create leaf
    uint32_t offset = static_cast<uint32_t>(refs_.size());
    refs_.insert(refs_.end(), refs.begin(), refs.end());
    nodes_[node_idx].setLeaf(offset, num_refs);
    return node_idx;
  }

  // Perform the split
  std::vector<PrimRef> left_refs, right_refs;
  left_refs.reserve(best_split.left_count);
  right_refs.reserve(best_split.right_count);

  if (best_split.type == SplitType::Object) {
    performObjectSplit(refs, best_split, left_refs, right_refs);
  } else {
    performSpatialSplit(refs, best_split, left_refs, right_refs);
  }

  // Handle degenerate case
  if (left_refs.empty() || right_refs.empty()) {
    size_t mid = refs.size() / 2;
    left_refs.assign(refs.begin(), refs.begin() + mid);
    right_refs.assign(refs.begin() + mid, refs.end());
  }

  // Clear refs to save memory
  refs.clear();
  refs.shrink_to_fit();

  // Build children
  uint32_t left_child = buildRecursive(left_refs, depth + 1);
  uint32_t right_child = buildRecursive(right_refs, depth + 1);

  nodes_[node_idx].setInterior(left_child, right_child);
  return node_idx;
}

SBVH::SplitResult SBVH::findObjectSplit(
    const std::vector<PrimRef>& refs,
    const AABB& node_bounds,
    const AABB& centroid_bounds) noexcept {

  SplitResult best;
  best.type = SplitType::Object;
  best.cost = kInfinity;
  best.axis = 0;
  best.pos = 0.0f;
  best.left_count = 0;
  best.right_count = 0;

  float inv_node_area = 1.0f / node_bounds.surfaceArea();

  // Try each axis with binned SAH
  for (int axis = 0; axis < 3; axis++) {
    float min_val = axis == 0 ? centroid_bounds.min.x :
                    axis == 1 ? centroid_bounds.min.y : centroid_bounds.min.z;
    float max_val = axis == 0 ? centroid_bounds.max.x :
                    axis == 1 ? centroid_bounds.max.y : centroid_bounds.max.z;

    if (max_val - min_val < kEpsilon) {
      continue;
    }

    // Initialize bins
    std::vector<ObjectBin> bins(config_.num_object_bins);

    // Put references into bins
    float scale = config_.num_object_bins / (max_val - min_val);
    for (const auto& ref : refs) {
      Vec3 centroid = ref.bounds.center();
      float val = axis == 0 ? centroid.x : axis == 1 ? centroid.y : centroid.z;

      uint32_t bin_idx = static_cast<uint32_t>((val - min_val) * scale);
      bin_idx = std::min(bin_idx, config_.num_object_bins - 1);

      bins[bin_idx].bounds.expand(ref.bounds);
      bins[bin_idx].count++;
    }

    // Sweep from left to compute prefix bounds/counts
    std::vector<AABB> left_bounds(config_.num_object_bins);
    std::vector<uint32_t> left_counts(config_.num_object_bins);
    AABB running_bounds;
    uint32_t running_count = 0;

    for (uint32_t i = 0; i < config_.num_object_bins - 1; i++) {
      running_bounds.expand(bins[i].bounds);
      running_count += bins[i].count;
      left_bounds[i] = running_bounds;
      left_counts[i] = running_count;
    }

    // Sweep from right to compute costs
    running_bounds = AABB();
    running_count = 0;

    for (uint32_t i = config_.num_object_bins - 1; i > 0; i--) {
      running_bounds.expand(bins[i].bounds);
      running_count += bins[i].count;

      uint32_t left_count = left_counts[i - 1];
      uint32_t right_count = running_count;

      if (left_count == 0 || right_count == 0) {
        continue;
      }

      float left_area = left_bounds[i - 1].surfaceArea() * inv_node_area;
      float right_area = running_bounds.surfaceArea() * inv_node_area;

      float cost = config_.traversal_cost +
                   config_.intersection_cost * (left_count * left_area + right_count * right_area);

      if (cost < best.cost) {
        best.cost = cost;
        best.axis = axis;
        best.pos = min_val + (max_val - min_val) * (static_cast<float>(i) / config_.num_object_bins);
        best.left_bounds = left_bounds[i - 1];
        best.right_bounds = running_bounds;
        best.left_count = left_count;
        best.right_count = right_count;
      }
    }
  }

  return best;
}

SBVH::SplitResult SBVH::findSpatialSplit(
    const std::vector<PrimRef>& refs,
    const AABB& node_bounds) noexcept {

  SplitResult best;
  best.type = SplitType::Spatial;
  best.cost = kInfinity;
  best.axis = 0;
  best.pos = 0.0f;
  best.left_count = 0;
  best.right_count = 0;

  float inv_node_area = 1.0f / node_bounds.surfaceArea();

  // Try each axis
  for (int axis = 0; axis < 3; axis++) {
    float min_val = axis == 0 ? node_bounds.min.x :
                    axis == 1 ? node_bounds.min.y : node_bounds.min.z;
    float max_val = axis == 0 ? node_bounds.max.x :
                    axis == 1 ? node_bounds.max.y : node_bounds.max.z;

    if (max_val - min_val < kEpsilon) {
      continue;
    }

    // Initialize spatial bins
    std::vector<SpatialBin> bins(config_.num_spatial_bins);
    float bin_size = (max_val - min_val) / config_.num_spatial_bins;

    // Fill bins with clipped triangle bounds
    for (const auto& ref : refs) {
      // Find bins this reference overlaps
      float ref_min = axis == 0 ? ref.bounds.min.x :
                      axis == 1 ? ref.bounds.min.y : ref.bounds.min.z;
      float ref_max = axis == 0 ? ref.bounds.max.x :
                      axis == 1 ? ref.bounds.max.y : ref.bounds.max.z;

      uint32_t first_bin = static_cast<uint32_t>((ref_min - min_val) / bin_size);
      uint32_t last_bin = static_cast<uint32_t>((ref_max - min_val) / bin_size);
      first_bin = std::min(first_bin, config_.num_spatial_bins - 1);
      last_bin = std::min(last_bin, config_.num_spatial_bins - 1);

      bins[first_bin].enter++;
      bins[last_bin].exit++;

      // Clip triangle to each overlapping bin
      const Triangle& tri = triangles_[ref.prim_id];
      for (uint32_t b = first_bin; b <= last_bin; b++) {
        float plane_left = min_val + b * bin_size;
        float plane_right = min_val + (b + 1) * bin_size;

        // Clip to left plane
        AABB clipped = ref.bounds;
        if (axis == 0) {
          clipped.min.x = std::max(clipped.min.x, plane_left);
          clipped.max.x = std::min(clipped.max.x, plane_right);
        } else if (axis == 1) {
          clipped.min.y = std::max(clipped.min.y, plane_left);
          clipped.max.y = std::min(clipped.max.y, plane_right);
        } else {
          clipped.min.z = std::max(clipped.min.z, plane_left);
          clipped.max.z = std::min(clipped.max.z, plane_right);
        }

        // Refine with actual triangle clipping for tighter bounds
        AABB tri_clipped = clipTriangleToPlane(tri, axis, plane_left, false);
        AABB tri_clipped2 = clipTriangleToPlane(tri, axis, plane_right, true);

        // Intersect all bounds
        clipped.min.x = std::max(clipped.min.x, std::max(tri_clipped.min.x, tri_clipped2.min.x));
        clipped.min.y = std::max(clipped.min.y, std::max(tri_clipped.min.y, tri_clipped2.min.y));
        clipped.min.z = std::max(clipped.min.z, std::max(tri_clipped.min.z, tri_clipped2.min.z));
        clipped.max.x = std::min(clipped.max.x, std::min(tri_clipped.max.x, tri_clipped2.max.x));
        clipped.max.y = std::min(clipped.max.y, std::min(tri_clipped.max.y, tri_clipped2.max.y));
        clipped.max.z = std::min(clipped.max.z, std::min(tri_clipped.max.z, tri_clipped2.max.z));

        bins[b].bounds.expand(clipped);
      }
    }

    // Sweep from left
    std::vector<AABB> left_bounds(config_.num_spatial_bins);
    std::vector<uint32_t> left_counts(config_.num_spatial_bins);
    AABB running_bounds;
    uint32_t running_count = 0;

    for (uint32_t i = 0; i < config_.num_spatial_bins - 1; i++) {
      running_bounds.expand(bins[i].bounds);
      running_count += bins[i].enter;
      left_bounds[i] = running_bounds;
      left_counts[i] = running_count;
    }

    // Sweep from right and compute costs
    running_bounds = AABB();
    running_count = 0;

    for (uint32_t i = config_.num_spatial_bins - 1; i > 0; i--) {
      running_count += bins[i].exit;
      running_bounds.expand(bins[i].bounds);

      uint32_t left_count = left_counts[i - 1];
      uint32_t right_count = running_count;

      if (left_count == 0 || right_count == 0) {
        continue;
      }

      float left_area = left_bounds[i - 1].surfaceArea() * inv_node_area;
      float right_area = running_bounds.surfaceArea() * inv_node_area;

      float cost = config_.traversal_cost +
                   config_.intersection_cost * (left_count * left_area + right_count * right_area);

      if (cost < best.cost) {
        best.cost = cost;
        best.axis = axis;
        best.pos = min_val + (max_val - min_val) * (static_cast<float>(i) / config_.num_spatial_bins);
        best.left_bounds = left_bounds[i - 1];
        best.right_bounds = running_bounds;
        best.left_count = left_count;
        best.right_count = right_count;
      }
    }
  }

  return best;
}

void SBVH::performObjectSplit(
    std::vector<PrimRef>& refs,
    const SplitResult& split,
    std::vector<PrimRef>& left_refs,
    std::vector<PrimRef>& right_refs) noexcept {

  for (auto& ref : refs) {
    Vec3 centroid = ref.bounds.center();
    float val = split.axis == 0 ? centroid.x : split.axis == 1 ? centroid.y : centroid.z;

    if (val < split.pos) {
      left_refs.push_back(std::move(ref));
    } else {
      right_refs.push_back(std::move(ref));
    }
  }
}

void SBVH::performSpatialSplit(
    std::vector<PrimRef>& refs,
    const SplitResult& split,
    std::vector<PrimRef>& left_refs,
    std::vector<PrimRef>& right_refs) noexcept {

  for (const auto& ref : refs) {
    float ref_min = split.axis == 0 ? ref.bounds.min.x :
                    split.axis == 1 ? ref.bounds.min.y : ref.bounds.min.z;
    float ref_max = split.axis == 0 ? ref.bounds.max.x :
                    split.axis == 1 ? ref.bounds.max.y : ref.bounds.max.z;

    // Reference is entirely on left
    if (ref_max <= split.pos) {
      left_refs.push_back(ref);
      continue;
    }

    // Reference is entirely on right
    if (ref_min >= split.pos) {
      right_refs.push_back(ref);
      continue;
    }

    // Reference straddles the split plane - clip and duplicate
    const Triangle& tri = triangles_[ref.prim_id];

    // Left portion
    AABB left_bounds = clipTriangleToPlane(tri, split.axis, split.pos, true);
    // Intersect with reference bounds
    left_bounds.min.x = std::max(left_bounds.min.x, ref.bounds.min.x);
    left_bounds.min.y = std::max(left_bounds.min.y, ref.bounds.min.y);
    left_bounds.min.z = std::max(left_bounds.min.z, ref.bounds.min.z);
    left_bounds.max.x = std::min(left_bounds.max.x, ref.bounds.max.x);
    left_bounds.max.y = std::min(left_bounds.max.y, ref.bounds.max.y);
    left_bounds.max.z = std::min(left_bounds.max.z, ref.bounds.max.z);

    if (left_bounds.min.x <= left_bounds.max.x &&
        left_bounds.min.y <= left_bounds.max.y &&
        left_bounds.min.z <= left_bounds.max.z) {
      left_refs.emplace_back(ref.prim_id, left_bounds);
    }

    // Right portion
    AABB right_bounds = clipTriangleToPlane(tri, split.axis, split.pos, false);
    right_bounds.min.x = std::max(right_bounds.min.x, ref.bounds.min.x);
    right_bounds.min.y = std::max(right_bounds.min.y, ref.bounds.min.y);
    right_bounds.min.z = std::max(right_bounds.min.z, ref.bounds.min.z);
    right_bounds.max.x = std::min(right_bounds.max.x, ref.bounds.max.x);
    right_bounds.max.y = std::min(right_bounds.max.y, ref.bounds.max.y);
    right_bounds.max.z = std::min(right_bounds.max.z, ref.bounds.max.z);

    if (right_bounds.min.x <= right_bounds.max.x &&
        right_bounds.min.y <= right_bounds.max.y &&
        right_bounds.min.z <= right_bounds.max.z) {
      right_refs.emplace_back(ref.prim_id, right_bounds);
    }
  }
}

AABB SBVH::clipTriangleToPlane(const Triangle& tri, int axis, float pos, bool left) const noexcept {
  // Clip triangle to half-space and return tight bounds
  AABB result;

  const Vec3* verts[3] = {&tri.v0, &tri.v1, &tri.v2};

  // Check each vertex
  for (int i = 0; i < 3; i++) {
    float v = axis == 0 ? verts[i]->x : axis == 1 ? verts[i]->y : verts[i]->z;

    if ((left && v <= pos) || (!left && v >= pos)) {
      result.expand(*verts[i]);
    }
  }

  // Check each edge for plane intersections
  for (int i = 0; i < 3; i++) {
    const Vec3& v0 = *verts[i];
    const Vec3& v1 = *verts[(i + 1) % 3];

    float t0 = axis == 0 ? v0.x : axis == 1 ? v0.y : v0.z;
    float t1 = axis == 0 ? v1.x : axis == 1 ? v1.y : v1.z;

    // Edge crosses plane
    if ((t0 < pos && t1 > pos) || (t0 > pos && t1 < pos)) {
      float t = (pos - t0) / (t1 - t0);
      Vec3 intersection = v0 + (v1 - v0) * t;
      result.expand(intersection);
    }
  }

  return result;
}

float SBVH::computeOverlap(const AABB& a, const AABB& b) const noexcept {
  // Compute surface area of intersection
  float x_overlap = std::max(0.0f, std::min(a.max.x, b.max.x) - std::max(a.min.x, b.min.x));
  float y_overlap = std::max(0.0f, std::min(a.max.y, b.max.y) - std::max(a.min.y, b.min.y));
  float z_overlap = std::max(0.0f, std::min(a.max.z, b.max.z) - std::max(a.min.z, b.min.z));

  if (x_overlap <= 0.0f || y_overlap <= 0.0f || z_overlap <= 0.0f) {
    return 0.0f;
  }

  return 2.0f * (x_overlap * y_overlap + y_overlap * z_overlap + z_overlap * x_overlap);
}

uint32_t SBVH::traverse(const Ray& ray, float& hit_t, float& hit_u, float& hit_v) const noexcept {
  if (nodes_.empty()) {
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
    const BVHNode& node = nodes_[node_idx];

    float tmin, tmax;
    if (!node.bounds.intersectSIMD(ray, tmin, tmax) || tmin > hit_t) {
      continue;
    }

    if (node.isLeaf()) {
      // Test triangles in leaf (using references)
      for (uint32_t i = 0; i < node.prim_count; i++) {
        const PrimRef& ref = refs_[node.prim_offset + i];

        // Early out: check if reference bounds are hit
        float ref_tmin, ref_tmax;
        if (!ref.bounds.intersect(ray, ref_tmin, ref_tmax) || ref_tmin > hit_t) {
          continue;
        }

        float t, u, v;
        if (triangles_[ref.prim_id].intersect(ray, t, u, v)) {
          if (t < hit_t) {
            hit_t = t;
            hit_u = u;
            hit_v = v;
            hit_tri = ref.prim_id;
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

  return hit_tri;
}

uint32_t SBVH::traverseWithConfig(const Ray& ray, float& hit_t, float& hit_u, float& hit_v,
                                   const TraversalConfig& config,
                                   TraversalStats* stats) const noexcept {
  if (nodes_.empty()) {
    return kInvalidIndex;
  }

  uint32_t hit_tri = kInvalidIndex;
  hit_t = ray.tmax;

  TraversalStats local_stats;
  uint32_t prim_tests = 0;
  const uint32_t max_tests = config.max_prim_tests;

  // Optional mailbox for avoiding duplicate tests
  // In SBVH, the same primitive can appear in multiple leaves
  std::vector<uint64_t> mailbox_bitset;
  std::vector<uint32_t> mailbox_hash;
  const uint32_t num_prims = static_cast<uint32_t>(triangles_.size());
  const bool use_mailbox = config.use_mailboxing && num_prims > 0;

  if (use_mailbox) {
    if (num_prims <= 65536) {
      mailbox_bitset.resize((num_prims + 63) / 64, 0);
    } else {
      mailbox_hash.resize(std::max(num_prims / 4, 256u), kInvalidIndex);
    }
  }

  auto testAndMarkMailbox = [&](uint32_t prim_id) -> bool {
    if (!use_mailbox) return false;

    if (num_prims <= 65536) {
      uint32_t word = prim_id / 64;
      uint64_t bit = 1ULL << (prim_id % 64);
      if (mailbox_bitset[word] & bit) {
        return true;  // Already tested
      }
      mailbox_bitset[word] |= bit;
      return false;
    } else {
      uint32_t idx = prim_id % mailbox_hash.size();
      for (uint32_t i = 0; i < 16; i++) {  // Limited probing
        uint32_t probe = (idx + i) % mailbox_hash.size();
        if (mailbox_hash[probe] == prim_id) {
          return true;  // Already tested
        }
        if (mailbox_hash[probe] == kInvalidIndex) {
          mailbox_hash[probe] = prim_id;
          return false;
        }
      }
      return false;  // Probe limit reached, test anyway
    }
  };

  // Stack-based traversal
  struct StackEntry {
    uint32_t node_idx;
  };

  StackEntry stack[64];
  int stack_ptr = 0;

  stack[stack_ptr++].node_idx = 0;

  while (stack_ptr > 0) {
    // Check if we've hit the primitive test limit
    if (max_tests > 0 && prim_tests >= max_tests) {
      local_stats.terminated_early = true;
      break;
    }

    uint32_t node_idx = stack[--stack_ptr].node_idx;
    const BVHNode& node = nodes_[node_idx];
    local_stats.nodes_visited++;

    float tmin, tmax;
    if (!node.bounds.intersectSIMD(ray, tmin, tmax) || tmin > hit_t) {
      continue;
    }

    if (node.isLeaf()) {
      // Test triangles in leaf (using references)
      for (uint32_t i = 0; i < node.prim_count; i++) {
        // Check limit before each test
        if (max_tests > 0 && prim_tests >= max_tests) {
          local_stats.terminated_early = true;
          break;
        }

        const PrimRef& ref = refs_[node.prim_offset + i];

        // Mailboxing: skip if already tested
        if (testAndMarkMailbox(ref.prim_id)) {
          continue;
        }

        // Early out: check if reference bounds are hit
        float ref_tmin, ref_tmax;
        if (!ref.bounds.intersect(ray, ref_tmin, ref_tmax) || ref_tmin > hit_t) {
          continue;
        }

        prim_tests++;
        local_stats.prims_tested++;

        float t, u, v;
        if (triangles_[ref.prim_id].intersect(ray, t, u, v)) {
          if (t < hit_t) {
            hit_t = t;
            hit_u = u;
            hit_v = v;
            hit_tri = ref.prim_id;
            local_stats.prims_hit++;

            // Early termination for any-hit queries
            if (config.early_termination) {
              if (stats) *stats = local_stats;
              return hit_tri;
            }
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

  if (stats) *stats = local_stats;
  return hit_tri;
}

SBVH::Stats SBVH::getStats() const noexcept {
  Stats stats = {};

  if (nodes_.empty()) {
    return stats;
  }

  stats.num_primitives = static_cast<uint32_t>(triangles_.size());
  stats.num_references = static_cast<uint32_t>(refs_.size());
  stats.split_ratio = static_cast<float>(stats.num_references) / stats.num_primitives;

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
// SBVHGeneric Implementation (AABB-based)
// ============================================================================

bool SBVHGeneric::build(const std::vector<AABB>& prim_aabbs, const SBVHBuildConfig& config) noexcept {
  if (prim_aabbs.empty()) {
    return false;
  }

  prim_aabbs_ = prim_aabbs;
  config_ = config;

  // Compute scene bounds and create initial references
  scene_bounds_ = AABB();
  std::vector<PrimRef> initial_refs;
  initial_refs.reserve(prim_aabbs.size());

  for (uint32_t i = 0; i < prim_aabbs.size(); i++) {
    scene_bounds_.expand(prim_aabbs[i]);
    initial_refs.emplace_back(i, prim_aabbs[i]);
  }

  nodes_.clear();
  nodes_.reserve(prim_aabbs.size() * 2);
  refs_.clear();
  refs_.reserve(static_cast<size_t>(prim_aabbs.size() * config_.max_split_factor));

  buildRecursive(initial_refs, 0);

  return true;
}

uint32_t SBVHGeneric::buildRecursive(std::vector<PrimRef>& refs, uint32_t depth) noexcept {
  uint32_t num_refs = static_cast<uint32_t>(refs.size());

  uint32_t node_idx = static_cast<uint32_t>(nodes_.size());
  nodes_.emplace_back();

  AABB node_bounds;
  AABB centroid_bounds;
  for (const auto& ref : refs) {
    node_bounds.expand(ref.bounds);
    centroid_bounds.expand(ref.bounds.center());
  }
  nodes_[node_idx].bounds = node_bounds;

  if (num_refs <= config_.max_leaf_size) {
    uint32_t offset = static_cast<uint32_t>(refs_.size());
    refs_.insert(refs_.end(), refs.begin(), refs.end());
    nodes_[node_idx].setLeaf(offset, num_refs);
    return node_idx;
  }

  SplitResult object_split = findObjectSplit(refs, node_bounds, centroid_bounds);

  float overlap_area = computeOverlap(object_split.left_bounds, object_split.right_bounds);
  float scene_area = scene_bounds_.surfaceArea();
  float overlap_ratio = scene_area > kEpsilon ? overlap_area / scene_area : 0.0f;

  bool can_split_spatially = refs_.size() + refs.size() * 2 <
                              static_cast<size_t>(prim_aabbs_.size() * config_.max_split_factor);

  SplitResult best_split = object_split;
  if (overlap_ratio > config_.alpha && can_split_spatially) {
    SplitResult spatial_split = findSpatialSplit(refs, node_bounds);
    if (spatial_split.cost < object_split.cost) {
      best_split = spatial_split;
    }
  }

  float leaf_cost = config_.intersection_cost * num_refs;
  if (best_split.cost >= leaf_cost || best_split.left_count == 0 || best_split.right_count == 0) {
    uint32_t offset = static_cast<uint32_t>(refs_.size());
    refs_.insert(refs_.end(), refs.begin(), refs.end());
    nodes_[node_idx].setLeaf(offset, num_refs);
    return node_idx;
  }

  std::vector<PrimRef> left_refs, right_refs;
  left_refs.reserve(best_split.left_count);
  right_refs.reserve(best_split.right_count);

  if (best_split.type == SplitType::Object) {
    performObjectSplit(refs, best_split, left_refs, right_refs);
  } else {
    performSpatialSplit(refs, best_split, left_refs, right_refs);
  }

  if (left_refs.empty() || right_refs.empty()) {
    size_t mid = refs.size() / 2;
    left_refs.assign(refs.begin(), refs.begin() + mid);
    right_refs.assign(refs.begin() + mid, refs.end());
  }

  refs.clear();
  refs.shrink_to_fit();

  uint32_t left_child = buildRecursive(left_refs, depth + 1);
  uint32_t right_child = buildRecursive(right_refs, depth + 1);

  nodes_[node_idx].setInterior(left_child, right_child);
  return node_idx;
}

SBVHGeneric::SplitResult SBVHGeneric::findObjectSplit(
    const std::vector<PrimRef>& refs,
    const AABB& node_bounds,
    const AABB& centroid_bounds) noexcept {

  SplitResult best;
  best.type = SplitType::Object;
  best.cost = kInfinity;
  best.axis = 0;
  best.pos = 0.0f;
  best.left_count = 0;
  best.right_count = 0;

  float inv_node_area = 1.0f / node_bounds.surfaceArea();

  for (int axis = 0; axis < 3; axis++) {
    float min_val = axis == 0 ? centroid_bounds.min.x :
                    axis == 1 ? centroid_bounds.min.y : centroid_bounds.min.z;
    float max_val = axis == 0 ? centroid_bounds.max.x :
                    axis == 1 ? centroid_bounds.max.y : centroid_bounds.max.z;

    if (max_val - min_val < kEpsilon) {
      continue;
    }

    std::vector<ObjectBin> bins(config_.num_object_bins);

    float scale = config_.num_object_bins / (max_val - min_val);
    for (const auto& ref : refs) {
      Vec3 centroid = ref.bounds.center();
      float val = axis == 0 ? centroid.x : axis == 1 ? centroid.y : centroid.z;

      uint32_t bin_idx = static_cast<uint32_t>((val - min_val) * scale);
      bin_idx = std::min(bin_idx, config_.num_object_bins - 1);

      bins[bin_idx].bounds.expand(ref.bounds);
      bins[bin_idx].count++;
    }

    std::vector<AABB> left_bounds(config_.num_object_bins);
    std::vector<uint32_t> left_counts(config_.num_object_bins);
    AABB running_bounds;
    uint32_t running_count = 0;

    for (uint32_t i = 0; i < config_.num_object_bins - 1; i++) {
      running_bounds.expand(bins[i].bounds);
      running_count += bins[i].count;
      left_bounds[i] = running_bounds;
      left_counts[i] = running_count;
    }

    running_bounds = AABB();
    running_count = 0;

    for (uint32_t i = config_.num_object_bins - 1; i > 0; i--) {
      running_bounds.expand(bins[i].bounds);
      running_count += bins[i].count;

      uint32_t left_count = left_counts[i - 1];
      uint32_t right_count = running_count;

      if (left_count == 0 || right_count == 0) {
        continue;
      }

      float left_area = left_bounds[i - 1].surfaceArea() * inv_node_area;
      float right_area = running_bounds.surfaceArea() * inv_node_area;

      float cost = config_.traversal_cost +
                   config_.intersection_cost * (left_count * left_area + right_count * right_area);

      if (cost < best.cost) {
        best.cost = cost;
        best.axis = axis;
        best.pos = min_val + (max_val - min_val) * (static_cast<float>(i) / config_.num_object_bins);
        best.left_bounds = left_bounds[i - 1];
        best.right_bounds = running_bounds;
        best.left_count = left_count;
        best.right_count = right_count;
      }
    }
  }

  return best;
}

SBVHGeneric::SplitResult SBVHGeneric::findSpatialSplit(
    const std::vector<PrimRef>& refs,
    const AABB& node_bounds) noexcept {

  SplitResult best;
  best.type = SplitType::Spatial;
  best.cost = kInfinity;
  best.axis = 0;
  best.pos = 0.0f;
  best.left_count = 0;
  best.right_count = 0;

  float inv_node_area = 1.0f / node_bounds.surfaceArea();

  for (int axis = 0; axis < 3; axis++) {
    float min_val = axis == 0 ? node_bounds.min.x :
                    axis == 1 ? node_bounds.min.y : node_bounds.min.z;
    float max_val = axis == 0 ? node_bounds.max.x :
                    axis == 1 ? node_bounds.max.y : node_bounds.max.z;

    if (max_val - min_val < kEpsilon) {
      continue;
    }

    std::vector<SpatialBin> bins(config_.num_spatial_bins);
    float bin_size = (max_val - min_val) / config_.num_spatial_bins;

    for (const auto& ref : refs) {
      float ref_min = axis == 0 ? ref.bounds.min.x :
                      axis == 1 ? ref.bounds.min.y : ref.bounds.min.z;
      float ref_max = axis == 0 ? ref.bounds.max.x :
                      axis == 1 ? ref.bounds.max.y : ref.bounds.max.z;

      uint32_t first_bin = static_cast<uint32_t>((ref_min - min_val) / bin_size);
      uint32_t last_bin = static_cast<uint32_t>((ref_max - min_val) / bin_size);
      first_bin = std::min(first_bin, config_.num_spatial_bins - 1);
      last_bin = std::min(last_bin, config_.num_spatial_bins - 1);

      bins[first_bin].enter++;
      bins[last_bin].exit++;

      for (uint32_t b = first_bin; b <= last_bin; b++) {
        float plane_left = min_val + b * bin_size;
        float plane_right = min_val + (b + 1) * bin_size;

        AABB clipped = clipAABBToPlane(ref.bounds, axis, plane_left, false);
        AABB clipped2 = clipAABBToPlane(clipped, axis, plane_right, true);
        bins[b].bounds.expand(clipped2);
      }
    }

    std::vector<AABB> left_bounds(config_.num_spatial_bins);
    std::vector<uint32_t> left_counts(config_.num_spatial_bins);
    AABB running_bounds;
    uint32_t running_count = 0;

    for (uint32_t i = 0; i < config_.num_spatial_bins - 1; i++) {
      running_bounds.expand(bins[i].bounds);
      running_count += bins[i].enter;
      left_bounds[i] = running_bounds;
      left_counts[i] = running_count;
    }

    running_bounds = AABB();
    running_count = 0;

    for (uint32_t i = config_.num_spatial_bins - 1; i > 0; i--) {
      running_count += bins[i].exit;
      running_bounds.expand(bins[i].bounds);

      uint32_t left_count = left_counts[i - 1];
      uint32_t right_count = running_count;

      if (left_count == 0 || right_count == 0) {
        continue;
      }

      float left_area = left_bounds[i - 1].surfaceArea() * inv_node_area;
      float right_area = running_bounds.surfaceArea() * inv_node_area;

      float cost = config_.traversal_cost +
                   config_.intersection_cost * (left_count * left_area + right_count * right_area);

      if (cost < best.cost) {
        best.cost = cost;
        best.axis = axis;
        best.pos = min_val + (max_val - min_val) * (static_cast<float>(i) / config_.num_spatial_bins);
        best.left_bounds = left_bounds[i - 1];
        best.right_bounds = running_bounds;
        best.left_count = left_count;
        best.right_count = right_count;
      }
    }
  }

  return best;
}

void SBVHGeneric::performObjectSplit(
    std::vector<PrimRef>& refs,
    const SplitResult& split,
    std::vector<PrimRef>& left_refs,
    std::vector<PrimRef>& right_refs) noexcept {

  for (auto& ref : refs) {
    Vec3 centroid = ref.bounds.center();
    float val = split.axis == 0 ? centroid.x : split.axis == 1 ? centroid.y : centroid.z;

    if (val < split.pos) {
      left_refs.push_back(std::move(ref));
    } else {
      right_refs.push_back(std::move(ref));
    }
  }
}

void SBVHGeneric::performSpatialSplit(
    std::vector<PrimRef>& refs,
    const SplitResult& split,
    std::vector<PrimRef>& left_refs,
    std::vector<PrimRef>& right_refs) noexcept {

  for (const auto& ref : refs) {
    float ref_min = split.axis == 0 ? ref.bounds.min.x :
                    split.axis == 1 ? ref.bounds.min.y : ref.bounds.min.z;
    float ref_max = split.axis == 0 ? ref.bounds.max.x :
                    split.axis == 1 ? ref.bounds.max.y : ref.bounds.max.z;

    if (ref_max <= split.pos) {
      left_refs.push_back(ref);
      continue;
    }

    if (ref_min >= split.pos) {
      right_refs.push_back(ref);
      continue;
    }

    // Split the reference
    AABB left_bounds = clipAABBToPlane(ref.bounds, split.axis, split.pos, true);
    AABB right_bounds = clipAABBToPlane(ref.bounds, split.axis, split.pos, false);

    if (left_bounds.min.x <= left_bounds.max.x &&
        left_bounds.min.y <= left_bounds.max.y &&
        left_bounds.min.z <= left_bounds.max.z) {
      left_refs.emplace_back(ref.prim_id, left_bounds);
    }

    if (right_bounds.min.x <= right_bounds.max.x &&
        right_bounds.min.y <= right_bounds.max.y &&
        right_bounds.min.z <= right_bounds.max.z) {
      right_refs.emplace_back(ref.prim_id, right_bounds);
    }
  }
}

AABB SBVHGeneric::clipAABBToPlane(const AABB& aabb, int axis, float pos, bool left) const noexcept {
  AABB result = aabb;

  if (left) {
    // Keep left half (min to pos)
    if (axis == 0) result.max.x = std::min(result.max.x, pos);
    else if (axis == 1) result.max.y = std::min(result.max.y, pos);
    else result.max.z = std::min(result.max.z, pos);
  } else {
    // Keep right half (pos to max)
    if (axis == 0) result.min.x = std::max(result.min.x, pos);
    else if (axis == 1) result.min.y = std::max(result.min.y, pos);
    else result.min.z = std::max(result.min.z, pos);
  }

  return result;
}

float SBVHGeneric::computeOverlap(const AABB& a, const AABB& b) const noexcept {
  float x_overlap = std::max(0.0f, std::min(a.max.x, b.max.x) - std::max(a.min.x, b.min.x));
  float y_overlap = std::max(0.0f, std::min(a.max.y, b.max.y) - std::max(a.min.y, b.min.y));
  float z_overlap = std::max(0.0f, std::min(a.max.z, b.max.z) - std::max(a.min.z, b.min.z));

  if (x_overlap <= 0.0f || y_overlap <= 0.0f || z_overlap <= 0.0f) {
    return 0.0f;
  }

  return 2.0f * (x_overlap * y_overlap + y_overlap * z_overlap + z_overlap * x_overlap);
}

uint32_t SBVHGeneric::traverse(const Ray& ray, float& hit_t) const noexcept {
  if (nodes_.empty()) {
    return kInvalidIndex;
  }

  uint32_t hit_prim = kInvalidIndex;
  hit_t = ray.tmax;

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
      for (uint32_t i = 0; i < node.prim_count; i++) {
        const PrimRef& ref = refs_[node.prim_offset + i];

        float prim_tmin, prim_tmax;
        if (prim_aabbs_[ref.prim_id].intersect(ray, prim_tmin, prim_tmax)) {
          if (prim_tmin < hit_t && prim_tmin > ray.tmin) {
            hit_t = prim_tmin;
            hit_prim = ref.prim_id;
          }
        }
      }
    } else {
      if (stack_ptr < 62) {
        stack[stack_ptr++].node_idx = node.left_child;
        stack[stack_ptr++].node_idx = node.right_child;
      }
    }
  }

  return hit_prim;
}

SBVHGeneric::Stats SBVHGeneric::getStats() const noexcept {
  Stats stats = {};

  if (nodes_.empty()) {
    return stats;
  }

  stats.num_primitives = static_cast<uint32_t>(prim_aabbs_.size());
  stats.num_references = static_cast<uint32_t>(refs_.size());
  stats.split_ratio = static_cast<float>(stats.num_references) / stats.num_primitives;

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
// MMapTriangleBVH Implementation
// ============================================================================

MMapTriangleBVH::MMapTriangleBVH() noexcept
  : triangles_(nullptr)
  , triangle_count_(0)
  , is_external_(true)
  , index_bytes_(4) {}

uint32_t MMapTriangleBVH::getPrimIndex(uint32_t offset) const noexcept {
  switch (index_bytes_) {
    case 1:
      return prim_indices_storage_[offset];
    case 2:
      return *reinterpret_cast<const uint16_t*>(&prim_indices_storage_[offset * 2]);
    case 4:
    default:
      return *reinterpret_cast<const uint32_t*>(&prim_indices_storage_[offset * 4]);
  }
}

void MMapTriangleBVH::reserveIndices(uint32_t count) noexcept {
  prim_indices_storage_.reserve(count * index_bytes_);
}

void MMapTriangleBVH::pushIndex(uint32_t index) noexcept {
  switch (index_bytes_) {
    case 1:
      prim_indices_storage_.push_back(static_cast<uint8_t>(index));
      break;
    case 2: {
      uint16_t idx16 = static_cast<uint16_t>(index);
      prim_indices_storage_.push_back(static_cast<uint8_t>(idx16 & 0xFF));
      prim_indices_storage_.push_back(static_cast<uint8_t>(idx16 >> 8));
      break;
    }
    case 4:
    default: {
      prim_indices_storage_.push_back(static_cast<uint8_t>(index & 0xFF));
      prim_indices_storage_.push_back(static_cast<uint8_t>((index >> 8) & 0xFF));
      prim_indices_storage_.push_back(static_cast<uint8_t>((index >> 16) & 0xFF));
      prim_indices_storage_.push_back(static_cast<uint8_t>((index >> 24) & 0xFF));
      break;
    }
  }
}

bool MMapTriangleBVH::build(const Triangle* triangles, uint32_t count,
                            const MMapBVHConfig& config) noexcept {
  if (!triangles || count == 0) {
    return false;
  }

  triangles_ = triangles;
  triangle_count_ = count;
  is_external_ = true;
  config_ = config;

  // Determine index precision
  if (config.index_precision == IndexPrecision::Auto) {
    if (count <= 255) {
      index_bytes_ = 1;
    } else if (count <= 65535) {
      index_bytes_ = 2;
    } else {
      index_bytes_ = 4;
    }
  } else {
    index_bytes_ = static_cast<uint8_t>(config.index_precision);
  }

  // Compute scene bounds and primitive bounds
  scene_bounds_ = AABB();
  std::vector<AABB> prim_bounds(count);

  for (uint32_t i = 0; i < count; i++) {
    prim_bounds[i] = triangles[i].bounds();
    scene_bounds_.expand(prim_bounds[i]);
  }

  // Slightly expand scene bounds to avoid edge cases
  Vec3 epsilon = scene_bounds_.extents() * 0.001f;
  scene_bounds_.min = scene_bounds_.min - epsilon;
  scene_bounds_.max = scene_bounds_.max + epsilon;

  // Initialize index array
  std::vector<uint32_t> indices(count);
  for (uint32_t i = 0; i < count; i++) {
    indices[i] = i;
  }

  // Clear previous data
  compact_nodes_.clear();
  full_nodes_.clear();
  prim_indices_storage_.clear();

  // Reserve estimated space
  uint32_t estimated_nodes = count * 2;
  if (config.use_compact_nodes) {
    compact_nodes_.reserve(estimated_nodes);
  } else {
    full_nodes_.reserve(estimated_nodes);
  }
  reserveIndices(count);

  // Build recursively
  buildRecursive(indices.data(), count, 0, prim_bounds);

  return true;
}

uint32_t MMapTriangleBVH::buildRecursive(uint32_t* indices, uint32_t num_prims,
                                          uint32_t depth, std::vector<AABB>& prim_bounds) noexcept {
  // Compute bounds for this node
  AABB node_bounds;
  AABB centroid_bounds;

  for (uint32_t i = 0; i < num_prims; i++) {
    uint32_t prim_idx = indices[i];
    node_bounds.expand(prim_bounds[prim_idx]);
    centroid_bounds.expand(prim_bounds[prim_idx].center());
  }

  // Create node
  uint32_t node_idx;
  if (config_.use_compact_nodes) {
    node_idx = static_cast<uint32_t>(compact_nodes_.size());
    compact_nodes_.emplace_back();
    compact_nodes_[node_idx].quantizeBounds(node_bounds, scene_bounds_.min, scene_bounds_.max);
  } else {
    node_idx = static_cast<uint32_t>(full_nodes_.size());
    full_nodes_.emplace_back();
    full_nodes_[node_idx].bounds = node_bounds;
  }

  // Check if we should make a leaf
  if (num_prims <= config_.build.max_leaf_size) {
    uint32_t prim_offset = static_cast<uint32_t>(prim_indices_storage_.size() / index_bytes_);

    for (uint32_t i = 0; i < num_prims; i++) {
      pushIndex(indices[i]);
    }

    if (config_.use_compact_nodes) {
      compact_nodes_[node_idx].setLeaf(prim_offset, num_prims);
    } else {
      full_nodes_[node_idx].setLeaf(prim_offset, num_prims);
    }
    return node_idx;
  }

  // Find best split axis using SAH
  int best_axis = centroid_bounds.longestAxis();
  float best_pos = 0.0f;
  float best_cost = kInfinity;

  float parent_area = node_bounds.surfaceArea();

  // Binned SAH
  const uint32_t num_bins = config_.build.num_bins;

  for (int axis = 0; axis < 3; axis++) {
    float axis_min = 0.0f, axis_max = 0.0f;
    switch (axis) {
      case 0: axis_min = centroid_bounds.min.x; axis_max = centroid_bounds.max.x; break;
      case 1: axis_min = centroid_bounds.min.y; axis_max = centroid_bounds.max.y; break;
      case 2: axis_min = centroid_bounds.min.z; axis_max = centroid_bounds.max.z; break;
    }

    if (axis_max - axis_min < kEpsilon) continue;

    float bin_size = (axis_max - axis_min) / num_bins;

    // Count primitives per bin and compute bounds
    std::vector<uint32_t> bin_counts(num_bins, 0);
    std::vector<AABB> bin_bounds(num_bins);

    for (uint32_t i = 0; i < num_prims; i++) {
      uint32_t prim_idx = indices[i];
      Vec3 centroid = prim_bounds[prim_idx].center();
      float pos = 0.0f;
      switch (axis) {
        case 0: pos = centroid.x; break;
        case 1: pos = centroid.y; break;
        case 2: pos = centroid.z; break;
      }

      uint32_t bin = std::min(static_cast<uint32_t>((pos - axis_min) / bin_size), num_bins - 1);
      bin_counts[bin]++;
      bin_bounds[bin].expand(prim_bounds[prim_idx]);
    }

    // Sweep from left
    std::vector<AABB> left_bounds(num_bins);
    std::vector<uint32_t> left_counts(num_bins);
    AABB running_bounds;
    uint32_t running_count = 0;

    for (uint32_t i = 0; i < num_bins; i++) {
      running_bounds.expand(bin_bounds[i]);
      running_count += bin_counts[i];
      left_bounds[i] = running_bounds;
      left_counts[i] = running_count;
    }

    // Sweep from right and compute costs
    running_bounds = AABB();
    running_count = 0;

    for (uint32_t i = num_bins - 1; i > 0; i--) {
      running_bounds.expand(bin_bounds[i]);
      running_count += bin_counts[i];

      uint32_t left_count = left_counts[i - 1];
      if (left_count == 0 || running_count == 0) continue;

      float left_area = left_bounds[i - 1].surfaceArea();
      float right_area = running_bounds.surfaceArea();

      float cost = config_.build.traversal_cost +
                   config_.build.intersection_cost * (left_count * left_area + running_count * right_area) / parent_area;

      if (cost < best_cost) {
        best_cost = cost;
        best_axis = axis;
        best_pos = axis_min + i * bin_size;
      }
    }
  }

  // Check if split is beneficial
  float leaf_cost = config_.build.intersection_cost * num_prims;
  if (best_cost >= leaf_cost && !config_.build.force_max_leaf_size) {
    // Make leaf
    uint32_t prim_offset = static_cast<uint32_t>(prim_indices_storage_.size() / index_bytes_);

    for (uint32_t i = 0; i < num_prims; i++) {
      pushIndex(indices[i]);
    }

    if (config_.use_compact_nodes) {
      compact_nodes_[node_idx].setLeaf(prim_offset, num_prims);
    } else {
      full_nodes_[node_idx].setLeaf(prim_offset, num_prims);
    }
    return node_idx;
  }

  // Partition primitives
  uint32_t mid = 0;
  for (uint32_t i = 0; i < num_prims; i++) {
    uint32_t prim_idx = indices[i];
    Vec3 centroid = prim_bounds[prim_idx].center();
    float pos = 0.0f;
    switch (best_axis) {
      case 0: pos = centroid.x; break;
      case 1: pos = centroid.y; break;
      case 2: pos = centroid.z; break;
    }

    if (pos < best_pos) {
      std::swap(indices[i], indices[mid]);
      mid++;
    }
  }

  // Handle degenerate case
  if (mid == 0 || mid == num_prims) {
    mid = num_prims / 2;
  }

  // Build children
  uint32_t left_child = buildRecursive(indices, mid, depth + 1, prim_bounds);
  uint32_t right_child = buildRecursive(indices + mid, num_prims - mid, depth + 1, prim_bounds);

  // Set interior node
  if (config_.use_compact_nodes) {
    compact_nodes_[node_idx].setInterior(left_child, right_child, static_cast<uint8_t>(best_axis));
  } else {
    full_nodes_[node_idx].setInterior(left_child, right_child);
  }

  return node_idx;
}

uint32_t MMapTriangleBVH::traverse(const Ray& ray, float& hit_t, float& hit_u, float& hit_v) const noexcept {
  if (config_.use_compact_nodes) {
    return traverseCompact(ray, hit_t, hit_u, hit_v);
  } else {
    return traverseFull(ray, hit_t, hit_u, hit_v);
  }
}

uint32_t MMapTriangleBVH::traverseCompact(const Ray& ray, float& hit_t, float& hit_u, float& hit_v) const noexcept {
  if (compact_nodes_.empty()) return kInvalidIndex;

  hit_t = ray.tmax;
  uint32_t hit_prim = kInvalidIndex;

  // Precompute inverse direction
  Vec3 inv_dir(1.0f / ray.direction.x, 1.0f / ray.direction.y, 1.0f / ray.direction.z);
  int dir_is_neg[3] = {
    inv_dir.x < 0 ? 1 : 0,
    inv_dir.y < 0 ? 1 : 0,
    inv_dir.z < 0 ? 1 : 0
  };

  // Stack-based traversal
  uint32_t stack[64];
  int stack_ptr = 0;
  stack[stack_ptr++] = 0;

  while (stack_ptr > 0) {
    uint32_t node_idx = stack[--stack_ptr];
    const CompactBVHNode& node = compact_nodes_[node_idx];

    // Dequantize and test bounds
    AABB bounds = node.dequantizeBounds(scene_bounds_.min, scene_bounds_.max);
    float tmin_box, tmax_box;
    if (!bounds.intersect(ray, tmin_box, tmax_box) || tmin_box > hit_t) {
      continue;
    }

    if (node.isLeaf()) {
      // Test primitives
      for (uint32_t i = 0; i < node.data1; i++) {
        uint32_t prim_idx = getPrimIndex(node.data0 + i);
        float t, u, v;
        if (triangles_[prim_idx].intersect(ray, t, u, v) && t < hit_t) {
          hit_t = t;
          hit_u = u;
          hit_v = v;
          hit_prim = prim_idx;
        }
      }
    } else {
      // Interior node - order traversal by split axis
      uint32_t first = node.data0;
      uint32_t second = node.data1;

      if (config_.use_ordered_traversal && dir_is_neg[node.axis]) {
        std::swap(first, second);
      }

      // Push far child first (so near child is processed first)
      stack[stack_ptr++] = second;
      stack[stack_ptr++] = first;
    }
  }

  return hit_prim;
}

uint32_t MMapTriangleBVH::traverseFull(const Ray& ray, float& hit_t, float& hit_u, float& hit_v) const noexcept {
  if (full_nodes_.empty()) return kInvalidIndex;

  hit_t = ray.tmax;
  uint32_t hit_prim = kInvalidIndex;

  uint32_t stack[64];
  int stack_ptr = 0;
  stack[stack_ptr++] = 0;

  while (stack_ptr > 0) {
    uint32_t node_idx = stack[--stack_ptr];
    const BVHNode& node = full_nodes_[node_idx];

    float tmin_box, tmax_box;
    if (!node.bounds.intersect(ray, tmin_box, tmax_box) || tmin_box > hit_t) {
      continue;
    }

    if (node.isLeaf()) {
      for (uint32_t i = 0; i < node.prim_count; i++) {
        uint32_t prim_idx = getPrimIndex(node.prim_offset + i);
        float t, u, v;
        if (triangles_[prim_idx].intersect(ray, t, u, v) && t < hit_t) {
          hit_t = t;
          hit_u = u;
          hit_v = v;
          hit_prim = prim_idx;
        }
      }
    } else {
      stack[stack_ptr++] = node.right_child;
      stack[stack_ptr++] = node.left_child;
    }
  }

  return hit_prim;
}

uint32_t MMapTriangleBVH::traverseWithConfig(const Ray& ray, float& hit_t, float& hit_u, float& hit_v,
                                              const TraversalConfig& config,
                                              TraversalStats* stats) const noexcept {
  if (stats) {
    *stats = TraversalStats();
  }

  if ((config_.use_compact_nodes && compact_nodes_.empty()) ||
      (!config_.use_compact_nodes && full_nodes_.empty())) {
    return kInvalidIndex;
  }

  hit_t = ray.tmax;
  uint32_t hit_prim = kInvalidIndex;
  uint32_t prims_tested = 0;

  uint32_t stack[64];
  int stack_ptr = 0;
  stack[stack_ptr++] = 0;

  while (stack_ptr > 0) {
    uint32_t node_idx = stack[--stack_ptr];

    AABB bounds;
    bool is_leaf;
    uint32_t data0, data1;
    uint8_t axis = 0;

    if (config_.use_compact_nodes) {
      const CompactBVHNode& node = compact_nodes_[node_idx];
      bounds = node.dequantizeBounds(scene_bounds_.min, scene_bounds_.max);
      is_leaf = node.isLeaf();
      data0 = node.data0;
      data1 = node.data1;
      axis = node.axis;
    } else {
      const BVHNode& node = full_nodes_[node_idx];
      bounds = node.bounds;
      is_leaf = node.isLeaf();
      data0 = node.prim_offset;
      data1 = is_leaf ? node.prim_count : node.right_child;
    }

    if (stats) stats->nodes_visited++;

    float tmin_box, tmax_box;
    if (!bounds.intersect(ray, tmin_box, tmax_box) || tmin_box > hit_t) {
      continue;
    }

    if (is_leaf) {
      uint32_t count = config_.use_compact_nodes ? data1 : data1;
      uint32_t offset = data0;

      for (uint32_t i = 0; i < count; i++) {
        if (config.max_prim_tests > 0 && prims_tested >= config.max_prim_tests) {
          if (stats) stats->terminated_early = true;
          goto done;
        }

        uint32_t prim_idx = getPrimIndex(offset + i);
        prims_tested++;

        float t, u, v;
        if (triangles_[prim_idx].intersect(ray, t, u, v) && t < hit_t) {
          hit_t = t;
          hit_u = u;
          hit_v = v;
          hit_prim = prim_idx;
          if (stats) stats->prims_hit++;

          if (config.early_termination) {
            goto done;
          }
        }
      }
    } else {
      uint32_t left = config_.use_compact_nodes ? data0 : data0;
      uint32_t right = config_.use_compact_nodes ? data1 : (full_nodes_[node_idx].right_child);

      // Order by axis if enabled
      if (config_.use_ordered_traversal && config_.use_compact_nodes) {
        float dir_component = 0.0f;
        switch (axis) {
          case 0: dir_component = ray.direction.x; break;
          case 1: dir_component = ray.direction.y; break;
          case 2: dir_component = ray.direction.z; break;
        }
        if (dir_component < 0) {
          std::swap(left, right);
        }
      }

      stack[stack_ptr++] = right;
      stack[stack_ptr++] = left;
    }
  }

done:
  if (stats) {
    stats->prims_tested = prims_tested;
  }

  return hit_prim;
}

size_t MMapTriangleBVH::getBVHMemoryUsage() const noexcept {
  size_t memory = 0;

  if (config_.use_compact_nodes) {
    memory += compact_nodes_.size() * sizeof(CompactBVHNode);
  } else {
    memory += full_nodes_.size() * sizeof(BVHNode);
  }

  memory += prim_indices_storage_.size();

  return memory;
}

size_t MMapTriangleBVH::getTotalMemoryUsage() const noexcept {
  size_t memory = getBVHMemoryUsage();

  // Primitives are external, so we don't count them
  // But we can report the reference size
  memory += sizeof(triangles_) + sizeof(triangle_count_);

  return memory;
}

MMapTriangleBVH::Stats MMapTriangleBVH::getStats() const noexcept {
  Stats stats = {};

  stats.num_primitives = triangle_count_;
  stats.index_bytes = index_bytes_;
  stats.uses_compact_nodes = config_.use_compact_nodes;
  stats.bvh_memory_bytes = getBVHMemoryUsage();
  stats.prim_memory_bytes = 0;  // External data

  if (config_.use_compact_nodes) {
    for (const auto& node : compact_nodes_) {
      stats.num_nodes++;
      if (node.isLeaf()) {
        stats.num_leaves++;
        stats.avg_leaf_size += node.data1;
      }
    }
  } else {
    std::vector<uint32_t> depths(full_nodes_.size(), 0);
    for (uint32_t i = 0; i < full_nodes_.size(); i++) {
      const auto& node = full_nodes_[i];
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
  }

  if (stats.num_leaves > 0) {
    stats.avg_leaf_size /= stats.num_leaves;
  }

  return stats;
}

// ============================================================================
// MMapGenericBVH Implementation
// ============================================================================

MMapGenericBVH::MMapGenericBVH() noexcept
  : prim_data_(nullptr)
  , prim_count_(0)
  , index_bytes_(4) {}

uint32_t MMapGenericBVH::getPrimIndex(uint32_t offset) const noexcept {
  switch (index_bytes_) {
    case 1:
      return prim_indices_storage_[offset];
    case 2:
      return *reinterpret_cast<const uint16_t*>(&prim_indices_storage_[offset * 2]);
    case 4:
    default:
      return *reinterpret_cast<const uint32_t*>(&prim_indices_storage_[offset * 4]);
  }
}

void MMapGenericBVH::reserveIndices(uint32_t count) noexcept {
  prim_indices_storage_.reserve(count * index_bytes_);
}

void MMapGenericBVH::pushIndex(uint32_t index) noexcept {
  switch (index_bytes_) {
    case 1:
      prim_indices_storage_.push_back(static_cast<uint8_t>(index));
      break;
    case 2: {
      uint16_t idx16 = static_cast<uint16_t>(index);
      prim_indices_storage_.push_back(static_cast<uint8_t>(idx16 & 0xFF));
      prim_indices_storage_.push_back(static_cast<uint8_t>(idx16 >> 8));
      break;
    }
    case 4:
    default: {
      prim_indices_storage_.push_back(static_cast<uint8_t>(index & 0xFF));
      prim_indices_storage_.push_back(static_cast<uint8_t>((index >> 8) & 0xFF));
      prim_indices_storage_.push_back(static_cast<uint8_t>((index >> 16) & 0xFF));
      prim_indices_storage_.push_back(static_cast<uint8_t>((index >> 24) & 0xFF));
      break;
    }
  }
}

bool MMapGenericBVH::build(const void* prim_data, uint32_t count,
                           BoundsFn bounds_fn,
                           const MMapBVHConfig& config) noexcept {
  if (!prim_data || count == 0 || !bounds_fn) {
    return false;
  }

  prim_data_ = prim_data;
  prim_count_ = count;
  config_ = config;

  // Determine index precision
  if (config.index_precision == IndexPrecision::Auto) {
    if (count <= 255) {
      index_bytes_ = 1;
    } else if (count <= 65535) {
      index_bytes_ = 2;
    } else {
      index_bytes_ = 4;
    }
  } else {
    index_bytes_ = static_cast<uint8_t>(config.index_precision);
  }

  // Compute bounds
  scene_bounds_ = AABB();
  std::vector<AABB> prim_bounds(count);

  for (uint32_t i = 0; i < count; i++) {
    prim_bounds[i] = bounds_fn(prim_data, i);
    scene_bounds_.expand(prim_bounds[i]);
  }

  Vec3 epsilon = scene_bounds_.extents() * 0.001f;
  scene_bounds_.min = scene_bounds_.min - epsilon;
  scene_bounds_.max = scene_bounds_.max + epsilon;

  std::vector<uint32_t> indices(count);
  for (uint32_t i = 0; i < count; i++) {
    indices[i] = i;
  }

  compact_nodes_.clear();
  full_nodes_.clear();
  prim_indices_storage_.clear();

  uint32_t estimated_nodes = count * 2;
  if (config.use_compact_nodes) {
    compact_nodes_.reserve(estimated_nodes);
  } else {
    full_nodes_.reserve(estimated_nodes);
  }
  reserveIndices(count);

  buildRecursive(indices.data(), count, 0, prim_bounds);

  return true;
}

uint32_t MMapGenericBVH::buildRecursive(uint32_t* indices, uint32_t num_prims,
                                         uint32_t depth, const std::vector<AABB>& prim_bounds) noexcept {
  AABB node_bounds;
  AABB centroid_bounds;

  for (uint32_t i = 0; i < num_prims; i++) {
    uint32_t prim_idx = indices[i];
    node_bounds.expand(prim_bounds[prim_idx]);
    centroid_bounds.expand(prim_bounds[prim_idx].center());
  }

  uint32_t node_idx;
  if (config_.use_compact_nodes) {
    node_idx = static_cast<uint32_t>(compact_nodes_.size());
    compact_nodes_.emplace_back();
    compact_nodes_[node_idx].quantizeBounds(node_bounds, scene_bounds_.min, scene_bounds_.max);
  } else {
    node_idx = static_cast<uint32_t>(full_nodes_.size());
    full_nodes_.emplace_back();
    full_nodes_[node_idx].bounds = node_bounds;
  }

  if (num_prims <= config_.build.max_leaf_size) {
    uint32_t prim_offset = static_cast<uint32_t>(prim_indices_storage_.size() / index_bytes_);

    for (uint32_t i = 0; i < num_prims; i++) {
      pushIndex(indices[i]);
    }

    if (config_.use_compact_nodes) {
      compact_nodes_[node_idx].setLeaf(prim_offset, num_prims);
    } else {
      full_nodes_[node_idx].setLeaf(prim_offset, num_prims);
    }
    return node_idx;
  }

  // Find best split
  int best_axis = centroid_bounds.longestAxis();
  float best_pos = 0.0f;
  float best_cost = kInfinity;
  float parent_area = node_bounds.surfaceArea();
  const uint32_t num_bins = config_.build.num_bins;

  for (int axis = 0; axis < 3; axis++) {
    float axis_min = 0.0f, axis_max = 0.0f;
    switch (axis) {
      case 0: axis_min = centroid_bounds.min.x; axis_max = centroid_bounds.max.x; break;
      case 1: axis_min = centroid_bounds.min.y; axis_max = centroid_bounds.max.y; break;
      case 2: axis_min = centroid_bounds.min.z; axis_max = centroid_bounds.max.z; break;
    }

    if (axis_max - axis_min < kEpsilon) continue;

    float bin_size = (axis_max - axis_min) / num_bins;

    std::vector<uint32_t> bin_counts(num_bins, 0);
    std::vector<AABB> bin_bounds(num_bins);

    for (uint32_t i = 0; i < num_prims; i++) {
      uint32_t prim_idx = indices[i];
      Vec3 centroid = prim_bounds[prim_idx].center();
      float pos = 0.0f;
      switch (axis) {
        case 0: pos = centroid.x; break;
        case 1: pos = centroid.y; break;
        case 2: pos = centroid.z; break;
      }

      uint32_t bin = std::min(static_cast<uint32_t>((pos - axis_min) / bin_size), num_bins - 1);
      bin_counts[bin]++;
      bin_bounds[bin].expand(prim_bounds[prim_idx]);
    }

    std::vector<AABB> left_bounds(num_bins);
    std::vector<uint32_t> left_counts(num_bins);
    AABB running_bounds;
    uint32_t running_count = 0;

    for (uint32_t i = 0; i < num_bins; i++) {
      running_bounds.expand(bin_bounds[i]);
      running_count += bin_counts[i];
      left_bounds[i] = running_bounds;
      left_counts[i] = running_count;
    }

    running_bounds = AABB();
    running_count = 0;

    for (uint32_t i = num_bins - 1; i > 0; i--) {
      running_bounds.expand(bin_bounds[i]);
      running_count += bin_counts[i];

      uint32_t left_count = left_counts[i - 1];
      if (left_count == 0 || running_count == 0) continue;

      float left_area = left_bounds[i - 1].surfaceArea();
      float right_area = running_bounds.surfaceArea();

      float cost = config_.build.traversal_cost +
                   config_.build.intersection_cost * (left_count * left_area + running_count * right_area) / parent_area;

      if (cost < best_cost) {
        best_cost = cost;
        best_axis = axis;
        best_pos = axis_min + i * bin_size;
      }
    }
  }

  float leaf_cost = config_.build.intersection_cost * num_prims;
  if (best_cost >= leaf_cost && !config_.build.force_max_leaf_size) {
    uint32_t prim_offset = static_cast<uint32_t>(prim_indices_storage_.size() / index_bytes_);

    for (uint32_t i = 0; i < num_prims; i++) {
      pushIndex(indices[i]);
    }

    if (config_.use_compact_nodes) {
      compact_nodes_[node_idx].setLeaf(prim_offset, num_prims);
    } else {
      full_nodes_[node_idx].setLeaf(prim_offset, num_prims);
    }
    return node_idx;
  }

  uint32_t mid = 0;
  for (uint32_t i = 0; i < num_prims; i++) {
    uint32_t prim_idx = indices[i];
    Vec3 centroid = prim_bounds[prim_idx].center();
    float pos = 0.0f;
    switch (best_axis) {
      case 0: pos = centroid.x; break;
      case 1: pos = centroid.y; break;
      case 2: pos = centroid.z; break;
    }

    if (pos < best_pos) {
      std::swap(indices[i], indices[mid]);
      mid++;
    }
  }

  if (mid == 0 || mid == num_prims) {
    mid = num_prims / 2;
  }

  uint32_t left_child = buildRecursive(indices, mid, depth + 1, prim_bounds);
  uint32_t right_child = buildRecursive(indices + mid, num_prims - mid, depth + 1, prim_bounds);

  if (config_.use_compact_nodes) {
    compact_nodes_[node_idx].setInterior(left_child, right_child, static_cast<uint8_t>(best_axis));
  } else {
    full_nodes_[node_idx].setInterior(left_child, right_child);
  }

  return node_idx;
}

uint32_t MMapGenericBVH::traverse(const Ray& ray, IntersectFn intersect_fn,
                                   float& hit_t, float& hit_u, float& hit_v) const noexcept {
  if (!intersect_fn) return kInvalidIndex;

  bool use_compact = config_.use_compact_nodes;
  if ((use_compact && compact_nodes_.empty()) || (!use_compact && full_nodes_.empty())) {
    return kInvalidIndex;
  }

  hit_t = ray.tmax;
  uint32_t hit_prim = kInvalidIndex;

  uint32_t stack[64];
  int stack_ptr = 0;
  stack[stack_ptr++] = 0;

  while (stack_ptr > 0) {
    uint32_t node_idx = stack[--stack_ptr];

    AABB bounds;
    bool is_leaf;
    uint32_t data0, data1;

    if (use_compact) {
      const CompactBVHNode& node = compact_nodes_[node_idx];
      bounds = node.dequantizeBounds(scene_bounds_.min, scene_bounds_.max);
      is_leaf = node.isLeaf();
      data0 = node.data0;
      data1 = node.data1;
    } else {
      const BVHNode& node = full_nodes_[node_idx];
      bounds = node.bounds;
      is_leaf = node.isLeaf();
      data0 = node.prim_offset;
      data1 = is_leaf ? node.prim_count : node.right_child;
    }

    float tmin_box, tmax_box;
    if (!bounds.intersect(ray, tmin_box, tmax_box) || tmin_box > hit_t) {
      continue;
    }

    if (is_leaf) {
      uint32_t count = data1;
      uint32_t offset = data0;

      for (uint32_t i = 0; i < count; i++) {
        uint32_t prim_idx = getPrimIndex(offset + i);
        float t, u, v;
        if (intersect_fn(ray, prim_data_, prim_idx, t, u, v) && t < hit_t) {
          hit_t = t;
          hit_u = u;
          hit_v = v;
          hit_prim = prim_idx;
        }
      }
    } else {
      uint32_t left = data0;
      uint32_t right = use_compact ? data1 : full_nodes_[node_idx].right_child;

      stack[stack_ptr++] = right;
      stack[stack_ptr++] = left;
    }
  }

  return hit_prim;
}

size_t MMapGenericBVH::getBVHMemoryUsage() const noexcept {
  size_t memory = 0;

  if (config_.use_compact_nodes) {
    memory += compact_nodes_.size() * sizeof(CompactBVHNode);
  } else {
    memory += full_nodes_.size() * sizeof(BVHNode);
  }

  memory += prim_indices_storage_.size();

  return memory;
}

MMapTriangleBVH::Stats MMapGenericBVH::getStats() const noexcept {
  MMapTriangleBVH::Stats stats = {};

  stats.num_primitives = prim_count_;
  stats.index_bytes = index_bytes_;
  stats.uses_compact_nodes = config_.use_compact_nodes;
  stats.bvh_memory_bytes = getBVHMemoryUsage();
  stats.prim_memory_bytes = 0;

  if (config_.use_compact_nodes) {
    for (const auto& node : compact_nodes_) {
      stats.num_nodes++;
      if (node.isLeaf()) {
        stats.num_leaves++;
        stats.avg_leaf_size += node.data1;
      }
    }
  } else {
    for (const auto& node : full_nodes_) {
      stats.num_nodes++;
      if (node.isLeaf()) {
        stats.num_leaves++;
        stats.avg_leaf_size += node.prim_count;
      }
    }
  }

  if (stats.num_leaves > 0) {
    stats.avg_leaf_size /= stats.num_leaves;
  }

  return stats;
}

// ============================================================================
// SimpleTimer Implementation
// ============================================================================

#if defined(_WIN32)
#include <windows.h>
void SimpleTimer::start() noexcept {
  LARGE_INTEGER counter;
  QueryPerformanceCounter(&counter);
  start_time_ = counter.QuadPart;
}

void SimpleTimer::stop() noexcept {
  LARGE_INTEGER counter;
  QueryPerformanceCounter(&counter);
  end_time_ = counter.QuadPart;
}

double SimpleTimer::elapsedMicroseconds() const noexcept {
  LARGE_INTEGER freq;
  QueryPerformanceFrequency(&freq);
  return static_cast<double>(end_time_ - start_time_) * 1000000.0 / freq.QuadPart;
}
#else
#include <time.h>
void SimpleTimer::start() noexcept {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  start_time_ = static_cast<uint64_t>(ts.tv_sec) * 1000000000ULL + ts.tv_nsec;
}

void SimpleTimer::stop() noexcept {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  end_time_ = static_cast<uint64_t>(ts.tv_sec) * 1000000000ULL + ts.tv_nsec;
}

double SimpleTimer::elapsedMicroseconds() const noexcept {
  return static_cast<double>(end_time_ - start_time_) / 1000.0;
}
#endif

// ============================================================================
// AutoTuner Implementation
// ============================================================================

std::vector<Triangle> AutoTuner::samplePrimitives(
    const std::vector<Triangle>& triangles,
    uint32_t sample_count,
    SimpleRNG& rng) noexcept {

  if (triangles.empty()) {
    return {};
  }

  // Clamp sample count to input size
  sample_count = std::min(sample_count, static_cast<uint32_t>(triangles.size()));

  if (sample_count == triangles.size()) {
    return triangles;
  }

  // Stratified sampling: divide into strata and sample from each
  // This preserves spatial distribution better than uniform random sampling

  // Compute scene bounds for spatial stratification
  AABB scene_bounds;
  for (const auto& tri : triangles) {
    scene_bounds.expand(tri.bounds());
  }

  Vec3 extent = scene_bounds.extents();
  int primary_axis = scene_bounds.longestAxis();

  // Divide along primary axis into strata
  uint32_t num_strata = std::min(sample_count, 16u);
  float strata_size = 0.0f;
  switch (primary_axis) {
    case 0: strata_size = extent.x / num_strata; break;
    case 1: strata_size = extent.y / num_strata; break;
    case 2: strata_size = extent.z / num_strata; break;
  }

  // Assign triangles to strata
  std::vector<std::vector<uint32_t>> strata(num_strata);
  for (uint32_t i = 0; i < triangles.size(); i++) {
    Vec3 centroid = triangles[i].centroid();
    float pos = 0.0f;
    switch (primary_axis) {
      case 0: pos = centroid.x - scene_bounds.min.x; break;
      case 1: pos = centroid.y - scene_bounds.min.y; break;
      case 2: pos = centroid.z - scene_bounds.min.z; break;
    }
    uint32_t stratum = std::min(static_cast<uint32_t>(pos / strata_size), num_strata - 1);
    strata[stratum].push_back(i);
  }

  // Sample from each stratum proportionally
  std::vector<Triangle> sampled;
  sampled.reserve(sample_count);

  uint32_t remaining = sample_count;
  for (uint32_t s = 0; s < num_strata && remaining > 0; s++) {
    if (strata[s].empty()) continue;

    // Calculate samples for this stratum (proportional to its size)
    uint32_t stratum_samples = static_cast<uint32_t>(
        static_cast<float>(strata[s].size()) / triangles.size() * sample_count);
    stratum_samples = std::max(1u, std::min(stratum_samples, remaining));
    stratum_samples = std::min(stratum_samples, static_cast<uint32_t>(strata[s].size()));

    // Shuffle and take first N
    rng.shuffle(strata[s]);
    for (uint32_t i = 0; i < stratum_samples && remaining > 0; i++) {
      sampled.push_back(triangles[strata[s][i]]);
      remaining--;
    }
  }

  // If we didn't get enough samples (due to rounding), fill with random
  while (sampled.size() < sample_count) {
    uint32_t idx = rng.next() % triangles.size();
    sampled.push_back(triangles[idx]);
  }

  return sampled;
}

std::vector<Ray> AutoTuner::generateTestRays(
    const AABB& scene_bounds,
    uint32_t ray_count,
    SimpleRNG& rng) noexcept {

  std::vector<Ray> rays;
  rays.reserve(ray_count);

  Vec3 center = scene_bounds.center();
  Vec3 extent = scene_bounds.extents();
  float diagonal = extent.length();

  // Mix of ray types: random, coherent, and edge cases
  uint32_t random_rays = ray_count * 60 / 100;      // 60% random
  uint32_t coherent_rays = ray_count * 30 / 100;    // 30% coherent (similar origins/directions)
  uint32_t edge_rays = ray_count - random_rays - coherent_rays; // 10% edge cases

  // Random rays from outside the scene looking in
  for (uint32_t i = 0; i < random_rays; i++) {
    // Random point on sphere around scene
    float theta = rng.nextFloat(0.0f, 2.0f * 3.14159265f);
    float phi = rng.nextFloat(0.0f, 3.14159265f);
    float r = diagonal * 1.5f;

    Vec3 origin(
        center.x + r * std::sin(phi) * std::cos(theta),
        center.y + r * std::sin(phi) * std::sin(theta),
        center.z + r * std::cos(phi)
    );

    // Random target inside scene
    Vec3 target(
        rng.nextFloat(scene_bounds.min.x, scene_bounds.max.x),
        rng.nextFloat(scene_bounds.min.y, scene_bounds.max.y),
        rng.nextFloat(scene_bounds.min.z, scene_bounds.max.z)
    );

    Vec3 dir = (target - origin).normalize();
    rays.emplace_back(origin, dir);
  }

  // Coherent rays (simulate camera-like rays from one viewpoint)
  Vec3 cam_origin = center + Vec3(0, 0, diagonal);
  for (uint32_t i = 0; i < coherent_rays; i++) {
    // Small variations around center target
    Vec3 target(
        center.x + rng.nextFloat(-extent.x * 0.5f, extent.x * 0.5f),
        center.y + rng.nextFloat(-extent.y * 0.5f, extent.y * 0.5f),
        center.z + rng.nextFloat(-extent.z * 0.1f, extent.z * 0.1f)
    );
    Vec3 dir = (target - cam_origin).normalize();
    rays.emplace_back(cam_origin, dir);
  }

  // Edge case rays: axis-aligned, grazing angles
  for (uint32_t i = 0; i < edge_rays; i++) {
    Vec3 origin, dir;

    switch (i % 6) {
      case 0: // +X axis
        origin = Vec3(scene_bounds.min.x - diagonal, center.y, center.z);
        dir = Vec3(1, 0, 0);
        break;
      case 1: // -X axis
        origin = Vec3(scene_bounds.max.x + diagonal, center.y, center.z);
        dir = Vec3(-1, 0, 0);
        break;
      case 2: // +Y axis
        origin = Vec3(center.x, scene_bounds.min.y - diagonal, center.z);
        dir = Vec3(0, 1, 0);
        break;
      case 3: // -Y axis
        origin = Vec3(center.x, scene_bounds.max.y + diagonal, center.z);
        dir = Vec3(0, -1, 0);
        break;
      case 4: // +Z axis
        origin = Vec3(center.x, center.y, scene_bounds.min.z - diagonal);
        dir = Vec3(0, 0, 1);
        break;
      case 5: // -Z axis
        origin = Vec3(center.x, center.y, scene_bounds.max.z + diagonal);
        dir = Vec3(0, 0, -1);
        break;
    }

    // Add small random perturbation
    origin.x += rng.nextFloat(-extent.x * 0.4f, extent.x * 0.4f);
    origin.y += rng.nextFloat(-extent.y * 0.4f, extent.y * 0.4f);
    origin.z += rng.nextFloat(-extent.z * 0.4f, extent.z * 0.4f);

    rays.emplace_back(origin, dir);
  }

  return rays;
}

double AutoTuner::measureBuildTime(
    const std::vector<Triangle>& triangles,
    const BVHBuildConfig& config,
    uint32_t iterations,
    TriangleBVH& out_bvh) noexcept {

  SimpleTimer timer;
  double total_time = 0.0;

  for (uint32_t i = 0; i < iterations; i++) {
    TriangleBVH temp_bvh;
    timer.start();
    temp_bvh.build(triangles, config);
    timer.stop();
    total_time += timer.elapsedMicroseconds();

    // Keep the last one
    if (i == iterations - 1) {
      out_bvh = std::move(temp_bvh);
    }
  }

  return total_time / iterations;
}

double AutoTuner::measureBuildTime(
    const std::vector<Triangle>& triangles,
    const SBVHBuildConfig& config,
    uint32_t iterations,
    SBVH& out_sbvh) noexcept {

  SimpleTimer timer;
  double total_time = 0.0;

  for (uint32_t i = 0; i < iterations; i++) {
    SBVH temp_sbvh;
    timer.start();
    temp_sbvh.build(triangles, config);
    timer.stop();
    total_time += timer.elapsedMicroseconds();

    if (i == iterations - 1) {
      out_sbvh = std::move(temp_sbvh);
    }
  }

  return total_time / iterations;
}

double AutoTuner::measureTraversalTime(
    const TriangleBVH& bvh,
    const std::vector<Ray>& rays,
    const TraversalConfig& trav_config,
    uint32_t iterations) noexcept {

  SimpleTimer timer;
  double total_time = 0.0;

  // Volatile to prevent optimization
  volatile uint32_t hit_count = 0;

  for (uint32_t iter = 0; iter < iterations; iter++) {
    timer.start();
    for (const auto& ray : rays) {
      float t, u, v;
      uint32_t hit = bvh.traverseWithConfig(ray, t, u, v, trav_config);
      if (hit != kInvalidIndex) {
        hit_count++;
      }
    }
    timer.stop();
    total_time += timer.elapsedMicroseconds();
  }

  (void)hit_count;  // Suppress unused warning
  return total_time / iterations;
}

double AutoTuner::measureTraversalTime(
    const SBVH& sbvh,
    const std::vector<Ray>& rays,
    const TraversalConfig& trav_config,
    uint32_t iterations) noexcept {

  SimpleTimer timer;
  double total_time = 0.0;

  volatile uint32_t hit_count = 0;

  for (uint32_t iter = 0; iter < iterations; iter++) {
    timer.start();
    for (const auto& ray : rays) {
      float t, u, v;
      uint32_t hit = sbvh.traverseWithConfig(ray, t, u, v, trav_config);
      if (hit != kInvalidIndex) {
        hit_count++;
      }
    }
    timer.stop();
    total_time += timer.elapsedMicroseconds();
  }

  (void)hit_count;
  return total_time / iterations;
}

size_t AutoTuner::estimateMemory(const TriangleBVH& bvh) noexcept {
  size_t memory = 0;

  // BVH nodes
  memory += bvh.getBVH().getNodes().size() * sizeof(BVHNode);

  // Primitive indices
  memory += bvh.getBVH().getPrimitiveIndices().size() * sizeof(uint32_t);

  // Triangles (stored internally)
  memory += bvh.getTriangles().size() * sizeof(Triangle);

  return memory;
}

size_t AutoTuner::estimateMemory(const SBVH& sbvh) noexcept {
  size_t memory = 0;

  // BVH nodes
  memory += sbvh.getNodes().size() * sizeof(BVHNode);

  // References (may be more than original primitives)
  memory += sbvh.getReferences().size() * sizeof(SBVH::PrimRef);

  // Triangles
  memory += sbvh.getTriangles().size() * sizeof(Triangle);

  return memory;
}

AutoTuneResult::SceneCharacteristics AutoTuner::analyzeScene(
    const std::vector<Triangle>& triangles) noexcept {

  AutoTuneResult::SceneCharacteristics info = {};

  if (triangles.empty()) {
    return info;
  }

  // Compute scene bounds
  AABB scene_bounds;
  std::vector<AABB> tri_bounds;
  tri_bounds.reserve(triangles.size());

  float total_area = 0.0f;
  float thin_count = 0;

  for (const auto& tri : triangles) {
    AABB bounds = tri.bounds();
    scene_bounds.expand(bounds);
    tri_bounds.push_back(bounds);

    // Compute triangle area using cross product
    Vec3 e1 = tri.v1 - tri.v0;
    Vec3 e2 = tri.v2 - tri.v0;
    float area = e1.cross(e2).length() * 0.5f;
    total_area += area;

    // Check for thin triangles (aspect ratio > 10)
    float edge_lengths[3] = {
        e1.length(),
        e2.length(),
        (tri.v2 - tri.v1).length()
    };
    float max_edge = std::max({edge_lengths[0], edge_lengths[1], edge_lengths[2]});
    float min_edge = std::min({edge_lengths[0], edge_lengths[1], edge_lengths[2]});
    if (min_edge > kEpsilon && max_edge / min_edge > 10.0f) {
      thin_count++;
    }
  }

  info.avg_triangle_area = total_area / triangles.size();

  Vec3 extent = scene_bounds.extents();
  info.scene_volume = extent.x * extent.y * extent.z;

  if (info.scene_volume > kEpsilon) {
    info.triangle_density = triangles.size() / info.scene_volume;
  }

  info.has_thin_triangles = (thin_count > triangles.size() * 0.1f);

  // Estimate overlap ratio using binning
  const uint32_t num_bins = 32;
  std::vector<uint32_t> bin_counts(num_bins * num_bins * num_bins, 0);

  float inv_extent_x = (extent.x > kEpsilon) ? num_bins / extent.x : 0.0f;
  float inv_extent_y = (extent.y > kEpsilon) ? num_bins / extent.y : 0.0f;
  float inv_extent_z = (extent.z > kEpsilon) ? num_bins / extent.z : 0.0f;

  for (const auto& bounds : tri_bounds) {
    Vec3 centroid = bounds.center();
    uint32_t bx = std::min(static_cast<uint32_t>((centroid.x - scene_bounds.min.x) * inv_extent_x), num_bins - 1);
    uint32_t by = std::min(static_cast<uint32_t>((centroid.y - scene_bounds.min.y) * inv_extent_y), num_bins - 1);
    uint32_t bz = std::min(static_cast<uint32_t>((centroid.z - scene_bounds.min.z) * inv_extent_z), num_bins - 1);
    bin_counts[bx * num_bins * num_bins + by * num_bins + bz]++;
  }

  // Count bins with more than one primitive
  uint32_t overlap_bins = 0;
  uint32_t non_empty_bins = 0;
  for (uint32_t count : bin_counts) {
    if (count > 0) {
      non_empty_bins++;
      if (count > 1) {
        overlap_bins++;
      }
    }
  }

  info.overlap_ratio = (non_empty_bins > 0) ?
      static_cast<float>(overlap_bins) / non_empty_bins : 0.0f;

  // Detect clustering: high variance in bin counts indicates clustering
  float mean_count = static_cast<float>(triangles.size()) / (num_bins * num_bins * num_bins);
  float variance = 0.0f;
  for (uint32_t count : bin_counts) {
    float diff = count - mean_count;
    variance += diff * diff;
  }
  variance /= (num_bins * num_bins * num_bins);
  info.has_clustered_distribution = (variance > mean_count * mean_count * 4.0f);

  // Detect co-planar regions: check for flat normal distribution
  const uint32_t normal_bins = 16;
  std::vector<uint32_t> normal_counts(normal_bins * normal_bins, 0);

  for (const auto& tri : triangles) {
    Vec3 normal = tri.normal();
    // Map normal to 2D bins using spherical coordinates
    float theta = std::atan2(normal.y, normal.x);  // [-pi, pi]
    float phi = std::acos(std::max(-1.0f, std::min(1.0f, normal.z)));  // [0, pi]

    uint32_t bt = std::min(static_cast<uint32_t>((theta + 3.14159265f) / (2.0f * 3.14159265f) * normal_bins), normal_bins - 1);
    uint32_t bp = std::min(static_cast<uint32_t>(phi / 3.14159265f * normal_bins), normal_bins - 1);

    normal_counts[bt * normal_bins + bp]++;
  }

  // If any bin has > 20% of triangles, likely co-planar region
  uint32_t threshold = triangles.size() / 5;
  for (uint32_t count : normal_counts) {
    if (count > threshold) {
      info.has_coplanar_regions = true;
      break;
    }
  }

  return info;
}

AutoTuneResult AutoTuner::tune(
    const std::vector<Triangle>& triangles,
    const AutoTuneConfig& config) noexcept {

  AutoTuneResult result;

  if (triangles.empty()) {
    return result;
  }

  // Analyze scene characteristics
  result.scene_info = analyzeScene(triangles);

  // Determine sample count: sqrt(N) for good coverage with reasonable cost
  uint32_t sample_count = config.sample_prim_count;
  if (sample_count == 0) {
    sample_count = static_cast<uint32_t>(std::sqrt(static_cast<float>(triangles.size())));
    sample_count = std::max(100u, std::min(sample_count, 5000u));
  }
  sample_count = std::min(sample_count, static_cast<uint32_t>(triangles.size()));

  // Sample primitives
  SimpleRNG rng(42);
  std::vector<Triangle> sampled = samplePrimitives(triangles, sample_count, rng);

  // Compute sample scene bounds
  AABB sample_bounds;
  for (const auto& tri : sampled) {
    sample_bounds.expand(tri.bounds());
  }

  // Generate test rays
  std::vector<Ray> test_rays = generateTestRays(sample_bounds, config.sample_ray_count, rng);

  // Configurations to test
  struct TestConfig {
    BVHBuildMethod method;
    BVHBuildConfig bvh_config;
    SBVHBuildConfig sbvh_config;
    TraversalConfig trav_config;
  };

  std::vector<TestConfig> configs_to_test;

  // Test TriangleBVH with different max_leaf_sizes
  uint32_t leaf_sizes[] = {2, 4, 8, 16};
  for (uint32_t leaf_size : leaf_sizes) {
    TestConfig tc;
    tc.method = BVHBuildMethod::TriangleBVH;
    tc.bvh_config.max_leaf_size = leaf_size;
    tc.bvh_config.use_sah = true;
    configs_to_test.push_back(tc);
  }

  // Test SBVH if enabled
  if (config.test_sbvh) {
    float alphas[] = {1e-5f, 1e-4f, 1e-3f};
    for (float alpha : alphas) {
      for (uint32_t leaf_size : {4u, 8u}) {
        TestConfig tc;
        tc.method = BVHBuildMethod::SBVH;
        tc.sbvh_config.max_leaf_size = leaf_size;
        tc.sbvh_config.alpha = alpha;
        configs_to_test.push_back(tc);
      }
    }
  }

  // Warmup phase
  for (uint32_t i = 0; i < config.warmup_iterations; i++) {
    TriangleBVH warmup_bvh;
    warmup_bvh.build(sampled);
    for (const auto& ray : test_rays) {
      float t, u, v;
      warmup_bvh.traverse(ray, t, u, v);
    }
  }

  // Test each configuration
  float best_cost = kInfinity;

  // Normalization factors (compute from first config)
  float max_build_time = 1.0f;
  float max_trav_time = 1.0f;
  float max_memory = 1.0f;

  // First pass: measure all configs and find max values for normalization
  std::vector<std::tuple<double, double, size_t>> raw_metrics;
  raw_metrics.reserve(configs_to_test.size());

  for (const auto& tc : configs_to_test) {
    double build_time;
    double trav_time;
    size_t memory;

    if (tc.method == BVHBuildMethod::TriangleBVH) {
      TriangleBVH temp_bvh;
      build_time = measureBuildTime(sampled, tc.bvh_config, config.timing_iterations, temp_bvh);
      trav_time = measureTraversalTime(temp_bvh, test_rays, tc.trav_config, config.timing_iterations);
      memory = estimateMemory(temp_bvh);
    } else {
      SBVH temp_sbvh;
      build_time = measureBuildTime(sampled, tc.sbvh_config, config.timing_iterations, temp_sbvh);
      trav_time = measureTraversalTime(temp_sbvh, test_rays, tc.trav_config, config.timing_iterations);
      memory = estimateMemory(temp_sbvh);
    }

    raw_metrics.push_back({build_time, trav_time, memory});

    max_build_time = std::max(max_build_time, static_cast<float>(build_time));
    max_trav_time = std::max(max_trav_time, static_cast<float>(trav_time));
    max_memory = std::max(max_memory, static_cast<float>(memory));
  }

  // Second pass: compute normalized costs and select best
  for (size_t i = 0; i < configs_to_test.size(); i++) {
    const auto& tc = configs_to_test[i];
    auto [build_time, trav_time, memory] = raw_metrics[i];

    // Normalize to [0, 1]
    float norm_build = static_cast<float>(build_time) / max_build_time;
    float norm_trav = static_cast<float>(trav_time) / max_trav_time;
    float norm_memory = static_cast<float>(memory) / max_memory;

    float combined_cost = config.build_weight * norm_build +
                          config.traversal_weight * norm_trav +
                          config.memory_weight * norm_memory;

    // Store metrics
    AutoTuneResult::ConfigMetrics metrics;
    metrics.method = tc.method;
    metrics.build_time_us_per_prim = static_cast<float>(build_time / sample_count);
    metrics.traversal_time_ns_per_ray = static_cast<float>(trav_time * 1000.0 / config.sample_ray_count);
    metrics.memory_bytes_per_prim = static_cast<float>(memory) / sample_count;
    metrics.combined_cost = combined_cost;
    metrics.max_leaf_size = (tc.method == BVHBuildMethod::TriangleBVH) ?
        tc.bvh_config.max_leaf_size : tc.sbvh_config.max_leaf_size;
    metrics.sbvh_alpha = (tc.method == BVHBuildMethod::SBVH) ? tc.sbvh_config.alpha : 0.0f;

    result.all_metrics.push_back(metrics);

    // Update best
    if (combined_cost < best_cost) {
      best_cost = combined_cost;
      result.best_method = tc.method;
      result.best_bvh_config = tc.bvh_config;
      result.best_sbvh_config = tc.sbvh_config;
      result.build_time_us_per_prim = metrics.build_time_us_per_prim;
      result.traversal_time_ns_per_ray = metrics.traversal_time_ns_per_ray;
      result.memory_bytes_per_prim = metrics.memory_bytes_per_prim;
    }
  }

  // Test traversal configurations if enabled
  if (config.test_traversal_configs) {
    // Build the best BVH
    TriangleBVH best_bvh;
    SBVH best_sbvh;

    if (result.best_method == BVHBuildMethod::TriangleBVH) {
      best_bvh.build(sampled, result.best_bvh_config);
    } else {
      best_sbvh.build(sampled, result.best_sbvh_config);
    }

    // Test different traversal configs
    uint32_t max_prim_tests_values[] = {0, 32, 64, 128, 256};
    bool mailboxing_values[] = {false, true};

    float best_trav_cost = kInfinity;

    for (uint32_t max_tests : max_prim_tests_values) {
      for (bool mailbox : mailboxing_values) {
        // Mailboxing only makes sense with max_prim_tests limit and SBVH
        if (mailbox && (max_tests == 0 || result.best_method != BVHBuildMethod::SBVH)) {
          continue;
        }

        TraversalConfig trav_cfg;
        trav_cfg.max_prim_tests = max_tests;
        trav_cfg.use_mailboxing = mailbox;

        double trav_time;
        if (result.best_method == BVHBuildMethod::TriangleBVH) {
          trav_time = measureTraversalTime(best_bvh, test_rays, trav_cfg, config.timing_iterations);
        } else {
          trav_time = measureTraversalTime(best_sbvh, test_rays, trav_cfg, config.timing_iterations);
        }

        float trav_cost = static_cast<float>(trav_time);

        // Penalize unlimited tests slightly for pathological cases
        if (max_tests == 0 && (result.scene_info.has_coplanar_regions ||
                               result.scene_info.overlap_ratio > 0.3f)) {
          trav_cost *= 1.1f;  // 10% penalty
        }

        if (trav_cost < best_trav_cost) {
          best_trav_cost = trav_cost;
          result.best_traversal_config = trav_cfg;
          result.traversal_time_ns_per_ray = static_cast<float>(trav_time * 1000.0 / config.sample_ray_count);
        }
      }
    }
  }

  return result;
}

TraversalConfig AutoTuner::tuneTraversal(
    const TriangleBVH& bvh,
    const AABB& scene_bounds,
    uint32_t sample_ray_count,
    uint32_t timing_iterations) noexcept {

  SimpleRNG rng(42);
  std::vector<Ray> test_rays = generateTestRays(scene_bounds, sample_ray_count, rng);

  TraversalConfig best_config;
  float best_time = kInfinity;

  // Warmup
  for (const auto& ray : test_rays) {
    float t, u, v;
    bvh.traverse(ray, t, u, v);
  }

  // Test different configurations
  uint32_t max_tests_values[] = {0, 32, 64, 128, 256, 512};

  for (uint32_t max_tests : max_tests_values) {
    TraversalConfig cfg;
    cfg.max_prim_tests = max_tests;

    double time = measureTraversalTime(bvh, test_rays, cfg, timing_iterations);

    if (time < best_time) {
      best_time = static_cast<float>(time);
      best_config = cfg;
    }
  }

  return best_config;
}

TraversalConfig AutoTuner::tuneTraversal(
    const SBVH& sbvh,
    const AABB& scene_bounds,
    uint32_t sample_ray_count,
    uint32_t timing_iterations) noexcept {

  SimpleRNG rng(42);
  std::vector<Ray> test_rays = generateTestRays(scene_bounds, sample_ray_count, rng);

  TraversalConfig best_config;
  float best_time = kInfinity;

  // Warmup
  for (const auto& ray : test_rays) {
    float t, u, v;
    sbvh.traverse(ray, t, u, v);
  }

  // Test different configurations
  uint32_t max_tests_values[] = {0, 32, 64, 128, 256, 512};
  bool mailbox_values[] = {false, true};

  for (uint32_t max_tests : max_tests_values) {
    for (bool mailbox : mailbox_values) {
      // Mailboxing only useful with SBVH and limited tests
      if (mailbox && max_tests == 0) {
        continue;
      }

      TraversalConfig cfg;
      cfg.max_prim_tests = max_tests;
      cfg.use_mailboxing = mailbox;

      double time = measureTraversalTime(sbvh, test_rays, cfg, timing_iterations);

      if (time < best_time) {
        best_time = static_cast<float>(time);
        best_config = cfg;
      }
    }
  }

  return best_config;
}

bool AutoTuner::buildOptimal(
    const std::vector<Triangle>& triangles,
    TriangleBVH& out_bvh,
    const AutoTuneConfig& config) noexcept {

  AutoTuneResult result = tune(triangles, config);

  if (result.best_method == BVHBuildMethod::TriangleBVH) {
    return out_bvh.build(triangles, result.best_bvh_config);
  } else {
    // Caller wanted TriangleBVH but SBVH was better
    // Build TriangleBVH with best config anyway
    return out_bvh.build(triangles, result.best_bvh_config);
  }
}

bool AutoTuner::buildOptimal(
    const std::vector<Triangle>& triangles,
    SBVH& out_sbvh,
    const AutoTuneConfig& config) noexcept {

  AutoTuneResult result = tune(triangles, config);

  if (result.best_method == BVHBuildMethod::SBVH) {
    return out_sbvh.build(triangles, result.best_sbvh_config);
  } else {
    // SBVH with default config since TriangleBVH was better
    return out_sbvh.build(triangles, result.best_sbvh_config);
  }
}

// ============================================================================
// Profiled Traversal Implementation
// ============================================================================

// Internal helper: profiled traversal for TriangleBVH
namespace {

template<typename Profiler>
uint32_t traverseTriangleBVHProfiled(
    const BVH& bvh,
    const std::vector<Triangle>& triangles,
    const Ray& ray,
    float& hit_t, float& hit_u, float& hit_v,
    Profiler& profiler) noexcept {

  const auto& nodes = bvh.getNodes();
  const auto& prim_indices = bvh.getPrimitiveIndices();

  if (nodes.empty()) {
    return kInvalidIndex;
  }

  uint32_t hit_tri = kInvalidIndex;
  hit_t = ray.tmax;

  // Stack-based traversal with depth tracking
  struct StackEntry {
    uint32_t node_idx;
    uint32_t depth;
  };

  StackEntry stack[64];
  int stack_ptr = 0;

  stack[stack_ptr++] = {0, 0};

  while (stack_ptr > 0) {
    StackEntry entry = stack[--stack_ptr];
    uint32_t node_idx = entry.node_idx;
    uint32_t depth = entry.depth;

    const BVHNode& node = nodes[node_idx];

    profiler.visitNode();
    profiler.pushDepth(depth);

    float tmin, tmax;
    if (!node.bounds.intersectSIMD(ray, tmin, tmax) || tmin > hit_t) {
      profiler.popDepth();
      continue;
    }

    if (node.isLeaf()) {
      profiler.visitLeaf();

      // Test triangles in leaf
      for (uint32_t i = 0; i < node.prim_count; i++) {
        profiler.testPrim();

        uint32_t tri_idx = prim_indices[node.prim_offset + i];
        float t, u, v;
        if (triangles[tri_idx].intersect(ray, t, u, v)) {
          if (t < hit_t) {
            hit_t = t;
            hit_u = u;
            hit_v = v;
            hit_tri = tri_idx;
          }
        }
      }
    } else {
      // Add children to stack
      if (stack_ptr < 62) {
        stack[stack_ptr++] = {node.left_child, depth + 1};
        stack[stack_ptr++] = {node.right_child, depth + 1};
      }
    }

    profiler.popDepth();
  }

  return hit_tri;
}

template<typename Profiler>
uint32_t traverseSBVHProfiled(
    const std::vector<BVHNode>& nodes,
    const std::vector<SBVH::PrimRef>& refs,
    const std::vector<Triangle>& triangles,
    const Ray& ray,
    float& hit_t, float& hit_u, float& hit_v,
    Profiler& profiler) noexcept {

  if (nodes.empty()) {
    return kInvalidIndex;
  }

  uint32_t hit_tri = kInvalidIndex;
  hit_t = ray.tmax;

  struct StackEntry {
    uint32_t node_idx;
    uint32_t depth;
  };

  StackEntry stack[64];
  int stack_ptr = 0;
  stack[stack_ptr++] = {0, 0};

  while (stack_ptr > 0) {
    StackEntry entry = stack[--stack_ptr];
    const BVHNode& node = nodes[entry.node_idx];

    profiler.visitNode();
    profiler.pushDepth(entry.depth);

    float tmin, tmax;
    if (!node.bounds.intersectSIMD(ray, tmin, tmax) || tmin > hit_t) {
      profiler.popDepth();
      continue;
    }

    if (node.isLeaf()) {
      profiler.visitLeaf();

      for (uint32_t i = 0; i < node.prim_count; i++) {
        profiler.testPrim();

        const SBVH::PrimRef& ref = refs[node.prim_offset + i];
        float t, u, v;
        if (triangles[ref.prim_id].intersect(ray, t, u, v) && t < hit_t) {
          hit_t = t;
          hit_u = u;
          hit_v = v;
          hit_tri = ref.prim_id;
        }
      }
    } else {
      if (stack_ptr < 62) {
        stack[stack_ptr++] = {node.left_child, entry.depth + 1};
        stack[stack_ptr++] = {node.right_child, entry.depth + 1};
      }
    }

    profiler.popDepth();
  }

  return hit_tri;
}

template<typename Profiler>
uint32_t traverseMMapBVHProfiled(
    const std::vector<CompactBVHNode>& compact_nodes,
    const std::vector<BVHNode>& full_nodes,
    const std::vector<uint8_t>& prim_indices_storage,
    uint8_t index_bytes,
    const Triangle* triangles,
    const AABB& scene_bounds,
    bool use_compact,
    bool use_ordered,
    const Ray& ray,
    float& hit_t, float& hit_u, float& hit_v,
    Profiler& profiler) noexcept {

  auto getPrimIndex = [&](uint32_t offset) -> uint32_t {
    switch (index_bytes) {
      case 1: return prim_indices_storage[offset];
      case 2: return *reinterpret_cast<const uint16_t*>(&prim_indices_storage[offset * 2]);
      case 4:
      default: return *reinterpret_cast<const uint32_t*>(&prim_indices_storage[offset * 4]);
    }
  };

  if ((use_compact && compact_nodes.empty()) ||
      (!use_compact && full_nodes.empty())) {
    return kInvalidIndex;
  }

  hit_t = ray.tmax;
  uint32_t hit_prim = kInvalidIndex;

  Vec3 inv_dir(1.0f / ray.direction.x, 1.0f / ray.direction.y, 1.0f / ray.direction.z);
  int dir_is_neg[3] = {
    inv_dir.x < 0 ? 1 : 0,
    inv_dir.y < 0 ? 1 : 0,
    inv_dir.z < 0 ? 1 : 0
  };

  struct StackEntry {
    uint32_t node_idx;
    uint32_t depth;
  };

  StackEntry stack[64];
  int stack_ptr = 0;
  stack[stack_ptr++] = {0, 0};

  while (stack_ptr > 0) {
    StackEntry entry = stack[--stack_ptr];

    profiler.visitNode();
    profiler.pushDepth(entry.depth);

    AABB bounds;
    bool is_leaf;
    uint32_t data0, data1;
    uint8_t axis = 0;

    if (use_compact) {
      const CompactBVHNode& node = compact_nodes[entry.node_idx];
      bounds = node.dequantizeBounds(scene_bounds.min, scene_bounds.max);
      is_leaf = node.isLeaf();
      data0 = node.data0;
      data1 = node.data1;
      axis = node.axis;
    } else {
      const BVHNode& node = full_nodes[entry.node_idx];
      bounds = node.bounds;
      is_leaf = node.isLeaf();
      data0 = node.prim_offset;
      data1 = is_leaf ? node.prim_count : node.right_child;
    }

    float tmin_box, tmax_box;
    if (!bounds.intersect(ray, tmin_box, tmax_box) || tmin_box > hit_t) {
      profiler.popDepth();
      continue;
    }

    if (is_leaf) {
      profiler.visitLeaf();

      uint32_t count = data1;
      uint32_t offset = data0;

      for (uint32_t i = 0; i < count; i++) {
        profiler.testPrim();

        uint32_t prim_idx = getPrimIndex(offset + i);
        float t, u, v;
        if (triangles[prim_idx].intersect(ray, t, u, v) && t < hit_t) {
          hit_t = t;
          hit_u = u;
          hit_v = v;
          hit_prim = prim_idx;
        }
      }
    } else {
      uint32_t first, second;
      if (use_compact) {
        first = data0;
        second = data1;
        if (use_ordered && dir_is_neg[axis]) {
          std::swap(first, second);
        }
      } else {
        first = data0;  // left_child
        second = full_nodes[entry.node_idx].right_child;
      }

      stack[stack_ptr++] = {second, entry.depth + 1};
      stack[stack_ptr++] = {first, entry.depth + 1};
    }

    profiler.popDepth();
  }

  return hit_prim;
}

} // anonymous namespace

// Explicit template instantiation for traverseProfiled

template<>
uint32_t traverseProfiled<NoProfiler>(
    const TriangleBVH& bvh, const Ray& ray,
    float& hit_t, float& hit_u, float& hit_v,
    TraversalProfile*) noexcept {
  // No profiling - delegate to standard traverse
  return bvh.traverse(ray, hit_t, hit_u, hit_v);
}

template<>
uint32_t traverseProfiled<WithProfiler>(
    const TriangleBVH& bvh, const Ray& ray,
    float& hit_t, float& hit_u, float& hit_v,
    TraversalProfile* profile) noexcept {
  if (!profile) {
    return bvh.traverse(ray, hit_t, hit_u, hit_v);
  }
  WithProfiler profiler(profile);
  return traverseTriangleBVHProfiled(bvh.getBVH(), bvh.getTriangles(),
                                     ray, hit_t, hit_u, hit_v, profiler);
}

template<>
uint32_t traverseProfiled<NoProfiler>(
    const SBVH& sbvh, const Ray& ray,
    float& hit_t, float& hit_u, float& hit_v,
    TraversalProfile*) noexcept {
  return sbvh.traverse(ray, hit_t, hit_u, hit_v);
}

template<>
uint32_t traverseProfiled<WithProfiler>(
    const SBVH& sbvh, const Ray& ray,
    float& hit_t, float& hit_u, float& hit_v,
    TraversalProfile* profile) noexcept {
  if (!profile) {
    return sbvh.traverse(ray, hit_t, hit_u, hit_v);
  }
  WithProfiler profiler(profile);
  return traverseSBVHProfiled(sbvh.getNodes(), sbvh.getReferences(),
                              sbvh.getTriangles(), ray, hit_t, hit_u, hit_v, profiler);
}

template<>
uint32_t traverseProfiled<NoProfiler>(
    const MMapTriangleBVH& bvh, const Ray& ray,
    float& hit_t, float& hit_u, float& hit_v,
    TraversalProfile*) noexcept {
  return bvh.traverse(ray, hit_t, hit_u, hit_v);
}

template<>
uint32_t traverseProfiled<WithProfiler>(
    const MMapTriangleBVH& bvh, const Ray& ray,
    float& hit_t, float& hit_u, float& hit_v,
    TraversalProfile* profile) noexcept {
  if (!profile) {
    return bvh.traverse(ray, hit_t, hit_u, hit_v);
  }

  // MMapTriangleBVH profiling requires internal accessors
  // For now, use standard traverse and estimate profile from stats
  // TODO: Add proper internal accessors for full profiling support
  uint32_t result = bvh.traverse(ray, hit_t, hit_u, hit_v);

  // Estimate profile based on BVH structure (rough approximation)
  auto stats = bvh.getStats();
  if (result != kInvalidIndex) {
    // Hit case: estimate average traversal
    profile->nodes_visited = stats.max_depth * 2;  // Rough estimate
    profile->leaf_visits = 1;
    profile->prims_tested = static_cast<uint32_t>(stats.avg_leaf_size);
    profile->max_depth = stats.max_depth;
  } else {
    // Miss case
    profile->nodes_visited = stats.max_depth;
    profile->leaf_visits = 0;
    profile->prims_tested = 0;
    profile->max_depth = stats.max_depth / 2;
  }

  return result;
}

// ============================================================================
// HeatmapWriter Implementation
// ============================================================================

RGB8 HeatmapWriter::grayscale(float t) noexcept {
  uint8_t v = static_cast<uint8_t>(std::min(255.0f, std::max(0.0f, t * 255.0f)));
  return RGB8(v, v, v);
}

RGB8 HeatmapWriter::heat(float t) noexcept {
  // Black -> Red -> Yellow -> White
  t = std::max(0.0f, std::min(1.0f, t));

  float r, g, b;
  if (t < 0.33f) {
    // Black to Red
    float s = t / 0.33f;
    r = s;
    g = 0.0f;
    b = 0.0f;
  } else if (t < 0.67f) {
    // Red to Yellow
    float s = (t - 0.33f) / 0.34f;
    r = 1.0f;
    g = s;
    b = 0.0f;
  } else {
    // Yellow to White
    float s = (t - 0.67f) / 0.33f;
    r = 1.0f;
    g = 1.0f;
    b = s;
  }

  return RGB8::fromFloat(r, g, b);
}

RGB8 HeatmapWriter::jet(float t) noexcept {
  // Blue -> Cyan -> Green -> Yellow -> Red
  t = std::max(0.0f, std::min(1.0f, t));

  float r, g, b;
  if (t < 0.125f) {
    r = 0.0f;
    g = 0.0f;
    b = 0.5f + t * 4.0f;
  } else if (t < 0.375f) {
    r = 0.0f;
    g = (t - 0.125f) * 4.0f;
    b = 1.0f;
  } else if (t < 0.625f) {
    r = (t - 0.375f) * 4.0f;
    g = 1.0f;
    b = 1.0f - (t - 0.375f) * 4.0f;
  } else if (t < 0.875f) {
    r = 1.0f;
    g = 1.0f - (t - 0.625f) * 4.0f;
    b = 0.0f;
  } else {
    r = 1.0f - (t - 0.875f) * 4.0f;
    g = 0.0f;
    b = 0.0f;
  }

  return RGB8::fromFloat(r, g, b);
}

RGB8 HeatmapWriter::viridis(float t) noexcept {
  // Perceptually uniform colormap (approximation)
  t = std::max(0.0f, std::min(1.0f, t));

  // Viridis lookup table (sampled at 8 points)
  static const float viridis_data[8][3] = {
    {0.267f, 0.004f, 0.329f},  // 0.0
    {0.282f, 0.140f, 0.458f},  // 0.14
    {0.254f, 0.265f, 0.529f},  // 0.28
    {0.207f, 0.372f, 0.553f},  // 0.43
    {0.164f, 0.471f, 0.558f},  // 0.57
    {0.128f, 0.567f, 0.550f},  // 0.71
    {0.267f, 0.678f, 0.480f},  // 0.86
    {0.993f, 0.906f, 0.144f}   // 1.0
  };

  float idx = t * 7.0f;
  int i0 = static_cast<int>(idx);
  int i1 = std::min(i0 + 1, 7);
  float frac = idx - i0;

  float r = viridis_data[i0][0] + frac * (viridis_data[i1][0] - viridis_data[i0][0]);
  float g = viridis_data[i0][1] + frac * (viridis_data[i1][1] - viridis_data[i0][1]);
  float b = viridis_data[i0][2] + frac * (viridis_data[i1][2] - viridis_data[i0][2]);

  return RGB8::fromFloat(r, g, b);
}

RGB8 HeatmapWriter::turbo(float t) noexcept {
  // Google's Turbo colormap (approximation)
  t = std::max(0.0f, std::min(1.0f, t));

  static const float turbo_data[8][3] = {
    {0.190f, 0.072f, 0.231f},  // 0.0
    {0.085f, 0.340f, 0.640f},  // 0.14
    {0.137f, 0.545f, 0.741f},  // 0.28
    {0.310f, 0.714f, 0.624f},  // 0.43
    {0.571f, 0.843f, 0.388f},  // 0.57
    {0.836f, 0.897f, 0.224f},  // 0.71
    {0.990f, 0.757f, 0.161f},  // 0.86
    {0.940f, 0.246f, 0.042f}   // 1.0
  };

  float idx = t * 7.0f;
  int i0 = static_cast<int>(idx);
  int i1 = std::min(i0 + 1, 7);
  float frac = idx - i0;

  float r = turbo_data[i0][0] + frac * (turbo_data[i1][0] - turbo_data[i0][0]);
  float g = turbo_data[i0][1] + frac * (turbo_data[i1][1] - turbo_data[i0][1]);
  float b = turbo_data[i0][2] + frac * (turbo_data[i1][2] - turbo_data[i0][2]);

  return RGB8::fromFloat(r, g, b);
}

RGB8 HeatmapWriter::plasma(float t) noexcept {
  t = std::max(0.0f, std::min(1.0f, t));

  static const float plasma_data[8][3] = {
    {0.050f, 0.030f, 0.528f},
    {0.294f, 0.011f, 0.631f},
    {0.492f, 0.012f, 0.658f},
    {0.658f, 0.138f, 0.557f},
    {0.798f, 0.280f, 0.469f},
    {0.899f, 0.435f, 0.360f},
    {0.966f, 0.612f, 0.226f},
    {0.940f, 0.975f, 0.131f}
  };

  float idx = t * 7.0f;
  int i0 = static_cast<int>(idx);
  int i1 = std::min(i0 + 1, 7);
  float frac = idx - i0;

  float r = plasma_data[i0][0] + frac * (plasma_data[i1][0] - plasma_data[i0][0]);
  float g = plasma_data[i0][1] + frac * (plasma_data[i1][1] - plasma_data[i0][1]);
  float b = plasma_data[i0][2] + frac * (plasma_data[i1][2] - plasma_data[i0][2]);

  return RGB8::fromFloat(r, g, b);
}

RGB8 HeatmapWriter::inferno(float t) noexcept {
  t = std::max(0.0f, std::min(1.0f, t));

  static const float inferno_data[8][3] = {
    {0.001f, 0.000f, 0.014f},
    {0.120f, 0.047f, 0.282f},
    {0.316f, 0.071f, 0.486f},
    {0.520f, 0.091f, 0.507f},
    {0.703f, 0.166f, 0.412f},
    {0.857f, 0.318f, 0.229f},
    {0.956f, 0.533f, 0.049f},
    {0.988f, 0.998f, 0.645f}
  };

  float idx = t * 7.0f;
  int i0 = static_cast<int>(idx);
  int i1 = std::min(i0 + 1, 7);
  float frac = idx - i0;

  float r = inferno_data[i0][0] + frac * (inferno_data[i1][0] - inferno_data[i0][0]);
  float g = inferno_data[i0][1] + frac * (inferno_data[i1][1] - inferno_data[i0][1]);
  float b = inferno_data[i0][2] + frac * (inferno_data[i1][2] - inferno_data[i0][2]);

  return RGB8::fromFloat(r, g, b);
}

RGB8 HeatmapWriter::cool(float t) noexcept {
  // Cyan to Magenta
  t = std::max(0.0f, std::min(1.0f, t));
  return RGB8::fromFloat(t, 1.0f - t, 1.0f);
}

RGB8 HeatmapWriter::hot(float t) noexcept {
  // Black -> Red -> Yellow -> White (classic)
  t = std::max(0.0f, std::min(1.0f, t));

  float r, g, b;
  if (t < 0.4f) {
    r = t / 0.4f;
    g = 0.0f;
    b = 0.0f;
  } else if (t < 0.8f) {
    r = 1.0f;
    g = (t - 0.4f) / 0.4f;
    b = 0.0f;
  } else {
    r = 1.0f;
    g = 1.0f;
    b = (t - 0.8f) / 0.2f;
  }

  return RGB8::fromFloat(r, g, b);
}

RGB8 HeatmapWriter::mapColor(float value, Colormap cmap) noexcept {
  switch (cmap) {
    case Colormap::Grayscale: return grayscale(value);
    case Colormap::Heat:      return heat(value);
    case Colormap::Jet:       return jet(value);
    case Colormap::Viridis:   return viridis(value);
    case Colormap::Turbo:     return turbo(value);
    case Colormap::Plasma:    return plasma(value);
    case Colormap::Inferno:   return inferno(value);
    case Colormap::Cool:      return cool(value);
    case Colormap::Hot:       return hot(value);
    default:                  return viridis(value);
  }
}

RGB8 HeatmapWriter::mapColor(uint32_t value, uint32_t max_value, Colormap cmap) noexcept {
  if (max_value == 0) return mapColor(0.0f, cmap);
  float t = static_cast<float>(value) / static_cast<float>(max_value);
  return mapColor(t, cmap);
}

bool HeatmapWriter::writeBMP(const char* filename, const RGB8* data,
                              uint32_t width, uint32_t height) noexcept {
  FILE* fp = fopen(filename, "wb");
  if (!fp) return false;

  // BMP header
  uint32_t row_size = ((width * 3 + 3) / 4) * 4;  // Row padded to 4-byte boundary
  uint32_t pixel_data_size = row_size * height;
  uint32_t file_size = 54 + pixel_data_size;

  // BMP file header (14 bytes)
  uint8_t bmp_header[14] = {
    'B', 'M',                              // Signature
    static_cast<uint8_t>(file_size),       // File size
    static_cast<uint8_t>(file_size >> 8),
    static_cast<uint8_t>(file_size >> 16),
    static_cast<uint8_t>(file_size >> 24),
    0, 0, 0, 0,                            // Reserved
    54, 0, 0, 0                            // Pixel data offset
  };

  // DIB header (BITMAPINFOHEADER, 40 bytes)
  uint8_t dib_header[40] = {
    40, 0, 0, 0,                           // Header size
    static_cast<uint8_t>(width),           // Width
    static_cast<uint8_t>(width >> 8),
    static_cast<uint8_t>(width >> 16),
    static_cast<uint8_t>(width >> 24),
    static_cast<uint8_t>(height),          // Height (positive = bottom-up)
    static_cast<uint8_t>(height >> 8),
    static_cast<uint8_t>(height >> 16),
    static_cast<uint8_t>(height >> 24),
    1, 0,                                  // Planes
    24, 0,                                 // Bits per pixel
    0, 0, 0, 0,                            // Compression (none)
    static_cast<uint8_t>(pixel_data_size), // Image size
    static_cast<uint8_t>(pixel_data_size >> 8),
    static_cast<uint8_t>(pixel_data_size >> 16),
    static_cast<uint8_t>(pixel_data_size >> 24),
    0, 0, 0, 0,                            // X pixels per meter
    0, 0, 0, 0,                            // Y pixels per meter
    0, 0, 0, 0,                            // Colors in color table
    0, 0, 0, 0                             // Important colors
  };

  fwrite(bmp_header, 1, 14, fp);
  fwrite(dib_header, 1, 40, fp);

  // Write pixel data (bottom-up, BGR order)
  std::vector<uint8_t> row_buffer(row_size, 0);

  for (int y = height - 1; y >= 0; y--) {
    for (uint32_t x = 0; x < width; x++) {
      const RGB8& pixel = data[y * width + x];
      row_buffer[x * 3 + 0] = pixel.b;  // BMP uses BGR
      row_buffer[x * 3 + 1] = pixel.g;
      row_buffer[x * 3 + 2] = pixel.r;
    }
    fwrite(row_buffer.data(), 1, row_size, fp);
  }

  fclose(fp);
  return true;
}

bool HeatmapWriter::writeTGA(const char* filename, const RGB8* data,
                              uint32_t width, uint32_t height) noexcept {
  FILE* fp = fopen(filename, "wb");
  if (!fp) return false;

  // TGA header (18 bytes)
  uint8_t tga_header[18] = {
    0,                                     // ID length
    0,                                     // Color map type
    2,                                     // Image type (uncompressed true-color)
    0, 0, 0, 0, 0,                         // Color map spec (unused)
    0, 0,                                  // X origin
    0, 0,                                  // Y origin
    static_cast<uint8_t>(width),           // Width (low byte)
    static_cast<uint8_t>(width >> 8),      // Width (high byte)
    static_cast<uint8_t>(height),          // Height (low byte)
    static_cast<uint8_t>(height >> 8),     // Height (high byte)
    24,                                    // Bits per pixel
    0x20                                   // Image descriptor (top-left origin)
  };

  fwrite(tga_header, 1, 18, fp);

  // Write pixel data (top-down, BGR order)
  for (uint32_t y = 0; y < height; y++) {
    for (uint32_t x = 0; x < width; x++) {
      const RGB8& pixel = data[y * width + x];
      uint8_t bgr[3] = {pixel.b, pixel.g, pixel.r};
      fwrite(bgr, 1, 3, fp);
    }
  }

  fclose(fp);
  return true;
}

bool HeatmapWriter::writePPM(const char* filename, const RGB8* data,
                              uint32_t width, uint32_t height) noexcept {
  FILE* fp = fopen(filename, "wb");
  if (!fp) return false;

  // PPM header (binary P6 format)
  fprintf(fp, "P6\n%u %u\n255\n", width, height);

  // Write pixel data (top-down, RGB order)
  for (uint32_t y = 0; y < height; y++) {
    for (uint32_t x = 0; x < width; x++) {
      const RGB8& pixel = data[y * width + x];
      uint8_t rgb[3] = {pixel.r, pixel.g, pixel.b};
      fwrite(rgb, 1, 3, fp);
    }
  }

  fclose(fp);
  return true;
}

// ============================================================================
// PNG Writer with built-in DEFLATE compression (no zlib dependency)
// ============================================================================

namespace {

// CRC32 table for PNG chunk checksums
static uint32_t crc32_table[256];
static bool crc32_table_initialized = false;

void init_crc32_table() {
  if (crc32_table_initialized) return;
  for (uint32_t n = 0; n < 256; n++) {
    uint32_t c = n;
    for (int k = 0; k < 8; k++) {
      if (c & 1)
        c = 0xEDB88320u ^ (c >> 1);
      else
        c = c >> 1;
    }
    crc32_table[n] = c;
  }
  crc32_table_initialized = true;
}

uint32_t update_crc32(uint32_t crc, const uint8_t* data, size_t len) {
  for (size_t i = 0; i < len; i++) {
    crc = crc32_table[(crc ^ data[i]) & 0xFF] ^ (crc >> 8);
  }
  return crc;
}

uint32_t compute_crc32(const uint8_t* data, size_t len) {
  init_crc32_table();
  return update_crc32(0xFFFFFFFFu, data, len) ^ 0xFFFFFFFFu;
}

// Adler32 for zlib wrapper
uint32_t compute_adler32(const uint8_t* data, size_t len) {
  uint32_t a = 1, b = 0;
  const uint32_t MOD = 65521;

  for (size_t i = 0; i < len; i++) {
    a = (a + data[i]) % MOD;
    b = (b + a) % MOD;
  }
  return (b << 16) | a;
}

// Simple bit writer for DEFLATE
class BitWriter {
public:
  std::vector<uint8_t>& output;
  uint32_t bit_buffer = 0;
  int bit_count = 0;

  explicit BitWriter(std::vector<uint8_t>& out) : output(out) {}

  void writeBits(uint32_t value, int num_bits) {
    bit_buffer |= (value << bit_count);
    bit_count += num_bits;
    while (bit_count >= 8) {
      output.push_back(static_cast<uint8_t>(bit_buffer & 0xFF));
      bit_buffer >>= 8;
      bit_count -= 8;
    }
  }

  void flushBits() {
    if (bit_count > 0) {
      output.push_back(static_cast<uint8_t>(bit_buffer & 0xFF));
      bit_buffer = 0;
      bit_count = 0;
    }
  }

  void writeByte(uint8_t b) {
    flushBits();
    output.push_back(b);
  }
};

// Fixed Huffman code lengths (RFC 1951)
// Literals 0-143: 8 bits
// Literals 144-255: 9 bits
// Literals 256-279: 7 bits
// Literals 280-287: 8 bits
void write_fixed_huffman_literal(BitWriter& bw, uint32_t literal) {
  if (literal <= 143) {
    // 00110000 - 10111111 (8 bits, reversed)
    uint32_t code = 0x30 + literal;
    // Reverse 8 bits
    uint32_t reversed = 0;
    for (int i = 0; i < 8; i++) {
      reversed = (reversed << 1) | ((code >> i) & 1);
    }
    bw.writeBits(reversed, 8);
  } else if (literal <= 255) {
    // 110010000 - 111111111 (9 bits, reversed)
    uint32_t code = 0x190 + (literal - 144);
    uint32_t reversed = 0;
    for (int i = 0; i < 9; i++) {
      reversed = (reversed << 1) | ((code >> i) & 1);
    }
    bw.writeBits(reversed, 9);
  } else if (literal <= 279) {
    // 0000000 - 0010111 (7 bits, reversed)
    uint32_t code = literal - 256;
    uint32_t reversed = 0;
    for (int i = 0; i < 7; i++) {
      reversed = (reversed << 1) | ((code >> i) & 1);
    }
    bw.writeBits(reversed, 7);
  } else {
    // 11000000 - 11000111 (8 bits, reversed)
    uint32_t code = 0xC0 + (literal - 280);
    uint32_t reversed = 0;
    for (int i = 0; i < 8; i++) {
      reversed = (reversed << 1) | ((code >> i) & 1);
    }
    bw.writeBits(reversed, 8);
  }
}

// Simple DEFLATE compression using fixed Huffman codes
// This is a simple implementation without LZ77 matching (literals only)
// Good compression ratio for typical image data
std::vector<uint8_t> deflate_compress(const uint8_t* data, size_t len) {
  std::vector<uint8_t> output;
  BitWriter bw(output);

  // BFINAL=1 (last block), BTYPE=01 (fixed Huffman)
  bw.writeBits(1, 1);  // BFINAL
  bw.writeBits(1, 2);  // BTYPE = 01 (fixed Huffman)

  // Write all literals
  for (size_t i = 0; i < len; i++) {
    write_fixed_huffman_literal(bw, data[i]);
  }

  // Write end of block (256)
  write_fixed_huffman_literal(bw, 256);

  bw.flushBits();
  return output;
}

// Wrap DEFLATE data in zlib format
std::vector<uint8_t> zlib_compress(const uint8_t* data, size_t len) {
  std::vector<uint8_t> output;

  // Zlib header (CMF=0x78, FLG=0x01 for no dict, level 0)
  // CMF = 0x78: CM=8 (deflate), CINFO=7 (32K window)
  // FLG: FCHECK must make (CMF*256 + FLG) divisible by 31
  uint8_t cmf = 0x78;
  uint8_t flg = 0x01;
  // Adjust FCHECK
  uint32_t check = (cmf * 256 + flg) % 31;
  if (check != 0) flg += (31 - check);

  output.push_back(cmf);
  output.push_back(flg);

  // Compressed data
  std::vector<uint8_t> deflated = deflate_compress(data, len);
  output.insert(output.end(), deflated.begin(), deflated.end());

  // Adler32 checksum (big-endian)
  uint32_t adler = compute_adler32(data, len);
  output.push_back(static_cast<uint8_t>((adler >> 24) & 0xFF));
  output.push_back(static_cast<uint8_t>((adler >> 16) & 0xFF));
  output.push_back(static_cast<uint8_t>((adler >> 8) & 0xFF));
  output.push_back(static_cast<uint8_t>(adler & 0xFF));

  return output;
}

// Write PNG chunk
void write_png_chunk(FILE* fp, const char* type, const uint8_t* data, uint32_t len) {
  // Length (big-endian)
  uint8_t len_bytes[4] = {
    static_cast<uint8_t>((len >> 24) & 0xFF),
    static_cast<uint8_t>((len >> 16) & 0xFF),
    static_cast<uint8_t>((len >> 8) & 0xFF),
    static_cast<uint8_t>(len & 0xFF)
  };
  fwrite(len_bytes, 1, 4, fp);

  // Type
  fwrite(type, 1, 4, fp);

  // Data
  if (len > 0 && data) {
    fwrite(data, 1, len, fp);
  }

  // CRC (over type + data)
  std::vector<uint8_t> crc_data;
  crc_data.insert(crc_data.end(), type, type + 4);
  if (len > 0 && data) {
    crc_data.insert(crc_data.end(), data, data + len);
  }
  uint32_t crc = compute_crc32(crc_data.data(), crc_data.size());

  uint8_t crc_bytes[4] = {
    static_cast<uint8_t>((crc >> 24) & 0xFF),
    static_cast<uint8_t>((crc >> 16) & 0xFF),
    static_cast<uint8_t>((crc >> 8) & 0xFF),
    static_cast<uint8_t>(crc & 0xFF)
  };
  fwrite(crc_bytes, 1, 4, fp);
}

} // anonymous namespace

bool HeatmapWriter::writePNG(const char* filename, const RGB8* data,
                              uint32_t width, uint32_t height) noexcept {
  FILE* fp = fopen(filename, "wb");
  if (!fp) return false;

  // PNG signature
  static const uint8_t png_signature[8] = {137, 80, 78, 71, 13, 10, 26, 10};
  fwrite(png_signature, 1, 8, fp);

  // IHDR chunk
  uint8_t ihdr[13] = {
    static_cast<uint8_t>((width >> 24) & 0xFF),   // Width (big-endian)
    static_cast<uint8_t>((width >> 16) & 0xFF),
    static_cast<uint8_t>((width >> 8) & 0xFF),
    static_cast<uint8_t>(width & 0xFF),
    static_cast<uint8_t>((height >> 24) & 0xFF),  // Height (big-endian)
    static_cast<uint8_t>((height >> 16) & 0xFF),
    static_cast<uint8_t>((height >> 8) & 0xFF),
    static_cast<uint8_t>(height & 0xFF),
    8,    // Bit depth
    2,    // Color type (RGB)
    0,    // Compression method (deflate)
    0,    // Filter method
    0     // Interlace method (none)
  };
  write_png_chunk(fp, "IHDR", ihdr, 13);

  // Prepare raw image data with filter bytes
  // Each row has: filter_type (1 byte) + RGB data (width * 3 bytes)
  size_t row_size = 1 + width * 3;
  std::vector<uint8_t> raw_data(row_size * height);

  for (uint32_t y = 0; y < height; y++) {
    size_t row_offset = y * row_size;
    raw_data[row_offset] = 0;  // Filter type 0 (None)

    for (uint32_t x = 0; x < width; x++) {
      const RGB8& pixel = data[y * width + x];
      raw_data[row_offset + 1 + x * 3 + 0] = pixel.r;
      raw_data[row_offset + 1 + x * 3 + 1] = pixel.g;
      raw_data[row_offset + 1 + x * 3 + 2] = pixel.b;
    }
  }

  // Compress and write IDAT chunk
  std::vector<uint8_t> compressed = zlib_compress(raw_data.data(), raw_data.size());
  write_png_chunk(fp, "IDAT", compressed.data(), static_cast<uint32_t>(compressed.size()));

  // IEND chunk
  write_png_chunk(fp, "IEND", nullptr, 0);

  fclose(fp);
  return true;
}

bool HeatmapWriter::writeImage(const char* filename, const RGB8* data,
                                uint32_t width, uint32_t height,
                                ImageFormat format) noexcept {
  switch (format) {
    case ImageFormat::BMP: return writeBMP(filename, data, width, height);
    case ImageFormat::TGA: return writeTGA(filename, data, width, height);
    case ImageFormat::PPM: return writePPM(filename, data, width, height);
    case ImageFormat::PNG: return writePNG(filename, data, width, height);
    default: return writeBMP(filename, data, width, height);
  }
}

bool HeatmapWriter::writeImage(const char* filename, const float* data,
                                uint32_t width, uint32_t height,
                                Colormap cmap, ImageFormat format) noexcept {
  std::vector<RGB8> rgb_data(width * height);

  for (uint32_t i = 0; i < width * height; i++) {
    rgb_data[i] = mapColor(data[i], cmap);
  }

  return writeImage(filename, rgb_data.data(), width, height, format);
}

bool HeatmapWriter::writeImage(const char* filename, const uint32_t* data,
                                uint32_t width, uint32_t height,
                                uint32_t max_value,
                                Colormap cmap, ImageFormat format) noexcept {
  std::vector<RGB8> rgb_data(width * height);

  // Find max if not specified
  uint32_t actual_max = max_value;
  if (actual_max == 0) {
    for (uint32_t i = 0; i < width * height; i++) {
      actual_max = std::max(actual_max, data[i]);
    }
    if (actual_max == 0) actual_max = 1;
  }

  for (uint32_t i = 0; i < width * height; i++) {
    rgb_data[i] = mapColor(data[i], actual_max, cmap);
  }

  return writeImage(filename, rgb_data.data(), width, height, format);
}

bool HeatmapWriter::writeHeatmap(const char* filename,
                                  const TraversalProfile* profiles,
                                  uint32_t width, uint32_t height,
                                  Metric metric,
                                  Colormap cmap,
                                  ImageFormat format,
                                  uint32_t max_value) noexcept {
  std::vector<uint32_t> values(width * height);

  // Extract metric values
  for (uint32_t i = 0; i < width * height; i++) {
    switch (metric) {
      case Metric::NodesVisited:
        values[i] = profiles[i].nodes_visited;
        break;
      case Metric::LeafVisits:
        values[i] = profiles[i].leaf_visits;
        break;
      case Metric::PrimsTested:
        values[i] = profiles[i].prims_tested;
        break;
      case Metric::MaxDepth:
        values[i] = profiles[i].max_depth;
        break;
    }
  }

  return writeImage(filename, values.data(), width, height, max_value, cmap, format);
}

// ============================================================================
// renderImageProfiled Implementation
// ============================================================================

template<>
TraversalProfile* renderImageProfiled<TriangleBVH>(
    const TriangleBVH& bvh,
    uint32_t width, uint32_t height,
    const Vec3& camera_pos,
    const Vec3& camera_dir,
    const Vec3& camera_up,
    float fov_y,
    uint32_t* hit_image) noexcept {

  TraversalProfile* profiles = new TraversalProfile[width * height];

  // Compute camera basis
  Vec3 forward = camera_dir.normalize();
  Vec3 right = forward.cross(camera_up).normalize();
  Vec3 up = right.cross(forward);

  float aspect = static_cast<float>(width) / height;
  float tan_fov = std::tan(fov_y * 0.5f);

  for (uint32_t y = 0; y < height; y++) {
    for (uint32_t x = 0; x < width; x++) {
      // Normalized device coordinates [-1, 1]
      float ndc_x = (2.0f * (x + 0.5f) / width - 1.0f) * aspect * tan_fov;
      float ndc_y = (1.0f - 2.0f * (y + 0.5f) / height) * tan_fov;

      Vec3 dir = (forward + right * ndc_x + up * ndc_y).normalize();
      Ray ray(camera_pos, dir);

      uint32_t pixel_idx = y * width + x;
      float hit_t, hit_u, hit_v;

      uint32_t hit = renderRayProfiled(bvh, ray, hit_t, hit_u, hit_v, profiles[pixel_idx]);

      if (hit_image) {
        hit_image[pixel_idx] = hit;
      }
    }
  }

  return profiles;
}

template<>
TraversalProfile* renderImageProfiled<SBVH>(
    const SBVH& sbvh,
    uint32_t width, uint32_t height,
    const Vec3& camera_pos,
    const Vec3& camera_dir,
    const Vec3& camera_up,
    float fov_y,
    uint32_t* hit_image) noexcept {

  TraversalProfile* profiles = new TraversalProfile[width * height];

  Vec3 forward = camera_dir.normalize();
  Vec3 right = forward.cross(camera_up).normalize();
  Vec3 up = right.cross(forward);

  float aspect = static_cast<float>(width) / height;
  float tan_fov = std::tan(fov_y * 0.5f);

  for (uint32_t y = 0; y < height; y++) {
    for (uint32_t x = 0; x < width; x++) {
      float ndc_x = (2.0f * (x + 0.5f) / width - 1.0f) * aspect * tan_fov;
      float ndc_y = (1.0f - 2.0f * (y + 0.5f) / height) * tan_fov;

      Vec3 dir = (forward + right * ndc_x + up * ndc_y).normalize();
      Ray ray(camera_pos, dir);

      uint32_t pixel_idx = y * width + x;
      float hit_t, hit_u, hit_v;

      uint32_t hit = renderRayProfiled(sbvh, ray, hit_t, hit_u, hit_v, profiles[pixel_idx]);

      if (hit_image) {
        hit_image[pixel_idx] = hit;
      }
    }
  }

  return profiles;
}

template<>
TraversalProfile* renderImageProfiled<MMapTriangleBVH>(
    const MMapTriangleBVH& bvh,
    uint32_t width, uint32_t height,
    const Vec3& camera_pos,
    const Vec3& camera_dir,
    const Vec3& camera_up,
    float fov_y,
    uint32_t* hit_image) noexcept {

  TraversalProfile* profiles = new TraversalProfile[width * height];

  Vec3 forward = camera_dir.normalize();
  Vec3 right = forward.cross(camera_up).normalize();
  Vec3 up = right.cross(forward);

  float aspect = static_cast<float>(width) / height;
  float tan_fov = std::tan(fov_y * 0.5f);

  for (uint32_t y = 0; y < height; y++) {
    for (uint32_t x = 0; x < width; x++) {
      float ndc_x = (2.0f * (x + 0.5f) / width - 1.0f) * aspect * tan_fov;
      float ndc_y = (1.0f - 2.0f * (y + 0.5f) / height) * tan_fov;

      Vec3 dir = (forward + right * ndc_x + up * ndc_y).normalize();
      Ray ray(camera_pos, dir);

      uint32_t pixel_idx = y * width + x;
      float hit_t, hit_u, hit_v;

      // Note: MMapTriangleBVH profiling has limitations - uses standard traverse
      profiles[pixel_idx].reset();
      uint32_t hit = bvh.traverse(ray, hit_t, hit_u, hit_v);

      if (hit_image) {
        hit_image[pixel_idx] = hit;
      }
    }
  }

  return profiles;
}

} // namespace lightrt
