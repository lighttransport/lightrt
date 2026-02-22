// Scene graph for CLI renderer
// Provides per-instance transforms, motion blur, and USD camera support
#pragma once

#include "lightrt.hh"
#include <vector>
#include <string>
#include <cmath>
#include <cstring>
#include <limits>

namespace scene {

struct MeshBLAS {
  lightrt::TriangleBVH bvh;
  lightrt::AABB local_bounds;
};

struct Instance {
  uint32_t mesh_id;
  float transform[12];       // 3x4 row-major (rows 0-2 of 4x4)
  float inv_transform[12];
  float transform_close[12]; // transform at shutter close
  float inv_transform_close[12];
  bool has_motion = false;
  lightrt::AABB world_bounds;
};

struct Camera {
  std::string name;
  float fov_y_rad = 0.7854f; // 45 degrees
  float znear = 0.1f;
  float zfar = 1000000.0f;
  float transform[16]; // 4x4 row-major
  double shutter_open = 0.0;
  double shutter_close = 0.0;
};

struct HitInfo {
  uint32_t instance_id = lightrt::kInvalidIndex;
  uint32_t triangle_id = lightrt::kInvalidIndex;
  float t = std::numeric_limits<float>::max();
  float u = 0.0f;
  float v = 0.0f;
};

struct Scene {
  std::vector<MeshBLAS> meshes;
  std::vector<Instance> instances;
  std::vector<Camera> cameras;
  lightrt::AABB scene_bounds;
};

// --- Transform utilities ---

inline void matrix4dTo3x4(const double m[4][4], float out[12]) {
  for (int r = 0; r < 3; r++)
    for (int c = 0; c < 4; c++)
      out[r * 4 + c] = static_cast<float>(m[r][c]);
}

inline bool invert3x4(const float m[12], float inv[12]) {
  // Extract 3x3 rotation/scale part
  float a00 = m[0], a01 = m[1], a02 = m[2];
  float a10 = m[4], a11 = m[5], a12 = m[6];
  float a20 = m[8], a21 = m[9], a22 = m[10];

  float det = a00 * (a11 * a22 - a12 * a21)
            - a01 * (a10 * a22 - a12 * a20)
            + a02 * (a10 * a21 - a11 * a20);

  if (std::fabs(det) < 1e-12f) return false;

  float inv_det = 1.0f / det;

  // Inverse of 3x3
  float i00 = (a11 * a22 - a12 * a21) * inv_det;
  float i01 = (a02 * a21 - a01 * a22) * inv_det;
  float i02 = (a01 * a12 - a02 * a11) * inv_det;
  float i10 = (a12 * a20 - a10 * a22) * inv_det;
  float i11 = (a00 * a22 - a02 * a20) * inv_det;
  float i12 = (a02 * a10 - a00 * a12) * inv_det;
  float i20 = (a10 * a21 - a11 * a20) * inv_det;
  float i21 = (a01 * a20 - a00 * a21) * inv_det;
  float i22 = (a00 * a11 - a01 * a10) * inv_det;

  inv[0] = i00; inv[1] = i01; inv[2] = i02;
  inv[4] = i10; inv[5] = i11; inv[6] = i12;
  inv[8] = i20; inv[9] = i21; inv[10] = i22;

  // Translation: -R^-1 * t
  float tx = m[3], ty = m[7], tz = m[11];
  inv[3]  = -(i00 * tx + i01 * ty + i02 * tz);
  inv[7]  = -(i10 * tx + i11 * ty + i12 * tz);
  inv[11] = -(i20 * tx + i21 * ty + i22 * tz);

  return true;
}

inline void lerp3x4(const float a[12], const float b[12], float t, float out[12]) {
  for (int i = 0; i < 12; i++)
    out[i] = a[i] + (b[i] - a[i]) * t;
}

inline lightrt::Vec3 transformPoint(const float m[12], const lightrt::Vec3& p) {
  return lightrt::Vec3(
    m[0] * p.x + m[1] * p.y + m[2]  * p.z + m[3],
    m[4] * p.x + m[5] * p.y + m[6]  * p.z + m[7],
    m[8] * p.x + m[9] * p.y + m[10] * p.z + m[11]);
}

inline lightrt::Vec3 transformDir(const float m[12], const lightrt::Vec3& d) {
  return lightrt::Vec3(
    m[0] * d.x + m[1] * d.y + m[2]  * d.z,
    m[4] * d.x + m[5] * d.y + m[6]  * d.z,
    m[8] * d.x + m[9] * d.y + m[10] * d.z);
}

inline lightrt::AABB transformAABB(const lightrt::AABB& box, const float m[12]) {
  lightrt::AABB result;
  for (int i = 0; i < 8; i++) {
    lightrt::Vec3 corner(
      (i & 1) ? box.max.x : box.min.x,
      (i & 2) ? box.max.y : box.min.y,
      (i & 4) ? box.max.z : box.min.z);
    result.expand(transformPoint(m, corner));
  }
  return result;
}

// --- Scene traversal ---

inline HitInfo traceScene(const Scene& scene, const lightrt::Ray& ray, float ray_time = 0.0f) {
  HitInfo best;
  float tmin_out, tmax_out;

  for (uint32_t i = 0; i < static_cast<uint32_t>(scene.instances.size()); i++) {
    const Instance& inst = scene.instances[i];

    // AABB culling
    if (!inst.world_bounds.intersect(ray, tmin_out, tmax_out)) continue;
    if (tmin_out > best.t) continue;

    // Get transform (interpolated for motion blur)
    float inv_m[12];
    if (inst.has_motion && ray_time > 0.0f && ray_time < 1.0f) {
      float blended[12];
      lerp3x4(inst.transform, inst.transform_close, ray_time, blended);
      if (!invert3x4(blended, inv_m)) continue;
    } else if (inst.has_motion && ray_time >= 1.0f) {
      std::memcpy(inv_m, inst.inv_transform_close, sizeof(inv_m));
    } else {
      std::memcpy(inv_m, inst.inv_transform, sizeof(inv_m));
    }

    // Transform ray to local space
    lightrt::Vec3 local_o = transformPoint(inv_m, ray.origin);
    lightrt::Vec3 local_d = transformDir(inv_m, ray.direction);
    float dir_len = local_d.length();
    if (dir_len < 1e-12f) continue;
    float inv_dir_len = 1.0f / dir_len;
    local_d = local_d * inv_dir_len;

    lightrt::Ray local_ray(local_o, local_d, ray.tmin * dir_len, best.t * dir_len);

    float hit_t = local_ray.tmax;
    float hit_u, hit_v;
    uint32_t tri_id = scene.meshes[inst.mesh_id].bvh.traverse(local_ray, hit_t, hit_u, hit_v);

    if (tri_id != lightrt::kInvalidIndex) {
      float world_t = hit_t * inv_dir_len;
      if (world_t < best.t) {
        best.instance_id = i;
        best.triangle_id = tri_id;
        best.t = world_t;
        best.u = hit_u;
        best.v = hit_v;
      }
    }
  }
  return best;
}

inline bool traceSceneAnyHit(const Scene& scene, const lightrt::Ray& ray,
                             uint32_t exclude_instance = lightrt::kInvalidIndex,
                             uint32_t exclude_tri = lightrt::kInvalidIndex,
                             float ray_time = 0.0f) {
  float tmin_out, tmax_out;

  for (uint32_t i = 0; i < static_cast<uint32_t>(scene.instances.size()); i++) {
    const Instance& inst = scene.instances[i];
    if (!inst.world_bounds.intersect(ray, tmin_out, tmax_out)) continue;

    float inv_m[12];
    if (inst.has_motion && ray_time > 0.0f && ray_time < 1.0f) {
      float blended[12];
      lerp3x4(inst.transform, inst.transform_close, ray_time, blended);
      if (!invert3x4(blended, inv_m)) continue;
    } else if (inst.has_motion && ray_time >= 1.0f) {
      std::memcpy(inv_m, inst.inv_transform_close, sizeof(inv_m));
    } else {
      std::memcpy(inv_m, inst.inv_transform, sizeof(inv_m));
    }

    lightrt::Vec3 local_o = transformPoint(inv_m, ray.origin);
    lightrt::Vec3 local_d = transformDir(inv_m, ray.direction);
    float dir_len = local_d.length();
    if (dir_len < 1e-12f) continue;
    local_d = local_d * (1.0f / dir_len);

    lightrt::Ray local_ray(local_o, local_d, ray.tmin * dir_len, ray.tmax * dir_len);

    uint32_t exclude = (i == exclude_instance) ? exclude_tri : lightrt::kInvalidIndex;
    if (scene.meshes[inst.mesh_id].bvh.traverseAnyHit(local_ray, exclude)) return true;
  }
  return false;
}

} // namespace scene
