// Shared scene graph for CLI and viewer renderers
// Provides per-instance transforms, motion blur, USD camera support,
// materials, lights, environment maps, and PBR shading
#pragma once

#include "lightrt.hh"
#include "common/transforms.hh"
#include "common/materials.hh"
#include "common/shading.hh"
#include <vector>
#include <string>
#include <cmath>
#include <cstring>
#include <limits>
#include <algorithm>
#include <numeric>

namespace scene {

// Re-export common types into scene namespace for backward compatibility
using MaterialData = lightrt_common::MaterialData;
using LightData = lightrt_common::LightData;
using EnvmapData = lightrt_common::EnvmapData;

// Re-export transform utilities
using lightrt_common::matrix4dTo3x4;
using lightrt_common::invert3x4;
using lightrt_common::lerp3x4;
using lightrt_common::transformPoint;
using lightrt_common::transformDir;
using lightrt_common::transformNormal;
using lightrt_common::transformAABB;

struct ImageData {
  std::vector<float> pixels; // width*height*4 RGBA linear float
  int width = 0, height = 0;
};

struct MeshBLAS {
  lightrt::TriangleBVH bvh;
  lightrt::AABB local_bounds;
  std::vector<int32_t> tri_material_ids;
  int32_t default_material_id = -1;
  std::vector<float> tri_uvs;     // num_tris * 6 (u0,v0,u1,v1,u2,v2)
  std::vector<float> tri_normals; // num_tris * 9 (nx0,ny0,nz0,...per vertex)
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
  std::vector<MaterialData> materials;
  std::vector<LightData> lights;
  EnvmapData envmap;
  std::vector<ImageData> images;
  lightrt::AABB scene_bounds;
  int up_axis = 0; // 0=Y, 1=Z, 2=X (USD upAxis)
};

// --- Scene traversal ---

inline HitInfo traceScene(const Scene& scene, const lightrt::Ray& ray, float ray_time = 0.0f) {
  HitInfo best;
  float tmin_out, tmax_out;

  for (uint32_t i = 0; i < static_cast<uint32_t>(scene.instances.size()); i++) {
    const Instance& inst = scene.instances[i];

    if (!inst.world_bounds.intersect(ray, tmin_out, tmax_out)) continue;
    if (tmin_out > best.t) continue;

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

// Re-export shading namespace for backward compatibility
namespace shading {
  using namespace lightrt_common::shading;
} // namespace shading

} // namespace scene
