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
#include <utility>

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

struct CurveBLAS {
  std::vector<lightrt::Curve> curves;
  std::vector<lightrt::AABB> curve_aabbs;
  std::vector<lightrt::AABB> segment_aabbs;
  std::vector<uint32_t> segment_curve_ids;
  std::vector<uint32_t> segment_local_ids;
  lightrt::BVH bvh;
  lightrt::BVHBuildConfig build_config;
  lightrt::AABB local_bounds;
  int32_t default_material_id = -1;
  std::vector<int32_t> curve_material_ids;

  void build(std::vector<lightrt::Curve> input_curves,
             const lightrt::BVHBuildConfig& cfg = lightrt::BVHBuildConfig()) {
    build_config = cfg;
    curves = std::move(input_curves);
    curve_aabbs.resize(curves.size());
    segment_aabbs.clear();
    segment_curve_ids.clear();
    segment_local_ids.clear();
    size_t segment_count = 0;
    for (const auto& curve : curves) {
      if (curve.control_points.size() >= 2)
        segment_count += curve.control_points.size() - 1;
    }
    segment_aabbs.reserve(segment_count);
    segment_curve_ids.reserve(segment_count);
    segment_local_ids.reserve(segment_count);
    local_bounds = lightrt::AABB();
    for (size_t i = 0; i < curves.size(); i++) {
      curve_aabbs[i] = curves[i].bounds();
      local_bounds.expand(curve_aabbs[i].min);
      local_bounds.expand(curve_aabbs[i].max);
      for (uint32_t segment = 0;
           segment + 1u < curves[i].control_points.size(); ++segment) {
        lightrt::AABB bounds;
        auto expand_endpoint = [&](const lightrt::Vec3& p,
                                   float radius) {
          const float r = std::max(0.0f, radius);
          const lightrt::Vec3 rv(r, r, r);
          bounds.expand(p - rv);
          bounds.expand(p + rv);
        };
        const float r0 = segment < curves[i].radii.size()
                             ? curves[i].radii[segment] : 0.01f;
        const float r1 = segment + 1u < curves[i].radii.size()
                             ? curves[i].radii[segment + 1u] : r0;
        expand_endpoint(curves[i].control_points[segment], r0);
        expand_endpoint(curves[i].control_points[segment + 1u], r1);
        if (curves[i].hasMotionSamples()) {
          const float close_r0 =
              curves[i].radii_close.size() == curves[i].radii.size()
                  ? curves[i].radii_close[segment] : r0;
          const float close_r1 =
              curves[i].radii_close.size() == curves[i].radii.size()
                  ? curves[i].radii_close[segment + 1u] : r1;
          expand_endpoint(curves[i].control_points_close[segment], close_r0);
          expand_endpoint(curves[i].control_points_close[segment + 1u],
                          close_r1);
        }
        segment_aabbs.push_back(bounds);
        segment_curve_ids.push_back(static_cast<uint32_t>(i));
        segment_local_ids.push_back(segment);
      }
    }
    bvh.build(segment_aabbs, cfg);
    curve_material_ids.assign(curves.size(), -1);
  }

  bool hasCompatibleMotionTopology(const CurveBLAS& sample) const {
    if (curves.size() != sample.curves.size()) return false;
    for (size_t i = 0; i < curves.size(); ++i) {
      if (curves[i].control_points.size() !=
          sample.curves[i].control_points.size())
        return false;
    }
    return true;
  }

  bool replaceOpenSamples(const CurveBLAS& sample) {
    if (!hasCompatibleMotionTopology(sample)) return false;

    std::vector<lightrt::Curve> sampled_curves = sample.curves;
    for (auto& curve : sampled_curves) {
      curve.control_points_close.clear();
      curve.radii_close.clear();
      curve.colors_close.clear();
    }
    const int32_t saved_default_material = default_material_id;
    std::vector<int32_t> saved_materials = std::move(curve_material_ids);
    const lightrt::BVHBuildConfig saved_config = build_config;
    build(std::move(sampled_curves), saved_config);
    default_material_id = saved_default_material;
    curve_material_ids = std::move(saved_materials);
    return true;
  }

  bool setMotionSamples(const CurveBLAS& close) {
    if (!hasCompatibleMotionTopology(close)) return false;
    bool changed = false;
    auto vec3_different = [](const std::vector<lightrt::Vec3>& a,
                             const std::vector<lightrt::Vec3>& b) {
      if (a.size() != b.size()) return true;
      for (size_t i = 0; i < a.size(); ++i) {
        if (a[i].x != b[i].x || a[i].y != b[i].y || a[i].z != b[i].z)
          return true;
      }
      return false;
    };
    auto float_different = [](const std::vector<float>& a,
                              const std::vector<float>& b) {
      return a != b;
    };

    for (size_t i = 0; i < curves.size(); ++i) {
      const bool geometry_changed = vec3_different(
          curves[i].control_points, close.curves[i].control_points);
      const bool radius_changed = float_different(
          curves[i].radii, close.curves[i].radii);
      const bool color_changed = vec3_different(
          curves[i].colors, close.curves[i].colors);
      if (geometry_changed || radius_changed) {
        curves[i].control_points_close = close.curves[i].control_points;
        curves[i].radii_close = close.curves[i].radii;
        changed = true;
      }
      if (color_changed && curves[i].colors.size() == close.curves[i].colors.size()) {
        curves[i].colors_close = close.curves[i].colors;
        changed = true;
      }
    }
    if (!changed) return false;

    const int32_t saved_default_material = default_material_id;
    std::vector<int32_t> saved_materials = std::move(curve_material_ids);
    const lightrt::BVHBuildConfig saved_config = build_config;
    build(std::move(curves), saved_config);
    default_material_id = saved_default_material;
    curve_material_ids = std::move(saved_materials);
    return true;
  }
};

struct PointBLAS {
  std::vector<lightrt::Sphere> points;
  std::vector<lightrt::AABB> point_aabbs;
  lightrt::BVH bvh;
  lightrt::AABB local_bounds;
  int32_t default_material_id = -1;
  std::vector<int32_t> point_material_ids;

  void build(const std::vector<lightrt::Sphere>& input_points,
             const lightrt::BVHBuildConfig& cfg = lightrt::BVHBuildConfig()) {
    points = input_points;
    point_aabbs.resize(points.size());
    local_bounds = lightrt::AABB();
    for (size_t i = 0; i < points.size(); ++i) {
      point_aabbs[i] = points[i].bounds();
      local_bounds.expand(point_aabbs[i].min);
      local_bounds.expand(point_aabbs[i].max);
    }
    bvh.build(point_aabbs, cfg);
    point_material_ids.assign(points.size(), -1);
  }
};

struct GaussianBLAS {
  std::vector<lightrt::GaussianSplat> splats;
  std::vector<lightrt::AABB> splat_aabbs;
  lightrt::BVH bvh;
  lightrt::AABB local_bounds;

  void build(std::vector<lightrt::GaussianSplat>&& input_splats,
             const lightrt::BVHBuildConfig& cfg = lightrt::BVHBuildConfig()) {
    splats = std::move(input_splats);
    splat_aabbs.resize(splats.size());
    local_bounds = lightrt::AABB();
    for (size_t i = 0; i < splats.size(); ++i) {
      splat_aabbs[i] = splats[i].bounds();
      local_bounds.expand(splat_aabbs[i].min);
      local_bounds.expand(splat_aabbs[i].max);
    }
    bvh.build(splat_aabbs, cfg);
  }
};

struct Instance {
  uint32_t mesh_id;       // kInvalidIndex = no mesh
  uint32_t curve_mesh_id; // kInvalidIndex = no curve mesh
  uint32_t point_mesh_id; // kInvalidIndex = no point mesh
  uint32_t gaussian_mesh_id; // kInvalidIndex = no Gaussian splat set
  float transform[12];       // 3x4 row-major (rows 0-2 of 4x4)
  float inv_transform[12];
  float transform_close[12]; // transform at shutter close
  float inv_transform_close[12];
  bool has_motion = false;
  lightrt::AABB world_bounds;

  Instance()
      : mesh_id(lightrt::kInvalidIndex),
        curve_mesh_id(lightrt::kInvalidIndex),
        point_mesh_id(lightrt::kInvalidIndex),
        gaussian_mesh_id(lightrt::kInvalidIndex) {}
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
  uint32_t curve_id = lightrt::kInvalidIndex;  // valid when curve hit
  uint32_t point_id = lightrt::kInvalidIndex;  // valid when point hit
  uint32_t gaussian_id = lightrt::kInvalidIndex;
  float gaussian_density = 0.0f;
  float curve_u = 0.0f;                         // curve parameter at hit
  float t = std::numeric_limits<float>::max();
  float u = 0.0f;  // (reused for curve internal use)
  float v = 0.0f;
};

struct Scene {
  std::vector<MeshBLAS> meshes;
  std::vector<CurveBLAS> curve_meshes;
  std::vector<PointBLAS> point_meshes;
  std::vector<GaussianBLAS> gaussian_meshes;
  std::vector<Instance> instances;
  lightrt::BVH instance_bvh;
  bool instance_bvh_valid = false;
  std::vector<Camera> cameras;
  std::vector<MaterialData> materials;
  std::vector<LightData> lights;
  EnvmapData envmap;
  std::vector<ImageData> images;
  lightrt::AABB scene_bounds;
  int up_axis = 0; // 0=Y, 1=Z, 2=X (USD upAxis)

  bool buildAcceleration() {
    std::vector<lightrt::AABB> bounds;
    bounds.reserve(instances.size());
    for (const auto& inst : instances) bounds.push_back(inst.world_bounds);
    if (bounds.empty()) {
      instance_bvh_valid = false;
      return false;
    }
    lightrt::BVHBuildConfig cfg = lightrt::BVHBuildConfig::fast();
    cfg.max_leaf_size = 4;
    instance_bvh_valid = instance_bvh.build(bounds, cfg);
    return instance_bvh_valid;
  }
};

// --- Scene traversal ---

inline HitInfo traceScene(const Scene& scene, const lightrt::Ray& ray, float ray_time = 0.0f) {
  HitInfo best;
  float tmin_out, tmax_out;

  thread_local std::vector<uint32_t> candidates;
  thread_local std::vector<uint32_t> primitive_candidates;
  if (scene.instance_bvh_valid) {
    scene.instance_bvh.queryRay(ray, ray.tmax, candidates);
  } else {
    candidates.resize(scene.instances.size());
    std::iota(candidates.begin(), candidates.end(), 0u);
  }

  for (uint32_t i : candidates) {
    if (i >= scene.instances.size()) continue;
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

    // Triangle mesh intersection
    if (inst.mesh_id != lightrt::kInvalidIndex) {
      float hit_t = local_ray.tmax;
      float hit_u, hit_v;
      uint32_t tri_id = scene.meshes[inst.mesh_id].bvh.traverse(local_ray, hit_t, hit_u, hit_v);
      if (tri_id != lightrt::kInvalidIndex) {
        float world_t = hit_t * inv_dir_len;
        if (world_t < best.t) {
          best.instance_id = i;
          best.triangle_id = tri_id;
          best.curve_id = lightrt::kInvalidIndex;
          best.point_id = lightrt::kInvalidIndex;
          best.gaussian_id = lightrt::kInvalidIndex;
          best.t = world_t;
          best.u = hit_u;
          best.v = hit_v;
        }
      }
    }

    // Curve mesh intersection
    if (inst.curve_mesh_id != lightrt::kInvalidIndex &&
        inst.curve_mesh_id < static_cast<uint32_t>(scene.curve_meshes.size())) {
      const CurveBLAS& cb = scene.curve_meshes[inst.curve_mesh_id];
      cb.bvh.queryRay(local_ray, best.t * dir_len, primitive_candidates);
      for (uint32_t segment_idx : primitive_candidates) {
        if (segment_idx >= cb.segment_curve_ids.size()) continue;
        const uint32_t curve_idx = cb.segment_curve_ids[segment_idx];
        const uint32_t local_idx = cb.segment_local_ids[segment_idx];
        if (curve_idx >= static_cast<uint32_t>(cb.curves.size())) continue;
        float ct, cu;
        if (cb.curves[curve_idx].intersectSegment(local_ray, local_idx,
                                                  ct, cu, ray_time)) {
          float world_t = ct * inv_dir_len;
          if (world_t < best.t) {
            best.instance_id = i;
            best.triangle_id = lightrt::kInvalidIndex;
            best.curve_id = curve_idx;
            best.point_id = lightrt::kInvalidIndex;
            best.gaussian_id = lightrt::kInvalidIndex;
            best.curve_u = cu;
            best.t = world_t;
            best.u = cu;
          }
        }
      }
    }

    // USD Points are rendered as sphere primitives with radius = width / 2.
    if (inst.point_mesh_id != lightrt::kInvalidIndex &&
        inst.point_mesh_id < static_cast<uint32_t>(scene.point_meshes.size())) {
      const PointBLAS& pb = scene.point_meshes[inst.point_mesh_id];
      pb.bvh.queryRay(local_ray, best.t * dir_len, primitive_candidates);
      for (uint32_t point_idx : primitive_candidates) {
        if (point_idx >= pb.points.size()) continue;
        float point_t = local_ray.tmax;
        if (pb.points[point_idx].intersect(local_ray, point_t)) {
          float world_t = point_t * inv_dir_len;
          if (world_t < best.t) {
            best.instance_id = i;
            best.triangle_id = lightrt::kInvalidIndex;
            best.curve_id = lightrt::kInvalidIndex;
            best.point_id = point_idx;
            best.gaussian_id = lightrt::kInvalidIndex;
            best.t = world_t;
          }
        }
      }
    }

    if (inst.gaussian_mesh_id != lightrt::kInvalidIndex &&
        inst.gaussian_mesh_id < scene.gaussian_meshes.size()) {
      const GaussianBLAS& gb = scene.gaussian_meshes[inst.gaussian_mesh_id];
      gb.bvh.queryRay(local_ray, best.t * dir_len, primitive_candidates);
      for (uint32_t splat_idx : primitive_candidates) {
        if (splat_idx >= gb.splats.size()) continue;
        float splat_t = local_ray.tmax;
        float density = 0.0f;
        if (gb.splats[splat_idx].intersect(local_ray, splat_t, density)) {
          float world_t = splat_t * inv_dir_len;
          if (density > 1.0e-4f && world_t < best.t) {
            best.instance_id = i;
            best.triangle_id = lightrt::kInvalidIndex;
            best.curve_id = lightrt::kInvalidIndex;
            best.point_id = lightrt::kInvalidIndex;
            best.gaussian_id = splat_idx;
            best.gaussian_density = density;
            best.t = world_t;
          }
        }
      }
    }
  }
  return best;
}

struct GaussianRadiance {
  lightrt::Vec3 color;
  float alpha = 0.0f;
};

// Front-to-back alpha composition of every Gaussian whose 3-sigma ellipsoid
// intersects the ray. This is the CPU reference path; the TLAS and per-splat
// BLAS keep it practical for validation renders without scanning the field.
inline GaussianRadiance traceGaussianRadiance(const Scene& scene,
                                               const lightrt::Ray& ray,
                                               float ray_time = 0.0f) {
  struct GaussianHit {
    uint32_t instance_id;
    uint32_t splat_id;
    float t;
    float density;
  };
  thread_local std::vector<uint32_t> instances;
  thread_local std::vector<uint32_t> splat_candidates;
  thread_local std::vector<GaussianHit> hits;
  hits.clear();

  if (scene.instance_bvh_valid) {
    scene.instance_bvh.queryRay(ray, ray.tmax, instances);
  } else {
    instances.resize(scene.instances.size());
    std::iota(instances.begin(), instances.end(), 0u);
  }

  for (uint32_t instance_id : instances) {
    if (instance_id >= scene.instances.size()) continue;
    const Instance& inst = scene.instances[instance_id];
    if (inst.gaussian_mesh_id == lightrt::kInvalidIndex ||
        inst.gaussian_mesh_id >= scene.gaussian_meshes.size()) continue;

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
    if (dir_len < 1.0e-12f) continue;
    float inv_dir_len = 1.0f / dir_len;
    local_d = local_d * inv_dir_len;
    lightrt::Ray local_ray(local_o, local_d, ray.tmin * dir_len,
                           ray.tmax * dir_len);

    const GaussianBLAS& gb = scene.gaussian_meshes[inst.gaussian_mesh_id];
    gb.bvh.queryRay(local_ray, local_ray.tmax, splat_candidates);
    for (uint32_t splat_id : splat_candidates) {
      if (splat_id >= gb.splats.size()) continue;
      float local_t = local_ray.tmax;
      float density = 0.0f;
      if (gb.splats[splat_id].intersect(local_ray, local_t, density) &&
          density > 1.0e-4f) {
        hits.push_back({instance_id, splat_id,
                        local_t * inv_dir_len, density});
      }
    }
  }

  std::sort(hits.begin(), hits.end(),
            [](const GaussianHit& a, const GaussianHit& b) {
              return a.t < b.t;
            });
  GaussianRadiance result;
  float transmittance = 1.0f;
  for (const GaussianHit& hit : hits) {
    const Instance& inst = scene.instances[hit.instance_id];
    const GaussianBLAS& gb = scene.gaussian_meshes[inst.gaussian_mesh_id];
    const lightrt::GaussianSplat& splat = gb.splats[hit.splat_id];
    lightrt::Vec3 local_view =
        transformDir(inst.inv_transform, ray.direction * -1.0f).normalize();
    float alpha = std::max(0.0f, std::min(0.99f, hit.density));
    result.color = result.color +
                   splat.getColor(local_view) * (transmittance * alpha);
    transmittance *= 1.0f - alpha;
    if (transmittance < 0.005f) break;
  }
  result.alpha = 1.0f - transmittance;
  return result;
}

inline bool traceSceneAnyHit(const Scene& scene, const lightrt::Ray& ray,
                             uint32_t exclude_instance = lightrt::kInvalidIndex,
                             uint32_t exclude_prim = lightrt::kInvalidIndex,
                             float ray_time = 0.0f) {
  float tmin_out, tmax_out;

  thread_local std::vector<uint32_t> candidates;
  thread_local std::vector<uint32_t> primitive_candidates;
  if (scene.instance_bvh_valid) {
    scene.instance_bvh.queryRay(ray, ray.tmax, candidates);
  } else {
    candidates.resize(scene.instances.size());
    std::iota(candidates.begin(), candidates.end(), 0u);
  }

  for (uint32_t i : candidates) {
    if (i >= scene.instances.size()) continue;
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

    if (inst.mesh_id != lightrt::kInvalidIndex) {
      uint32_t exclude = (i == exclude_instance) ? exclude_prim : lightrt::kInvalidIndex;
      if (scene.meshes[inst.mesh_id].bvh.traverseAnyHit(local_ray, exclude)) return true;
    }

    if (inst.curve_mesh_id != lightrt::kInvalidIndex &&
        inst.curve_mesh_id < static_cast<uint32_t>(scene.curve_meshes.size())) {
      const CurveBLAS& cb = scene.curve_meshes[inst.curve_mesh_id];
      cb.bvh.queryRay(local_ray, local_ray.tmax, primitive_candidates);
      for (uint32_t segment_idx : primitive_candidates) {
        if (segment_idx >= cb.segment_curve_ids.size()) continue;
        const uint32_t cidx = cb.segment_curve_ids[segment_idx];
        const uint32_t local_idx = cb.segment_local_ids[segment_idx];
        if (cidx >= static_cast<uint32_t>(cb.curves.size())) continue;
        if (i == exclude_instance && cidx == exclude_prim) continue;
        float ct, cu;
        if (cb.curves[cidx].intersectSegment(local_ray, local_idx, ct, cu,
                                              ray_time))
          return true;
      }
    }

    if (inst.point_mesh_id != lightrt::kInvalidIndex &&
        inst.point_mesh_id < static_cast<uint32_t>(scene.point_meshes.size())) {
      const PointBLAS& pb = scene.point_meshes[inst.point_mesh_id];
      pb.bvh.queryRay(local_ray, local_ray.tmax, primitive_candidates);
      for (uint32_t point_idx : primitive_candidates) {
        if (point_idx >= pb.points.size()) continue;
        if (i == exclude_instance && point_idx == exclude_prim) continue;
        float point_t = local_ray.tmax;
        if (pb.points[point_idx].intersect(local_ray, point_t)) return true;
      }
    }


    if (inst.gaussian_mesh_id != lightrt::kInvalidIndex &&
        inst.gaussian_mesh_id < scene.gaussian_meshes.size()) {
      const GaussianBLAS& gb = scene.gaussian_meshes[inst.gaussian_mesh_id];
      gb.bvh.queryRay(local_ray, local_ray.tmax, primitive_candidates);
      for (uint32_t splat_idx : primitive_candidates) {
        if (splat_idx >= gb.splats.size()) continue;
        if (i == exclude_instance && splat_idx == exclude_prim) continue;
        float splat_t = local_ray.tmax;
        float density = 0.0f;
        if (gb.splats[splat_idx].intersect(local_ray, splat_t, density) &&
            density > 0.05f) return true;
      }
    }
  }
  return false;
}

// Re-export shading namespace for backward compatibility
namespace shading {
  using namespace lightrt_common::shading;
} // namespace shading

} // namespace scene
