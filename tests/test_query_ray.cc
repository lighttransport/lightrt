#include "lightrt.hh"
#include "common/scene.hh"

#include <algorithm>
#include <cmath>
#include <cstring>
#include <cstdio>
#include <utility>
#include <vector>

int main() {
  std::vector<lightrt::AABB> boxes;
  boxes.emplace_back(lightrt::Vec3(1.0f, -1.0f, -1.0f),
                     lightrt::Vec3(2.0f, 1.0f, 1.0f));
  boxes.emplace_back(lightrt::Vec3(4.0f, -1.0f, -1.0f),
                     lightrt::Vec3(5.0f, 1.0f, 1.0f));
  boxes.emplace_back(lightrt::Vec3(1.0f, 3.0f, -1.0f),
                     lightrt::Vec3(2.0f, 4.0f, 1.0f));

  lightrt::BVH bvh;
  if (!bvh.build(boxes)) {
    std::fprintf(stderr, "failed to build test BVH\n");
    return 1;
  }

  const lightrt::Ray ray(lightrt::Vec3(0.0f, 0.0f, 0.0f),
                         lightrt::Vec3(1.0f, 0.0f, 0.0f));
  std::vector<uint32_t> hits;
  bvh.queryRay(ray, 10.0f, hits);
  std::sort(hits.begin(), hits.end());
  if (hits != std::vector<uint32_t>({0, 1})) {
    std::fprintf(stderr, "queryRay did not return both intersected boxes\n");
    return 1;
  }

  bvh.queryRay(ray, 3.0f, hits);
  if (hits != std::vector<uint32_t>({0})) {
    std::fprintf(stderr, "queryRay did not honor max_t\n");
    return 1;
  }

  lightrt::GaussianSplat splat;
  splat.position = lightrt::Vec3(2.0f, 0.0f, 0.0f);
  splat.scale = lightrt::Vec3(0.5f, 0.25f, 0.25f);
  splat.opacity = 0.75f;
  float splat_t = 100.0f;
  float density = 0.0f;
  if (!splat.intersect(ray, splat_t, density) ||
      std::abs(splat_t - 2.0f) > 1.0e-4f ||
      std::abs(density - 0.75f) > 1.0e-4f) {
    std::fprintf(stderr, "Gaussian peak-density intersection failed\n");
    return 1;
  }
  lightrt::Vec3 dc = splat.getColor(lightrt::Vec3(0.0f, 0.0f, 1.0f));
  if (std::abs(dc.x - 0.5f) > 1.0e-5f ||
      std::abs(dc.y - 0.5f) > 1.0e-5f ||
      std::abs(dc.z - 0.5f) > 1.0e-5f) {
    std::fprintf(stderr, "Gaussian SH DC evaluation failed\n");
    return 1;
  }

  splat.sh_coeffs[0] = 0.6f;
  splat.sh_coeffs[1] = -0.3f;
  splat.sh_coeffs[2] = 0.15f;
  lightrt::QuantizedGaussianSplat quantized;
  quantized.quantize(splat, lightrt::Vec3(0.0f, -1.0f, -1.0f),
                     lightrt::Vec3(4.0f, 1.0f, 1.0f), 0.01f, 1.0f);
  const lightrt::GaussianSplat restored = quantized.dequantize(
      lightrt::Vec3(0.0f, -1.0f, -1.0f),
      lightrt::Vec3(4.0f, 1.0f, 1.0f), 0.01f, 1.0f);
  const lightrt::Vec3 original_color =
      splat.getColor(lightrt::Vec3(0.0f, 0.0f, 1.0f));
  const lightrt::Vec3 restored_color =
      restored.getColor(lightrt::Vec3(0.0f, 0.0f, 1.0f));
  if (std::abs(original_color.x - restored_color.x) > 1.0f / 255.0f ||
      std::abs(original_color.y - restored_color.y) > 1.0f / 255.0f ||
      std::abs(original_color.z - restored_color.z) > 1.0f / 255.0f) {
    std::fprintf(stderr, "Quantized Gaussian DC round-trip failed\n");
    return 1;
  }

  const lightrt::Curve capsule(
      {lightrt::Vec3(0.0f, 0.0f, 0.0f),
       lightrt::Vec3(1.0f, 0.0f, 0.0f)},
      0.25f, lightrt::CurveType::Linear);
  float curve_t = 100.0f;
  float curve_u = -1.0f;
  const lightrt::Ray axial_ray(lightrt::Vec3(-2.0f, 0.0f, 0.0f),
                               lightrt::Vec3(1.0f, 0.0f, 0.0f));
  if (!capsule.intersect(axial_ray, curve_t, curve_u) ||
      std::abs(curve_t - 1.75f) > 1.0e-4f ||
      std::abs(curve_u) > 1.0e-4f) {
    std::fprintf(stderr, "Axial ray-capsule intersection failed\n");
    return 1;
  }

  curve_t = 100.0f;
  curve_u = -1.0f;
  const lightrt::Ray side_ray(lightrt::Vec3(0.5f, 1.0f, 0.0f),
                              lightrt::Vec3(0.0f, -1.0f, 0.0f));
  if (!capsule.intersect(side_ray, curve_t, curve_u) ||
      std::abs(curve_t - 0.75f) > 1.0e-4f ||
      std::abs(curve_u - 0.5f) > 1.0e-4f) {
    std::fprintf(stderr, "Side ray-capsule intersection failed\n");
    return 1;
  }

  const lightrt::Curve tapered(
      {lightrt::Vec3(0.0f, 0.0f, 0.0f),
       lightrt::Vec3(1.0f, 0.0f, 0.0f)},
      {0.1f, 0.3f}, lightrt::CurveType::Linear);
  curve_t = 100.0f;
  curve_u = -1.0f;
  const lightrt::Ray taper_ray(lightrt::Vec3(0.75f, 1.0f, 0.0f),
                               lightrt::Vec3(0.0f, -1.0f, 0.0f));
  if (!tapered.intersect(taper_ray, curve_t, curve_u) ||
      std::abs(curve_t - 0.75f) > 1.0e-4f ||
      std::abs(curve_u - 0.75f) > 1.0e-4f) {
    std::fprintf(stderr, "Tapered curve-segment intersection failed\n");
    return 1;
  }

  lightrt::Curve colored = capsule;
  colored.colors = {lightrt::Vec3(1.0f, 0.0f, 0.0f),
                    lightrt::Vec3(0.0f, 0.0f, 1.0f)};
  const lightrt::Vec3 midpoint_color = colored.colorAt(0.5f);
  if (std::abs(midpoint_color.x - 0.5f) > 1.0e-5f ||
      std::abs(midpoint_color.y) > 1.0e-5f ||
      std::abs(midpoint_color.z - 0.5f) > 1.0e-5f) {
    std::fprintf(stderr, "Curve display-color interpolation failed\n");
    return 1;
  }

  lightrt::Curve moving = capsule;
  moving.control_points_close = {
      lightrt::Vec3(0.0f, 2.0f, 0.0f),
      lightrt::Vec3(1.0f, 2.0f, 0.0f)};
  moving.radii_close = {0.5f, 0.5f};
  if (std::abs(moving.evaluate(0.5f, 0.5f).y - 1.0f) > 1.0e-5f ||
      std::abs(moving.radiusAt(0.5f, 0.5f) - 0.375f) > 1.0e-5f ||
      std::abs(moving.bounds().max.y - 2.5f) > 1.0e-5f) {
    std::fprintf(stderr, "Curve shutter interpolation or bounds failed\n");
    return 1;
  }
  curve_t = 100.0f;
  curve_u = -1.0f;
  const lightrt::Ray moving_ray(lightrt::Vec3(0.5f, 3.0f, 0.0f),
                                lightrt::Vec3(0.0f, -1.0f, 0.0f));
  if (!moving.intersect(moving_ray, curve_t, curve_u, 1.0f) ||
      std::abs(curve_t - 0.5f) > 1.0e-4f) {
    std::fprintf(stderr, "Motion-sampled curve intersection failed\n");
    return 1;
  }

  scene::Scene motion_scene;
  motion_scene.curve_meshes.emplace_back();
  motion_scene.curve_meshes.back().build({capsule});
  lightrt::Curve close_capsule = capsule;
  close_capsule.control_points = moving.control_points_close;
  close_capsule.radii = moving.radii_close;
  scene::CurveBLAS close_curves;
  close_curves.build({close_capsule});
  if (!motion_scene.curve_meshes.back().setMotionSamples(close_curves)) {
    std::fprintf(stderr, "Curve BLAS rejected compatible motion samples\n");
    return 1;
  }
  scene::Instance motion_instance;
  motion_instance.curve_mesh_id = 0;
  std::memset(motion_instance.transform, 0, sizeof(motion_instance.transform));
  motion_instance.transform[0] = 1.0f;
  motion_instance.transform[5] = 1.0f;
  motion_instance.transform[10] = 1.0f;
  std::memcpy(motion_instance.inv_transform, motion_instance.transform,
              sizeof(motion_instance.transform));
  std::memcpy(motion_instance.transform_close, motion_instance.transform,
              sizeof(motion_instance.transform));
  std::memcpy(motion_instance.inv_transform_close,
              motion_instance.inv_transform,
              sizeof(motion_instance.inv_transform));
  motion_instance.has_motion = true;
  motion_instance.world_bounds = motion_scene.curve_meshes[0].local_bounds;
  motion_scene.instances.push_back(motion_instance);
  motion_scene.scene_bounds = motion_instance.world_bounds;
  motion_scene.buildAcceleration();
  const lightrt::Ray close_only_ray(lightrt::Vec3(-2.0f, 2.0f, 0.0f),
                                    lightrt::Vec3(1.0f, 0.0f, 0.0f));
  const scene::HitInfo close_hit =
      scene::traceScene(motion_scene, close_only_ray, 1.0f);
  if (close_hit.curve_id == lightrt::kInvalidIndex ||
      std::abs(close_hit.t - 1.5f) > 1.0e-4f) {
    std::fprintf(stderr, "Swept curve-segment BLAS query failed\n");
    return 1;
  }
  if (!scene::traceSceneAnyHit(motion_scene, close_only_ray,
                               lightrt::kInvalidIndex,
                               lightrt::kInvalidIndex, 1.0f)) {
    std::fprintf(stderr, "Swept curve-segment any-hit query failed\n");
    return 1;
  }

  std::puts("queryRay, Gaussian, and curve primitive tests passed");
  return 0;
}
