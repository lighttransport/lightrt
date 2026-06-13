// Shared random-walk SSS path tracer — used by cli/ and viewer/.
// Extracted from common/renderer.cc so both renderers share the same SSS logic.
#pragma once

#include "common/scene.hh"
#include "common/sss.hh"
#include <random>

namespace lightrt_common {
namespace sss_render {

struct SSSResult {
  lightrt::Vec3 exit_pos;
  lightrt::Vec3 exit_normal;
  lightrt::Vec3 throughput;
  uint32_t exit_instance_id = lightrt::kInvalidIndex;
  uint32_t exit_triangle_id = lightrt::kInvalidIndex;
  bool success = false;
};

// Compute world-space normal for a hit (interpolated vertex normal or face normal).
static inline lightrt::Vec3 computeWorldNormal(const scene::Scene& scene,
                                                uint32_t inst_id, uint32_t tri_id,
                                                float u = 0.333f, float v = 0.333f) {
  const auto& inst = scene.instances[inst_id];
  const auto& mesh = scene.meshes[inst.mesh_id];
  lightrt::Vec3 local_n;
  if (!mesh.tri_normals.empty() && tri_id * 9 + 8 < mesh.tri_normals.size()) {
    size_t nb = tri_id * 9;
    float w = 1.0f - u - v;
    local_n = lightrt::Vec3(
        mesh.tri_normals[nb + 0] * w + mesh.tri_normals[nb + 3] * u + mesh.tri_normals[nb + 6] * v,
        mesh.tri_normals[nb + 1] * w + mesh.tri_normals[nb + 4] * u + mesh.tri_normals[nb + 7] * v,
        mesh.tri_normals[nb + 2] * w + mesh.tri_normals[nb + 5] * u + mesh.tri_normals[nb + 8] * v)
        .normalize();
  } else {
    const auto& tris = mesh.bvh.getTriangles();
    const auto& tri = tris[tri_id];
    local_n = (tri.v1 - tri.v0).cross(tri.v2 - tri.v0).normalize();
  }
  return scene::transformNormal(inst.inv_transform, local_n).normalize();
}

// Random-walk subsurface scattering.
// Traces a random walk inside the volume starting at entry_pos/entry_N on
// entry_instance_id.  Returns the exit point on the same instance with the
// spectral throughput through the medium.
//
// RNG must satisfy std::uniform_random_bit_generator (e.g. std::mt19937).
template <typename RNG>
static inline SSSResult randomWalkSSS(const scene::Scene& scene,
                                       const lightrt::Vec3& entry_pos,
                                       const lightrt::Vec3& entry_N,
                                       uint32_t entry_instance_id,
                                       const scene::MaterialData& mat,
                                       RNG& rng,
                                       std::uniform_real_distribution<float>& dist01) {
  using namespace lightrt_common::sss;
  SSSResult result{};

  const SSSCoeffs c = computeCoeffsFromMaterial(mat);
  if (c.sigma_t.x > 1e14f && c.sigma_t.y > 1e14f && c.sigma_t.z > 1e14f)
    return result;

  float g = std::max(-0.99f, std::min(0.99f, mat.subsurface_anisotropy));

  // Estimate local thickness by casting a probe ray inward
  float thickness = kInfThickness;
  {
    lightrt::Vec3 inward = entry_N * -1.0f;
    lightrt::Ray probe(entry_pos + inward * 1e-3f, inward, 0.0f, 1000.0f);
    scene::HitInfo probe_hit = scene::traceScene(scene, probe);
    if (probe_hit.instance_id == entry_instance_id)
      thickness = probe_hit.t + 1e-3f;
  }

  lightrt::Vec3 inward_N = entry_N * -1.0f;
  lightrt::Vec3 ray_dir = sampleCosineHemisphere(inward_N,
                                                 dist01(rng), dist01(rng));
  if (ray_dir.dot(inward_N) <= 0.0f) ray_dir = ray_dir * -1.0f;

  lightrt::Vec3 ray_pos = entry_pos + inward_N * 1e-3f;
  lightrt::Vec3 throughput(1.0f, 1.0f, 1.0f);

  constexpr int kMaxBounces = 512;
  for (int bounce = 0; bounce < kMaxBounces; ++bounce) {
    lightrt::Vec3 ch_pdf;
    int ch = sampleChannel(throughput, c.sigma_s, dist01(rng), ch_pdf);
    float t_max = sampleFreePath(c.sigma_t, ch, dist01(rng));
    if (bounce == 0) t_max = std::min(t_max, thickness);

    lightrt::Ray walk_ray(ray_pos, ray_dir, 1e-4f, t_max);
    scene::HitInfo hit = scene::traceScene(scene, walk_ray);

    if (hit.instance_id != lightrt::kInvalidIndex &&
        hit.instance_id == entry_instance_id) {
      float t = hit.t;
      lightrt::Vec3 tau = transmittance(c.sigma_t, t);

      float exit_pdf = ch_pdf.x * tau.x + ch_pdf.y * tau.y + ch_pdf.z * tau.z;
      if (exit_pdf < 1e-16f) break;

      throughput.x *= tau.x / exit_pdf;
      throughput.y *= tau.y / exit_pdf;
      throughput.z *= tau.z / exit_pdf;

      lightrt::Vec3 exit_N = computeWorldNormal(scene,
                                                hit.instance_id,
                                                hit.triangle_id,
                                                hit.u, hit.v);
      if (exit_N.dot(ray_dir) < 0.0f) exit_N = exit_N * -1.0f;

      constexpr float kMaxTp = 1e4f;
      throughput.x = std::max(0.0f, std::min(throughput.x, kMaxTp));
      throughput.y = std::max(0.0f, std::min(throughput.y, kMaxTp));
      throughput.z = std::max(0.0f, std::min(throughput.z, kMaxTp));

      result.exit_pos = ray_pos + ray_dir * t;
      result.exit_normal = exit_N;
      result.throughput = throughput;
      result.exit_instance_id = hit.instance_id;
      result.exit_triangle_id = hit.triangle_id;
      result.success = true;
      return result;
    }

    float t = t_max;
    lightrt::Vec3 tau = transmittance(c.sigma_t, t);
    float pdf_scatter = ch_pdf.x * c.sigma_t.x * tau.x +
                        ch_pdf.y * c.sigma_t.y * tau.y +
                        ch_pdf.z * c.sigma_t.z * tau.z;
    if (pdf_scatter < 1e-16f) break;

    throughput.x *= c.sigma_s.x * tau.x / pdf_scatter;
    throughput.y *= c.sigma_s.y * tau.y / pdf_scatter;
    throughput.z *= c.sigma_s.z * tau.z / pdf_scatter;

    if (!std::isfinite(throughput.x) || !std::isfinite(throughput.y) ||
        !std::isfinite(throughput.z)) break;

    ray_pos = ray_pos + ray_dir * t;

    float lum = 0.2126f * throughput.x +
                0.7152f * throughput.y +
                0.0722f * throughput.z;
    lum = std::max(0.0f, std::min(1.0f, lum));
    if (dist01(rng) >= lum) break;
    throughput.x /= lum;
    throughput.y /= lum;
    throughput.z /= lum;

    lightrt::Vec3 T, B;
    buildONB(ray_dir, T, B);
    lightrt::Vec3 local_scatter = sampleHGLocal(g, dist01(rng), dist01(rng));
    ray_dir = toWorld(local_scatter, T, B, ray_dir).normalize();
  }

  return result;
}

} // namespace sss_render
} // namespace lightrt_common
