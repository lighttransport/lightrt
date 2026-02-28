// Shared CPU renderer implementation.
#include "common/renderer.hh"
#include "common/sss.hh"

#include <algorithm>
#include <cmath>
#include <random>

namespace lightrt_common {

// Resolve material for a hit
static const scene::MaterialData& resolveMaterial(const scene::Scene& scene,
                                                  const scene::HitInfo& hit) {
  static const scene::MaterialData kDefaultMat;
  if (hit.instance_id == lightrt::kInvalidIndex) return kDefaultMat;

  const auto& mesh = scene.meshes[scene.instances[hit.instance_id].mesh_id];
  if (hit.triangle_id < mesh.tri_material_ids.size()) {
    int32_t mat_id = mesh.tri_material_ids[hit.triangle_id];
    if (mat_id >= 0 && static_cast<size_t>(mat_id) < scene.materials.size())
      return scene.materials[static_cast<size_t>(mat_id)];
  }
  if (mesh.default_material_id >= 0 &&
      static_cast<size_t>(mesh.default_material_id) < scene.materials.size())
    return scene.materials[static_cast<size_t>(mesh.default_material_id)];
  return kDefaultMat;
}

// Bilinear image sample with repeat wrap
static lightrt::Vec3 sampleImage(const scene::ImageData& img, float u, float v) {
  u = u - std::floor(u);
  v = v - std::floor(v);
  float fx = u * img.width - 0.5f;
  float fy = v * img.height - 0.5f;
  int x0 = static_cast<int>(std::floor(fx));
  int y0 = static_cast<int>(std::floor(fy));
  float sx = fx - x0;
  float sy = fy - y0;
  auto fetch = [&](int x, int y) -> lightrt::Vec3 {
    x = ((x % img.width) + img.width) % img.width;
    y = ((y % img.height) + img.height) % img.height;
    size_t idx = (static_cast<size_t>(y) * img.width + x) * 4;
    return lightrt::Vec3(img.pixels[idx], img.pixels[idx + 1], img.pixels[idx + 2]);
  };
  lightrt::Vec3 c00 = fetch(x0, y0), c10 = fetch(x0 + 1, y0);
  lightrt::Vec3 c01 = fetch(x0, y0 + 1), c11 = fetch(x0 + 1, y0 + 1);
  return (c00 * (1 - sx) + c10 * sx) * (1 - sy) + (c01 * (1 - sx) + c11 * sx) * sy;
}

static float sampleImageChannel(const scene::ImageData& img, float u, float v, int ch) {
  u = u - std::floor(u);
  v = v - std::floor(v);
  float fx = u * img.width - 0.5f;
  float fy = v * img.height - 0.5f;
  int x0 = static_cast<int>(std::floor(fx));
  int y0 = static_cast<int>(std::floor(fy));
  float sx = fx - x0;
  float sy = fy - y0;
  auto fetch = [&](int x, int y) -> float {
    x = ((x % img.width) + img.width) % img.width;
    y = ((y % img.height) + img.height) % img.height;
    return img.pixels[(static_cast<size_t>(y) * img.width + x) * 4 + ch];
  };
  return (fetch(x0, y0) * (1 - sx) + fetch(x0 + 1, y0) * sx) * (1 - sy)
       + (fetch(x0, y0 + 1) * (1 - sx) + fetch(x0 + 1, y0 + 1) * sx) * sy;
}

// Compute TBN-perturbed normal from a normal map texture.
static lightrt::Vec3 applyNormalMap(const scene::Scene& scene,
                                    const scene::HitInfo& hit,
                                    const lightrt::Vec3& N_world,
                                    float tex_u, float tex_v) {
  const auto& inst = scene.instances[hit.instance_id];
  const auto& mesh = scene.meshes[inst.mesh_id];
  const auto& mat_data = resolveMaterial(scene, hit);

  if (mat_data.normal_tex_id < 0 ||
      static_cast<size_t>(mat_data.normal_tex_id) >= scene.images.size())
    return N_world;
  if (mesh.tri_uvs.empty() || hit.triangle_id * 6 + 5 >= mesh.tri_uvs.size())
    return N_world;

  lightrt::Vec3 tn = sampleImage(scene.images[mat_data.normal_tex_id], tex_u, tex_v);
  tn = tn * 2.0f - lightrt::Vec3(1.0f, 1.0f, 1.0f);
  tn = tn.normalize();

  const auto& tris = mesh.bvh.getTriangles();
  const auto& tri = tris[hit.triangle_id];
  lightrt::Vec3 e1 = tri.v1 - tri.v0;
  lightrt::Vec3 e2 = tri.v2 - tri.v0;

  size_t ub = hit.triangle_id * 6;
  float du1 = mesh.tri_uvs[ub + 2] - mesh.tri_uvs[ub + 0];
  float dv1 = mesh.tri_uvs[ub + 3] - mesh.tri_uvs[ub + 1];
  float du2 = mesh.tri_uvs[ub + 4] - mesh.tri_uvs[ub + 0];
  float dv2 = mesh.tri_uvs[ub + 5] - mesh.tri_uvs[ub + 1];

  float det = du1 * dv2 - du2 * dv1;
  if (std::abs(det) < 1e-8f) return N_world;
  float inv_det = 1.0f / det;

  lightrt::Vec3 T_local = (e1 * dv2 - e2 * dv1) * inv_det;
  lightrt::Vec3 T_world = scene::transformNormal(inst.inv_transform, T_local);
  T_world = (T_world - N_world * N_world.dot(T_world)).normalize();
  lightrt::Vec3 B_world = N_world.cross(T_world);

  return (T_world * tn.x + B_world * tn.y + N_world * tn.z).normalize();
}

static scene::MaterialData resolveMaterialTextured(const scene::Scene& scene,
                                                   const scene::HitInfo& hit) {
  scene::MaterialData mat = resolveMaterial(scene, hit);

  const auto& mesh = scene.meshes[scene.instances[hit.instance_id].mesh_id];
  if (mesh.tri_uvs.empty()) return mat;
  if (hit.triangle_id * 6 + 5 >= mesh.tri_uvs.size()) return mat;

  float w = 1.0f - hit.u - hit.v;
  size_t uv_base = hit.triangle_id * 6;
  float tex_u = mesh.tri_uvs[uv_base + 0] * w +
                mesh.tri_uvs[uv_base + 2] * hit.u +
                mesh.tri_uvs[uv_base + 4] * hit.v;
  float tex_v = mesh.tri_uvs[uv_base + 1] * w +
                mesh.tri_uvs[uv_base + 3] * hit.u +
                mesh.tri_uvs[uv_base + 5] * hit.v;

  if (mat.base_color_tex_id >= 0 &&
      static_cast<size_t>(mat.base_color_tex_id) < scene.images.size())
    mat.base_color = sampleImage(scene.images[mat.base_color_tex_id], tex_u, tex_v);
  if (mat.metalness_tex_id >= 0 &&
      static_cast<size_t>(mat.metalness_tex_id) < scene.images.size())
    mat.base_metalness = sampleImageChannel(scene.images[mat.metalness_tex_id], tex_u, tex_v, 0);
  if (mat.roughness_tex_id >= 0 &&
      static_cast<size_t>(mat.roughness_tex_id) < scene.images.size())
    mat.specular_roughness = sampleImageChannel(scene.images[mat.roughness_tex_id], tex_u, tex_v, 0);
  if (mat.emissive_tex_id >= 0 &&
      static_cast<size_t>(mat.emissive_tex_id) < scene.images.size())
    mat.emission_color = sampleImage(scene.images[mat.emissive_tex_id], tex_u, tex_v);
  if (mat.opacity_tex_id >= 0 &&
      static_cast<size_t>(mat.opacity_tex_id) < scene.images.size())
    mat.opacity = sampleImageChannel(scene.images[mat.opacity_tex_id], tex_u, tex_v, 0);

  return mat;
}

struct SSSResult {
  lightrt::Vec3 exit_pos;
  lightrt::Vec3 exit_normal;
  lightrt::Vec3 throughput;
  uint32_t exit_instance_id = lightrt::kInvalidIndex;
  uint32_t exit_triangle_id = lightrt::kInvalidIndex;
  bool success = false;
};

static lightrt::Vec3 computeWorldNormal(const scene::Scene& scene,
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

static SSSResult randomWalkSSS(const scene::Scene& scene,
                               const lightrt::Vec3& entry_pos,
                               const lightrt::Vec3& entry_N,
                               uint32_t entry_instance_id,
                               const scene::MaterialData& mat,
                               std::mt19937& rng,
                               std::uniform_real_distribution<float>& dist01) {
  using namespace lightrt_common::sss;
  SSSResult result{};

  const SSSCoeffs c = computeCoeffsFromMaterial(mat);
  if (c.sigma_t.x > 1e14f && c.sigma_t.y > 1e14f && c.sigma_t.z > 1e14f)
    return result;

  float g = std::max(-0.99f, std::min(0.99f, mat.subsurface_anisotropy));

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

void renderFrame(const scene::Scene& scene,
                 const RenderSettings& settings,
                 const CameraView& camera,
                 std::vector<lightrt::RGB8>& image) {
  using namespace scene::shading;
  image.resize(settings.width * settings.height);

  bool has_lights = !scene.lights.empty();
  bool has_envmap = scene.envmap.valid();
  bool use_fallback = !has_lights && !has_envmap;

  lightrt::Vec3 fallback_light_dir = lightrt::Vec3(0.5f, 0.8f, 0.3f).normalize();

  uint32_t total_samples = settings.spp * settings.mblur_samples;
  if (total_samples == 0) total_samples = 1;

  for (uint32_t y = 0; y < settings.height; y++) {
    for (uint32_t x = 0; x < settings.width; x++) {
      float r_acc = 0.0f, g_acc = 0.0f, b_acc = 0.0f;

      uint32_t seed = y * settings.width + x;
      std::mt19937 rng(seed ^ 0x9e3779b9u);
      std::uniform_real_distribution<float> dist01(0.0f, 1.0f);

      for (uint32_t s = 0; s < total_samples; s++) {
        float jx = (total_samples > 1) ? dist01(rng) : 0.5f;
        float jy = (total_samples > 1) ? dist01(rng) : 0.5f;
        float u = (2.0f * (x + jx) / settings.width - 1.0f) * camera.half_width;
        float v = (1.0f - 2.0f * (y + jy) / settings.height) * camera.half_height;

        lightrt::Vec3 dir = (camera.direction + camera.right * u + camera.up * v).normalize();
        lightrt::Ray ray(camera.position, dir);

        float ray_time = (settings.mblur_samples > 1) ? dist01(rng) : 0.0f;

        scene::HitInfo hit = scene::traceScene(scene, ray, ray_time);

        lightrt::Vec3 color(0.0f, 0.0f, 0.0f);

        if (hit.instance_id == lightrt::kInvalidIndex) {
          if (has_envmap) {
            color = evalEnvmap(scene.envmap, dir);
          } else {
            color = lightrt::Vec3(0.118f, 0.118f, 0.157f);
          }
        } else {
          const auto& inst = scene.instances[hit.instance_id];
          const auto& mesh_blas = scene.meshes[inst.mesh_id];
          const auto& tris = mesh_blas.bvh.getTriangles();
          const auto& tri = tris[hit.triangle_id];

          lightrt::Vec3 local_n;
          if (!mesh_blas.tri_normals.empty() && hit.triangle_id * 9 + 8 < mesh_blas.tri_normals.size()) {
            size_t nb = hit.triangle_id * 9;
            float w = 1.0f - hit.u - hit.v;
            local_n = lightrt::Vec3(
              mesh_blas.tri_normals[nb + 0] * w + mesh_blas.tri_normals[nb + 3] * hit.u + mesh_blas.tri_normals[nb + 6] * hit.v,
              mesh_blas.tri_normals[nb + 1] * w + mesh_blas.tri_normals[nb + 4] * hit.u + mesh_blas.tri_normals[nb + 7] * hit.v,
              mesh_blas.tri_normals[nb + 2] * w + mesh_blas.tri_normals[nb + 5] * hit.u + mesh_blas.tri_normals[nb + 8] * hit.v
            ).normalize();
          } else {
            lightrt::Vec3 e1 = tri.v1 - tri.v0;
            lightrt::Vec3 e2 = tri.v2 - tri.v0;
            local_n = e1.cross(e2).normalize();
          }

          lightrt::Vec3 N = scene::transformNormal(inst.inv_transform, local_n).normalize();
          lightrt::Vec3 V = dir * -1.0f;
          if (N.dot(V) < 0.0f) N = N * -1.0f;

          lightrt::Vec3 hit_pos = camera.position + dir * hit.t;
          float bias = 0.001f;

          const scene::MaterialData mat = resolveMaterialTextured(scene, hit);

          if (!mesh_blas.tri_uvs.empty() && hit.triangle_id * 6 + 5 < mesh_blas.tri_uvs.size()) {
            float w = 1.0f - hit.u - hit.v;
            size_t ub = hit.triangle_id * 6;
            float tu = mesh_blas.tri_uvs[ub + 0] * w + mesh_blas.tri_uvs[ub + 2] * hit.u + mesh_blas.tri_uvs[ub + 4] * hit.v;
            float tv = mesh_blas.tri_uvs[ub + 1] * w + mesh_blas.tri_uvs[ub + 3] * hit.u + mesh_blas.tri_uvs[ub + 5] * hit.v;
            N = applyNormalMap(scene, hit, N, tu, tv);
            if (N.dot(V) < 0.0f) N = N * -1.0f;
          }

          if (mat.emission_luminance > 0.0f) {
            color = color + mat.emission_color * mat.emission_luminance;
          }

          const float sss_weight = (mat.subsurface_radius > 1e-8f)
                                     ? std::max(0.0f, std::min(1.0f, mat.subsurface_weight))
                                     : 0.0f;
          const float brdf_scale = 1.0f - sss_weight;

          if (use_fallback) {
            float ndl = std::max(0.0f, N.dot(fallback_light_dir));
            lightrt::Ray shadow_ray(hit_pos + N * bias, fallback_light_dir);
            bool in_shadow = scene::traceSceneAnyHit(scene, shadow_ray,
              hit.instance_id, hit.triangle_id, ray_time);

            float ambient = 0.15f;
            float diffuse = in_shadow ? 0.0f : ndl * 0.85f;
            float shade = std::min(1.0f, ambient + diffuse);
            color = color + mat.base_color * shade;
          } else {
            constexpr float kTwoPi = 6.28318530718f;
            for (const auto& light : scene.lights) {
              lightrt::Vec3 L;
              float light_dist = 1e20f;
              float geom_factor = 1.0f;

              if (light.type == scene::LightData::Distant) {
                L = light.direction * -1.0f;
              } else if (light.type == scene::LightData::Point) {
                lightrt::Vec3 to_light = light.position - hit_pos;
                light_dist = to_light.length();
                if (light_dist < 1e-6f) continue;
                L = to_light * (1.0f / light_dist);
              } else if (light.type == scene::LightData::Sphere) {
                if (light.radius <= 0.0f) {
                  lightrt::Vec3 to_light = light.position - hit_pos;
                  light_dist = to_light.length();
                  if (light_dist < 1e-6f) continue;
                  L = to_light * (1.0f / light_dist);
                  geom_factor = 1.0f / (light_dist * light_dist);
                } else {
                  float u1 = dist01(rng);
                  float u2 = dist01(rng);
                  float z = 1.0f - 2.0f * u1;
                  float r = std::sqrt(std::max(0.0f, 1.0f - z * z));
                  float phi = kTwoPi * u2;
                  lightrt::Vec3 normal(r * std::cos(phi), r * std::sin(phi), z);
                  lightrt::Vec3 sample_pos = light.position + normal * light.radius;
                  lightrt::Vec3 to_light = sample_pos - hit_pos;
                  light_dist = to_light.length();
                  if (light_dist < 1e-6f) continue;
                  L = to_light * (1.0f / light_dist);
                  float cos_emit = normal.dot(L * -1.0f);
                  if (cos_emit <= 0.0f) continue;
                  float sphere_area = 4.0f * 3.14159265f * light.radius * light.radius;
                  geom_factor = cos_emit * sphere_area / (light_dist * light_dist);
                }
              } else if (light.type == scene::LightData::Rect) {
                float u = dist01(rng) * 2.0f - 1.0f;
                float v = dist01(rng) * 2.0f - 1.0f;
                lightrt::Vec3 sample_pos =
                  light.position
                  + light.rect_axis_u * (u * light.rect_half_width)
                  + light.rect_axis_v * (v * light.rect_half_height);
                lightrt::Vec3 to_light = sample_pos - hit_pos;
                light_dist = to_light.length();
                if (light_dist < 1e-6f) continue;
                L = to_light * (1.0f / light_dist);
                float cos_emit = light.direction.dot(L * -1.0f);
                if (cos_emit <= 0.0f) continue;
                float rect_area = (light.rect_half_width * 2.0f) * (light.rect_half_height * 2.0f);
                geom_factor = cos_emit * rect_area / (light_dist * light_dist);
              } else {
                continue;
              }

              lightrt::Ray shadow_ray(hit_pos + N * bias, L, 0.0f, light_dist - bias);
              if (scene::traceSceneAnyHit(scene, shadow_ray, hit.instance_id,
                                          hit.triangle_id, ray_time))
                continue;

              lightrt::Vec3 brdf_ndl = evalBRDF(N, V, L, mat);
              lightrt::Vec3 light_contribution = light.color;
              if (light.type == scene::LightData::Point) {
                float inv_r2 = 1.0f / (light_dist * light_dist);
                light_contribution = light_contribution * inv_r2;
              } else if (light.type == scene::LightData::Sphere) {
                light_contribution = light_contribution * geom_factor;
              } else if (light.type == scene::LightData::Rect) {
                light_contribution = light_contribution * geom_factor;
              }

              color = color + lightrt::Vec3(
                brdf_ndl.x * light_contribution.x,
                brdf_ndl.y * light_contribution.y,
                brdf_ndl.z * light_contribution.z) * brdf_scale;
            }

            if (has_envmap && mat.base_metalness > 0.5f && mat.specular_roughness < 0.05f) {
              float NdotV = std::max(0.0f, N.dot(V));
              float r0 = ((mat.specular_ior - 1.0f) / (mat.specular_ior + 1.0f));
              r0 = r0 * r0;
              lightrt::Vec3 F0(
                r0 + (mat.base_color.x - r0) * mat.base_metalness,
                r0 + (mat.base_color.y - r0) * mat.base_metalness,
                r0 + (mat.base_color.z - r0) * mat.base_metalness);
              float schlick = std::pow(1.0f - NdotV, 5.0f);
              lightrt::Vec3 F(
                F0.x + (1.0f - F0.x) * schlick,
                F0.y + (1.0f - F0.y) * schlick,
                F0.z + (1.0f - F0.z) * schlick);
              lightrt::Vec3 refl_d = (V * -1.0f + N * (2.0f * NdotV)).normalize();
              lightrt::Ray refl_ray(hit_pos + N * bias, refl_d);
              if (!scene::traceSceneAnyHit(scene, refl_ray, hit.instance_id, hit.triangle_id, ray_time)) {
                lightrt::Vec3 env_col = evalEnvmap(scene.envmap, refl_d);
                color.x += F.x * env_col.x * brdf_scale;
                color.y += F.y * env_col.y * brdf_scale;
                color.z += F.z * env_col.z * brdf_scale;
              }
            } else if (has_envmap) {
              float alpha = std::max(0.001f, mat.specular_roughness * mat.specular_roughness);
              lightrt::Vec3 T, B;
              buildONB(N, T, B);

              {
                float env_pdf = 0.0f;
                lightrt::Vec3 L = sampleEnvmap(scene.envmap, dist01(rng), dist01(rng), env_pdf);
                float NdotL = N.dot(L);
                if (NdotL > 0.0f && env_pdf > 1e-8f) {
                  lightrt::Ray shadow_ray(hit_pos + N * bias, L);
                  if (!scene::traceSceneAnyHit(scene, shadow_ray, hit.instance_id,
                                               hit.triangle_id, ray_time)) {
                    lightrt::Vec3 brdf_ndl = evalBRDF(N, V, L, mat);
                    lightrt::Vec3 env_col = evalEnvmap(scene.envmap, L);
                    lightrt::Vec3 H = (V + L).normalize();
                    float NdotH = std::max(0.0f, N.dot(H));
                    float VdotH = std::max(0.0f, V.dot(H));
                    float brdf_pdf = pdfGGX(NdotH, VdotH, alpha);
                    float p_spec = (mat.base_metalness >= 0.9f) ? 1.0f : 0.5f;
                    float p_diff = 1.0f - p_spec;
                    float combined_brdf_pdf = p_spec * brdf_pdf + p_diff * NdotL * kInvPi;
                    float w = misBalance(env_pdf, combined_brdf_pdf);
                    lightrt::Vec3 contrib(
                      brdf_ndl.x * env_col.x * w / env_pdf,
                      brdf_ndl.y * env_col.y * w / env_pdf,
                      brdf_ndl.z * env_col.z * w / env_pdf);
                    color = color + contrib * brdf_scale;
                  }
                }
              }

              {
                bool sample_diffuse = (mat.base_metalness < 0.9f) && (dist01(rng) < 0.5f);
                lightrt::Vec3 L;
                if (sample_diffuse) {
                  float r1 = dist01(rng), r2 = dist01(rng);
                  float cos_theta = std::sqrt(1.0f - r1);
                  float sin_theta = std::sqrt(r1);
                  float phi = 2.0f * kPi * r2;
                  lightrt::Vec3 local(sin_theta * std::cos(phi), sin_theta * std::sin(phi), cos_theta);
                  L = toWorld(local, N, T, B);
                } else {
                  lightrt::Vec3 H_local = sampleGGX(dist01(rng), dist01(rng), alpha);
                  lightrt::Vec3 H = toWorld(H_local, N, T, B);
                  L = V * -1.0f + H * (2.0f * V.dot(H));
                  L = L.normalize();
                }

                float NdotL = N.dot(L);
                if (NdotL > 0.0f) {
                  lightrt::Ray shadow_ray(hit_pos + N * bias, L);
                  if (!scene::traceSceneAnyHit(scene, shadow_ray, hit.instance_id,
                                               hit.triangle_id, ray_time)) {
                    lightrt::Vec3 brdf_ndl = evalBRDF(N, V, L, mat);
                    lightrt::Vec3 env_col = evalEnvmap(scene.envmap, L);
                    lightrt::Vec3 H = (V + L).normalize();
                    float NdotH = std::max(0.0f, N.dot(H));
                    float VdotH = std::max(0.0f, V.dot(H));
                    float brdf_pdf = pdfGGX(NdotH, VdotH, alpha);
                    float p_spec = (mat.base_metalness >= 0.9f) ? 1.0f : 0.5f;
                    float p_diff = 1.0f - p_spec;
                    float combined_brdf_pdf = p_spec * brdf_pdf + p_diff * NdotL * kInvPi;
                    float env_pdf = envmapPDF(scene.envmap, L);
                    float w = misBalance(combined_brdf_pdf, env_pdf);
                    if (combined_brdf_pdf > 1e-8f) {
                      lightrt::Vec3 contrib(
                        brdf_ndl.x * env_col.x * w / combined_brdf_pdf,
                        brdf_ndl.y * env_col.y * w / combined_brdf_pdf,
                        brdf_ndl.z * env_col.z * w / combined_brdf_pdf);
                      color = color + contrib * brdf_scale;
                    }
                  }
                }
              }
            }

            if (sss_weight > 1e-4f) {
              SSSResult sss_r = randomWalkSSS(scene, hit_pos, N,
                                              hit.instance_id, mat, rng, dist01);
              if (sss_r.success) {
                const lightrt::Vec3& eN = sss_r.exit_normal;
                const lightrt::Vec3& eP = sss_r.exit_pos;
                const lightrt::Vec3& tp = sss_r.throughput;

                constexpr float kTwoPi = 6.28318530718f;
                for (const auto& light : scene.lights) {
                  lightrt::Vec3 Lex;
                  float ld = 1e20f;
                  float sss_geom = 1.0f;
                  if (light.type == scene::LightData::Distant) {
                    Lex = light.direction * -1.0f;
                  } else if (light.type == scene::LightData::Point) {
                    lightrt::Vec3 tl = light.position - eP;
                    ld = tl.length();
                    if (ld < 1e-6f) continue;
                    Lex = tl * (1.0f / ld);
                  } else if (light.type == scene::LightData::Sphere) {
                    if (light.radius <= 0.0f) {
                      lightrt::Vec3 tl = light.position - eP;
                      ld = tl.length();
                      if (ld < 1e-6f) continue;
                      Lex = tl * (1.0f / ld);
                      sss_geom = 1.0f / (ld * ld);
                    } else {
                      float u1 = dist01(rng);
                      float u2 = dist01(rng);
                      float z = 1.0f - 2.0f * u1;
                      float r = std::sqrt(std::max(0.0f, 1.0f - z * z));
                      float phi = kTwoPi * u2;
                      lightrt::Vec3 normal(r * std::cos(phi), r * std::sin(phi), z);
                      lightrt::Vec3 sp = light.position + normal * light.radius;
                      lightrt::Vec3 tl = sp - eP;
                      ld = tl.length();
                      if (ld < 1e-6f) continue;
                      Lex = tl * (1.0f / ld);
                      float cos_emit = normal.dot(Lex * -1.0f);
                      if (cos_emit <= 0.0f) continue;
                      float sphere_area = 4.0f * 3.14159265f * light.radius * light.radius;
                      sss_geom = cos_emit * sphere_area / (ld * ld);
                    }
                  } else if (light.type == scene::LightData::Rect) {
                    float u = dist01(rng) * 2.0f - 1.0f;
                    float v = dist01(rng) * 2.0f - 1.0f;
                    lightrt::Vec3 sp = light.position
                      + light.rect_axis_u * (u * light.rect_half_width)
                      + light.rect_axis_v * (v * light.rect_half_height);
                    lightrt::Vec3 tl = sp - eP;
                    ld = tl.length();
                    if (ld < 1e-6f) continue;
                    Lex = tl * (1.0f / ld);
                    float cos_emit = light.direction.dot(Lex * -1.0f);
                    if (cos_emit <= 0.0f) continue;
                    float rect_area = (light.rect_half_width * 2.0f) *
                                      (light.rect_half_height * 2.0f);
                    sss_geom = cos_emit * rect_area / (ld * ld);
                  } else {
                    continue;
                  }

                  float NdotL_ex = std::max(0.0f, eN.dot(Lex));
                  if (NdotL_ex <= 0.0f) continue;

                  lightrt::Ray sh(eP + eN * bias, Lex, 0.0f, ld - bias);
                  if (scene::traceSceneAnyHit(scene, sh,
                        sss_r.exit_instance_id, sss_r.exit_triangle_id,
                        ray_time)) continue;

                  lightrt::Vec3 lc = light.color;
                  if (light.type == scene::LightData::Point)
                    lc = lc * (1.0f / (ld * ld));
                  else if (light.type == scene::LightData::Sphere)
                    lc = lc * sss_geom;
                  else if (light.type == scene::LightData::Rect)
                    lc = lc * sss_geom;

                  float lambert = NdotL_ex * kInvPi;
                  color = color + lightrt::Vec3(
                    lc.x * mat.base_color.x * lambert * tp.x,
                    lc.y * mat.base_color.y * lambert * tp.y,
                    lc.z * mat.base_color.z * lambert * tp.z) * sss_weight;
                }

                if (has_envmap) {
                  float env_pdf = 0.0f;
                  lightrt::Vec3 Lex = sampleEnvmap(scene.envmap,
                                                    dist01(rng), dist01(rng),
                                                    env_pdf);
                  float NdotL_ex = std::max(0.0f, eN.dot(Lex));
                  if (NdotL_ex > 0.0f && env_pdf > 1e-8f) {
                    lightrt::Ray sh(eP + eN * bias, Lex);
                    if (!scene::traceSceneAnyHit(scene, sh,
                          sss_r.exit_instance_id, sss_r.exit_triangle_id,
                          ray_time)) {
                      lightrt::Vec3 env_col = evalEnvmap(scene.envmap, Lex);
                      float lambert = NdotL_ex * kInvPi;
                      float lam_pdf = NdotL_ex * kInvPi;
                      float wm = misBalance(env_pdf, lam_pdf);
                      color = color + lightrt::Vec3(
                        env_col.x * mat.base_color.x * lambert * tp.x * wm / env_pdf,
                        env_col.y * mat.base_color.y * lambert * tp.y * wm / env_pdf,
                        env_col.z * mat.base_color.z * lambert * tp.z * wm / env_pdf) * sss_weight;
                    }
                  }

                  {
                    lightrt::Vec3 eT, eB;
                    buildONB(eN, eT, eB);
                    float r1 = dist01(rng), r2 = dist01(rng);
                    float cos_t = std::sqrt(1.0f - r1);
                    float sin_t = std::sqrt(r1);
                    float phi = 2.0f * kPi * r2;
                    lightrt::Vec3 local(sin_t * std::cos(phi), sin_t * std::sin(phi), cos_t);
                    lightrt::Vec3 Lex2 = toWorld(local, eN, eT, eB);
                    float NdotL2 = std::max(0.0f, eN.dot(Lex2));
                    if (NdotL2 > 0.0f) {
                      lightrt::Ray sh2(eP + eN * bias, Lex2);
                      if (!scene::traceSceneAnyHit(scene, sh2,
                            sss_r.exit_instance_id, sss_r.exit_triangle_id,
                            ray_time)) {
                        lightrt::Vec3 env_col2 = evalEnvmap(scene.envmap, Lex2);
                        float lam_pdf2 = NdotL2 * kInvPi;
                        float env_pdf2 = envmapPDF(scene.envmap, Lex2);
                        float wm2 = misBalance(lam_pdf2, env_pdf2);
                        if (lam_pdf2 > 1e-8f) {
                          float lambert2 = NdotL2 * kInvPi;
                          color = color + lightrt::Vec3(
                            env_col2.x * mat.base_color.x * lambert2 * tp.x * wm2 / lam_pdf2,
                            env_col2.y * mat.base_color.y * lambert2 * tp.y * wm2 / lam_pdf2,
                            env_col2.z * mat.base_color.z * lambert2 * tp.z * wm2 / lam_pdf2) * sss_weight;
                        }
                      }
                    }
                  }
                }
              }
            }

            if (mat.transmission_weight > 0.01f) {
              float NdotV_raw = N.dot(V);
              bool inside = NdotV_raw < 0.0f;
              lightrt::Vec3 fN = inside ? N * -1.0f : N;
              float cos_i = std::max(0.0f, fN.dot(V));

              float ior = mat.specular_ior > 1.0f ? mat.specular_ior : 1.5f;
              float eta = inside ? ior : (1.0f / ior);
              float r0 = (ior - 1.0f) / (ior + 1.0f);
              r0 = r0 * r0;
              float fresnel = r0 + (1.0f - r0) * std::pow(1.0f - cos_i, 5.0f);

              lightrt::Vec3 trans_col(0.0f, 0.0f, 0.0f);
              if (dist01(rng) < fresnel) {
                lightrt::Vec3 refl_d = (V * -1.0f + fN * (2.0f * cos_i)).normalize();
                lightrt::Ray refl_ray(hit_pos + fN * bias, refl_d);
                scene::HitInfo rh = scene::traceScene(scene, refl_ray, ray_time);
                if (rh.triangle_id != lightrt::kInvalidIndex) {
                  trans_col = resolveMaterialTextured(scene, rh).base_color;
                } else if (has_envmap) {
                  trans_col = evalEnvmap(scene.envmap, refl_d);
                } else {
                  trans_col = lightrt::Vec3(0.118f, 0.118f, 0.157f);
                }
              } else {
                float sin2t = eta * eta * (1.0f - cos_i * cos_i);
                if (sin2t > 1.0f) {
                  lightrt::Vec3 refl_d = (V * -1.0f + fN * (2.0f * cos_i)).normalize();
                  if (has_envmap) trans_col = evalEnvmap(scene.envmap, refl_d);
                  else trans_col = lightrt::Vec3(0.118f, 0.118f, 0.157f);
                } else {
                  float cos_t = std::sqrt(1.0f - sin2t);
                  lightrt::Vec3 refr_d = (V * -1.0f) * eta + fN * (eta * cos_i - cos_t);
                  refr_d = refr_d.normalize();
                  lightrt::Ray refr_ray(hit_pos - fN * bias, refr_d);
                  scene::HitInfo rh = scene::traceScene(scene, refr_ray, ray_time);
                  if (rh.triangle_id != lightrt::kInvalidIndex) {
                    trans_col = resolveMaterialTextured(scene, rh).base_color;
                  } else if (has_envmap) {
                    trans_col = evalEnvmap(scene.envmap, refr_d);
                  } else {
                    trans_col = lightrt::Vec3(0.118f, 0.118f, 0.157f);
                  }
                }
              }
              trans_col.x *= mat.transmission_color.x;
              trans_col.y *= mat.transmission_color.y;
              trans_col.z *= mat.transmission_color.z;
              color.x = color.x * (1.0f - mat.transmission_weight) + trans_col.x * mat.transmission_weight;
              color.y = color.y * (1.0f - mat.transmission_weight) + trans_col.y * mat.transmission_weight;
              color.z = color.z * (1.0f - mat.transmission_weight) + trans_col.z * mat.transmission_weight;
            }
          }
        }

        r_acc += color.x;
        g_acc += color.y;
        b_acc += color.z;
      }

      float inv_s = 1.0f / static_cast<float>(total_samples);
      float r = r_acc * inv_s;
      float g = g_acc * inv_s;
      float b = b_acc * inv_s;

      r = r / (r + 1.0f);
      g = g / (g + 1.0f);
      b = b / (b + 1.0f);

      r = std::pow(std::max(0.0f, r), 1.0f / 2.2f);
      g = std::pow(std::max(0.0f, g), 1.0f / 2.2f);
      b = std::pow(std::max(0.0f, b), 1.0f / 2.2f);

      uint8_t cr = static_cast<uint8_t>(std::min(255.0f, r * 255.0f));
      uint8_t cg = static_cast<uint8_t>(std::min(255.0f, g * 255.0f));
      uint8_t cb = static_cast<uint8_t>(std::min(255.0f, b * 255.0f));
      image[y * settings.width + x] = lightrt::RGB8(cr, cg, cb);
    }
  }
}

} // namespace lightrt_common
