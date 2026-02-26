// BRDF, environment map, and tonemapping utilities
// Extracted from cli/scene.hh and viewer/common/viewer_common.cc for shared use
#pragma once

#include "lightrt.hh"
#include "common/materials.hh"
#include <cmath>
#include <algorithm>

namespace lightrt_common {
namespace shading {

constexpr float kPi = 3.14159265358979323846f;
constexpr float kInvPi = 1.0f / kPi;

// --- Tonemapping ---

inline float reinhardTonemap(float x) { return x / (1.0f + x); }

inline float linearToSRGB(float x) {
  return std::pow(std::max(0.0f, x), 1.0f / 2.2f);
}

// --- Fresnel / GGX BRDF ---

inline lightrt::Vec3 fresnelSchlick(float cos_theta, const lightrt::Vec3& F0) {
  float t = 1.0f - cos_theta;
  float t2 = t * t;
  float t5 = t2 * t2 * t;
  return F0 + (lightrt::Vec3(1.0f, 1.0f, 1.0f) - F0) * t5;
}

inline float ggxD(float NdotH, float alpha) {
  float a2 = alpha * alpha;
  float denom = NdotH * NdotH * (a2 - 1.0f) + 1.0f;
  return a2 * kInvPi / (denom * denom + 1e-7f);
}

inline float ggxG1(float NdotX, float alpha) {
  float a2 = alpha * alpha;
  return 2.0f * NdotX / (NdotX + std::sqrt(a2 + (1.0f - a2) * NdotX * NdotX) + 1e-7f);
}

inline float ggxG(float NdotV, float NdotL, float alpha) {
  return ggxG1(NdotV, alpha) * ggxG1(NdotL, alpha);
}

// Evaluate BRDF * NdotL for combined Lambertian diffuse + GGX specular
inline lightrt::Vec3 evalBRDF(const lightrt::Vec3& N, const lightrt::Vec3& V,
                              const lightrt::Vec3& L, const MaterialData& mat) {
  float NdotL = std::max(0.0f, N.dot(L));
  if (NdotL <= 0.0f) return lightrt::Vec3(0.0f, 0.0f, 0.0f);

  float NdotV = std::max(0.001f, N.dot(V));
  lightrt::Vec3 H = (V + L).normalize();
  float NdotH = std::max(0.0f, N.dot(H));
  float VdotH = std::max(0.0f, V.dot(H));

  float alpha = std::max(0.001f, mat.specular_roughness * mat.specular_roughness);

  // F0: blend between dielectric (from IOR) and metallic (base_color)
  float f0_dielectric = ((mat.specular_ior - 1.0f) * (mat.specular_ior - 1.0f)) /
                        ((mat.specular_ior + 1.0f) * (mat.specular_ior + 1.0f));
  lightrt::Vec3 F0(
    f0_dielectric * (1.0f - mat.base_metalness) + mat.base_color.x * mat.base_metalness,
    f0_dielectric * (1.0f - mat.base_metalness) + mat.base_color.y * mat.base_metalness,
    f0_dielectric * (1.0f - mat.base_metalness) + mat.base_color.z * mat.base_metalness);

  lightrt::Vec3 F = fresnelSchlick(VdotH, F0);
  float D = ggxD(NdotH, alpha);
  float G = ggxG(NdotV, NdotL, alpha);

  // Specular
  lightrt::Vec3 spec = F * (D * G / (4.0f * NdotV * NdotL + 1e-7f));

  // Diffuse (energy-conserving: scale by (1-F)(1-metalness))
  lightrt::Vec3 kd(
    (1.0f - F.x) * (1.0f - mat.base_metalness),
    (1.0f - F.y) * (1.0f - mat.base_metalness),
    (1.0f - F.z) * (1.0f - mat.base_metalness));
  lightrt::Vec3 diffuse(
    kd.x * mat.base_color.x * kInvPi,
    kd.y * mat.base_color.y * kInvPi,
    kd.z * mat.base_color.z * kInvPi);

  return (diffuse + spec) * NdotL;
}

// --- Coat lobe (GGX specular) ---

inline lightrt::Vec3 evalCoat(const lightrt::Vec3& N, const lightrt::Vec3& V,
                               const lightrt::Vec3& L,
                               const OpenPBRMaterial& mat) {
  if (mat.coat_weight <= 0.0f) return lightrt::Vec3(0.0f, 0.0f, 0.0f);
  float NdotL = std::max(0.0f, N.dot(L));
  if (NdotL <= 0.0f) return lightrt::Vec3(0.0f, 0.0f, 0.0f);
  float NdotV = std::max(0.001f, N.dot(V));
  lightrt::Vec3 H = (V + L).normalize();
  float NdotH = std::max(0.0f, N.dot(H));
  float VdotH = std::max(0.0f, V.dot(H));
  float alpha = std::max(0.001f, mat.coat_roughness * mat.coat_roughness);
  float f0_coat = ((mat.coat_ior - 1.0f) * (mat.coat_ior - 1.0f)) /
                  ((mat.coat_ior + 1.0f) * (mat.coat_ior + 1.0f));
  lightrt::Vec3 F0c(f0_coat, f0_coat, f0_coat);
  lightrt::Vec3 F = fresnelSchlick(VdotH, F0c);
  float D = ggxD(NdotH, alpha);
  float G = ggxG(NdotV, NdotL, alpha);
  float brdf_scalar = D * G / (4.0f * NdotV * NdotL + 1e-7f);
  lightrt::Vec3 coat_spec(
    mat.coat_color.x * F.x * brdf_scalar,
    mat.coat_color.y * F.y * brdf_scalar,
    mat.coat_color.z * F.z * brdf_scalar);
  return coat_spec * (mat.coat_weight * NdotL);
}

// --- Sheen / Fuzz lobe (Charlie distribution approximation) ---

inline float charlieD(float NdotH, float alpha) {
  float inv_a = 1.0f / (alpha * alpha);
  float cos2   = NdotH * NdotH;
  float sin2   = 1.0f - cos2;
  return (2.0f + inv_a) * std::pow(std::max(0.0f, sin2), inv_a * 0.5f) / (2.0f * kPi);
}

inline lightrt::Vec3 evalSheen(const lightrt::Vec3& N, const lightrt::Vec3& V,
                                const lightrt::Vec3& L,
                                const OpenPBRMaterial& mat) {
  if (mat.sheen_weight <= 0.0f) return lightrt::Vec3(0.0f, 0.0f, 0.0f);
  float NdotL = std::max(0.0f, N.dot(L));
  if (NdotL <= 0.0f) return lightrt::Vec3(0.0f, 0.0f, 0.0f);
  float NdotV = std::max(0.001f, N.dot(V));
  lightrt::Vec3 H = (V + L).normalize();
  float NdotH = std::max(0.001f, N.dot(H));
  float alpha = std::max(0.01f, mat.sheen_roughness);
  float D   = charlieD(NdotH, alpha);
  float Vis = 1.0f / (4.0f * (NdotV + NdotL - NdotV * NdotL) + 1e-7f);
  return mat.sheen_color * (mat.sheen_weight * D * Vis * NdotL);
}

inline lightrt::Vec3 evalFuzz(const lightrt::Vec3& N, const lightrt::Vec3& V,
                               const lightrt::Vec3& L,
                               const OpenPBRMaterial& mat) {
  if (mat.fuzz_weight <= 0.0f) return lightrt::Vec3(0.0f, 0.0f, 0.0f);
  float NdotL = std::max(0.0f, N.dot(L));
  if (NdotL <= 0.0f) return lightrt::Vec3(0.0f, 0.0f, 0.0f);
  float NdotV = std::max(0.001f, N.dot(V));
  lightrt::Vec3 H = (V + L).normalize();
  float NdotH = std::max(0.001f, N.dot(H));
  float alpha = std::max(0.01f, mat.fuzz_roughness);
  float D   = charlieD(NdotH, alpha);
  float Vis = 1.0f / (4.0f * (NdotV + NdotL - NdotV * NdotL) + 1e-7f);
  return mat.fuzz_color * (mat.fuzz_weight * D * Vis * NdotL);
}

// --- Subsurface lobe (wrapped-diffuse approximation) ---

inline lightrt::Vec3 evalSubsurface(const lightrt::Vec3& N, const lightrt::Vec3& V,
                                     const lightrt::Vec3& L,
                                     const OpenPBRMaterial& mat) {
  if (mat.subsurface_weight <= 0.0f) return lightrt::Vec3(0.0f, 0.0f, 0.0f);
  (void)V;
  float NdotL_wrap = (N.dot(L) + 0.5f) / 1.5f;
  float wrapped    = std::max(0.0f, NdotL_wrap);
  lightrt::Vec3 scat_color(
    mat.base_color.x * mat.subsurface_radius_scale.x,
    mat.base_color.y * mat.subsurface_radius_scale.y,
    mat.base_color.z * mat.subsurface_radius_scale.z);
  return scat_color * (mat.subsurface_weight * wrapped * kInvPi);
}

// --- Transmission refraction direction helper ---
// Returns refracted ray direction; zero-vector on total internal reflection.
inline lightrt::Vec3 refractionDir(const lightrt::Vec3& I, const lightrt::Vec3& N,
                                    float ior_ratio) {
  float cos_i = -I.dot(N);
  float sin2t = ior_ratio * ior_ratio * (1.0f - cos_i * cos_i);
  if (sin2t > 1.0f) return lightrt::Vec3(0.0f, 0.0f, 0.0f);
  float cos_t = std::sqrt(1.0f - sin2t);
  return I * ior_ratio + N * (ior_ratio * cos_i - cos_t);
}

// --- Combined OpenPBR evaluation (all direct-lighting lobes) ---
// Transmission requires separate refracted-ray handling by the caller.
inline lightrt::Vec3 evalOpenPBR(const lightrt::Vec3& N, const lightrt::Vec3& V,
                                  const lightrt::Vec3& L,
                                  const OpenPBRMaterial& mat) {
  lightrt::Vec3 base = evalBRDF(N, V, L, mat);
  float coat_atten   = 1.0f - mat.coat_weight * 0.5f;
  lightrt::Vec3 coat = evalCoat(N, V, L, mat);
  lightrt::Vec3 sheen = evalSheen(N, V, L, mat);
  lightrt::Vec3 fuzz  = evalFuzz(N, V, L, mat);
  lightrt::Vec3 sss   = evalSubsurface(N, V, L, mat);
  return base * coat_atten + coat + sheen + fuzz + sss;
}

// --- ONB / hemisphere sampling ---

inline void buildONB(const lightrt::Vec3& N, lightrt::Vec3& T, lightrt::Vec3& B) {
  lightrt::Vec3 up = (std::fabs(N.y) < 0.999f)
    ? lightrt::Vec3(0.0f, 1.0f, 0.0f)
    : lightrt::Vec3(1.0f, 0.0f, 0.0f);
  T = up.cross(N).normalize();
  B = N.cross(T);
}

inline lightrt::Vec3 toWorld(const lightrt::Vec3& local,
                             const lightrt::Vec3& N,
                             const lightrt::Vec3& T,
                             const lightrt::Vec3& B) {
  return T * local.x + B * local.y + N * local.z;
}

// Cosine-weighted hemisphere sample around normal
inline lightrt::Vec3 cosineHemisphere(float u1, float u2, const lightrt::Vec3& normal) {
  lightrt::Vec3 tangent;
  if (std::fabs(normal.x) > 0.9f) {
    tangent = lightrt::Vec3(0, 1, 0).cross(normal).normalize();
  } else {
    tangent = lightrt::Vec3(1, 0, 0).cross(normal).normalize();
  }
  lightrt::Vec3 bitangent = normal.cross(tangent);

  float r = std::sqrt(u1);
  float theta = 2.0f * kPi * u2;
  float x = r * std::cos(theta);
  float y = r * std::sin(theta);
  float z = std::sqrt(std::max(0.0f, 1.0f - u1));

  return (tangent * x + bitangent * y + normal * z).normalize();
}

// --- GGX importance sampling ---

inline lightrt::Vec3 sampleGGX(float xi1, float xi2, float alpha) {
  float a2 = alpha * alpha;
  float cos_theta = std::sqrt((1.0f - xi1) / (1.0f + (a2 - 1.0f) * xi1 + 1e-7f));
  float sin_theta = std::sqrt(std::max(0.0f, 1.0f - cos_theta * cos_theta));
  float phi = 2.0f * kPi * xi2;
  return lightrt::Vec3(sin_theta * std::cos(phi), sin_theta * std::sin(phi), cos_theta);
}

inline float pdfGGX(float NdotH, float VdotH, float alpha) {
  return ggxD(NdotH, alpha) * NdotH / (4.0f * VdotH + 1e-7f);
}

// --- Environment map utilities ---

inline void buildEnvmapCDF(EnvmapData& env) {
  if (!env.valid()) return;
  int w = env.width, h = env.height;

  // Conditional CDFs (per-row)
  env.conditional_cdfs.resize(static_cast<size_t>(h) * static_cast<size_t>(w + 1));
  std::vector<float> row_sums(static_cast<size_t>(h));

  for (int y = 0; y < h; y++) {
    float sin_theta = std::sin(kPi * (y + 0.5f) / h);
    float* cdf = &env.conditional_cdfs[static_cast<size_t>(y) * static_cast<size_t>(w + 1)];
    cdf[0] = 0.0f;
    for (int x = 0; x < w; x++) {
      size_t idx = (static_cast<size_t>(y) * static_cast<size_t>(w) + static_cast<size_t>(x)) * 3;
      float lum = 0.2126f * env.pixels[idx] + 0.7152f * env.pixels[idx+1] + 0.0722f * env.pixels[idx+2];
      cdf[x + 1] = cdf[x] + lum * sin_theta;
    }
    row_sums[static_cast<size_t>(y)] = cdf[w];
    if (cdf[w] > 0.0f) {
      float inv = 1.0f / cdf[w];
      for (int x = 1; x <= w; x++) cdf[x] *= inv;
    }
  }

  // Marginal CDF
  env.marginal_cdf.resize(static_cast<size_t>(h + 1));
  env.marginal_cdf[0] = 0.0f;
  for (int y = 0; y < h; y++)
    env.marginal_cdf[static_cast<size_t>(y) + 1] = env.marginal_cdf[static_cast<size_t>(y)] + row_sums[static_cast<size_t>(y)];
  env.total_power = env.marginal_cdf[static_cast<size_t>(h)];
  if (env.total_power > 0.0f) {
    float inv = 1.0f / env.total_power;
    for (int y = 1; y <= h; y++) env.marginal_cdf[static_cast<size_t>(y)] *= inv;
  }
}

// Binary search in CDF, returns index
inline int sampleCDF(const float* cdf, int n, float xi) {
  int lo = 0, hi = n - 1;
  while (lo < hi) {
    int mid = (lo + hi) / 2;
    if (cdf[mid + 1] <= xi) lo = mid + 1;
    else hi = mid;
  }
  return lo;
}

// Importance-sample direction from envmap, returns direction and pdf
inline lightrt::Vec3 sampleEnvmap(const EnvmapData& env, float xi1, float xi2, float& pdf) {
  int h = env.height, w = env.width;

  // Sample row
  int y = sampleCDF(env.marginal_cdf.data(), h, xi1);
  float dy = (xi1 - env.marginal_cdf[static_cast<size_t>(y)]) /
             (env.marginal_cdf[static_cast<size_t>(y) + 1] - env.marginal_cdf[static_cast<size_t>(y)] + 1e-10f);

  // Sample column
  const float* row_cdf = &env.conditional_cdfs[static_cast<size_t>(y) * static_cast<size_t>(w + 1)];
  int x = sampleCDF(row_cdf, w, xi2);
  float dx = (xi2 - row_cdf[x]) / (row_cdf[x + 1] - row_cdf[x] + 1e-10f);

  // Convert to direction (lat-long)
  float u = (x + dx) / w;
  float v = (y + dy) / h;
  float theta = v * kPi;
  float phi = u * 2.0f * kPi;
  float sin_theta = std::sin(theta);

  lightrt::Vec3 dir(
    sin_theta * std::cos(phi),
    std::cos(theta),
    sin_theta * std::sin(phi));

  // PDF
  size_t idx = (static_cast<size_t>(y) * static_cast<size_t>(w) + static_cast<size_t>(x)) * 3;
  float lum = 0.2126f * env.pixels[idx] + 0.7152f * env.pixels[idx+1] + 0.0722f * env.pixels[idx+2];
  pdf = (env.total_power > 0.0f)
    ? (lum * sin_theta) / (env.total_power * 2.0f * kPi * kPi / (w * h) * sin_theta + 1e-10f)
    : 0.0f;
  // Simplifies to: lum * w * h / (total_power * 2 * pi^2)
  if (env.total_power > 0.0f) {
    pdf = lum * static_cast<float>(w * h) / (env.total_power * 2.0f * kPi * kPi + 1e-10f);
  }

  return dir;
}

// Evaluate envmap color at lat-long direction
inline lightrt::Vec3 evalEnvmap(const EnvmapData& env, const lightrt::Vec3& dir) {
  if (!env.valid()) return lightrt::Vec3(0.0f, 0.0f, 0.0f);
  float theta = std::acos(std::max(-1.0f, std::min(1.0f, dir.y)));
  float phi = std::atan2(dir.z, dir.x);
  if (phi < 0.0f) phi += 2.0f * kPi;

  float u = phi / (2.0f * kPi);
  float v = theta / kPi;

  int x = std::min(static_cast<int>(u * env.width), env.width - 1);
  int y = std::min(static_cast<int>(v * env.height), env.height - 1);
  size_t idx = (static_cast<size_t>(y) * static_cast<size_t>(env.width) + static_cast<size_t>(x)) * 3;
  return lightrt::Vec3(env.pixels[idx], env.pixels[idx+1], env.pixels[idx+2]);
}

// PDF of sampling a given direction from the envmap
inline float envmapPDF(const EnvmapData& env, const lightrt::Vec3& dir) {
  if (!env.valid() || env.total_power <= 0.0f) return 0.0f;
  float theta = std::acos(std::max(-1.0f, std::min(1.0f, dir.y)));
  float phi = std::atan2(dir.z, dir.x);
  if (phi < 0.0f) phi += 2.0f * kPi;

  float u = phi / (2.0f * kPi);
  float v = theta / kPi;

  int x = std::min(static_cast<int>(u * env.width), env.width - 1);
  int y = std::min(static_cast<int>(v * env.height), env.height - 1);
  size_t idx = (static_cast<size_t>(y) * static_cast<size_t>(env.width) + static_cast<size_t>(x)) * 3;
  float lum = 0.2126f * env.pixels[idx] + 0.7152f * env.pixels[idx+1] + 0.0722f * env.pixels[idx+2];
  return lum * static_cast<float>(env.width * env.height) /
         (env.total_power * 2.0f * kPi * kPi + 1e-10f);
}

// Balance heuristic MIS weight
inline float misBalance(float pdf_a, float pdf_b) {
  return pdf_a / (pdf_a + pdf_b + 1e-10f);
}

} // namespace shading
} // namespace lightrt_common
