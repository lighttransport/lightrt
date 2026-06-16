// Marschner-style hair BSDF — R/TT/TRT lobes with longitudinal + azimuthal scattering.
// References:
//   [Marschner03] Marschner et al. "Light Scattering from Human Hair Fibers", SIGGRAPH 2003
//   [Chiang16]    Chiang et al. "A Practical and Controllable Hair BSDF", SIGGRAPH 2016
//   [d'Eon11]     d'Eon et al. "An Energy-Conserving Hair Reflectance Model", EG 2011
#pragma once

#include "lightrt.hh"
#include "common/materials.hh"
#include <cmath>
#include <algorithm>

namespace lightrt_common {
namespace hair {

static constexpr float kPi = 3.14159265358979323846f;
static constexpr float kInvPi = 1.0f / kPi;

// ---------------------------------------------------------------------------
// Hair material parameters extracted from OpenPBRMaterial.
// ---------------------------------------------------------------------------
struct HairParams {
  float roughness_longitudinal;  // Gaussian sigma along fiber
  float roughness_azimuthal;     // Gaussian sigma around fiber
  float ior;                     // fiber IOR (~1.55 for hair)
  float cuticle_angle;           // cuticle tilt in degrees (~3° for human hair)
  lightrt::Vec3 absorption;      // per-channel Beer absorption
  lightrt::Vec3 color;           // base hair color (for diffuse fallback)

  static HairParams fromMaterial(const MaterialData& mat) {
    HairParams p;
    p.roughness_longitudinal = mat.hair_roughness_longitudinal;
    p.roughness_azimuthal    = mat.hair_roughness_azimuthal;
    p.ior                    = mat.hair_ior;
    p.cuticle_angle          = mat.hair_cuticle_angle;
    p.absorption             = mat.hair_absorption;
    p.color                  = mat.hair_color;
    return p;
  }
};

// ---------------------------------------------------------------------------
// Angle utilities — convert between unit vectors and the Marschner angular
// parameterization (theta = angle from fiber tangent plane, phi = azimuth).
// ---------------------------------------------------------------------------

// Compute incident/outgoing theta and phi given the fiber tangent T and
// the shading normal N (N . T = 0, outward-facing).
// Returns (theta, phi) in radians.
inline void computeAngles(const lightrt::Vec3& T,   // fiber tangent
                          const lightrt::Vec3& N,   // fiber normal (perp to T)
                          const lightrt::Vec3& V,   // view direction (toward camera)
                          float& theta, float& phi) {
  // Project V onto the fiber plane (T, B) where B = N.cross(T)
  lightrt::Vec3 B = T.cross(N).normalize();
  float vT = V.dot(T);
  float vN = V.dot(N);
  float vB = V.dot(B);
  // Theta: angle from the plane perpendicular to T
  // sin(theta) = projection onto T
  float len = std::sqrt(vN*vN + vB*vB);
  theta = std::atan2(vT, len);
  // Phi: azimuth in the (N,B) plane
  phi = std::atan2(vB, vN);
}

// ---------------------------------------------------------------------------
// Longitudinal scattering — Gaussian in theta.
// ---------------------------------------------------------------------------

// Normalized Gaussian with mean mu and standard deviation sigma.
inline float gaussian(float x, float mu, float sigma) {
  float d = (x - mu) / sigma;
  return std::exp(-0.5f * d * d) / (sigma * std::sqrt(2.0f * kPi));
}

// Longitudinal scattering function M_lobe(theta) — centered Gaussian.
inline float longitudinal(float theta, float roughness) {
  float sigma = std::max(roughness, 0.001f);
  return gaussian(theta, 0.0f, sigma);
}

// Sample longitudinal scattering direction.
// Returns sampled theta_delta (deviation from perfect specular).
inline float sampleLongitudinal(float roughness, float xi1, float xi2) {
  float sigma = std::max(roughness, 0.001f);
  // Box-Muller for Gaussian
  float r = std::sqrt(-2.0f * std::log(std::max(1e-7f, xi1)));
  float theta = r * std::cos(2.0f * kPi * xi2) * sigma;
  return theta;
}

// PDF of longitudinal scattering.
inline float longitudinalPDF(float theta, float roughness) {
  return longitudinal(theta, roughness);
}

// ---------------------------------------------------------------------------
// Azimuthal scattering — elliptical Gaussian in phi.
// Each lobe (R/TT/TRT) has a different center (phi_half) and width.
// ---------------------------------------------------------------------------

// Azimuthal scattering: Gaussian around phi_half with given width.
inline float azimuthal(float phi, float phi_half, float roughness) {
  float sigma = std::max(roughness, 0.001f);
  return gaussian(phi, phi_half, sigma);
}

// Sample azimuthal scattering.
inline float sampleAzimuthal(float phi_half, float roughness, float xi1, float xi2) {
  float sigma = std::max(roughness, 0.001f);
  // Box-Muller Gaussian
  float r = std::sqrt(-2.0f * std::log(std::max(1e-7f, xi1)));
  float phi = phi_half + r * std::cos(2.0f * kPi * xi2) * sigma;
  // Wrap to [-pi, pi]
  while (phi > kPi) phi -= 2.0f * kPi;
  while (phi < -kPi) phi += 2.0f * kPi;
  return phi;
}

// ---------------------------------------------------------------------------
// Fresnel for hair: use Schlick approximation with the given IOR.
// Returns reflectivity for unpolarized light at angle cos_theta.
// ---------------------------------------------------------------------------
inline float fresnelReflectance(float cos_theta, float ior) {
  // Schlick approximation
  float r0 = (ior - 1.0f) / (ior + 1.0f);
  r0 = r0 * r0;
  return r0 + (1.0f - r0) * std::pow(std::max(0.0f, 1.0f - cos_theta), 5.0f);
}

// ---------------------------------------------------------------------------
// Absorption through fiber: Beer-Lambert.
// chord_length depends on lobe and azimuthal angle.
// ---------------------------------------------------------------------------
inline lightrt::Vec3 beerAbsorption(const lightrt::Vec3& sigma_a, float distance) {
  return lightrt::Vec3(
    std::exp(-sigma_a.x * distance),
    std::exp(-sigma_a.y * distance),
    std::exp(-sigma_a.z * distance));
}

// Approximate chord length through a cylindrical fiber for a given lobe
// and azimuthal angle phi (in radians from the lobe center).
inline float chordLength(int lobe, float cos_gamma) {
  // R: external reflection, no transmission — chord = 0
  // TT: refracts through, chord proportional to cos(gamma)
  // TRT: reflects internally, longer chord
  // gamma = asin(sin(phi) / ior) internally
  float c = std::max(0.0f, cos_gamma);
  if (lobe == 0) return 0.0f;           // R
  if (lobe == 1) return 2.0f * c;       // TT
  return 4.0f * c;                       // TRT
}

// ---------------------------------------------------------------------------
// Lobe probability for importance sampling.
// Based on roughness — smooth hair has stronger R, rough hair diffuses.
// ---------------------------------------------------------------------------
inline float lobeProbability(int lobe, float roughness) {
  // Roughness-dependent lobe probabilities
  float r = std::max(roughness, 0.01f);
  if (lobe == 0) return 0.5f - 0.2f * r;      // R
  if (lobe == 1) return 0.3f + 0.1f * r;      // TT
  return 0.2f + 0.1f * r;                       // TRT
}

// ---------------------------------------------------------------------------
// Hair BSDF evaluation.
//
// Given the fiber shading frame (T = tangent, N = fiber normal orthogonal to T),
// incident direction Wi (toward light), and outgoing direction Wo (toward camera),
// evaluate the hair BSDF contribution.
//
// Returns the BSDF value (spectral).
// ---------------------------------------------------------------------------
inline lightrt::Vec3 evalHair(const HairParams& params,
                               const lightrt::Vec3& T,   // fiber tangent
                               const lightrt::Vec3& N,   // fiber normal (perpendicular to T)
                               const lightrt::Vec3& Wi,  // incident (toward light)
                               const lightrt::Vec3& Wo)  // outgoing (toward camera)
{
  // Compute angular parameterization
  float theta_i, phi_i, theta_o, phi_o;
  computeAngles(T, N, Wi, theta_i, phi_i);
  computeAngles(T, N, Wo, theta_o, phi_o);

  float theta_h = (theta_o + theta_i) * 0.5f;  // half-angle longitude
  float phi_diff = phi_o - phi_i;               // azimuthal difference

  // Lobe centers (azimuthal offset)
  float gamma = params.cuticle_angle * kPi / 180.0f;
  float phi_centers[3] = {0.0f, kPi, 2.0f * gamma};
  // Longitudinal shift
  float theta_shift[3] = {0.0f, 0.0f, gamma * 0.5f};

  lightrt::Vec3 result(0.0f, 0.0f, 0.0f);

  for (int lobe = 0; lobe < 3; lobe++) {
    // Longitudinal scattering
    float theta_mu = theta_h - theta_shift[lobe];
    float long_val = longitudinal(theta_o - theta_mu, params.roughness_longitudinal);

    // Azimuthal scattering
    float azim_val = azimuthal(phi_diff - phi_centers[lobe], 0.0f, params.roughness_azimuthal);

    // Fresnel at the fiber surface
    float cos_theta_d = std::cos(theta_h);
    float F = fresnelReflectance(cos_theta_d, params.ior);

    // Geometric term
    float geom = 1.0f / (4.0f * std::abs(std::cos(theta_h) * std::cos(theta_h)));

    // Absorption (beer's law through fiber)
    float cos_gamma = std::cos(phi_diff * 0.5f);
    float chord = chordLength(lobe, cos_gamma);
    float r_fiber = 1.0f;  // unit radius, scale handled by geometry
    lightrt::Vec3 beer = beerAbsorption(params.absorption, chord * r_fiber);

    // Lobe contribution
    float lobe_contrib = (lobe == 0) ? F             // R: Fresnel reflection
                       : (lobe == 1) ? (1.0f - F) * (1.0f - F)  // TT: transmit in, transmit out
                       :               (1.0f - F) * F * (1.0f - F);  // TRT: T-R-T

    lightrt::Vec3 contrib(
      lobe_contrib * long_val * azim_val * geom * beer.x,
      lobe_contrib * long_val * azim_val * geom * beer.y,
      lobe_contrib * long_val * azim_val * geom * beer.z);

    // Clamp to avoid fireflies
    contrib.x = std::min(contrib.x, 100.0f);
    contrib.y = std::min(contrib.y, 100.0f);
    contrib.z = std::min(contrib.z, 100.0f);

    result.x += contrib.x;
    result.y += contrib.y;
    result.z += contrib.z;
  }

  return result;
}

// ---------------------------------------------------------------------------
// Hair BSDF sampling.
// Returns the sampled direction, PDF, and the BSDF value at that direction.
// ---------------------------------------------------------------------------
inline lightrt::Vec3 sampleHair(const HairParams& params,
                                 const lightrt::Vec3& T,
                                 const lightrt::Vec3& N,
                                 const lightrt::Vec3& Wo,
                                 float xi1, float xi2, float xi3,
                                 float& pdf, lightrt::Vec3& bsdf_val) {
  // First, compute theta_o and phi_o from Wo
  float theta_o, phi_o;
  computeAngles(T, N, Wo, theta_o, phi_o);

  float gamma = params.cuticle_angle * kPi / 180.0f;
  float phi_centers[3] = {0.0f, kPi, 2.0f * gamma};
  float theta_shift[3] = {0.0f, 0.0f, gamma * 0.5f};
  float probs[3];
  float psum = 0.0f;
  float r = std::max(params.roughness_longitudinal, 0.01f);
  for (int l = 0; l < 3; l++) {
    probs[l] = lobeProbability(l, r);
    psum += probs[l];
  }
  float inv_psum = 1.0f / psum;
  for (int l = 0; l < 3; l++) probs[l] *= inv_psum;

  // Sample lobe
  int lobe = 0;
  float xi = xi3;
  for (int l = 0; l < 3; l++) {
    if (xi < probs[l]) { lobe = l; break; }
    xi -= probs[l];
  }

  // Sample longitudinal deviation
  float theta_delta = sampleLongitudinal(params.roughness_longitudinal, xi1, xi2);
  float theta_i = 2.0f * theta_o - 2.0f * theta_shift[lobe] - theta_delta;
  // Actually, sample from the lobe center:
  // Wi is sampled such that theta_h = (theta_o + theta_i)/2 is the lobe center
  // So theta_i = 2 * (lobe_center + shift) - theta_o + noise
  float theta_h_center = theta_shift[lobe];
  float theta_i_sampled = 2.0f * theta_h_center - theta_o + theta_delta;

  // Sample azimuthal deviation (use xi2 as second uniform for Box-Muller)
  float phi_diff = sampleAzimuthal(phi_centers[lobe], params.roughness_azimuthal, xi1, xi2);
  float phi_i_sampled = phi_o - phi_diff;

  // Reconstruct Wi direction
  lightrt::Vec3 B = T.cross(N).normalize();
  float cos_theta = std::cos(theta_i_sampled);
  float sin_theta = std::sin(theta_i_sampled);
  float cos_phi = std::cos(phi_i_sampled);
  float sin_phi = std::sin(phi_i_sampled);
  lightrt::Vec3 Wi = T * sin_theta + N * (cos_theta * cos_phi) + B * (cos_theta * sin_phi);
  Wi = Wi.normalize();

  // Evaluate BSDF at sampled direction
  bsdf_val = evalHair(params, T, N, Wi, Wo);

  // Compute PDF: sum over lobes of p(lobe) * p(theta|lobe) * p(phi|lobe) / |J|
  // Jacobian from (theta,phi) to solid angle = 1/cos(theta_i)
  float pdf_theta = longitudinalPDF(theta_delta, params.roughness_longitudinal);
  float pdf_phi = azimuthal(phi_diff, phi_centers[lobe], params.roughness_azimuthal);
  float jacobian = 1.0f / std::max(std::abs(std::cos(theta_i_sampled)), 1e-7f);
  pdf = probs[lobe] * pdf_theta * pdf_phi * jacobian;

  return Wi;
}

// ---------------------------------------------------------------------------
// Simple diffuse fallback (for non-hair shading)
// ---------------------------------------------------------------------------
inline lightrt::Vec3 evalDiffuse(const lightrt::Vec3& albedo,
                                  const lightrt::Vec3& N,
                                  const lightrt::Vec3& L) {
  float NdotL = std::max(0.0f, N.dot(L));
  return albedo * (NdotL * kInvPi);
}

} // namespace hair
} // namespace lightrt_common
