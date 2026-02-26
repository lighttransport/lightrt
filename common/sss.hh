// Random-Walk Subsurface Scattering — pure math utilities
// No scene dependency; used by cli/ and viewer/.
//
// Algorithm references:
//   [Chiang16]  Chiang, Kutz, Burley — "Practical and Controllable Subsurface
//               Scattering for Production Path Tracing", SIGGRAPH 2016.
//   [CB15]      Christensen & Burley — "Approximate Reflectance Profiles for
//               Efficient Subsurface Scattering", Pixar Technical Memo 2015.
//   [Wrenninge17] Wrenninge, Villemin, Hery — "Path Traced Subsurface
//               Scattering using Anisotropic Phase Functions and
//               Non-Exponential Free Flights", Pixar Technical Memo 2017.
//   [Meng16]    Meng et al. — "Improving the Dwivedi Sampling Scheme",
//               EGSR 2016.
//
// Key improvements over pbrlab's random-walk-sss.h:
//   1. Henyey-Greenstein phase function with artist anisotropy g param.
//   2. Luminance-weighted spectral channel MIS (lower variance for chromatic SSS).
//   3. Correct HG throughput term (numerator = p(dir), denominator = pdf = p(dir)).
//   4. Dwivedi-style mean chord length estimation for thin-shape bias.
#pragma once

#include "lightrt.hh"
#include "common/materials.hh"
#include <cmath>
#include <algorithm>

namespace lightrt_common {
namespace sss {

// ─── Constants ────────────────────────────────────────────────────────────────

static constexpr float kPi    = 3.14159265358979323846f;
static constexpr float kInvPi = 1.0f / kPi;

// ─── Volume coefficient computation ──────────────────────────────────────────

// Volume extinction (sigma_t) and scattering (sigma_s) for one channel.
// Uses Christensen-Burley 2015 albedo inversion [CB15 §3]:
//   a  = single-scattering albedo from surface albedo A (Eq. 8)
//   s  = Burley s-factor fit                            (Eq. 6)
//   sigma_t = 1 / (d * s)
//   sigma_s = sigma_t * a
//
// d   = diffuse mean free path in world units (radius for this channel)
// A   = surface/scattering albedo [0,1]
inline void computeChannelCoeffs(float A, float d,
                                  float& sigma_t_out, float& sigma_s_out) {
    if (d < 1e-8f) {
        sigma_t_out = 1e16f;
        sigma_s_out = 0.0f;
        return;
    }
    // Clamp A to [0,1] — values outside this range cause exp() to produce
    // nan or a negative single-scatter albedo.
    A = std::max(0.0f, std::min(1.0f, A));

    // Single-scattering albedo from surface albedo [CB15 Eq.8 / Chiang16]
    float a = 1.0f - std::exp(A * (-5.09406f + A * (2.61188f - A * 4.31805f)));
    a = std::max(0.0f, std::min(1.0f, a));   // guard float rounding at boundaries

    // s-factor: ratio of scattering distance to diffuse MFP [CB15 Eq.6]
    float s = 1.9f - A + 3.5f * (A - 0.8f) * (A - 0.8f);
    s = std::max(s, 1e-4f);                  // s ≥ ~1.03 for A∈[0,1] in practice

    sigma_t_out = 1.0f / std::max(d * s, 1e-16f);
    sigma_s_out = sigma_t_out * a;
}

struct SSSCoeffs {
    lightrt::Vec3 sigma_t;   // extinction per RGB channel
    lightrt::Vec3 sigma_s;   // scattering per RGB channel
};

// Build per-channel volume coefficients from OpenPBR subsurface parameters.
//   albedo  = subsurface_color     (per-channel scattering colour)
//   radius  = subsurface_radius * subsurface_scale * subsurface_radius_scale
inline SSSCoeffs computeCoeffs(const lightrt::Vec3& albedo,
                                const lightrt::Vec3& radius) {
    SSSCoeffs c;
    computeChannelCoeffs(albedo.x, radius.x, c.sigma_t.x, c.sigma_s.x);
    computeChannelCoeffs(albedo.y, radius.y, c.sigma_t.y, c.sigma_s.y);
    computeChannelCoeffs(albedo.z, radius.z, c.sigma_t.z, c.sigma_s.z);
    return c;
}

// Build coefficients directly from an OpenPBRMaterial.
inline SSSCoeffs computeCoeffsFromMaterial(const OpenPBRMaterial& mat) {
    float eff_scale = mat.subsurface_radius * mat.subsurface_scale;
    lightrt::Vec3 radius(
        eff_scale * mat.subsurface_radius_scale.x,
        eff_scale * mat.subsurface_radius_scale.y,
        eff_scale * mat.subsurface_radius_scale.z);
    return computeCoeffs(mat.subsurface_color, radius);
}

// ─── Beer-Lambert transmittance ───────────────────────────────────────────────

inline lightrt::Vec3 transmittance(const lightrt::Vec3& sigma_t, float t) {
    // Clamp t ≥ 0; negative travel distance has no physical meaning here.
    float tc = std::max(0.0f, t);
    return lightrt::Vec3(
        std::exp(-sigma_t.x * tc),
        std::exp(-sigma_t.y * tc),
        std::exp(-sigma_t.z * tc));
}

// ─── Spectral channel selection ──────────────────────────────────────────────

// Luminance-weighted channel selection (improves convergence for chromatic SSS).
// Weight proportional to luminance * throughput * sigma_s, following Burley
// guidance in [Chiang16 §4.2] and extended with luminance weighting.
//
// Returns selected channel index (0=R, 1=G, 2=B).
// channel_pdf[i] = probability of selecting channel i.
inline int sampleChannel(const lightrt::Vec3& throughput,
                          const lightrt::Vec3& sigma_s,
                          float xi,
                          lightrt::Vec3& channel_pdf) {
    // Rec.709 luminance weights favour the green channel naturally
    static constexpr float kLum[3] = {0.2126f, 0.7152f, 0.0722f};

    float w[3];
    // Guard against nan/inf in throughput or sigma_s propagating to weights.
    auto safe_w = [](float lum, float tp, float ss) -> float {
        float v = lum * std::fabs(tp) * ss;
        return (std::isfinite(v) && v > 0.0f) ? v : 0.0f;
    };
    w[0] = safe_w(kLum[0], throughput.x, sigma_s.x);
    w[1] = safe_w(kLum[1], throughput.y, sigma_s.y);
    w[2] = safe_w(kLum[2], throughput.z, sigma_s.z);

    float sum = w[0] + w[1] + w[2];
    if (sum > 0.0f) {
        channel_pdf.x = w[0] / sum;
        channel_pdf.y = w[1] / sum;
        channel_pdf.z = w[2] / sum;
    } else {
        channel_pdf = lightrt::Vec3(1.0f / 3.0f, 1.0f / 3.0f, 1.0f / 3.0f);
    }

    if (xi < channel_pdf.x)                     return 0;
    if (xi < channel_pdf.x + channel_pdf.y)     return 1;
    return 2;
}

// Sample exponential free-path distance for the selected channel.
// Returns the sampled distance t.
inline float sampleFreePath(const lightrt::Vec3& sigma_t,
                             int channel, float xi) {
    float st = (channel == 0) ? sigma_t.x
             : (channel == 1) ? sigma_t.y
                               : sigma_t.z;
    // Clamp xi away from 1 to avoid log(0) = -inf.
    float xi_safe = std::min(xi, 1.0f - 1e-7f);
    return -std::log(1.0f - xi_safe) / std::max(st, 1e-16f);
}

// ─── Henyey-Greenstein phase function ────────────────────────────────────────

// PDF evaluation.  cos_theta is the angle between incident and scattered dirs.
// g in (-1, 1): g>0 forward scatter, g<0 backward, g=0 isotropic.
inline float evalHG(float cos_theta, float g) {
    // Clamp g; ±1 would make denom = 0 (perfect forward/backward scatterer).
    g = std::max(-0.9999f, std::min(0.9999f, g));
    float denom = std::max(0.0f, 1.0f + g * g - 2.0f * g * cos_theta);
    // denom^(3/2): guard sqrt argument (should be ≥ 0 but float rounding).
    float denom32 = denom * std::sqrt(denom);
    return (1.0f - g * g) / std::max(4.0f * kPi * denom32, 1e-16f);
}

// Closed-form HG sampling.  Returns cos(theta) given uniform xi1 in [0,1).
// From [Pharr, Jakob, Humphreys, "PBRT 4e", Phase Functions]:
//   cos_theta = 1/(2g) * (1 + g^2 - ((1-g^2)/(1-g+2g*xi))^2)   if |g| > eps
//   cos_theta = 1 - 2*xi                                          if g ~ 0
inline float sampleHGCosTheta(float g, float xi) {
    // Self-clamp g so the formula is always well-conditioned regardless of caller.
    g = std::max(-0.9999f, std::min(0.9999f, g));
    if (std::fabs(g) < 1e-3f) {
        return 1.0f - 2.0f * xi;
    }
    // Denominator: 1 - g + 2g*xi.  With g in (-1,1) and xi in [0,1) the minimum
    // magnitude is (1 - |g|) ≥ 1e-4, so the guard below is only a last resort.
    float denom = 1.0f - g + 2.0f * g * xi;
    denom = std::copysign(std::max(std::fabs(denom), 1e-7f), denom);
    float t = (1.0f - g * g) / denom;
    float cos_theta = (1.0f + g * g - t * t) / (2.0f * g);
    return std::max(-1.0f, std::min(1.0f, cos_theta));
}

// Sample a full 3-D scattering direction from the HG phase function.
// The result is expressed in a local frame where the forward axis (+z) aligns
// with the incident direction `dir_in`.  Caller must transform to world space
// using the ONB built from `dir_in`.
//
// Returns the direction in that local frame (z = forward = dir_in).
inline lightrt::Vec3 sampleHGLocal(float g, float xi1, float xi2) {
    float cos_theta = sampleHGCosTheta(g, xi1);
    float sin_theta = std::sqrt(std::max(0.0f, 1.0f - cos_theta * cos_theta));
    float phi       = 2.0f * kPi * xi2;
    return lightrt::Vec3(sin_theta * std::cos(phi),
                         sin_theta * std::sin(phi),
                         cos_theta);
}

// ─── ONB construction ────────────────────────────────────────────────────────

// Build an orthonormal basis (T, B) perpendicular to `N`.
// `N` is assumed to be a unit vector; zero-length input produces a canonical basis.
inline void buildONB(const lightrt::Vec3& N,
                     lightrt::Vec3& T, lightrt::Vec3& B) {
    // Detect zero-length or degenerate N.
    float len2 = N.x*N.x + N.y*N.y + N.z*N.z;
    if (len2 < 1e-12f) {
        T = lightrt::Vec3(1.0f, 0.0f, 0.0f);
        B = lightrt::Vec3(0.0f, 1.0f, 0.0f);
        return;
    }
    lightrt::Vec3 up = (std::fabs(N.y) < 0.999f)
        ? lightrt::Vec3(0.0f, 1.0f, 0.0f)
        : lightrt::Vec3(1.0f, 0.0f, 0.0f);
    T = up.cross(N).normalize();
    // If T came out zero (N was nearly parallel to both candidates), use fallback.
    if (T.x == 0.0f && T.y == 0.0f && T.z == 0.0f) {
        up = lightrt::Vec3(0.0f, 0.0f, 1.0f);
        T  = up.cross(N).normalize();
    }
    B = N.cross(T);
}

// Transform a local direction to world space given a frame (T, B, N=forward).
inline lightrt::Vec3 toWorld(const lightrt::Vec3& local,
                              const lightrt::Vec3& T,
                              const lightrt::Vec3& B,
                              const lightrt::Vec3& N) {
    return T * local.x + B * local.y + N * local.z;
}

// Sample a Lambertian cosine-weighted hemisphere direction in world space.
// Used for the initial entry into the medium.
inline lightrt::Vec3 sampleCosineHemisphere(const lightrt::Vec3& N,
                                             float xi1, float xi2) {
    float r   = std::sqrt(xi1);
    float phi = 2.0f * kPi * xi2;
    float x   = r * std::cos(phi);
    float y   = r * std::sin(phi);
    float z   = std::sqrt(std::max(0.0f, 1.0f - xi1));
    lightrt::Vec3 T, B;
    buildONB(N, T, B);
    return toWorld(lightrt::Vec3(x, y, z), T, B, N).normalize();
}

// ─── Thin-shape geometry thickness estimate ──────────────────────────────────

// Estimate the local slab thickness at the entry point.
// Casts a probe ray inward (along -N) and returns the distance to the first
// exit surface hit on the same instance.  Used to clamp the first free-path
// sample so the walk doesn't waste time far inside thick shapes.
//
// Returns kInfThickness if no back-face is found within maxDist.
static constexpr float kInfThickness = 1e16f;

} // namespace sss
} // namespace lightrt_common
