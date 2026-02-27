// Material, light, and environment map data structures
// Extracted from cli/scene.hh for shared use
#pragma once

#include "lightrt.hh"
#include <vector>

namespace lightrt_common {

struct OpenPBRMaterial {
  // --- Base ---
  float          base_weight           = 1.0f;
  lightrt::Vec3  base_color            = {0.8f, 0.8f, 0.8f};
  float          base_roughness        = 0.0f;
  float          base_metalness        = 0.0f;
  float          base_diffuse_roughness= 0.0f;

  // --- Specular ---
  float          specular_weight       = 1.0f;
  lightrt::Vec3  specular_color        = {1.0f, 1.0f, 1.0f};
  float          specular_roughness    = 0.3f;
  float          specular_ior          = 1.5f;
  float          specular_ior_level    = 0.5f;
  float          specular_anisotropy   = 0.0f;
  float          specular_rotation     = 0.0f;

  // --- Transmission ---
  float          transmission_weight   = 0.0f;
  lightrt::Vec3  transmission_color    = {1.0f, 1.0f, 1.0f};
  float          transmission_depth    = 0.0f;
  lightrt::Vec3  transmission_scatter  = {0.0f, 0.0f, 0.0f};
  float          transmission_scatter_anisotropy = 0.0f;
  float          transmission_dispersion = 0.0f;

  // --- Subsurface ---
  float          subsurface_weight     = 0.0f;
  lightrt::Vec3  subsurface_color      = {0.8f, 0.8f, 0.8f};
  float          subsurface_radius     = 1.0f;
  lightrt::Vec3  subsurface_radius_scale = {1.0f, 1.0f, 1.0f};
  float          subsurface_scale      = 1.0f;
  float          subsurface_anisotropy = 0.0f;

  // --- Sheen ---
  float          sheen_weight          = 0.0f;
  lightrt::Vec3  sheen_color           = {1.0f, 1.0f, 1.0f};
  float          sheen_roughness       = 0.3f;

  // --- Fuzz ---
  float          fuzz_weight           = 0.0f;
  lightrt::Vec3  fuzz_color            = {1.0f, 1.0f, 1.0f};
  float          fuzz_roughness        = 0.5f;

  // --- Thin Film ---
  float          thin_film_weight      = 0.0f;
  float          thin_film_thickness   = 0.5f;
  float          thin_film_ior         = 1.5f;

  // --- Coat ---
  float          coat_weight           = 0.0f;
  lightrt::Vec3  coat_color            = {1.0f, 1.0f, 1.0f};
  float          coat_roughness        = 0.1f;
  float          coat_anisotropy       = 0.0f;
  float          coat_rotation         = 0.0f;
  float          coat_ior              = 1.6f;
  lightrt::Vec3  coat_affect_color     = {0.0f, 0.0f, 0.0f};
  float          coat_affect_roughness = 0.0f;

  // --- Emission ---
  float          emission_luminance    = 0.0f;
  lightrt::Vec3  emission_color        = {1.0f, 1.0f, 1.0f};

  // --- Geometry ---
  float          opacity               = 1.0f;

  // --- Texture image indices (-1 = none) ---
  int32_t        base_color_tex_id     = -1;
  int32_t        metalness_tex_id      = -1;
  int32_t        roughness_tex_id      = -1;
  int32_t        normal_tex_id         = -1;
  int32_t        emissive_tex_id       = -1;
  int32_t        opacity_tex_id        = -1;
};

// Backward-compatibility alias.
// Note: old fields .metalness, .roughness, .ior no longer exist.
// Use .base_metalness, .specular_roughness, .specular_ior instead.
using MaterialData = OpenPBRMaterial;

struct LightData {
  enum Type { Distant, Point, Dome, Rect };
  Type type = Distant;
  lightrt::Vec3 color{1.0f, 1.0f, 1.0f}; // pre-multiplied intensity * 2^exposure
  lightrt::Vec3 direction{0.0f, -1.0f, 0.0f}; // Distant: toward-light; Rect: outward normal
  lightrt::Vec3 position{0.0f, 0.0f, 0.0f};
  // Rect-light specific
  lightrt::Vec3 rect_axis_u{1.0f, 0.0f, 0.0f}; // local +X (half-width direction)
  lightrt::Vec3 rect_axis_v{0.0f, 1.0f, 0.0f}; // local +Y (half-height direction)
  float rect_half_width  = 0.5f;
  float rect_half_height = 0.5f;
};

struct EnvmapData {
  std::vector<float> pixels; // RGB float
  int width = 0;
  int height = 0;
  std::vector<float> marginal_cdf;     // height+1: CDF over rows
  std::vector<float> conditional_cdfs; // height * (width+1): per-row CDF over cols
  float total_power = 0.0f;
  bool valid() const { return width > 0 && height > 0 && !pixels.empty(); }
};

} // namespace lightrt_common
