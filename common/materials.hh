// Material, light, and environment map data structures
// Extracted from cli/scene.hh for shared use
#pragma once

#include "lightrt.hh"
#include <vector>

namespace lightrt_common {

struct MaterialData {
  lightrt::Vec3 base_color{0.5f, 0.5f, 0.5f};
  float metalness = 0.0f;
  float roughness = 0.5f;
  lightrt::Vec3 specular_color{1.0f, 1.0f, 1.0f};
  float ior = 1.5f;
  lightrt::Vec3 emission_color{0.0f, 0.0f, 0.0f};
  float emission_luminance = 0.0f;
  float opacity = 1.0f;
};

struct LightData {
  enum Type { Distant, Point, Dome };
  Type type = Distant;
  lightrt::Vec3 color{1.0f, 1.0f, 1.0f}; // pre-multiplied intensity * 2^exposure
  lightrt::Vec3 direction{0.0f, -1.0f, 0.0f};
  lightrt::Vec3 position{0.0f, 0.0f, 0.0f};
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
