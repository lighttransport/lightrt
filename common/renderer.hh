// Shared CPU renderer for CLI and viewer.
#pragma once

#include "common/scene.hh"
#include "lightrt.hh"

#include <cstdint>
#include <vector>

namespace lightrt_common {

struct RenderSettings {
  uint32_t width = 800;
  uint32_t height = 600;
  uint32_t spp = 1;
  uint32_t mblur_samples = 1;
};

struct CameraView {
  lightrt::Vec3 position;
  lightrt::Vec3 direction;
  lightrt::Vec3 right;
  lightrt::Vec3 up;
  float half_width = 1.0f;
  float half_height = 1.0f;
};

void renderFrame(const scene::Scene& scene,
                 const RenderSettings& settings,
                 const CameraView& camera,
                 std::vector<lightrt::RGB8>& image);

} // namespace lightrt_common
