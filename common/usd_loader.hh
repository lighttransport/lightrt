// Shared USD scene loader for CLI and viewer.
#pragma once

#include "common/scene.hh"

#include <string>

namespace lightrt_common {

bool loadUSDScene(const std::string& filename,
                  double timecode,
                  scene::Scene& out_scene);

// Add supported geometry/transform endpoint samples at frame time plus the
// selected camera's authored shutter offsets.
void applyMotionBlur(const std::string& filename,
                     double timecode,
                     double shutter_open_offset,
                     double shutter_close_offset,
                     scene::Scene& scene);

} // namespace lightrt_common
