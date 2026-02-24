#pragma once

#include <string>

namespace softrt {

// Normalizes WGSL text for current Clair limitations.
// In particular, pipeline-overridable globals (`override`) are rewritten
// to concrete `const` declarations with default initializers.
std::string normalizeWGSLForClair(const std::string& source);

}  // namespace softrt

