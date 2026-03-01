// AOV (Arbitrary Output Variable) rendering support for LightRT

#ifndef AOV_RENDERING_HH
#define AOV_RENDERING_HH

#include "lightrt.hh"
#include <vector>
#include <string>

// AOV rendering options
struct AOVRenderOptions {
  bool beauty = true;           // Standard color output
  bool geom_normal = false;     // Geometry normals (pre-transformation)
  bool shading_normal = false;  // Normals after transformation (for curved surfaces)
  bool vertex_color = false;    // Vertex displayColor from USD
  bool vertex_opacity = false;  // Vertex displayOpacity from USD
  bool depth = false;           // Distance to hit point
  bool material_id = false;     // Per-triangle material ID
  
  // Parse AOV outputs from comma-separated string
  void parse(const std::string& outputs) {
    std::string temp = outputs;
    std::string part;
    
    size_t start = 0;
    while ((start = temp.find_first_of(',', start)) != std::string::npos) {
      part = temp.substr(start, temp.find(',', start) - start);
      part.erase(0, part.find_first_not_of(" \t"));
      part.erase(part.find_last_not_of(" \t") + 1);
      
      if (part == "beauty") {
        beauty = true;
        geom_normal = false;
        shading_normal = false;
        vertex_color = false;
        vertex_opacity = false;
        depth = false;
        material_id = false;
      }
      else if (part == "geom_normal") geom_normal = true;
      else if (part == "shading_normal") shading_normal = true;
      else if (part == "vertex_color") vertex_color = true;
      else if (part == "vertex_opacity") vertex_opacity = true;
      else if (part == "depth") depth = true;
      else if (part == "material_id") material_id = true;
      else fprintf(stderr, "Unknown AOV output: %s\n", part.c_str());
    }
  }
};

// AOV rendering result for single pixel
struct AOVResult {
  lightrt::Vec3 beauty;           // Final color
  lightrt::Vec3 geom_normal;      // Geometry normal
  lightrt::Vec3 shading_normal;  // Shading normal
  lightrt::Vec3 vertex_color;    // Vertex color
  float vertex_opacity;            // Vertex opacity
  float depth;                     // Distance to hit
  int32_t material_id;             // Material ID
  float hit_t;                      // Hit distance
  float hit_u, hit_v;              // Hit UV coordinates
};

// Render a single ray and collect AOV data
AOVResult renderRayWithAOV(
    const lightrt::BVHType& bvh,
    const lightrt::Ray& ray,
    const AOVRenderOptions& opts);

#endif // AOV_RENDERING_HH

