// Standalone hair BSDF validation program.
// Generates procedural hair curves with configurable hair material,
// renders with the shared renderFrame() function.
//
// Usage:
//   lightrt_hair_test --output out.ppm [options]
//
// Options:
//   --num-strands N        Number of hair curves (default 50)
//   --hair-roughness F     Longitudinal roughness (default 0.3)
//   --hair-azimuth-rough F Azimuthal roughness (default 0.3)
//   --hair-ior F           Fiber IOR (default 1.55)
//   --hair-cuticle F       Cuticle angle in degrees (default 3.0)
//   --hair-color R G B     Base hair color (default 0.6 0.3 0.1)
//   --hair-absorption R G B  Per-channel absorption (default 0.2 0.5 0.8)
//   --hair-weight F        Hair BSDF weight (default 1.0)
//   --width W --height H   Resolution
//   --spp N                Samples per pixel
//   --output FILE          Output image path
//   --reference            Also output diffuse-only reference image

#include "common/renderer.hh"
#include "common/scene.hh"
#include "common/materials.hh"
#include "lightrt.hh"

#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

using namespace lightrt;
using namespace lightrt_common;

// ---------------------------------------------------------------------------
// Simple PPM writer (no external dependencies)
// ---------------------------------------------------------------------------
static bool writePPM(const char* filename, int w, int h,
                     const std::vector<lightrt::RGB8>& pixels) {
  FILE* f = std::fopen(filename, "wb");
  if (!f) return false;
  std::fprintf(f, "P6\n%d %d\n255\n", w, h);
  for (int y = 0; y < h; ++y)
    for (int x = 0; x < w; ++x) {
      const auto& p = pixels[y * w + x];
      std::fputc((int)p.r, f);
      std::fputc((int)p.g, f);
      std::fputc((int)p.b, f);
    }
  std::fclose(f);
  return true;
}

// ---------------------------------------------------------------------------
// Procedural hair strand generation
// ---------------------------------------------------------------------------
static void generateHairStrand(float root_x, float root_z,
                               float length, float radius,
                               int segments,
                               CurveType type,
                               std::vector<Curve>& curves) {
  std::vector<Vec3> points;
  std::vector<float> radii;
  float r = radius;
  float bend = 0.2f;
  for (int i = 0; i <= segments; i++) {
    float t = (float)i / (float)segments;
    float y = t * length;
    float x = root_x + std::sin(t * 3.14159f * 0.5f) * bend * (root_x * 0.3f);
    float z = root_z + std::cos(t * 3.14159f * 0.5f) * bend * (root_z * 0.3f);
    points.push_back(Vec3(x, y, z));
    radii.push_back(r * (1.0f - t * 0.5f)); // taper toward tip
  }
  curves.emplace_back(points, radii, type);
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
static int addMaterial(scene::Scene& sc, const scene::MaterialData& mat) {
  int id = (int)sc.materials.size();
  sc.materials.push_back(mat);
  return id;
}

static int addCurveMesh(scene::Scene& sc, std::vector<Curve> curves,
                        int material_id) {
  int mesh_id = (int)sc.curve_meshes.size();
  sc.curve_meshes.emplace_back();
  auto& cb = sc.curve_meshes.back();
  cb.default_material_id = material_id;
  cb.build(curves);
  return mesh_id;
}

static int addInstance(scene::Scene& sc, int curve_mesh_id,
                        const Vec3& translate = Vec3(0,0,0)) {
  int inst_id = (int)sc.instances.size();
  sc.instances.emplace_back();
  auto& inst = sc.instances.back();
  inst.mesh_id = kInvalidIndex;
  inst.curve_mesh_id = (uint32_t)curve_mesh_id;

  float m[12] = {1,0,0,translate.x, 0,1,0,translate.y, 0,0,1,translate.z};
  std::memcpy(inst.transform, m, sizeof(m));
  std::memcpy(inst.inv_transform, m, sizeof(m));
  std::memcpy(inst.transform_close, m, sizeof(m));
  std::memcpy(inst.inv_transform_close, m, sizeof(m));
  inst.inv_transform[3] = -translate.x;
  inst.inv_transform[7] = -translate.y;
  inst.inv_transform[11] = -translate.z;

  inst.world_bounds = sc.curve_meshes[(size_t)curve_mesh_id].local_bounds;
  sc.scene_bounds.expand(inst.world_bounds);
  return inst_id;
}

static int addSphereLight(scene::Scene& sc, const Vec3& pos,
                           const Vec3& color, float intensity, float radius) {
  int id = (int)sc.lights.size();
  scene::LightData l;
  l.type = scene::LightData::Sphere;
  l.position = pos;
  l.color = color * intensity;
  l.radius = radius;
  sc.lights.push_back(l);
  return id;
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------
int main(int argc, char* argv[]) {
  // Defaults
  scene::MaterialData mat;
  mat.hair_roughness_longitudinal = 0.3f;
  mat.hair_roughness_azimuthal = 0.3f;
  mat.hair_ior = 1.55f;
  mat.hair_cuticle_angle = 3.0f;
  mat.hair_color = Vec3(0.6f, 0.3f, 0.1f);
  mat.hair_absorption = Vec3(0.2f, 0.5f, 0.8f);
  mat.hair_weight = 1.0f;
  mat.base_color = Vec3(0.6f, 0.3f, 0.1f);

  int num_strands = 50;
  RenderSettings settings;
  settings.width = 512;
  settings.height = 384;
  settings.spp = 64;
  std::string output_file = "hair_output.ppm";
  bool save_reference = false;

  // Parse command line
  for (int i = 1; i < argc; ++i) {
    if (!std::strcmp(argv[i], "--num-strands") && i + 1 < argc)
      num_strands = std::atoi(argv[++i]);
    else if (!std::strcmp(argv[i], "--hair-roughness") && i + 1 < argc)
      mat.hair_roughness_longitudinal = (float)std::atof(argv[++i]);
    else if (!std::strcmp(argv[i], "--hair-azimuth-rough") && i + 1 < argc)
      mat.hair_roughness_azimuthal = (float)std::atof(argv[++i]);
    else if (!std::strcmp(argv[i], "--hair-ior") && i + 1 < argc)
      mat.hair_ior = (float)std::atof(argv[++i]);
    else if (!std::strcmp(argv[i], "--hair-cuticle") && i + 1 < argc)
      mat.hair_cuticle_angle = (float)std::atof(argv[++i]);
    else if (!std::strcmp(argv[i], "--hair-color") && i + 3 < argc) {
      mat.hair_color.x = (float)std::atof(argv[++i]);
      mat.hair_color.y = (float)std::atof(argv[++i]);
      mat.hair_color.z = (float)std::atof(argv[++i]);
      mat.base_color = mat.hair_color;
    } else if (!std::strcmp(argv[i], "--hair-absorption") && i + 3 < argc) {
      mat.hair_absorption.x = (float)std::atof(argv[++i]);
      mat.hair_absorption.y = (float)std::atof(argv[++i]);
      mat.hair_absorption.z = (float)std::atof(argv[++i]);
    } else if (!std::strcmp(argv[i], "--hair-weight") && i + 1 < argc)
      mat.hair_weight = (float)std::atof(argv[++i]);
    else if (!std::strcmp(argv[i], "--width") && i + 1 < argc)
      settings.width = (uint32_t)std::atoi(argv[++i]);
    else if (!std::strcmp(argv[i], "--height") && i + 1 < argc)
      settings.height = (uint32_t)std::atoi(argv[++i]);
    else if (!std::strcmp(argv[i], "--spp") && i + 1 < argc)
      settings.spp = (uint32_t)std::atoi(argv[++i]);
    else if (!std::strcmp(argv[i], "--output") && i + 1 < argc)
      output_file = argv[++i];
    else if (!std::strcmp(argv[i], "--reference"))
      save_reference = true;
  }

  // Build scene
  scene::Scene sc;

  int mat_id = addMaterial(sc, mat);

  // Generate hair strands in a grid pattern
  std::vector<Curve> curves;
  float spacing = 2.0f / std::sqrt((float)num_strands);
  int cols = (int)std::ceil(std::sqrt((float)num_strands));
  int rows = (int)std::ceil((float)num_strands / (float)cols);
  float offset = (float)(cols - 1) * spacing * 0.5f;

  int strand = 0;
  for (int r = 0; r < rows && strand < num_strands; r++) {
    for (int c = 0; c < cols && strand < num_strands; c++, strand++) {
      float x = c * spacing - offset;
      float z = r * spacing - offset + 0.5f;
      float len = 0.8f + ((float)strand / (float)num_strands) * 1.2f;
      float rad = 0.008f + ((float)strand / (float)num_strands) * 0.005f;
      generateHairStrand(x, z, len, rad, 6, CurveType::Bezier, curves);
    }
  }

  int curve_mesh_id = addCurveMesh(sc, std::move(curves), mat_id);
  addInstance(sc, curve_mesh_id, Vec3(0, -0.6f, 0));

  // Lights
  addSphereLight(sc, Vec3(-2.0f, 3.0f, 2.5f), Vec3(1.0f, 0.95f, 0.85f), 60.0f, 0.5f);
  addSphereLight(sc, Vec3(1.5f, 1.0f, -2.5f), Vec3(0.7f, 0.8f, 1.0f), 40.0f, 0.3f);

  // Camera setup
  CameraView cam;
  cam.position = Vec3(0.0f, 1.2f, 3.0f);
  cam.direction = (Vec3(0, 0.3f, 0) - cam.position).normalize();
  cam.up = Vec3(0, 1, 0);
  cam.right = cam.direction.cross(cam.up).normalize();
  cam.up = cam.right.cross(cam.direction).normalize();
  float fov_y = 40.0f * 3.14159265f / 180.0f;
  float half_h = std::tan(fov_y * 0.5f);
  cam.half_width = half_h * (float)settings.width / (float)settings.height;
  cam.half_height = half_h;

  // Render
  std::vector<lightrt::RGB8> image(settings.width * settings.height);
  std::printf("Rendering hair: %u strands, %ux%u, %u spp\n",
              (unsigned)num_strands, settings.width, settings.height, settings.spp);
  renderFrame(sc, settings, cam, image);
  writePPM(output_file.c_str(), (int)settings.width, (int)settings.height, image);
  std::printf("Saved: %s\n", output_file.c_str());

  // Reference without hair BSDF
  if (save_reference) {
    scene::MaterialData no_hair_mat = mat;
    no_hair_mat.hair_weight = 0.0f;
    int no_hair_id = addMaterial(sc, no_hair_mat);
    sc.curve_meshes[0].default_material_id = no_hair_id;

    std::string ref_file = output_file;
    size_t dot = ref_file.rfind('.');
    if (dot != std::string::npos) ref_file.insert(dot, "_no_hair");
    else ref_file += "_no_hair";

    std::vector<lightrt::RGB8> ref_image(settings.width * settings.height);
    renderFrame(sc, settings, cam, ref_image);
    writePPM(ref_file.c_str(), (int)settings.width, (int)settings.height, ref_image);
    std::printf("Saved reference: %s\n", ref_file.c_str());
  }

  return 0;
}
