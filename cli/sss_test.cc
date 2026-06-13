// Standalone SSS validation renderer.
// Generates a procedural sphere with configurable SSS parameters and renders it
// with the shared renderFrame() function.
//
// Usage:
//   lightrt_sss_test --output out.ppm [options]
//
// Options:
//   --sss-weight F       Subsurface weight (default: 0.8)
//   --sss-color R G B    Subsurface color (default: 0.85 0.25 0.08)
//   --sss-radius F       Mean free path (default: 0.5)
//   --sss-radius-scale R G B  Per-channel scale (default: 1.0 0.35 0.15)
//   --sss-anisotropy F   HG phase function g (default: 0.3)
//   --base-color R G B   Surface base color (default: 0.85 0.50 0.35)
//   --width W --height H Resolution (default: 512 384)
//   --spp N              Samples per pixel (default: 64)
//   --reference          Also output non-SSS reference image
//   --output FILE        Output image path
//   --key-light-pos X Y Z   Key light position
//   --back-light-pos X Y Z  Back light position
//   --camera-pos X Y Z      Camera position

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
// Procedural sphere mesh generation
// ---------------------------------------------------------------------------
static void generateSphere(float radius, int segments, int rings,
                           std::vector<Triangle>& tris,
                           std::vector<Vec3>& normals,
                           std::vector<float>& uvs) {
  tris.clear();
  normals.clear();
  uvs.clear();

  struct Vertex { Vec3 p; Vec3 n; float u, v; };
  std::vector<Vertex> verts;

  // Top pole
  verts.push_back({Vec3(0, radius, 0), Vec3(0, 1, 0), 0.5f, 1.0f});

  for (int r = 1; r < rings; ++r) {
    constexpr float kPi = 3.14159265358979323846f;
    float phi = kPi * (float)r / (float)rings;
    float y = std::cos(phi) * radius;
    float ring_r = std::sin(phi) * radius;
    float v = (float)r / (float)rings;
    for (int s = 0; s < segments; ++s) {
      float theta = 2.0f * kPi * (float)s / (float)segments;
      float x = std::cos(theta) * ring_r;
      float z = std::sin(theta) * ring_r;
      Vec3 p(x, y, z);
      Vec3 n = p.normalize();
      float u = (float)s / (float)segments;
      verts.push_back({p, n, u, v});
    }
  }

  // Bottom pole
  verts.push_back({Vec3(0, -radius, 0), Vec3(0, -1, 0), 0.5f, 0.0f});

  // Top cap
  for (int s = 0; s < segments; ++s) {
    int next = (s + 1) % segments;
    int a = 0, b = 1 + s, c = 1 + next;
    tris.push_back(Triangle(verts[a].p, verts[c].p, verts[b].p));
    normals.push_back(verts[a].n);
    normals.push_back(verts[c].n);
    normals.push_back(verts[b].n);
    uvs.push_back(verts[a].u); uvs.push_back(verts[a].v);
    uvs.push_back(verts[c].u); uvs.push_back(verts[c].v);
    uvs.push_back(verts[b].u); uvs.push_back(verts[b].v);
  }

  // Middle rings
  for (int r = 0; r < rings - 2; ++r) {
    int row0 = 1 + r * segments;
    int row1 = 1 + (r + 1) * segments;
    for (int s = 0; s < segments; ++s) {
      int next = (s + 1) % segments;
      int a = row0 + s, b = row1 + s, cc = row1 + next, d = row0 + next;
      tris.push_back(Triangle(verts[a].p, verts[b].p, verts[cc].p));
      tris.push_back(Triangle(verts[a].p, verts[cc].p, verts[d].p));
      normals.push_back(verts[a].n); normals.push_back(verts[b].n); normals.push_back(verts[cc].n);
      normals.push_back(verts[a].n); normals.push_back(verts[cc].n); normals.push_back(verts[d].n);
      uvs.push_back(verts[a].u); uvs.push_back(verts[a].v);
      uvs.push_back(verts[b].u); uvs.push_back(verts[b].v);
      uvs.push_back(verts[cc].u); uvs.push_back(verts[cc].v);
      uvs.push_back(verts[a].u); uvs.push_back(verts[a].v);
      uvs.push_back(verts[cc].u); uvs.push_back(verts[cc].v);
      uvs.push_back(verts[d].u); uvs.push_back(verts[d].v);
    }
  }

  // Bottom cap
  int last_ring = 1 + (rings - 2) * segments;
  int pole = (int)verts.size() - 1;
  for (int s = 0; s < segments; ++s) {
    int next = (s + 1) % segments;
    int a = pole, b = last_ring + next, cc = last_ring + s;
    tris.push_back(Triangle(verts[a].p, verts[b].p, verts[cc].p));
    normals.push_back(verts[a].n);
    normals.push_back(verts[b].n);
    normals.push_back(verts[cc].n);
    uvs.push_back(verts[a].u); uvs.push_back(verts[a].v);
    uvs.push_back(verts[b].u); uvs.push_back(verts[b].v);
    uvs.push_back(verts[cc].u); uvs.push_back(verts[cc].v);
  }
}

// ---------------------------------------------------------------------------
// Simple PPM writer (no external dependencies)
// ---------------------------------------------------------------------------
static bool writePPM(const char* filename, int w, int h,
                     const std::vector<lightrt::RGB8>& pixels) {
  FILE* f = std::fopen(filename, "wb");
  if (!f) return false;
  std::fprintf(f, "P6\n%d %d\n255\n", w, h);
  // RGB8 is likely R, G, B in that order; PPM expects RGB
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
// Helpers to add geometry/lights to the scene
// ---------------------------------------------------------------------------
static int addMaterial(scene::Scene& sc, const scene::MaterialData& mat) {
  int id = (int)sc.materials.size();
  sc.materials.push_back(mat);
  return id;
}

static int addMesh(scene::Scene& sc, std::vector<Triangle> tris,
                   std::vector<Vec3> normals, std::vector<float> uvs,
                   int material_id) {
  int mesh_id = (int)sc.meshes.size();
  sc.meshes.emplace_back();
  auto& blas = sc.meshes.back();
  blas.default_material_id = material_id;
  blas.tri_normals.reserve(normals.size() * 3);
  for (const auto& n : normals) {
    blas.tri_normals.push_back(n.x);
    blas.tri_normals.push_back(n.y);
    blas.tri_normals.push_back(n.z);
  }
  blas.tri_uvs = std::move(uvs);
  for (const auto& tri : tris) {
    blas.local_bounds.expand(tri.v0);
    blas.local_bounds.expand(tri.v1);
    blas.local_bounds.expand(tri.v2);
  }
  BVHBuildConfig cfg;
  blas.bvh.build(tris, cfg);
  return mesh_id;
}

static int addInstance(scene::Scene& sc, int mesh_id,
                        const Vec3& translate = Vec3(0,0,0),
                        const Vec3& rotate = Vec3(0,0,0)) {
  int inst_id = (int)sc.instances.size();
  sc.instances.emplace_back();
  auto& inst = sc.instances.back();
  inst.mesh_id = (uint32_t)mesh_id;

  float m[12] = {1,0,0,translate.x, 0,1,0,translate.y, 0,0,1,translate.z};
  std::memcpy(inst.transform, m, sizeof(m));
  std::memcpy(inst.inv_transform, m, sizeof(m));
  std::memcpy(inst.transform_close, m, sizeof(m));
  std::memcpy(inst.inv_transform_close, m, sizeof(m));
  inst.inv_transform[3] = -translate.x;
  inst.inv_transform[7] = -translate.y;
  inst.inv_transform[11] = -translate.z;

  inst.world_bounds = sc.meshes[(size_t)mesh_id].local_bounds;
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
  mat.base_color = Vec3(0.85f, 0.50f, 0.35f);
  mat.subsurface_weight = 0.8f;
  mat.subsurface_color = Vec3(0.85f, 0.25f, 0.08f);
  mat.subsurface_radius = 0.5f;
  mat.subsurface_radius_scale = Vec3(1.0f, 0.35f, 0.15f);
  mat.subsurface_scale = 1.0f;
  mat.subsurface_anisotropy = 0.3f;
  mat.base_roughness = 0.0f;
  mat.base_metalness = 0.0f;
  mat.specular_weight = 1.0f;
  mat.specular_color = Vec3(1.0f, 1.0f, 1.0f);
  mat.specular_roughness = 0.35f;
  mat.specular_ior = 1.4f;

  RenderSettings settings;
  settings.width = 512;
  settings.height = 384;
  settings.spp = 64;

  std::string output_file = "sss_output.ppm";
  bool save_reference = false;

  Vec3 key_light_pos(-2.5f, 2.0f, 3.0f);
  Vec3 back_light_pos(0.0f, 0.5f, -3.5f);
  Vec3 camera_pos(0.0f, 0.3f, 4.5f);

  // Parse command line
  for (int i = 1; i < argc; ++i) {
    if (!std::strcmp(argv[i], "--sss-weight") && i + 1 < argc)
      mat.subsurface_weight = (float)std::atof(argv[++i]);
    else if (!std::strcmp(argv[i], "--sss-color") && i + 3 < argc) {
      mat.subsurface_color.x = (float)std::atof(argv[++i]);
      mat.subsurface_color.y = (float)std::atof(argv[++i]);
      mat.subsurface_color.z = (float)std::atof(argv[++i]);
    } else if (!std::strcmp(argv[i], "--sss-radius") && i + 1 < argc)
      mat.subsurface_radius = (float)std::atof(argv[++i]);
    else if (!std::strcmp(argv[i], "--sss-radius-scale") && i + 3 < argc) {
      mat.subsurface_radius_scale.x = (float)std::atof(argv[++i]);
      mat.subsurface_radius_scale.y = (float)std::atof(argv[++i]);
      mat.subsurface_radius_scale.z = (float)std::atof(argv[++i]);
    } else if (!std::strcmp(argv[i], "--sss-anisotropy") && i + 1 < argc)
      mat.subsurface_anisotropy = (float)std::atof(argv[++i]);
    else if (!std::strcmp(argv[i], "--base-color") && i + 3 < argc) {
      mat.base_color.x = (float)std::atof(argv[++i]);
      mat.base_color.y = (float)std::atof(argv[++i]);
      mat.base_color.z = (float)std::atof(argv[++i]);
    } else if (!std::strcmp(argv[i], "--width") && i + 1 < argc)
      settings.width = (uint32_t)std::atoi(argv[++i]);
    else if (!std::strcmp(argv[i], "--height") && i + 1 < argc)
      settings.height = (uint32_t)std::atoi(argv[++i]);
    else if (!std::strcmp(argv[i], "--spp") && i + 1 < argc)
      settings.spp = (uint32_t)std::atoi(argv[++i]);
    else if (!std::strcmp(argv[i], "--output") && i + 1 < argc)
      output_file = argv[++i];
    else if (!std::strcmp(argv[i], "--reference"))
      save_reference = true;
    else if (!std::strcmp(argv[i], "--key-light-pos") && i + 3 < argc) {
      key_light_pos.x = (float)std::atof(argv[++i]);
      key_light_pos.y = (float)std::atof(argv[++i]);
      key_light_pos.z = (float)std::atof(argv[++i]);
    } else if (!std::strcmp(argv[i], "--back-light-pos") && i + 3 < argc) {
      back_light_pos.x = (float)std::atof(argv[++i]);
      back_light_pos.y = (float)std::atof(argv[++i]);
      back_light_pos.z = (float)std::atof(argv[++i]);
    } else if (!std::strcmp(argv[i], "--camera-pos") && i + 3 < argc) {
      camera_pos.x = (float)std::atof(argv[++i]);
      camera_pos.y = (float)std::atof(argv[++i]);
      camera_pos.z = (float)std::atof(argv[++i]);
    }
  }

  // Build scene
  scene::Scene sc;

  int mat_id = addMaterial(sc, mat);

  std::vector<Triangle> tris;
  std::vector<Vec3> normals;
  std::vector<float> uvs;
  generateSphere(1.0f, 32, 16, tris, normals, uvs);
  int mesh_id = addMesh(sc, tris, normals, uvs, mat_id);
  addInstance(sc, mesh_id);

  // Lights
  addSphereLight(sc, key_light_pos, Vec3(1.0f, 0.92f, 0.80f), 40.0f, 0.5f);
  addSphereLight(sc, back_light_pos, Vec3(0.6f, 0.85f, 1.0f), 80.0f, 0.3f);

  sc.scene_bounds = sc.meshes[0].local_bounds;

  // Camera setup
  CameraView cam;
  cam.position = camera_pos;
  cam.direction = (Vec3(0, 0, 0) - cam.position).normalize();
  cam.up = Vec3(0, 1, 0);
  cam.right = cam.direction.cross(cam.up).normalize();
  cam.up = cam.right.cross(cam.direction).normalize();
  float fov_y = 45.0f * 3.14159265f / 180.0f;
  float half_h = std::tan(fov_y * 0.5f);
  float half_w = half_h * (float)settings.width / (float)settings.height;
  cam.half_width = half_w;
  cam.half_height = half_h;

  // Render SSS
  std::vector<lightrt::RGB8> image(settings.width * settings.height);
  std::printf("Rendering SSS: %ux%u, %u spp\n", settings.width, settings.height, settings.spp);
  renderFrame(sc, settings, cam, image);
  writePPM(output_file.c_str(), (int)settings.width, (int)settings.height, image);
  std::printf("Saved: %s\n", output_file.c_str());

  // Optionally render without SSS for reference
  if (save_reference) {
    scene::MaterialData no_sss_mat = mat;
    no_sss_mat.subsurface_weight = 0.0f;
    int no_sss_mat_id = addMaterial(sc, no_sss_mat);
    sc.meshes[0].default_material_id = no_sss_mat_id;

    std::string ref_file = output_file;
    size_t dot = ref_file.rfind('.');
    if (dot != std::string::npos) ref_file.insert(dot, "_no_sss");
    else ref_file += "_no_sss";

    std::vector<lightrt::RGB8> ref_image(settings.width * settings.height);
    renderFrame(sc, settings, cam, ref_image);
    writePPM(ref_file.c_str(), (int)settings.width, (int)settings.height, ref_image);
    std::printf("Saved reference: %s\n", ref_file.c_str());
  }

  return 0;
}
