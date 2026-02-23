// LightRT CLI renderer with USD loading via TinyUSDZ
// Usage: lightrt_cli input.usd [-o output.png] [-w 800] [-h 600] [-t timecode]
//        [--time-range start end step] [--camera name_or_index]
//        [--mblur-samples N] [--spp N]

#include "scene.hh"

#include "tinyusdz.hh"
#include "tydra/render-data.hh"
#include "tydra/scene-access.hh"

#include "stb_image_write.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <cmath>
#include <algorithm>
#include <chrono>
#include <random>
#include <map>
#include <tuple>

struct Options {
  std::string input_file;
  std::string output_file = "output.png";
  uint32_t width = 800;
  uint32_t height = 600;
  double timecode = -1e30; // sentinel: use stage default
  double time_range_start = 0;
  double time_range_end = 0;
  double time_range_step = 1;
  bool has_time_range = false;
  std::string camera_name;
  int camera_index = -1; // -1 = auto
  uint32_t mblur_samples = 1;
  uint32_t spp = 1;
};

static bool parseArgs(int argc, char** argv, Options& opts) {
  if (argc < 2) {
    fprintf(stderr,
      "Usage: %s input.usd [-o output.png] [-w 800] [-h 600]\n"
      "       [-t timecode] [--time-range start end step]\n"
      "       [--camera name_or_index] [--mblur-samples N] [--spp N]\n",
      argv[0]);
    return false;
  }
  opts.input_file = argv[1];
  for (int i = 2; i < argc; i++) {
    if (strcmp(argv[i], "-o") == 0 && i + 1 < argc) {
      opts.output_file = argv[++i];
    } else if (strcmp(argv[i], "-w") == 0 && i + 1 < argc) {
      opts.width = static_cast<uint32_t>(atoi(argv[++i]));
    } else if (strcmp(argv[i], "-h") == 0 && i + 1 < argc) {
      opts.height = static_cast<uint32_t>(atoi(argv[++i]));
    } else if (strcmp(argv[i], "-t") == 0 && i + 1 < argc) {
      opts.timecode = atof(argv[++i]);
    } else if (strcmp(argv[i], "--time-range") == 0 && i + 3 < argc) {
      opts.time_range_start = atof(argv[++i]);
      opts.time_range_end = atof(argv[++i]);
      opts.time_range_step = atof(argv[++i]);
      opts.has_time_range = true;
    } else if (strcmp(argv[i], "--camera") == 0 && i + 1 < argc) {
      ++i;
      char* endp = nullptr;
      long idx = strtol(argv[i], &endp, 10);
      if (endp != argv[i] && *endp == '\0') {
        opts.camera_index = static_cast<int>(idx);
      } else {
        opts.camera_name = argv[i];
      }
    } else if (strcmp(argv[i], "--mblur-samples") == 0 && i + 1 < argc) {
      opts.mblur_samples = static_cast<uint32_t>(atoi(argv[++i]));
      if (opts.mblur_samples < 1) opts.mblur_samples = 1;
    } else if (strcmp(argv[i], "--spp") == 0 && i + 1 < argc) {
      opts.spp = static_cast<uint32_t>(atoi(argv[++i]));
      if (opts.spp < 1) opts.spp = 1;
    }
  }
  return true;
}

// Walk node tree recursively to create instances
static void walkNodes(const tinyusdz::tydra::RenderScene& render_scene,
                      const tinyusdz::tydra::Node& node,
                      scene::Scene& out_scene,
                      std::vector<int>& camera_node_indices) {
  if (node.nodeType == tinyusdz::tydra::NodeType::Mesh && node.id >= 0 &&
      node.id < static_cast<int32_t>(out_scene.meshes.size())) {
    scene::Instance inst;
    inst.mesh_id = static_cast<uint32_t>(node.id);
    scene::matrix4dTo3x4(node.global_matrix.m, inst.transform);
    scene::invert3x4(inst.transform, inst.inv_transform);
    std::memcpy(inst.transform_close, inst.transform, sizeof(inst.transform));
    std::memcpy(inst.inv_transform_close, inst.inv_transform, sizeof(inst.inv_transform));
    inst.has_motion = false;
    inst.world_bounds = scene::transformAABB(
      out_scene.meshes[inst.mesh_id].local_bounds, inst.transform);
    out_scene.scene_bounds.expand(inst.world_bounds);
    out_scene.instances.push_back(inst);
  }

  if (node.nodeType == tinyusdz::tydra::NodeType::Camera && node.id >= 0) {
    camera_node_indices.push_back(static_cast<int>(out_scene.instances.size()));
    if (node.id < static_cast<int32_t>(render_scene.cameras.size())) {
      const auto& rc = render_scene.cameras[static_cast<size_t>(node.id)];
      scene::Camera cam;
      cam.name = rc.name;
      cam.fov_y_rad = 2.0f * std::atan(0.5f * rc.verticalAperture / rc.focalLength);
      cam.znear = rc.znear;
      cam.zfar = rc.zfar;
      cam.shutter_open = rc.shutterOpen;
      cam.shutter_close = rc.shutterClose;
      for (int r = 0; r < 4; r++)
        for (int c = 0; c < 4; c++)
          cam.transform[r * 4 + c] = static_cast<float>(node.global_matrix.m[r][c]);
      out_scene.cameras.push_back(cam);
    }
  }

  for (const auto& child : node.children) {
    walkNodes(render_scene, child, out_scene, camera_node_indices);
  }
}

// Extract materials from RenderScene
static void extractMaterials(const tinyusdz::tydra::RenderScene& render_scene,
                             scene::Scene& out_scene) {
  out_scene.materials.resize(render_scene.materials.size());
  for (size_t i = 0; i < render_scene.materials.size(); i++) {
    const auto& rm = render_scene.materials[i];
    scene::MaterialData& mat = out_scene.materials[i];

    if (rm.hasOpenPBR()) {
      const auto& pbr = rm.openPBRShader.value();
      mat.base_color = lightrt::Vec3(pbr.base_color.value[0], pbr.base_color.value[1], pbr.base_color.value[2]);
      mat.metalness = pbr.base_metalness.value;
      mat.roughness = pbr.specular_roughness.value;
      mat.specular_color = lightrt::Vec3(pbr.specular_color.value[0], pbr.specular_color.value[1], pbr.specular_color.value[2]);
      mat.ior = pbr.specular_ior.value;
      mat.emission_color = lightrt::Vec3(pbr.emission_color.value[0], pbr.emission_color.value[1], pbr.emission_color.value[2]);
      mat.emission_luminance = pbr.emission_luminance.value;
      mat.opacity = pbr.opacity.value;
    } else if (rm.hasUsdPreviewSurface()) {
      const auto& ps = rm.surfaceShader.value();
      mat.base_color = lightrt::Vec3(ps.diffuseColor.value[0], ps.diffuseColor.value[1], ps.diffuseColor.value[2]);
      mat.metalness = ps.metallic.value;
      mat.roughness = ps.roughness.value;
      mat.specular_color = lightrt::Vec3(ps.specularColor.value[0], ps.specularColor.value[1], ps.specularColor.value[2]);
      mat.ior = ps.ior.value;
      mat.emission_color = lightrt::Vec3(ps.emissiveColor.value[0], ps.emissiveColor.value[1], ps.emissiveColor.value[2]);
      mat.emission_luminance = (ps.emissiveColor.value[0] + ps.emissiveColor.value[1] + ps.emissiveColor.value[2] > 0.0f) ? 1.0f : 0.0f;
      mat.opacity = ps.opacity.value;
    }
    // else: default grey material
  }
  if (!out_scene.materials.empty())
    printf("Extracted %zu materials\n", out_scene.materials.size());
}

// Extract lights from RenderScene
static void extractLights(const tinyusdz::tydra::RenderScene& render_scene,
                          scene::Scene& out_scene) {
  for (size_t i = 0; i < render_scene.lights.size(); i++) {
    const auto& rl = render_scene.lights[i];
    if (rl.type == tinyusdz::tydra::RenderLight::Type::Dome) continue; // handled separately

    scene::LightData light;
    float multiplier = rl.intensity * std::pow(2.0f, rl.exposure);
    light.color = lightrt::Vec3(rl.color[0] * multiplier, rl.color[1] * multiplier, rl.color[2] * multiplier);

    if (rl.type == tinyusdz::tydra::RenderLight::Type::Distant) {
      light.type = scene::LightData::Distant;
      // Transform direction by light's world transform
      // Light direction in local space is (0,0,-1) for USD
      float dir_x = -rl.transform.m[0][2];
      float dir_y = -rl.transform.m[1][2];
      float dir_z = -rl.transform.m[2][2];
      float len = std::sqrt(dir_x*dir_x + dir_y*dir_y + dir_z*dir_z);
      if (len > 1e-8f) {
        light.direction = lightrt::Vec3(dir_x/len, dir_y/len, dir_z/len);
      } else {
        light.direction = lightrt::Vec3(rl.direction[0], rl.direction[1], rl.direction[2]).normalize();
      }
    } else if (rl.type == tinyusdz::tydra::RenderLight::Type::Point ||
               rl.type == tinyusdz::tydra::RenderLight::Type::Sphere) {
      light.type = scene::LightData::Point;
      light.position = lightrt::Vec3(
        static_cast<float>(rl.transform.m[0][3]),
        static_cast<float>(rl.transform.m[1][3]),
        static_cast<float>(rl.transform.m[2][3]));
    } else {
      continue; // skip unsupported light types
    }
    out_scene.lights.push_back(light);
  }
  if (!out_scene.lights.empty())
    printf("Extracted %zu lights\n", out_scene.lights.size());
}

// Load environment map from dome light
static void loadEnvmap(const tinyusdz::tydra::RenderScene& render_scene,
                       scene::Scene& out_scene) {
  for (const auto& rl : render_scene.lights) {
    if (rl.type != tinyusdz::tydra::RenderLight::Type::Dome) continue;
    if (rl.envmap_texture_id < 0) continue;
    size_t img_idx = static_cast<size_t>(rl.envmap_texture_id);
    if (img_idx >= render_scene.images.size()) continue;

    const auto& img = render_scene.images[img_idx];
    if (img.buffer_id < 0) continue;
    size_t buf_idx = static_cast<size_t>(img.buffer_id);
    if (buf_idx >= render_scene.buffers.size()) continue;
    if (img.width <= 0 || img.height <= 0 || img.channels <= 0) continue;

    const auto& buf = render_scene.buffers[buf_idx];
    int w = img.width, h = img.height, ch = img.channels;
    scene::EnvmapData& env = out_scene.envmap;
    env.width = w;
    env.height = h;
    env.pixels.resize(static_cast<size_t>(w) * static_cast<size_t>(h) * 3);

    float multiplier = rl.intensity * std::pow(2.0f, rl.exposure);
    bool is_srgb = (img.colorSpace == tinyusdz::tydra::ColorSpace::sRGB ||
                    img.colorSpace == tinyusdz::tydra::ColorSpace::sRGB_Texture);

    if (img.texelComponentType == tinyusdz::tydra::ComponentType::Float) {
      const float* src = reinterpret_cast<const float*>(buf.data.data());
      size_t src_count = buf.data.size() / sizeof(float);
      for (int y = 0; y < h; y++) {
        for (int x = 0; x < w; x++) {
          size_t si = (static_cast<size_t>(y) * static_cast<size_t>(w) + static_cast<size_t>(x)) * static_cast<size_t>(ch);
          size_t di = (static_cast<size_t>(y) * static_cast<size_t>(w) + static_cast<size_t>(x)) * 3;
          for (int c = 0; c < 3 && si + static_cast<size_t>(c) < src_count; c++)
            env.pixels[di + static_cast<size_t>(c)] = src[si + static_cast<size_t>(c)] * multiplier * rl.color[c];
        }
      }
    } else {
      // uint8
      const uint8_t* src = buf.data.data();
      size_t src_count = buf.data.size();
      for (int y = 0; y < h; y++) {
        for (int x = 0; x < w; x++) {
          size_t si = (static_cast<size_t>(y) * static_cast<size_t>(w) + static_cast<size_t>(x)) * static_cast<size_t>(ch);
          size_t di = (static_cast<size_t>(y) * static_cast<size_t>(w) + static_cast<size_t>(x)) * 3;
          for (int c = 0; c < 3 && si + static_cast<size_t>(c) < src_count; c++) {
            float v = src[si + static_cast<size_t>(c)] / 255.0f;
            if (is_srgb) v = std::pow(v, 2.2f); // sRGB to linear
            env.pixels[di + static_cast<size_t>(c)] = v * multiplier * rl.color[c];
          }
        }
      }
    }

    scene::shading::buildEnvmapCDF(env);
    printf("Loaded envmap %dx%d from dome light\n", w, h);
    break; // use first dome light
  }
}

// Centroid key for triangle remapping after BVH reorder
struct CentroidKey {
  int32_t cx, cy, cz;
  bool operator<(const CentroidKey& o) const {
    return std::tie(cx, cy, cz) < std::tie(o.cx, o.cy, o.cz);
  }
};

static CentroidKey makeCentroidKey(const lightrt::Triangle& tri) {
  float x = (tri.v0.x + tri.v1.x + tri.v2.x) * (1.0f / 3.0f);
  float y = (tri.v0.y + tri.v1.y + tri.v2.y) * (1.0f / 3.0f);
  float z = (tri.v0.z + tri.v1.z + tri.v2.z) * (1.0f / 3.0f);
  // Quantize to avoid floating point comparison issues
  return {static_cast<int32_t>(x * 1e4f), static_cast<int32_t>(y * 1e4f), static_cast<int32_t>(z * 1e4f)};
}

static bool loadUSDScene(const std::string& filename, double timecode,
                         scene::Scene& out_scene) {
  std::string warn, err;
  tinyusdz::Stage stage;

  bool ret = tinyusdz::LoadUSDFromFile(filename, &stage, &warn, &err);
  if (!warn.empty()) fprintf(stderr, "USD warn: %s\n", warn.c_str());
  if (!ret) {
    fprintf(stderr, "USD load error: %s\n", err.c_str());
    return false;
  }

  if (timecode < -1e29) {
    timecode = stage.metas().startTimeCode.get_value();
  }

  tinyusdz::tydra::RenderScene render_scene;
  tinyusdz::tydra::RenderSceneConverter converter;
  tinyusdz::tydra::RenderSceneConverterEnv env(stage);
  env.mesh_config.triangulate = true;
  env.timecode = timecode;

  ret = converter.ConvertToRenderScene(env, &render_scene);
  if (!ret) {
    fprintf(stderr, "Failed to convert USD to render scene\n");
    return false;
  }

  // Extract materials
  extractMaterials(render_scene, out_scene);

  // Build per-mesh BLAS with material ID tracking
  out_scene.meshes.resize(render_scene.meshes.size());
  for (size_t mi = 0; mi < render_scene.meshes.size(); mi++) {
    const auto& mesh = render_scene.meshes[mi];
    const auto& pts = mesh.points;
    const auto& idx = mesh.faceVertexIndices();

    std::vector<lightrt::Triangle> triangles;
    std::vector<int32_t> mat_ids;

    if (idx.size() % 3 != 0) {
      fprintf(stderr, "Warning: non-triangulated mesh %zu, skipping\n", mi);
      continue;
    }

    int32_t mesh_mat_id = mesh.material_id;
    out_scene.meshes[mi].default_material_id = mesh_mat_id;

    // Build per-face material ID map from subsets
    // MaterialSubset.triangulatedIndices contains triangle indices (into the triangulated mesh)
    // that use that subset's material
    std::vector<int32_t> face_mat_ids(idx.size() / 3, mesh_mat_id);
    for (const auto& kv : mesh.material_subsetMap) {
      const auto& subset = kv.second;
      const auto& tri_indices = subset.indices();
      for (int ti : tri_indices) {
        if (ti >= 0 && static_cast<size_t>(ti) < face_mat_ids.size())
          face_mat_ids[static_cast<size_t>(ti)] = subset.material_id;
      }
    }

    for (size_t i = 0; i + 2 < idx.size(); i += 3) {
      uint32_t i0 = idx[i], i1 = idx[i + 1], i2 = idx[i + 2];
      if (i0 >= pts.size() || i1 >= pts.size() || i2 >= pts.size()) continue;
      lightrt::Triangle tri;
      tri.v0 = lightrt::Vec3(pts[i0][0], pts[i0][1], pts[i0][2]);
      tri.v1 = lightrt::Vec3(pts[i1][0], pts[i1][1], pts[i1][2]);
      tri.v2 = lightrt::Vec3(pts[i2][0], pts[i2][1], pts[i2][2]);
      triangles.push_back(tri);
      mat_ids.push_back(face_mat_ids[i / 3]);
    }
    if (triangles.empty()) continue;

    // Build centroid→mat_id map before BVH reorders triangles
    std::multimap<CentroidKey, int32_t> centroid_to_mat;
    for (size_t i = 0; i < triangles.size(); i++) {
      centroid_to_mat.emplace(makeCentroidKey(triangles[i]), mat_ids[i]);
    }

    // Compute local bounds
    lightrt::AABB& lb = out_scene.meshes[mi].local_bounds;
    for (const auto& tri : triangles) {
      lb.expand(tri.v0);
      lb.expand(tri.v1);
      lb.expand(tri.v2);
    }

    out_scene.meshes[mi].bvh.build(triangles);

    // Remap material IDs to match BVH-reordered triangles
    const auto& bvh_tris = out_scene.meshes[mi].bvh.getTriangles();
    auto& remapped_ids = out_scene.meshes[mi].tri_material_ids;
    remapped_ids.resize(bvh_tris.size());
    for (size_t i = 0; i < bvh_tris.size(); i++) {
      CentroidKey key = makeCentroidKey(bvh_tris[i]);
      auto it = centroid_to_mat.find(key);
      if (it != centroid_to_mat.end()) {
        remapped_ids[i] = it->second;
        centroid_to_mat.erase(it); // consume to handle duplicates
      } else {
        remapped_ids[i] = mesh_mat_id;
      }
    }
  }

  // Extract lights and envmap
  extractLights(render_scene, out_scene);
  loadEnvmap(render_scene, out_scene);

  // Walk node tree to create instances and find cameras
  std::vector<int> camera_node_indices;
  for (const auto& root_node : render_scene.nodes) {
    walkNodes(render_scene, root_node, out_scene, camera_node_indices);
  }

  // If no instances were created (flat scene), create identity instances
  if (out_scene.instances.empty()) {
    for (size_t mi = 0; mi < out_scene.meshes.size(); mi++) {
      if (out_scene.meshes[mi].local_bounds.min.x > out_scene.meshes[mi].local_bounds.max.x)
        continue;
      scene::Instance inst;
      inst.mesh_id = static_cast<uint32_t>(mi);
      std::memset(inst.transform, 0, sizeof(inst.transform));
      inst.transform[0] = 1.0f; inst.transform[5] = 1.0f; inst.transform[10] = 1.0f;
      std::memcpy(inst.inv_transform, inst.transform, sizeof(inst.transform));
      std::memcpy(inst.transform_close, inst.transform, sizeof(inst.transform));
      std::memcpy(inst.inv_transform_close, inst.transform, sizeof(inst.transform));
      inst.world_bounds = out_scene.meshes[mi].local_bounds;
      out_scene.scene_bounds.expand(inst.world_bounds);
      out_scene.instances.push_back(inst);
    }
  }

  printf("Loaded %zu meshes, %zu instances, %zu cameras (timecode=%.1f)\n",
         out_scene.meshes.size(), out_scene.instances.size(),
         out_scene.cameras.size(), timecode);
  return !out_scene.instances.empty();
}

// Apply motion blur: evaluate scene at shutter close and set close transforms
static void applyMotionBlur(const std::string& filename, double timecode,
                            double shutter_close_offset, scene::Scene& scene) {
  if (shutter_close_offset <= 0.0) return;

  std::string warn, err;
  tinyusdz::Stage stage;
  if (!tinyusdz::LoadUSDFromFile(filename, &stage, &warn, &err)) return;

  tinyusdz::tydra::RenderScene render_scene;
  tinyusdz::tydra::RenderSceneConverter converter;
  tinyusdz::tydra::RenderSceneConverterEnv env(stage);
  env.mesh_config.triangulate = true;
  env.timecode = timecode + shutter_close_offset;

  if (!converter.ConvertToRenderScene(env, &render_scene)) return;

  uint32_t inst_idx = 0;
  std::function<void(const tinyusdz::tydra::Node&)> walkClose;
  walkClose = [&](const tinyusdz::tydra::Node& node) {
    if (node.nodeType == tinyusdz::tydra::NodeType::Mesh && node.id >= 0 &&
        inst_idx < static_cast<uint32_t>(scene.instances.size())) {
      auto& inst = scene.instances[inst_idx];
      float close_xform[12];
      scene::matrix4dTo3x4(node.global_matrix.m, close_xform);

      bool differs = false;
      for (int j = 0; j < 12; j++) {
        if (std::fabs(close_xform[j] - inst.transform[j]) > 1e-6f) {
          differs = true;
          break;
        }
      }
      if (differs) {
        std::memcpy(inst.transform_close, close_xform, sizeof(close_xform));
        scene::invert3x4(close_xform, inst.inv_transform_close);
        inst.has_motion = true;
        lightrt::AABB close_bounds = scene::transformAABB(
          scene.meshes[inst.mesh_id].local_bounds, close_xform);
        inst.world_bounds.expand(close_bounds);
        scene.scene_bounds.expand(inst.world_bounds);
      }
      inst_idx++;
    }
    for (const auto& child : node.children) walkClose(child);
  };

  for (const auto& root_node : render_scene.nodes) walkClose(root_node);
}

static bool writeImage(const std::string& path, const std::vector<lightrt::RGB8>& image,
                       uint32_t w, uint32_t h) {
  std::string ext;
  auto dot = path.rfind('.');
  if (dot != std::string::npos) {
    ext = path.substr(dot);
    for (auto& c : ext) c = static_cast<char>(tolower(c));
  }

  int iw = static_cast<int>(w), ih = static_cast<int>(h);
  const uint8_t* data = reinterpret_cast<const uint8_t*>(image.data());
  int stride = iw * 3;
  int ok = 0;

  if (ext == ".png")       ok = stbi_write_png(path.c_str(), iw, ih, 3, data, stride);
  else if (ext == ".jpg" || ext == ".jpeg") ok = stbi_write_jpg(path.c_str(), iw, ih, 3, data, 95);
  else if (ext == ".bmp")  ok = stbi_write_bmp(path.c_str(), iw, ih, 3, data);
  else if (ext == ".tga")  ok = stbi_write_tga(path.c_str(), iw, ih, 3, data);
  else {
    fprintf(stderr, "Unknown output format '%s'. Use .png, .jpg, .bmp, or .tga\n", ext.c_str());
    return false;
  }

  if (!ok) {
    fprintf(stderr, "Failed to write %s\n", path.c_str());
    return false;
  }
  return true;
}

// Resolve material for a hit
static const scene::MaterialData& resolveMaterial(const scene::Scene& scene,
                                                  const scene::HitInfo& hit) {
  static const scene::MaterialData kDefaultMat;
  if (hit.instance_id == lightrt::kInvalidIndex) return kDefaultMat;

  const auto& mesh = scene.meshes[scene.instances[hit.instance_id].mesh_id];
  if (hit.triangle_id < mesh.tri_material_ids.size()) {
    int32_t mat_id = mesh.tri_material_ids[hit.triangle_id];
    if (mat_id >= 0 && static_cast<size_t>(mat_id) < scene.materials.size())
      return scene.materials[static_cast<size_t>(mat_id)];
  }
  if (mesh.default_material_id >= 0 &&
      static_cast<size_t>(mesh.default_material_id) < scene.materials.size())
    return scene.materials[static_cast<size_t>(mesh.default_material_id)];
  return kDefaultMat;
}

static void renderFrame(const scene::Scene& scene, const Options& opts,
                        const lightrt::Vec3& cam_pos,
                        const lightrt::Vec3& cam_dir,
                        const lightrt::Vec3& cam_right,
                        const lightrt::Vec3& cam_up,
                        float half_w, float half_h,
                        std::vector<lightrt::RGB8>& image) {
  using namespace scene::shading;
  image.resize(opts.width * opts.height);

  bool has_lights = !scene.lights.empty();
  bool has_envmap = scene.envmap.valid();
  bool use_fallback = !has_lights && !has_envmap;

  // Fallback light (backward compatible)
  lightrt::Vec3 fallback_light_dir = lightrt::Vec3(0.5f, 0.8f, 0.3f).normalize();

  uint32_t total_samples = opts.spp * opts.mblur_samples;

  for (uint32_t y = 0; y < opts.height; y++) {
    for (uint32_t x = 0; x < opts.width; x++) {
      float r_acc = 0.0f, g_acc = 0.0f, b_acc = 0.0f;

      // Per-pixel RNG seeded by pixel coords for reproducibility
      uint32_t seed = y * opts.width + x;
      std::mt19937 rng(seed ^ 0x9e3779b9u);
      std::uniform_real_distribution<float> dist01(0.0f, 1.0f);

      for (uint32_t s = 0; s < total_samples; s++) {
        // Jittered pixel position for AA
        float jx = (total_samples > 1) ? dist01(rng) : 0.5f;
        float jy = (total_samples > 1) ? dist01(rng) : 0.5f;
        float u = (2.0f * (x + jx) / opts.width - 1.0f) * half_w;
        float v = (1.0f - 2.0f * (y + jy) / opts.height) * half_h;

        lightrt::Vec3 dir = (cam_dir + cam_right * u + cam_up * v).normalize();
        lightrt::Ray ray(cam_pos, dir);

        float ray_time = (opts.mblur_samples > 1) ? dist01(rng) : 0.0f;

        scene::HitInfo hit = scene::traceScene(scene, ray, ray_time);

        lightrt::Vec3 color(0.0f, 0.0f, 0.0f);

        if (hit.instance_id == lightrt::kInvalidIndex) {
          // Miss: eval envmap or sky
          if (has_envmap) {
            color = evalEnvmap(scene.envmap, dir);
          } else {
            color = lightrt::Vec3(0.118f, 0.118f, 0.157f); // dark sky
          }
        } else {
          // Hit: compute shading
          const auto& inst = scene.instances[hit.instance_id];
          const auto& mesh_blas = scene.meshes[inst.mesh_id];
          const auto& tris = mesh_blas.bvh.getTriangles();
          const auto& tri = tris[hit.triangle_id];

          // Compute local normal
          lightrt::Vec3 e1 = tri.v1 - tri.v0;
          lightrt::Vec3 e2 = tri.v2 - tri.v0;
          lightrt::Vec3 local_n = e1.cross(e2).normalize();

          // Transform normal to world space
          lightrt::Vec3 N = scene::transformNormal(inst.inv_transform, local_n).normalize();
          lightrt::Vec3 V = dir * -1.0f;
          if (N.dot(V) < 0.0f) N = N * -1.0f;

          lightrt::Vec3 hit_pos = cam_pos + dir * hit.t;
          float bias = 0.001f;

          const scene::MaterialData& mat = resolveMaterial(scene, hit);

          // Emission
          if (mat.emission_luminance > 0.0f) {
            color = color + mat.emission_color * mat.emission_luminance;
          }

          if (use_fallback) {
            // Backward compatible fallback: hardcoded directional + ambient
            float ndl = std::max(0.0f, N.dot(fallback_light_dir));
            lightrt::Ray shadow_ray(hit_pos + N * bias, fallback_light_dir);
            bool in_shadow = scene::traceSceneAnyHit(scene, shadow_ray,
              hit.instance_id, hit.triangle_id, ray_time);

            float ambient = 0.15f;
            float diffuse = in_shadow ? 0.0f : ndl * 0.85f;
            float shade = std::min(1.0f, ambient + diffuse);
            color = color + mat.base_color * shade;
          } else {
            // Analytic light loop
            for (const auto& light : scene.lights) {
              lightrt::Vec3 L;
              float light_dist = 1e20f;

              if (light.type == scene::LightData::Distant) {
                L = light.direction * -1.0f; // light.direction points from light
                // Actually for distant lights, direction is where the light points
                // We want L = direction toward light = -light.direction
              } else if (light.type == scene::LightData::Point) {
                lightrt::Vec3 to_light = light.position - hit_pos;
                light_dist = to_light.length();
                if (light_dist < 1e-6f) continue;
                L = to_light * (1.0f / light_dist);
              } else {
                continue;
              }

              // Shadow test
              lightrt::Ray shadow_ray(hit_pos + N * bias, L, 0.0f, light_dist - bias);
              if (scene::traceSceneAnyHit(scene, shadow_ray, hit.instance_id,
                                          hit.triangle_id, ray_time))
                continue;

              lightrt::Vec3 brdf_ndl = evalBRDF(N, V, L, mat);

              // Light attenuation
              lightrt::Vec3 light_contribution = light.color;
              if (light.type == scene::LightData::Point) {
                float inv_r2 = 1.0f / (light_dist * light_dist);
                light_contribution = light_contribution * inv_r2;
              }

              color = color + lightrt::Vec3(
                brdf_ndl.x * light_contribution.x,
                brdf_ndl.y * light_contribution.y,
                brdf_ndl.z * light_contribution.z);
            }

            // Envmap MIS (if dome light exists)
            if (has_envmap) {
              float alpha = std::max(0.001f, mat.roughness * mat.roughness);
              lightrt::Vec3 T, B;
              buildONB(N, T, B);

              // 1) Envmap sample
              {
                float env_pdf = 0.0f;
                lightrt::Vec3 L = sampleEnvmap(scene.envmap, dist01(rng), dist01(rng), env_pdf);
                float NdotL = N.dot(L);
                if (NdotL > 0.0f && env_pdf > 1e-8f) {
                  lightrt::Ray shadow_ray(hit_pos + N * bias, L);
                  if (!scene::traceSceneAnyHit(scene, shadow_ray, hit.instance_id,
                                               hit.triangle_id, ray_time)) {
                    lightrt::Vec3 brdf_ndl = evalBRDF(N, V, L, mat);
                    lightrt::Vec3 env_col = evalEnvmap(scene.envmap, L);
                    // BRDF PDF for this direction
                    lightrt::Vec3 H = (V + L).normalize();
                    float NdotH = std::max(0.0f, N.dot(H));
                    float VdotH = std::max(0.0f, V.dot(H));
                    float brdf_pdf = pdfGGX(NdotH, VdotH, alpha);
                    // Add diffuse PDF component
                    float combined_brdf_pdf = 0.5f * brdf_pdf + 0.5f * NdotL * kInvPi;
                    float w = misBalance(env_pdf, combined_brdf_pdf);
                    lightrt::Vec3 contrib(
                      brdf_ndl.x * env_col.x * w / env_pdf,
                      brdf_ndl.y * env_col.y * w / env_pdf,
                      brdf_ndl.z * env_col.z * w / env_pdf);
                    color = color + contrib;
                  }
                }
              }

              // 2) BRDF sample
              {
                // Choose diffuse or specular sampling
                bool sample_diffuse = dist01(rng) < 0.5f;
                lightrt::Vec3 L;
                if (sample_diffuse) {
                  // Cosine-weighted hemisphere
                  float r1 = dist01(rng), r2 = dist01(rng);
                  float cos_theta = std::sqrt(1.0f - r1);
                  float sin_theta = std::sqrt(r1);
                  float phi = 2.0f * kPi * r2;
                  lightrt::Vec3 local(sin_theta * std::cos(phi), sin_theta * std::sin(phi), cos_theta);
                  L = toWorld(local, N, T, B);
                } else {
                  // GGX importance sampling
                  lightrt::Vec3 H_local = sampleGGX(dist01(rng), dist01(rng), alpha);
                  lightrt::Vec3 H = toWorld(H_local, N, T, B);
                  L = V * -1.0f + H * (2.0f * V.dot(H)); // reflect
                  L = L.normalize();
                }

                float NdotL = N.dot(L);
                if (NdotL > 0.0f) {
                  lightrt::Ray shadow_ray(hit_pos + N * bias, L);
                  if (!scene::traceSceneAnyHit(scene, shadow_ray, hit.instance_id,
                                               hit.triangle_id, ray_time)) {
                    lightrt::Vec3 brdf_ndl = evalBRDF(N, V, L, mat);
                    lightrt::Vec3 env_col = evalEnvmap(scene.envmap, L);
                    lightrt::Vec3 H = (V + L).normalize();
                    float NdotH = std::max(0.0f, N.dot(H));
                    float VdotH = std::max(0.0f, V.dot(H));
                    float brdf_pdf = pdfGGX(NdotH, VdotH, alpha);
                    float combined_brdf_pdf = 0.5f * brdf_pdf + 0.5f * NdotL * kInvPi;
                    float env_pdf = envmapPDF(scene.envmap, L);
                    float w = misBalance(combined_brdf_pdf, env_pdf);
                    if (combined_brdf_pdf > 1e-8f) {
                      lightrt::Vec3 contrib(
                        brdf_ndl.x * env_col.x * w / combined_brdf_pdf,
                        brdf_ndl.y * env_col.y * w / combined_brdf_pdf,
                        brdf_ndl.z * env_col.z * w / combined_brdf_pdf);
                      color = color + contrib;
                    }
                  }
                }
              }
            }
          }
        }

        r_acc += color.x;
        g_acc += color.y;
        b_acc += color.z;
      }

      float inv_s = 1.0f / static_cast<float>(total_samples);
      float r = r_acc * inv_s;
      float g = g_acc * inv_s;
      float b = b_acc * inv_s;

      // Reinhard tone mapping
      r = r / (r + 1.0f);
      g = g / (g + 1.0f);
      b = b / (b + 1.0f);

      // Gamma 2.2
      r = std::pow(std::max(0.0f, r), 1.0f / 2.2f);
      g = std::pow(std::max(0.0f, g), 1.0f / 2.2f);
      b = std::pow(std::max(0.0f, b), 1.0f / 2.2f);

      uint8_t cr = static_cast<uint8_t>(std::min(255.0f, r * 255.0f));
      uint8_t cg = static_cast<uint8_t>(std::min(255.0f, g * 255.0f));
      uint8_t cb = static_cast<uint8_t>(std::min(255.0f, b * 255.0f));
      image[y * opts.width + x] = lightrt::RGB8(cr, cg, cb);
    }
  }
}

int main(int argc, char** argv) {
  Options opts;
  if (!parseArgs(argc, argv, opts)) return 1;

  auto renderOneFrame = [&](double timecode, const std::string& outpath) -> bool {
    scene::Scene scene;
    if (!loadUSDScene(opts.input_file, timecode, scene)) return false;

    // Apply motion blur if a camera has shutter interval
    double shutter_offset = 0.0;
    if (!scene.cameras.empty()) {
      int cam_idx = 0;
      if (opts.camera_index >= 0 && opts.camera_index < static_cast<int>(scene.cameras.size()))
        cam_idx = opts.camera_index;
      else if (!opts.camera_name.empty()) {
        for (size_t i = 0; i < scene.cameras.size(); i++) {
          if (scene.cameras[i].name == opts.camera_name) { cam_idx = static_cast<int>(i); break; }
        }
      }
      shutter_offset = scene.cameras[cam_idx].shutter_close - scene.cameras[cam_idx].shutter_open;
    }
    if (opts.mblur_samples > 1 && shutter_offset > 0.0) {
      applyMotionBlur(opts.input_file, timecode, shutter_offset, scene);
    }

    // Setup camera
    lightrt::Vec3 cam_pos, cam_dir, cam_up;
    float fov_y = 45.0f * 3.14159265f / 180.0f;

    int cam_idx = -1;
    if (opts.camera_index >= 0 && opts.camera_index < static_cast<int>(scene.cameras.size())) {
      cam_idx = opts.camera_index;
    } else if (!opts.camera_name.empty()) {
      for (size_t i = 0; i < scene.cameras.size(); i++) {
        if (scene.cameras[i].name == opts.camera_name) { cam_idx = static_cast<int>(i); break; }
      }
    } else if (!scene.cameras.empty()) {
      cam_idx = 0;
    }

    if (cam_idx >= 0) {
      const auto& cam = scene.cameras[cam_idx];
      fov_y = cam.fov_y_rad;
      const float* m = cam.transform;
      cam_pos = lightrt::Vec3(m[3], m[7], m[11]);
      cam_dir = lightrt::Vec3(-m[2], -m[6], -m[10]).normalize();
      cam_up = lightrt::Vec3(m[1], m[5], m[9]).normalize();
      printf("Using camera '%s' (fov=%.1f deg)\n", cam.name.c_str(),
             fov_y * 180.0f / 3.14159265f);
    } else {
      lightrt::Vec3 center = (scene.scene_bounds.min + scene.scene_bounds.max) * 0.5f;
      lightrt::Vec3 extent = scene.scene_bounds.max - scene.scene_bounds.min;
      float scene_radius = extent.length() * 0.5f;
      cam_pos = center + lightrt::Vec3(0.0f, 0.0f, scene_radius * 2.5f);
      cam_dir = (center - cam_pos).normalize();
      cam_up = lightrt::Vec3(0.0f, 1.0f, 0.0f);
    }

    lightrt::Vec3 cam_right = cam_dir.cross(cam_up).normalize();
    cam_up = cam_right.cross(cam_dir).normalize();

    float aspect = static_cast<float>(opts.width) / opts.height;
    float half_h = tanf(fov_y * 0.5f);
    float half_w = half_h * aspect;

    // Render
    std::vector<lightrt::RGB8> image;
    auto t2 = std::chrono::high_resolution_clock::now();
    renderFrame(scene, opts, cam_pos, cam_dir, cam_right, cam_up,
                half_w, half_h, image);
    auto t3 = std::chrono::high_resolution_clock::now();
    double render_ms = std::chrono::duration<double, std::milli>(t3 - t2).count();
    printf("Rendered %ux%u (%u spp, %u mblur) in %.1f ms\n",
           opts.width, opts.height, opts.spp, opts.mblur_samples, render_ms);

    if (!writeImage(outpath, image, opts.width, opts.height)) return false;
    printf("Wrote %s\n", outpath.c_str());
    return true;
  };

  if (opts.has_time_range) {
    std::string base = opts.output_file;
    std::string ext;
    auto dot = base.rfind('.');
    if (dot != std::string::npos) {
      ext = base.substr(dot);
      base = base.substr(0, dot);
    }

    int frame_num = 1;
    for (double tc = opts.time_range_start; tc <= opts.time_range_end + 1e-6;
         tc += opts.time_range_step, frame_num++) {
      char buf[16];
      snprintf(buf, sizeof(buf), "_%04d", frame_num);
      std::string outpath = base + buf + ext;
      printf("\n=== Frame %d (timecode=%.1f) ===\n", frame_num, tc);
      if (!renderOneFrame(tc, outpath)) {
        fprintf(stderr, "Failed to render frame at timecode %.1f\n", tc);
      }
    }
  } else {
    double tc = opts.timecode;
    if (!renderOneFrame(tc, opts.output_file)) return 1;
  }

  return 0;
}
