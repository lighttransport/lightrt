// LightRT CLI renderer with USD loading via TinyUSDZ
// Usage: lightrt_cli input.usd [-o output.png] [-w 800] [-h 600] [-t timecode]
//        [--time-range start end step] [--camera name_or_index]
//        [--mblur-samples N]

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
};

static bool parseArgs(int argc, char** argv, Options& opts) {
  if (argc < 2) {
    fprintf(stderr,
      "Usage: %s input.usd [-o output.png] [-w 800] [-h 600]\n"
      "       [-t timecode] [--time-range start end step]\n"
      "       [--camera name_or_index] [--mblur-samples N]\n",
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
      // Try as integer index first
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
    // Copy open transform to close (will be overwritten if motion blur)
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
    // Store camera with its node transform
    if (node.id < static_cast<int32_t>(render_scene.cameras.size())) {
      const auto& rc = render_scene.cameras[static_cast<size_t>(node.id)];
      scene::Camera cam;
      cam.name = rc.name;
      cam.fov_y_rad = 2.0f * std::atan(0.5f * rc.verticalAperture / rc.focalLength);
      cam.znear = rc.znear;
      cam.zfar = rc.zfar;
      cam.shutter_open = rc.shutterOpen;
      cam.shutter_close = rc.shutterClose;
      // Store full 4x4 transform
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

  // Determine timecode
  if (timecode < -1e29) {
    // Use stage default
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

  // Build per-mesh BLAS
  out_scene.meshes.resize(render_scene.meshes.size());
  for (size_t mi = 0; mi < render_scene.meshes.size(); mi++) {
    const auto& mesh = render_scene.meshes[mi];
    const auto& pts = mesh.points;
    const auto& idx = mesh.faceVertexIndices();

    std::vector<lightrt::Triangle> triangles;
    if (idx.size() % 3 != 0) {
      fprintf(stderr, "Warning: non-triangulated mesh %zu, skipping\n", mi);
      continue;
    }
    for (size_t i = 0; i + 2 < idx.size(); i += 3) {
      uint32_t i0 = idx[i], i1 = idx[i + 1], i2 = idx[i + 2];
      if (i0 >= pts.size() || i1 >= pts.size() || i2 >= pts.size()) continue;
      lightrt::Triangle tri;
      tri.v0 = lightrt::Vec3(pts[i0][0], pts[i0][1], pts[i0][2]);
      tri.v1 = lightrt::Vec3(pts[i1][0], pts[i1][1], pts[i1][2]);
      tri.v2 = lightrt::Vec3(pts[i2][0], pts[i2][1], pts[i2][2]);
      triangles.push_back(tri);
    }
    if (triangles.empty()) continue;

    // Compute local bounds
    lightrt::AABB& lb = out_scene.meshes[mi].local_bounds;
    for (const auto& tri : triangles) {
      lb.expand(tri.v0);
      lb.expand(tri.v1);
      lb.expand(tri.v2);
    }

    out_scene.meshes[mi].bvh.build(triangles);
  }

  // Walk node tree to create instances and find cameras
  std::vector<int> camera_node_indices;
  for (const auto& root_node : render_scene.nodes) {
    walkNodes(render_scene, root_node, out_scene, camera_node_indices);
  }

  // If no instances were created (flat scene), create identity instances for all meshes
  if (out_scene.instances.empty()) {
    for (size_t mi = 0; mi < out_scene.meshes.size(); mi++) {
      // Skip meshes with no triangles
      if (out_scene.meshes[mi].local_bounds.min.x > out_scene.meshes[mi].local_bounds.max.x)
        continue;
      scene::Instance inst;
      inst.mesh_id = static_cast<uint32_t>(mi);
      // Identity 3x4
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

  // Walk nodes in same order and update close transforms
  uint32_t inst_idx = 0;
  std::function<void(const tinyusdz::tydra::Node&)> walkClose;
  walkClose = [&](const tinyusdz::tydra::Node& node) {
    if (node.nodeType == tinyusdz::tydra::NodeType::Mesh && node.id >= 0 &&
        inst_idx < static_cast<uint32_t>(scene.instances.size())) {
      auto& inst = scene.instances[inst_idx];
      float close_xform[12];
      scene::matrix4dTo3x4(node.global_matrix.m, close_xform);

      // Check if transforms differ
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
        // Expand world bounds to include close transform
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

static void renderFrame(const scene::Scene& scene, const Options& opts,
                        const lightrt::Vec3& cam_pos,
                        const lightrt::Vec3& cam_dir,
                        const lightrt::Vec3& cam_right,
                        const lightrt::Vec3& cam_up,
                        float half_w, float half_h,
                        const lightrt::Vec3& light_dir,
                        std::vector<lightrt::RGB8>& image) {
  image.resize(opts.width * opts.height);

  std::mt19937 rng(42);
  std::uniform_real_distribution<float> dist01(0.0f, 1.0f);
  uint32_t mblur = opts.mblur_samples;

  for (uint32_t y = 0; y < opts.height; y++) {
    for (uint32_t x = 0; x < opts.width; x++) {
      float r_acc = 0, g_acc = 0, b_acc = 0;

      for (uint32_t s = 0; s < mblur; s++) {
        float u = (2.0f * (x + 0.5f) / opts.width - 1.0f) * half_w;
        float v = (1.0f - 2.0f * (y + 0.5f) / opts.height) * half_h;

        lightrt::Vec3 dir = (cam_dir + cam_right * u + cam_up * v).normalize();
        lightrt::Ray ray(cam_pos, dir);

        float ray_time = (mblur > 1) ? dist01(rng) : 0.0f;

        scene::HitInfo hit = scene::traceScene(scene, ray, ray_time);

        float shade = 0.0f;
        if (hit.instance_id != lightrt::kInvalidIndex) {
          const auto& tris = scene.meshes[scene.instances[hit.instance_id].mesh_id].bvh.getTriangles();
          const auto& tri = tris[hit.triangle_id];
          lightrt::Vec3 e1 = tri.v1 - tri.v0;
          lightrt::Vec3 e2 = tri.v2 - tri.v0;
          lightrt::Vec3 normal = e1.cross(e2).normalize();
          if (normal.dot(dir) > 0.0f) normal = normal * -1.0f;

          float ndl = std::max(0.0f, normal.dot(light_dir));
          lightrt::Vec3 hit_pos = cam_pos + dir * hit.t;
          lightrt::Ray shadow_ray(hit_pos + normal * 0.001f, light_dir);
          bool in_shadow = scene::traceSceneAnyHit(scene, shadow_ray,
            hit.instance_id, hit.triangle_id, ray_time);

          float ambient = 0.15f;
          float diffuse = in_shadow ? 0.0f : ndl * 0.85f;
          shade = std::min(1.0f, ambient + diffuse);
        } else {
          // Background
          r_acc += 30; g_acc += 30; b_acc += 40;
          continue;
        }
        float c = shade * 255.0f;
        r_acc += c; g_acc += c; b_acc += c;
      }

      float inv_s = 1.0f / mblur;
      uint8_t cr = static_cast<uint8_t>(std::min(255.0f, r_acc * inv_s));
      uint8_t cg = static_cast<uint8_t>(std::min(255.0f, g_acc * inv_s));
      uint8_t cb = static_cast<uint8_t>(std::min(255.0f, b_acc * inv_s));
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
      // Find selected camera's shutter
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

    // Build BVH timing
    auto t0 = std::chrono::high_resolution_clock::now();
    // BVHs already built in loadUSDScene
    auto t1 = std::chrono::high_resolution_clock::now();

    // Setup camera
    lightrt::Vec3 cam_pos, cam_dir, cam_up;
    float fov_y = 45.0f * 3.14159265f / 180.0f;

    // Select camera
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
      // Translation = column 3 of row-major 4x4
      cam_pos = lightrt::Vec3(m[3], m[7], m[11]);
      // USD cameras look down -Z in local space
      cam_dir = lightrt::Vec3(-m[2], -m[6], -m[10]).normalize();
      cam_up = lightrt::Vec3(m[1], m[5], m[9]).normalize();
      printf("Using camera '%s' (fov=%.1f°)\n", cam.name.c_str(),
             fov_y * 180.0f / 3.14159265f);
    } else {
      // Auto camera: look at center from +Z
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

    lightrt::Vec3 light_dir = lightrt::Vec3(0.5f, 0.8f, 0.3f).normalize();

    // Render
    std::vector<lightrt::RGB8> image;
    auto t2 = std::chrono::high_resolution_clock::now();
    renderFrame(scene, opts, cam_pos, cam_dir, cam_right, cam_up,
                half_w, half_h, light_dir, image);
    auto t3 = std::chrono::high_resolution_clock::now();
    double render_ms = std::chrono::duration<double, std::milli>(t3 - t2).count();
    printf("Rendered %ux%u in %.1f ms\n", opts.width, opts.height, render_ms);

    if (!writeImage(outpath, image, opts.width, opts.height)) return false;
    printf("Wrote %s\n", outpath.c_str());
    return true;
  };

  if (opts.has_time_range) {
    // Sequence rendering
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
