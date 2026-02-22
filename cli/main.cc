// LightRT CLI renderer with USD loading via TinyUSDZ
// Usage: lightrt_cli input.usd [-o output.png] [-w 800] [-h 600]

#include "lightrt.hh"

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

struct Options {
  std::string input_file;
  std::string output_file = "output.png";
  uint32_t width = 800;
  uint32_t height = 600;
};

static bool parseArgs(int argc, char** argv, Options& opts) {
  if (argc < 2) {
    fprintf(stderr, "Usage: %s input.usd [-o output.png] [-w 800] [-h 600]\n",
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
    }
  }
  return true;
}

static bool loadUSD(const std::string& filename,
                    std::vector<lightrt::Triangle>& triangles) {
  std::string warn, err;
  tinyusdz::Stage stage;

  bool ret = tinyusdz::LoadUSDFromFile(filename, &stage, &warn, &err);
  if (!warn.empty()) fprintf(stderr, "USD warn: %s\n", warn.c_str());
  if (!ret) {
    fprintf(stderr, "USD load error: %s\n", err.c_str());
    return false;
  }

  tinyusdz::tydra::RenderScene render_scene;
  tinyusdz::tydra::RenderSceneConverter converter;
  tinyusdz::tydra::RenderSceneConverterEnv env(stage);
  env.mesh_config.triangulate = true;

  ret = converter.ConvertToRenderScene(env, &render_scene);
  if (!ret) {
    fprintf(stderr, "Failed to convert USD to render scene\n");
    return false;
  }

  for (const auto& mesh : render_scene.meshes) {
    const auto& pts = mesh.points;
    const auto& idx = mesh.faceVertexIndices();

    if (idx.size() % 3 != 0) {
      fprintf(stderr, "Warning: non-triangulated mesh, skipping\n");
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
  }

  printf("Loaded %zu triangles from %zu meshes\n", triangles.size(),
         render_scene.meshes.size());
  return !triangles.empty();
}

int main(int argc, char** argv) {
  Options opts;
  if (!parseArgs(argc, argv, opts)) return 1;

  // Load USD
  std::vector<lightrt::Triangle> triangles;
  if (!loadUSD(opts.input_file, triangles)) return 1;

  // Build BVH
  auto t0 = std::chrono::high_resolution_clock::now();
  lightrt::TriangleBVH bvh;
  bvh.build(triangles);
  auto t1 = std::chrono::high_resolution_clock::now();
  double build_ms =
      std::chrono::duration<double, std::milli>(t1 - t0).count();
  auto stats = bvh.getBVH().getStats();
  printf("BVH built in %.1f ms (%u nodes)\n", build_ms, stats.num_nodes);

  // Compute scene bounds for camera setup
  lightrt::AABB bounds;
  for (const auto& tri : triangles) {
    bounds.expand(tri.v0);
    bounds.expand(tri.v1);
    bounds.expand(tri.v2);
  }
  lightrt::Vec3 center = (bounds.min + bounds.max) * 0.5f;
  lightrt::Vec3 extent = bounds.max - bounds.min;
  float scene_radius = extent.length() * 0.5f;

  // Camera: look at center from +Z
  lightrt::Vec3 cam_pos =
      center + lightrt::Vec3(0.0f, 0.0f, scene_radius * 2.5f);
  lightrt::Vec3 cam_dir = (center - cam_pos).normalize();
  lightrt::Vec3 cam_up(0.0f, 1.0f, 0.0f);
  lightrt::Vec3 cam_right = cam_dir.cross(cam_up).normalize();
  cam_up = cam_right.cross(cam_dir).normalize();

  float fov_y = 45.0f;
  float aspect = static_cast<float>(opts.width) / opts.height;
  float half_h = tanf(fov_y * 0.5f * 3.14159265f / 180.0f);
  float half_w = half_h * aspect;

  // Light direction (sun from upper-right-front)
  lightrt::Vec3 light_dir =
      lightrt::Vec3(0.5f, 0.8f, 0.3f).normalize();

  // Render
  std::vector<lightrt::RGB8> image(opts.width * opts.height);

  auto t2 = std::chrono::high_resolution_clock::now();
  for (uint32_t y = 0; y < opts.height; y++) {
    for (uint32_t x = 0; x < opts.width; x++) {
      float u = (2.0f * (x + 0.5f) / opts.width - 1.0f) * half_w;
      float v = (1.0f - 2.0f * (y + 0.5f) / opts.height) * half_h;

      lightrt::Vec3 dir =
          (cam_dir + cam_right * u + cam_up * v).normalize();
      lightrt::Ray ray(cam_pos, dir);

      float hit_t = std::numeric_limits<float>::max();
      float hit_u, hit_v;
      uint32_t hit_idx = bvh.traverse(ray, hit_t, hit_u, hit_v);

      lightrt::RGB8 color(30, 30, 40); // background
      if (hit_idx != lightrt::kInvalidIndex) {
        // Compute normal
        const auto& tri = triangles[hit_idx];
        lightrt::Vec3 e1 = tri.v1 - tri.v0;
        lightrt::Vec3 e2 = tri.v2 - tri.v0;
        lightrt::Vec3 normal = e1.cross(e2).normalize();

        // Face forward
        if (normal.dot(dir) > 0.0f) normal = normal * -1.0f;

        // Diffuse lighting
        float ndl = std::max(0.0f, normal.dot(light_dir));

        // Shadow ray
        lightrt::Vec3 hit_pos = cam_pos + dir * hit_t;
        lightrt::Ray shadow_ray(hit_pos + normal * 0.001f, light_dir);
        bool in_shadow = bvh.traverseAnyHit(shadow_ray, hit_idx);

        float ambient = 0.15f;
        float diffuse = in_shadow ? 0.0f : ndl * 0.85f;
        float shade = std::min(1.0f, ambient + diffuse);

        uint8_t c = static_cast<uint8_t>(shade * 255.0f);
        color = lightrt::RGB8(c, c, c);
      }
      image[y * opts.width + x] = color;
    }
  }
  auto t3 = std::chrono::high_resolution_clock::now();
  double render_ms =
      std::chrono::duration<double, std::milli>(t3 - t2).count();
  printf("Rendered %ux%u in %.1f ms\n", opts.width, opts.height, render_ms);

  // Write output - detect format from extension
  const char* outpath = opts.output_file.c_str();
  std::string ext;
  {
    auto dot = opts.output_file.rfind('.');
    if (dot != std::string::npos) {
      ext = opts.output_file.substr(dot);
      for (auto& c : ext) c = static_cast<char>(tolower(c));
    }
  }

  int ok = 0;
  int w = static_cast<int>(opts.width);
  int h = static_cast<int>(opts.height);
  const uint8_t* data = reinterpret_cast<const uint8_t*>(image.data());
  int stride = w * 3;

  if (ext == ".png") {
    ok = stbi_write_png(outpath, w, h, 3, data, stride);
  } else if (ext == ".jpg" || ext == ".jpeg") {
    ok = stbi_write_jpg(outpath, w, h, 3, data, 95);
  } else if (ext == ".bmp") {
    ok = stbi_write_bmp(outpath, w, h, 3, data);
  } else if (ext == ".tga") {
    ok = stbi_write_tga(outpath, w, h, 3, data);
  } else {
    fprintf(stderr, "Unknown output format '%s'. Use .png, .jpg, .bmp, or .tga\n", ext.c_str());
    return 1;
  }

  if (!ok) {
    fprintf(stderr, "Failed to write %s\n", outpath);
    return 1;
  }
  printf("Wrote %s\n", outpath);
  return 0;
}
