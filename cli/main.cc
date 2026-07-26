// LightRT CLI renderer with USD loading via TinyUSDZ or lightusd-c
// Usage: lightrt_cli input.usd [-o output.png] [-w 800] [-h 600] [-t timecode]
//        [--time-range start end step] [--camera name_or_index]
//        [--mblur-samples N] [--spp N]
//
// Build with -DLIGHTRT_USE_LIGHTUSD_C=ON to use lightusd-c + lydra backend.

#include "scene.hh"
#include "common/usd_loader.hh"
#include "common/renderer.hh"

#include "stb_image.h"
#include "stb_image_write.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <cmath>
#include <chrono>

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
  std::string envmap_file;
  int camera_index = -1; // -1 = auto
  bool fallback_camera = false;
  uint32_t mblur_samples = 1;
  uint32_t spp = 1;
  uint32_t curve_segments = 8;
  bool geometry_only = false;
  bool compose = false;
  bool load_only = false;
};

static void enableGeometryOnlyMode() {
#if defined(_WIN32)
  _putenv_s("LIGHTRT_USD_GEOMETRY_ONLY", "1");
#else
  setenv("LIGHTRT_USD_GEOMETRY_ONLY", "1", 1);
#endif
}

static void enableCompositionMode() {
#if defined(_WIN32)
  _putenv_s("LIGHTRT_USD_COMPOSE", "1");
#else
  setenv("LIGHTRT_USD_COMPOSE", "1", 1);
#endif
}

static void setCurveSegments(uint32_t segments) {
  char value[16];
  std::snprintf(value, sizeof(value), "%u", segments);
#if defined(_WIN32)
  _putenv_s("LIGHTRT_USD_CURVE_SEGMENTS", value);
#else
  setenv("LIGHTRT_USD_CURVE_SEGMENTS", value, 1);
#endif
}

static bool parseArgs(int argc, char** argv, Options& opts) {
  if (argc < 2) {
    fprintf(stderr,
      "Usage: %s input.usd [-o output.png] [-w 800] [-h 600]\n"
      "       [-t timecode] [--time-range start end step]\n"
      "       [--camera name_or_index] [--mblur-samples N] [--spp N]\n"
      "       [--compose] [--curve-segments N] [--geometry-only] [--load-only]\n",
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
      if (strcmp(argv[i], "fallback") == 0) {
        opts.fallback_camera = true;
        continue;
      }
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
    } else if (strcmp(argv[i], "--envmap") == 0 && i + 1 < argc) {
      opts.envmap_file = argv[++i];
    } else if (strcmp(argv[i], "--geometry-only") == 0) {
      opts.geometry_only = true;
    } else if (strcmp(argv[i], "--compose") == 0) {
      opts.compose = true;
    } else if (strcmp(argv[i], "--curve-segments") == 0 && i + 1 < argc) {
      const int requested = atoi(argv[++i]);
      if (requested < 1 || requested > 64) {
        fprintf(stderr, "Curve segments must be between 1 and 64\n");
        return false;
      }
      opts.curve_segments = static_cast<uint32_t>(requested);
    } else if (strcmp(argv[i], "--load-only") == 0) {
      opts.load_only = true;
    } else {
      fprintf(stderr, "Unknown or incomplete option: %s\n", argv[i]);
      return false;
    }
  }
  if (opts.width == 0 || opts.height == 0) {
    fprintf(stderr, "Image dimensions must be greater than zero\n");
    return false;
  }
  if (opts.has_time_range && opts.time_range_step <= 0.0) {
    fprintf(stderr, "Time-range step must be greater than zero\n");
    return false;
  }
  return true;
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

int main(int argc, char** argv) {
  Options opts;
  if (!parseArgs(argc, argv, opts)) return 1;
  if (opts.geometry_only) enableGeometryOnlyMode();
  if (opts.compose) enableCompositionMode();
  setCurveSegments(opts.curve_segments);

  auto renderOneFrame = [&](double timecode, const std::string& outpath) -> bool {
    scene::Scene scene;
    auto load_begin = std::chrono::high_resolution_clock::now();
    if (!lightrt_common::loadUSDScene(opts.input_file, timecode, scene)) return false;
    auto load_end = std::chrono::high_resolution_clock::now();
    double load_ms = std::chrono::duration<double, std::milli>(
                         load_end - load_begin).count();
    printf("USD load + CPU BVH build: %.1f ms\n", load_ms);
    if (opts.load_only) return true;

    // CLI --envmap override: load HDR/EXR and set as environment map
    if (!opts.envmap_file.empty() && !scene.envmap.valid()) {
      int w, h, ch;
      float* hdr = stbi_loadf(opts.envmap_file.c_str(), &w, &h, &ch, 3);
      if (hdr) {
        scene::EnvmapData& env = scene.envmap;
        env.width = w; env.height = h;
        env.pixels.assign(hdr, hdr + (size_t)w * h * 3);
        stbi_image_free(hdr);
        scene::shading::buildEnvmapCDF(env);
        printf("Loaded envmap %dx%d from %s\n", w, h, opts.envmap_file.c_str());
      } else {
        fprintf(stderr, "Warning: failed to load envmap '%s'\n", opts.envmap_file.c_str());
      }
    }

    // Apply motion blur if a camera has shutter interval
    double shutter_open = 0.0;
    double shutter_close = 0.0;
    if (!scene.cameras.empty()) {
      int cam_idx = 0;
      if (opts.camera_index >= 0 && opts.camera_index < static_cast<int>(scene.cameras.size()))
        cam_idx = opts.camera_index;
      else if (!opts.camera_name.empty()) {
        for (size_t i = 0; i < scene.cameras.size(); i++) {
          if (scene.cameras[i].name == opts.camera_name) { cam_idx = static_cast<int>(i); break; }
        }
      }
      shutter_open = scene.cameras[cam_idx].shutter_open;
      shutter_close = scene.cameras[cam_idx].shutter_close;
    }
    if (opts.mblur_samples > 1 && shutter_close > shutter_open) {
      lightrt_common::applyMotionBlur(opts.input_file, timecode,
                                     shutter_open, shutter_close, scene);
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
    } else if (!opts.fallback_camera && !scene.cameras.empty()) {
      cam_idx = 0;
    }

    if (cam_idx >= 0) {
      const auto& cam = scene.cameras[cam_idx];
      fov_y = cam.fov_y_rad;
      const float* m = cam.transform;
      // Row-major, column-vector transform, consistent with scene transforms.
      cam_pos = lightrt::Vec3(m[3], m[7], m[11]);
      cam_dir = lightrt::Vec3(-m[2], -m[6], -m[10]).normalize();
      cam_up  = lightrt::Vec3( m[1],  m[5],  m[9]).normalize();
      printf("Using camera '%s' (fov=%.1f deg)\n",
             cam.name.c_str(), fov_y * 180.0f / 3.14159265f);
    } else {
      lightrt::Vec3 center = (scene.scene_bounds.min + scene.scene_bounds.max) * 0.5f;
      lightrt::Vec3 extent = scene.scene_bounds.max - scene.scene_bounds.min;
      float scene_radius = extent.length() * 0.5f;
      float vertical_extent = extent.y;
      float horizontal_extent = std::sqrt(extent.x * extent.x + extent.z * extent.z);
      if (scene.up_axis == 1) {
        vertical_extent = extent.z;
        horizontal_extent = std::sqrt(extent.x * extent.x + extent.y * extent.y);
      } else if (scene.up_axis == 2) {
        vertical_extent = extent.x;
        horizontal_extent = std::sqrt(extent.y * extent.y + extent.z * extent.z);
      }
      bool is_flat = (horizontal_extent > 1e-4f) &&
                     (vertical_extent < horizontal_extent * 0.15f);
      float d = std::max(scene_radius * 2.5f, 1.0f);
      if (scene.up_axis == 1) {
        cam_pos = center + lightrt::Vec3(0.0f, -d * 0.8f,
                                        is_flat ? d * 0.6f : d * 0.3f);
      } else if (scene.up_axis == 2) {
        cam_pos = center + lightrt::Vec3(is_flat ? d * 0.6f : d * 0.3f,
                                        0.0f, d * 0.8f);
      } else if (is_flat) {
        cam_pos = center + lightrt::Vec3(0.0f, d * 0.6f, d * 0.8f);
      } else {
        cam_pos = center + lightrt::Vec3(0.0f, 0.0f, scene_radius * 2.5f);
      }
      cam_dir = (center - cam_pos).normalize();
      // Respect USD upAxis for fallback camera orientation.
      if (scene.up_axis == 1) {
        // Z-up
        cam_up = lightrt::Vec3(0.0f, 0.0f, 1.0f);
      } else if (scene.up_axis == 2) {
        // X-up
        cam_up = lightrt::Vec3(1.0f, 0.0f, 0.0f);
      } else {
        // Y-up (default)
        cam_up = lightrt::Vec3(0.0f, 1.0f, 0.0f);
      }
    }

    lightrt::Vec3 cam_right = cam_dir.cross(cam_up).normalize();
    cam_up = cam_right.cross(cam_dir).normalize();

    float aspect = static_cast<float>(opts.width) / opts.height;
    float half_h = tanf(fov_y * 0.5f);
    float half_w = half_h * aspect;

    lightrt_common::RenderSettings settings;
    settings.width = opts.width;
    settings.height = opts.height;
    settings.spp = opts.spp;
    settings.mblur_samples = opts.mblur_samples;

    lightrt_common::CameraView cam_view;
    cam_view.position  = cam_pos;
    cam_view.direction = cam_dir;
    cam_view.right     = cam_right;
    cam_view.up        = cam_up;
    cam_view.half_width  = half_w;
    cam_view.half_height = half_h;

    // Render
    std::vector<lightrt::RGB8> image;
    auto t2 = std::chrono::high_resolution_clock::now();
    lightrt_common::renderFrame(scene, settings, cam_view, image);
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
