// Shared USD scene loader implementation.
#include "common/usd_loader.hh"

#include "lightrt.hh"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <map>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

#if defined(LIGHTRT_USE_LIGHTUSD_C)
// lightusd-c Layer API + lydra-c mesh utilities
extern "C" {
#include "lightusd/lightusd-c.h"
#include "internal/lusd_layer_internal.h"
#include "lydra_c_scene.h"
#include "lydra_c_mesh.h"
#include "lydra_c_curves.h"
}

#include "stb_image.h"
#else
#if defined(LIGHTRT_HAS_TINYUSDZ)
#include "tinyusdz.hh"
#include "tydra/render-data.hh"
#include "tydra/scene-access.hh"
#endif
#endif

namespace lightrt_common {

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
  return {static_cast<int32_t>(x * 1e4f), static_cast<int32_t>(y * 1e4f), static_cast<int32_t>(z * 1e4f)};
}

#if defined(LIGHTRT_USE_LIGHTUSD_C)

static LusdResult host_read_file(void*, const char* path, uint8_t** out_data,
                                 uint64_t* out_size) {
  if (!path || !out_data || !out_size) return LUSD_ERROR_INVALID_ARGUMENT;
  FILE* file = std::fopen(path, "rb");
  if (!file) return LUSD_ERROR_FILE_NOT_FOUND;
#if defined(_WIN32)
  if (_fseeki64(file, 0, SEEK_END) != 0) { std::fclose(file); return LUSD_ERROR_IO_FAILED; }
  const __int64 end = _ftelli64(file);
  if (end <= 0 || _fseeki64(file, 0, SEEK_SET) != 0) {
#else
  if (fseeko(file, 0, SEEK_END) != 0) { std::fclose(file); return LUSD_ERROR_IO_FAILED; }
  const off_t end = ftello(file);
  if (end <= 0 || fseeko(file, 0, SEEK_SET) != 0) {
#endif
    std::fclose(file);
    return LUSD_ERROR_IO_FAILED;
  }
  const uint64_t size = static_cast<uint64_t>(end);
  if (size > static_cast<uint64_t>(SIZE_MAX)) {
    std::fclose(file);
    return LUSD_ERROR_OUT_OF_MEMORY;
  }
  uint8_t* data = static_cast<uint8_t*>(std::malloc(static_cast<size_t>(size)));
  if (!data) { std::fclose(file); return LUSD_ERROR_OUT_OF_MEMORY; }
  const size_t read_size = std::fread(data, 1, static_cast<size_t>(size), file);
  std::fclose(file);
  if (read_size != static_cast<size_t>(size)) {
    std::free(data);
    return LUSD_ERROR_IO_FAILED;
  }
  *out_data = data;
  *out_size = size;
  return LUSD_SUCCESS;
}

static void host_release_file(void*, uint8_t* data, uint64_t) {
  std::free(data);
}

static const LusdFilesystemCallbacks kHostFilesystem = {
    nullptr, host_read_file, host_release_file, nullptr, true};

struct FlattenedBuffer {
  uint8_t* data = nullptr;
  uint64_t size = 0;
};

static LusdResult flattened_read_file(void* user, const char*,
                                      uint8_t** out_data,
                                      uint64_t* out_size) {
  auto* buffer = static_cast<FlattenedBuffer*>(user);
  if (!buffer || !buffer->data || !out_data || !out_size)
    return LUSD_ERROR_INVALID_ARGUMENT;
  *out_data = buffer->data;
  *out_size = buffer->size;
  return LUSD_SUCCESS;
}

static void flattened_release_file(void* user, uint8_t* data, uint64_t) {
  auto* buffer = static_cast<FlattenedBuffer*>(user);
  if (buffer && buffer->data == data) buffer->data = nullptr;
  lusd_free(data);
}

static void collect_materials(LusdLayer_T* L, const LusdPrim_T* P,
                              scene::Scene& out_scene,
                              std::map<std::string, int>& mat_map,
                              const std::string& usd_base_dir,
                              std::map<std::string, int>& tex_map) {
  if (P->type_name && strcmp(P->type_name, "Material") == 0) {
    LydraCOpenPBRData pbr;
    LusdResult r = lydra_c_extract_openpbr(
        reinterpret_cast<LusdLayer>(L),
        reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
        &pbr);
    if (r == LUSD_SUCCESS) {
      const char* prim_path = nullptr;
      if (P->spec_index < L->spec_count) {
        uint32_t pi = L->specs[P->spec_index].path_index;
        if (pi < L->path_count) prim_path = L->paths[pi];
      }
      if (prim_path) {
        int idx = static_cast<int>(out_scene.materials.size());
        mat_map[prim_path] = idx;

        scene::MaterialData mat;
        mat.base_weight            = pbr.base_weight;
        mat.base_color             = lightrt::Vec3(pbr.base_color[0], pbr.base_color[1], pbr.base_color[2]);
        mat.base_roughness         = pbr.base_roughness;
        mat.base_metalness         = pbr.base_metalness;
        mat.base_diffuse_roughness = pbr.base_diffuse_roughness;
        mat.specular_weight        = pbr.specular_weight;
        mat.specular_color         = lightrt::Vec3(pbr.specular_color[0], pbr.specular_color[1], pbr.specular_color[2]);
        mat.specular_roughness     = pbr.specular_roughness;
        mat.specular_ior           = pbr.specular_ior;
        mat.specular_ior_level     = pbr.specular_ior_level;
        mat.specular_anisotropy    = pbr.specular_anisotropy;
        mat.specular_rotation      = pbr.specular_rotation;
        mat.transmission_weight    = pbr.transmission_weight;
        mat.transmission_color     = lightrt::Vec3(pbr.transmission_color[0], pbr.transmission_color[1], pbr.transmission_color[2]);
        mat.transmission_depth     = pbr.transmission_depth;
        mat.transmission_scatter   = lightrt::Vec3(pbr.transmission_scatter[0], pbr.transmission_scatter[1], pbr.transmission_scatter[2]);
        mat.transmission_scatter_anisotropy = pbr.transmission_scatter_anisotropy;
        mat.transmission_dispersion = pbr.transmission_dispersion;
        mat.subsurface_weight      = pbr.subsurface_weight;
        mat.subsurface_color       = lightrt::Vec3(pbr.subsurface_color[0], pbr.subsurface_color[1], pbr.subsurface_color[2]);
        mat.subsurface_radius      = pbr.subsurface_radius;
        mat.subsurface_radius_scale = lightrt::Vec3(pbr.subsurface_radius_scale[0], pbr.subsurface_radius_scale[1], pbr.subsurface_radius_scale[2]);
        mat.subsurface_scale       = pbr.subsurface_scale;
        mat.subsurface_anisotropy  = pbr.subsurface_anisotropy;
        mat.sheen_weight           = pbr.sheen_weight;
        mat.sheen_color            = lightrt::Vec3(pbr.sheen_color[0], pbr.sheen_color[1], pbr.sheen_color[2]);
        mat.sheen_roughness        = pbr.sheen_roughness;
        mat.fuzz_weight            = pbr.fuzz_weight;
        mat.fuzz_color             = lightrt::Vec3(pbr.fuzz_color[0], pbr.fuzz_color[1], pbr.fuzz_color[2]);
        mat.fuzz_roughness         = pbr.fuzz_roughness;
        mat.thin_film_weight       = pbr.thin_film_weight;
        mat.thin_film_thickness    = pbr.thin_film_thickness;
        mat.thin_film_ior          = pbr.thin_film_ior;
        mat.coat_weight            = pbr.coat_weight;
        mat.coat_color             = lightrt::Vec3(pbr.coat_color[0], pbr.coat_color[1], pbr.coat_color[2]);
        mat.coat_roughness         = pbr.coat_roughness;
        mat.coat_anisotropy        = pbr.coat_anisotropy;
        mat.coat_rotation          = pbr.coat_rotation;
        mat.coat_ior               = pbr.coat_ior;
        mat.coat_affect_color      = lightrt::Vec3(pbr.coat_affect_color[0], pbr.coat_affect_color[1], pbr.coat_affect_color[2]);
        mat.coat_affect_roughness  = pbr.coat_affect_roughness;
        mat.emission_luminance     = pbr.emission_luminance;
        mat.emission_color         = lightrt::Vec3(pbr.emission_color[0], pbr.emission_color[1], pbr.emission_color[2]);
        mat.opacity                = pbr.opacity;

        auto load_tex = [&](const char* tex_path, int32_t& tex_id, bool is_srgb) {
          if (!tex_path) return;
          char resolved[1024];
          const char* rp = lydra_c_resolve_asset_path(
              usd_base_dir.c_str(), tex_path, resolved, sizeof(resolved));
          if (!rp) return;
          std::string rpath(rp);
          auto tex_it = tex_map.find(rpath);
          if (tex_it != tex_map.end()) { tex_id = tex_it->second; return; }
          int tw = 0, th = 0, tch = 0;
          unsigned char* pixels = stbi_load(rpath.c_str(), &tw, &th, &tch, 4);
          if (!pixels) return;
          int img_idx = static_cast<int>(out_scene.images.size());
          out_scene.images.emplace_back();
          auto& img = out_scene.images.back();
          img.width = tw; img.height = th;
          img.pixels.resize(static_cast<size_t>(tw) * th * 4);
          bool is_hdr = stbi_is_hdr(rpath.c_str());
          for (size_t pi = 0; pi < static_cast<size_t>(tw) * th * 4; pi++) {
            float v = pixels[pi] / 255.0f;
            if (is_srgb && !is_hdr && (pi % 4) < 3) v = std::pow(v, 2.2f);
            img.pixels[pi] = v;
          }
          stbi_image_free(pixels);
          tex_map[rpath] = img_idx;
          tex_id = img_idx;
          printf("    Texture[%d]: \"%s\" %dx%d%s\n", img_idx, rpath.c_str(), tw, th,
                 is_srgb ? "" : " [linear]");
        };
        load_tex(pbr.base_color_tex, mat.base_color_tex_id, true);
        load_tex(pbr.metalness_tex, mat.metalness_tex_id, false);
        load_tex(pbr.roughness_tex, mat.roughness_tex_id, false);
        load_tex(pbr.normal_tex, mat.normal_tex_id, false);
        load_tex(pbr.emissive_tex, mat.emissive_tex_id, true);
        load_tex(pbr.opacity_tex, mat.opacity_tex_id, false);

        out_scene.materials.push_back(mat);
        printf("  Material[%d]: \"%s\" base=(%.2f,%.2f,%.2f) metallic=%.2f roughness=%.2f%s\n",
               idx, prim_path,
               pbr.base_color[0], pbr.base_color[1], pbr.base_color[2],
               pbr.base_metalness, pbr.specular_roughness,
               pbr.is_openpbr ? " [OpenPBR]" : "");
      }
    }
  }
  for (uint32_t j = 0; j < P->child_count; j++)
    collect_materials(L, &L->prim_nodes[P->child_spec_indices[j]], out_scene, mat_map, usd_base_dir, tex_map);
}

static void mat4d_mul(const double A[16], const double B[16], double C[16]) {
  for (int r = 0; r < 4; r++)
    for (int c = 0; c < 4; c++) {
      double s = 0.0;
      for (int k = 0; k < 4; k++) s += A[r*4+k] * B[k*4+c];
      C[r*4+c] = s;
    }
}

static void mat4d_to_3x4f(const double m[16], float out[12]) {
  for (int r = 0; r < 3; r++)
    for (int c = 0; c < 4; c++)
      out[r*4+c] = static_cast<float>(m[r*4+c]);
}

static void mat4d_to_4x4f(const double m[16], float out[16]) {
  for (int i = 0; i < 16; i++) out[i] = static_cast<float>(m[i]);
}

static const double kIdentity4d[16] = {
  1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1
};

static bool loader_verbose() {
  const char* value = std::getenv("LIGHTRT_USD_VERBOSE");
  return value && value[0] == '1';
}

static bool loader_geometry_only() {
  const char* value = std::getenv("LIGHTRT_USD_GEOMETRY_ONLY");
  return value && value[0] == '1';
}

static bool loader_composition() {
  const char* value = std::getenv("LIGHTRT_USD_COMPOSE");
  return value && value[0] == '1';
}

static int32_t resolve_material_id(LusdLayer_T* L, const LusdPrim_T* P,
                                   const std::map<std::string, int>& mat_map) {
  const char* path = lydra_c_resolve_material_binding(
      reinterpret_cast<LusdLayer>(L),
      reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)));
  if (!path) return -1;
  auto it = mat_map.find(path);
  return it == mat_map.end() ? -1 : it->second;
}

static scene::Instance make_instance(const double world_xform[16],
                                     const lightrt::AABB& local_bounds) {
  scene::Instance inst;
  mat4d_to_3x4f(world_xform, inst.transform);
  scene::invert3x4(inst.transform, inst.inv_transform);
  std::memcpy(inst.transform_close, inst.transform, sizeof(inst.transform));
  std::memcpy(inst.inv_transform_close, inst.inv_transform,
              sizeof(inst.inv_transform));
  inst.has_motion = false;
  inst.world_bounds = scene::transformAABB(local_bounds, inst.transform);
  return inst;
}

static float curve_radius(const LydraCCurveData& data, uint32_t point_index,
                          uint32_t curve_index) {
  float width = 1.0f;
  if (data.width_count == 1) width = data.widths[0];
  else if (data.width_count == data.point_count) width = data.widths[point_index];
  else if (data.width_count == data.curve_count) width = data.widths[curve_index];
  return std::max(1.0e-6f, width * 0.5f);
}

static bool append_curve_set(LusdLayer_T* L, const LusdPrim_T* P,
                             scene::Scene& out_scene,
                             const std::map<std::string, int>& mat_map,
                             const double world_xform[16],
                             std::vector<lightrt::Curve>&& curves) {
  if (curves.empty()) return false;
  const uint32_t curve_mesh_id = static_cast<uint32_t>(out_scene.curve_meshes.size());
  out_scene.curve_meshes.emplace_back();
  auto& cb = out_scene.curve_meshes.back();
  lightrt::BVHBuildConfig cfg = curves.size() > 4096
                                    ? lightrt::BVHBuildConfig::fast()
                                    : lightrt::BVHBuildConfig();
  cb.build(curves, cfg);
  cb.default_material_id = resolve_material_id(L, P, mat_map);
  cb.curve_material_ids.assign(curves.size(), cb.default_material_id);

  scene::Instance inst = make_instance(world_xform, cb.local_bounds);
  inst.curve_mesh_id = curve_mesh_id;
  out_scene.scene_bounds.expand(inst.world_bounds);
  out_scene.instances.push_back(inst);
  return true;
}

static bool append_curve_prim(LusdLayer_T* L, const LusdPrim_T* P,
                              scene::Scene& out_scene,
                              const std::map<std::string, int>& mat_map,
                              const double world_xform[16]) {
  const bool is_hermite = P->type_name &&
                          std::strcmp(P->type_name, "HermiteCurves") == 0;

  // lightusd's renderer tessellator evaluates every BasisCurves wrap/basis
  // mode and rational NURBS (orders, knots, ranges, and point weights).
  if (!is_hermite) {
    LydraCTessellatedCurves tess = {};
    LusdResult result = lydra_c_extract_render_curves(
        reinterpret_cast<LusdLayer>(L),
        reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)), 8, &tess);
    if (result == LUSD_SUCCESS && tess.points && tess.point_count >= 2) {
      std::vector<lightrt::Curve> curves;
      curves.reserve(tess.curve_count);
      uint32_t offset = 0;
      for (uint32_t ci = 0; ci < tess.curve_count; ++ci) {
        uint32_t count = tess.vertex_counts[ci];
        if (count < 2 || offset > tess.point_count ||
            count > tess.point_count - offset) {
          offset += count;
          continue;
        }
        std::vector<lightrt::Vec3> points;
        std::vector<float> radii;
        points.reserve(count);
        radii.reserve(count);
        for (uint32_t j = 0; j < count; ++j) {
          uint32_t pi = offset + j;
          points.emplace_back(tess.points[pi * 3], tess.points[pi * 3 + 1],
                              tess.points[pi * 3 + 2]);
          float width = (tess.widths && pi < tess.width_count)
                            ? tess.widths[pi] : 1.0f;
          radii.push_back(std::max(1.0e-6f, width * 0.5f));
        }
        curves.emplace_back(points, radii, lightrt::CurveType::Linear);
        offset += count;
      }
      if (loader_verbose()) {
        for (uint32_t i = 0; i < tess.warning_count; ++i)
          std::fprintf(stderr, "  Curve warning: %s\n", tess.warnings[i]);
      }
      lydra_c_free_tessellated_curves(&tess);
      return append_curve_set(L, P, out_scene, mat_map, world_xform,
                              std::move(curves));
    }
    lydra_c_free_tessellated_curves(&tess);
  }

  // HermiteCurves carries one tangent per control point. Evaluate cubic
  // Hermite spans directly; malformed/missing tangent arrays fall back to the
  // control polygon so the prim remains visible.
  LydraCCurveData data = {};
  if (lydra_c_extract_curve(
          reinterpret_cast<LusdLayer>(L),
          reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
          &data) != LUSD_SUCCESS || !data.points || data.point_count < 2) {
    lydra_c_free_curve_data(&data);
    return false;
  }

  LusdValue tangent_value = LUSD_NULL_HANDLE;
  const LusdFloat3* tangents = nullptr;
  uint64_t tangent_count = 0;
  if (lusdPrimGetAttributeDefault(
          reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)), "tangents",
          &tangent_value) == LUSD_SUCCESS) {
    (void)lusdValueGetArrayPtrFloat3(tangent_value, &tangent_count, &tangents);
  }

  std::vector<lightrt::Curve> curves;
  curves.reserve(data.curve_count);
  uint32_t offset = 0;
  constexpr uint32_t kSamplesPerSpan = 8;
  for (uint32_t ci = 0; ci < data.curve_count; ++ci) {
    uint32_t count = data.curve_vertex_counts[ci] > 0
                         ? static_cast<uint32_t>(data.curve_vertex_counts[ci])
                         : 0u;
    if (count < 2 || offset > data.point_count ||
        count > data.point_count - offset) {
      offset += count;
      continue;
    }
    std::vector<lightrt::Vec3> points;
    std::vector<float> radii;
    if (tangents && offset + count <= tangent_count) {
      points.reserve((count - 1) * kSamplesPerSpan + 1);
      radii.reserve((count - 1) * kSamplesPerSpan + 1);
      for (uint32_t span = 0; span + 1 < count; ++span) {
        uint32_t i0 = offset + span;
        uint32_t i1 = i0 + 1;
        lightrt::Vec3 p0(data.points[i0*3], data.points[i0*3+1], data.points[i0*3+2]);
        lightrt::Vec3 p1(data.points[i1*3], data.points[i1*3+1], data.points[i1*3+2]);
        lightrt::Vec3 t0(tangents[i0].x, tangents[i0].y, tangents[i0].z);
        lightrt::Vec3 t1(tangents[i1].x, tangents[i1].y, tangents[i1].z);
        float r0 = curve_radius(data, i0, ci);
        float r1 = curve_radius(data, i1, ci);
        for (uint32_t sample = span ? 1u : 0u;
             sample <= kSamplesPerSpan; ++sample) {
          float u = static_cast<float>(sample) / kSamplesPerSpan;
          float u2 = u*u, u3 = u2*u;
          float h00 = 2*u3 - 3*u2 + 1;
          float h10 = u3 - 2*u2 + u;
          float h01 = -2*u3 + 3*u2;
          float h11 = u3 - u2;
          points.push_back(p0*h00 + t0*h10 + p1*h01 + t1*h11);
          radii.push_back(r0 + (r1 - r0) * u);
        }
      }
    } else {
      points.reserve(count);
      radii.reserve(count);
      for (uint32_t j = 0; j < count; ++j) {
        uint32_t pi = offset + j;
        points.emplace_back(data.points[pi*3], data.points[pi*3+1],
                            data.points[pi*3+2]);
        radii.push_back(curve_radius(data, pi, ci));
      }
    }
    curves.emplace_back(points, radii, lightrt::CurveType::Linear);
    offset += count;
  }
  if (tangent_value) lusdDestroyValue(L->inst, tangent_value);
  lydra_c_free_curve_data(&data);
  return append_curve_set(L, P, out_scene, mat_map, world_xform,
                          std::move(curves));
}

static bool append_points_prim(LusdLayer_T* L, const LusdPrim_T* P,
                               scene::Scene& out_scene,
                               const std::map<std::string, int>& mat_map,
                               const double world_xform[16]) {
  LydraCPointsData data = {};
  if (lydra_c_extract_points(
          reinterpret_cast<LusdLayer>(L),
          reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
          &data) != LUSD_SUCCESS || !data.points || data.point_count == 0) {
    lydra_c_free_points_data(&data);
    return false;
  }

  std::vector<lightrt::Sphere> points;
  points.reserve(data.point_count);
  for (uint32_t i = 0; i < data.point_count; ++i) {
    float width = 1.0f;
    if (data.width_count == 1) width = data.widths[0];
    else if (data.width_count == data.point_count) width = data.widths[i];
    points.emplace_back(
        lightrt::Vec3(data.points[i * 3], data.points[i * 3 + 1],
                      data.points[i * 3 + 2]),
        std::max(1.0e-6f, width * 0.5f));
  }

  const uint32_t point_mesh_id = static_cast<uint32_t>(out_scene.point_meshes.size());
  out_scene.point_meshes.emplace_back();
  auto& pb = out_scene.point_meshes.back();
  lightrt::BVHBuildConfig cfg = points.size() > 4096
                                    ? lightrt::BVHBuildConfig::fast()
                                    : lightrt::BVHBuildConfig();
  pb.build(points, cfg);
  pb.default_material_id = resolve_material_id(L, P, mat_map);
  pb.point_material_ids.assign(points.size(), pb.default_material_id);

  scene::Instance inst = make_instance(world_xform, pb.local_bounds);
  inst.point_mesh_id = point_mesh_id;
  out_scene.scene_bounds.expand(inst.world_bounds);
  out_scene.instances.push_back(inst);
  lydra_c_free_points_data(&data);
  return true;
}

static bool append_gaussian_prim(LusdLayer_T* L, const LusdPrim_T* P,
                                 scene::Scene& out_scene,
                                 const double world_xform[16]) {
  LusdPrim prim = reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P));
  LusdValue position_value = LUSD_NULL_HANDLE;
  LusdValue scale_value = LUSD_NULL_HANDLE;
  LusdValue orientation_value = LUSD_NULL_HANDLE;
  LusdValue opacity_value = LUSD_NULL_HANDLE;
  LusdValue sh_value = LUSD_NULL_HANDLE;
  LusdValue degree_value = LUSD_NULL_HANDLE;

  const LusdFloat3* positions = nullptr;
  const LusdFloat3* scales = nullptr;
  const LusdQuatf* orientations = nullptr;
  const float* opacities = nullptr;
  const LusdFloat3* sh_coefficients = nullptr;
  uint64_t position_count = 0, scale_count = 0, orientation_count = 0;
  uint64_t opacity_count = 0, sh_count = 0;
  int32_t authored_degree = 0;

  bool valid =
      lusdPrimGetAttributeDefault(prim, "positions", &position_value) == LUSD_SUCCESS &&
      lusdValueGetArrayPtrFloat3(position_value, &position_count, &positions) == LUSD_SUCCESS &&
      lusdPrimGetAttributeDefault(prim, "scales", &scale_value) == LUSD_SUCCESS &&
      lusdValueGetArrayPtrFloat3(scale_value, &scale_count, &scales) == LUSD_SUCCESS &&
      lusdPrimGetAttributeDefault(prim, "orientations", &orientation_value) == LUSD_SUCCESS &&
      lusdValueGetArrayPtrQuatf(orientation_value, &orientation_count,
                                &orientations) == LUSD_SUCCESS;
  if (!valid || !positions || !scales || !orientations || position_count == 0 ||
      scale_count < position_count || orientation_count < position_count) {
    if (position_value) lusdDestroyValue(L->inst, position_value);
    if (scale_value) lusdDestroyValue(L->inst, scale_value);
    if (orientation_value) lusdDestroyValue(L->inst, orientation_value);
    return false;
  }

  if (lusdPrimGetAttributeDefault(prim, "opacities", &opacity_value) == LUSD_SUCCESS)
    (void)lusdValueGetArrayPtrFloat(opacity_value, &opacity_count, &opacities);
  if (lusdPrimGetAttributeDefault(
          prim, "radiance:sphericalHarmonicsCoefficients", &sh_value) ==
      LUSD_SUCCESS)
    (void)lusdValueGetArrayPtrFloat3(sh_value, &sh_count, &sh_coefficients);
  if (lusdPrimGetAttributeDefault(
          prim, "radiance:sphericalHarmonicsDegree", &degree_value) ==
      LUSD_SUCCESS)
    (void)lusdValueGetInt32(degree_value, &authored_degree);

  uint32_t coefficient_count = 0;
  if (sh_coefficients && sh_count >= position_count &&
      sh_count % position_count == 0)
    coefficient_count = static_cast<uint32_t>(
        std::min<uint64_t>(16, sh_count / position_count));
  uint32_t available_degree = coefficient_count >= 16 ? 3
                            : coefficient_count >= 9 ? 2
                            : coefficient_count >= 4 ? 1 : 0;
  uint32_t degree = std::min<uint32_t>(
      std::max(0, authored_degree), available_degree);
  if (loader_geometry_only()) degree = 0;

  std::vector<lightrt::GaussianSplat> splats;
  splats.reserve(static_cast<size_t>(position_count));
  for (uint64_t i = 0; i < position_count; ++i) {
    float opacity = (opacities && i < opacity_count) ? opacities[i] : 1.0f;
    if (opacity <= 1.0e-5f) continue;
    lightrt::GaussianSplat splat;
    splat.position = lightrt::Vec3(positions[i].x, positions[i].y,
                                   positions[i].z);
    splat.scale = lightrt::Vec3(std::max(1.0e-7f, std::abs(scales[i].x)),
                                std::max(1.0e-7f, std::abs(scales[i].y)),
                                std::max(1.0e-7f, std::abs(scales[i].z)));
    // LusdQuatf is xyzw; LightRT stores wxyz.
    splat.rotation[0] = orientations[i].w;
    splat.rotation[1] = orientations[i].x;
    splat.rotation[2] = orientations[i].y;
    splat.rotation[3] = orientations[i].z;
    float qlen = std::sqrt(splat.rotation[0]*splat.rotation[0] +
                           splat.rotation[1]*splat.rotation[1] +
                           splat.rotation[2]*splat.rotation[2] +
                           splat.rotation[3]*splat.rotation[3]);
    if (qlen > 1.0e-8f) {
      for (float& q : splat.rotation) q /= qlen;
    } else {
      splat.rotation[0] = 1.0f;
      splat.rotation[1] = splat.rotation[2] = splat.rotation[3] = 0.0f;
    }
    splat.opacity = std::max(0.0f, std::min(1.0f, opacity));
    splat.sh_degree = static_cast<lightrt::SHDegree>(degree);
    if (sh_coefficients && coefficient_count > 0) {
      uint32_t copied_coefficients = degree == 0 ? 1u : (degree + 1u) * (degree + 1u);
      for (uint32_t c = 0; c < copied_coefficients; ++c) {
        const LusdFloat3& coefficient =
            sh_coefficients[i * coefficient_count + c];
        splat.sh_coeffs[c*3] = coefficient.x;
        splat.sh_coeffs[c*3+1] = coefficient.y;
        splat.sh_coeffs[c*3+2] = coefficient.z;
      }
    }
    splats.push_back(splat);
  }

  if (position_value) lusdDestroyValue(L->inst, position_value);
  if (scale_value) lusdDestroyValue(L->inst, scale_value);
  if (orientation_value) lusdDestroyValue(L->inst, orientation_value);
  if (opacity_value) lusdDestroyValue(L->inst, opacity_value);
  if (sh_value) lusdDestroyValue(L->inst, sh_value);
  if (degree_value) lusdDestroyValue(L->inst, degree_value);
  if (splats.empty()) return false;

  const uint32_t gaussian_mesh_id =
      static_cast<uint32_t>(out_scene.gaussian_meshes.size());
  out_scene.gaussian_meshes.emplace_back();
  auto& gb = out_scene.gaussian_meshes.back();
  lightrt::BVHBuildConfig cfg = lightrt::BVHBuildConfig::fast();
  cfg.max_leaf_size = 8;
  gb.build(std::move(splats), cfg);

  scene::Instance inst = make_instance(world_xform, gb.local_bounds);
  inst.gaussian_mesh_id = gaussian_mesh_id;
  out_scene.scene_bounds.expand(inst.world_bounds);
  out_scene.instances.push_back(inst);
  if (loader_verbose())
    std::printf("  Gaussian splats: %zu (SH degree %u)\n",
                gb.splats.size(), degree);
  return true;
}

static void walk_prim(LusdLayer_T* L, const LusdPrim_T* P,
                      scene::Scene& out_scene,
                      const std::map<std::string, int>& mat_map,
                      const double parent_xform[16],
                      const std::string& usd_base_dir,
                      double time_code) {
  double local_xform[16];
  double world_xform[16];
  int has_local = lydra_c_extract_xform_at(
      reinterpret_cast<LusdLayer>(L),
      reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
      time_code, local_xform);
  if (has_local == 0) {
    mat4d_mul(parent_xform, local_xform, world_xform);
  } else {
    std::memcpy(world_xform, parent_xform, sizeof(world_xform));
  }

  if (P->type_name && strcmp(P->type_name, "Mesh") == 0) {
    LydraCMeshData mesh_data_c;
    LusdResult r = lydra_c_extract_mesh(
        reinterpret_cast<LusdLayer>(L),
        reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
        &mesh_data_c);
    if (r == LUSD_SUCCESS) {
      uint32_t* tri_idx = nullptr;
      uint32_t tri_idx_count = 0;
      bool owns_tri_idx = false;
      std::vector<uint32_t> face_to_tri_start;

      if (mesh_data_c.fvc_count > 0) {
        if (lydra_c_triangulate(mesh_data_c.face_vertex_indices,
                                mesh_data_c.fvi_count,
                                mesh_data_c.face_vertex_counts,
                                mesh_data_c.fvc_count,
                                &tri_idx, &tri_idx_count) != 0) {
          lydra_c_free_mesh_data(&mesh_data_c);
          goto recurse;
        }
        owns_tri_idx = true;
        face_to_tri_start.resize(mesh_data_c.fvc_count);
        uint32_t tri_offset = 0;
        for (uint32_t fi = 0; fi < mesh_data_c.fvc_count; fi++) {
          face_to_tri_start[fi] = tri_offset;
          int32_t fvc = mesh_data_c.face_vertex_counts[fi];
          if (fvc >= 3) tri_offset += static_cast<uint32_t>(fvc - 2);
        }
      } else {
        tri_idx = reinterpret_cast<uint32_t*>(mesh_data_c.face_vertex_indices);
        tri_idx_count = mesh_data_c.fvi_count;
      }

      uint32_t pt_count = mesh_data_c.point_count;
      std::vector<lightrt::Triangle> triangles;
      std::vector<float> pre_uvs;
      std::vector<float> pre_normals;
      triangles.reserve(tri_idx_count / 3);

      float* smooth_norms = nullptr;
      const bool keep_prim_data = !loader_geometry_only();
      bool has_authored_normals = keep_prim_data &&
          (mesh_data_c.normals != nullptr && mesh_data_c.normal_count > 0);
      bool normals_facevarying = false;
      if (has_authored_normals) {
        normals_facevarying = (mesh_data_c.normal_count == mesh_data_c.fvi_count);
      } else if (keep_prim_data) {
        lydra_c_compute_smooth_normals(
            mesh_data_c.points, pt_count,
            reinterpret_cast<uint32_t*>(mesh_data_c.face_vertex_indices),
            mesh_data_c.fvi_count,
            &smooth_norms);
      }

      bool has_uvs = keep_prim_data &&
                     (mesh_data_c.uvs != nullptr && mesh_data_c.uv_count > 0);
      bool uvs_facevarying = has_uvs && (mesh_data_c.uv_count == mesh_data_c.fvi_count);

      for (uint32_t i = 0; i + 2 < tri_idx_count; i += 3) {
        uint32_t i0 = tri_idx[i], i1 = tri_idx[i + 1], i2 = tri_idx[i + 2];
        if (i0 >= pt_count || i1 >= pt_count || i2 >= pt_count) continue;
        lightrt::Triangle tri;
        tri.v0 = lightrt::Vec3(mesh_data_c.points[i0*3], mesh_data_c.points[i0*3+1], mesh_data_c.points[i0*3+2]);
        tri.v1 = lightrt::Vec3(mesh_data_c.points[i1*3], mesh_data_c.points[i1*3+1], mesh_data_c.points[i1*3+2]);
        tri.v2 = lightrt::Vec3(mesh_data_c.points[i2*3], mesh_data_c.points[i2*3+1], mesh_data_c.points[i2*3+2]);
        triangles.push_back(tri);

        if (has_uvs) {
          if (uvs_facevarying) {
            pre_uvs.push_back(mesh_data_c.uvs[i*2+0]); pre_uvs.push_back(mesh_data_c.uvs[i*2+1]);
            pre_uvs.push_back(mesh_data_c.uvs[(i+1)*2+0]); pre_uvs.push_back(mesh_data_c.uvs[(i+1)*2+1]);
            pre_uvs.push_back(mesh_data_c.uvs[(i+2)*2+0]); pre_uvs.push_back(mesh_data_c.uvs[(i+2)*2+1]);
          } else {
            pre_uvs.push_back(mesh_data_c.uvs[i0*2+0]); pre_uvs.push_back(mesh_data_c.uvs[i0*2+1]);
            pre_uvs.push_back(mesh_data_c.uvs[i1*2+0]); pre_uvs.push_back(mesh_data_c.uvs[i1*2+1]);
            pre_uvs.push_back(mesh_data_c.uvs[i2*2+0]); pre_uvs.push_back(mesh_data_c.uvs[i2*2+1]);
          }
        }

        if (has_authored_normals) {
          const float* n = mesh_data_c.normals;
          if (normals_facevarying) {
            pre_normals.push_back(n[i*3+0]); pre_normals.push_back(n[i*3+1]); pre_normals.push_back(n[i*3+2]);
            pre_normals.push_back(n[(i+1)*3+0]); pre_normals.push_back(n[(i+1)*3+1]); pre_normals.push_back(n[(i+1)*3+2]);
            pre_normals.push_back(n[(i+2)*3+0]); pre_normals.push_back(n[(i+2)*3+1]); pre_normals.push_back(n[(i+2)*3+2]);
          } else {
            pre_normals.push_back(n[i0*3+0]); pre_normals.push_back(n[i0*3+1]); pre_normals.push_back(n[i0*3+2]);
            pre_normals.push_back(n[i1*3+0]); pre_normals.push_back(n[i1*3+1]); pre_normals.push_back(n[i1*3+2]);
            pre_normals.push_back(n[i2*3+0]); pre_normals.push_back(n[i2*3+1]); pre_normals.push_back(n[i2*3+2]);
          }
        } else if (smooth_norms) {
          pre_normals.push_back(smooth_norms[i0*3+0]); pre_normals.push_back(smooth_norms[i0*3+1]); pre_normals.push_back(smooth_norms[i0*3+2]);
          pre_normals.push_back(smooth_norms[i1*3+0]); pre_normals.push_back(smooth_norms[i1*3+1]); pre_normals.push_back(smooth_norms[i1*3+2]);
          pre_normals.push_back(smooth_norms[i2*3+0]); pre_normals.push_back(smooth_norms[i2*3+1]); pre_normals.push_back(smooth_norms[i2*3+2]);
        }
      }

      if (smooth_norms) lusd_free(smooth_norms);
      if (owns_tri_idx) lusd_free(tri_idx);

      if (!triangles.empty()) {
        size_t mi = out_scene.meshes.size();
        out_scene.meshes.emplace_back();
        auto& md = out_scene.meshes.back();
        int32_t mat_id = -1;
        const char* mat_path = lydra_c_resolve_material_binding(
            reinterpret_cast<LusdLayer>(L),
            reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)));
        if (mat_path) {
          auto it = mat_map.find(mat_path);
          if (it != mat_map.end()) mat_id = it->second;
        }
        md.default_material_id = mat_id;

        std::vector<int32_t> pre_mat_ids;
        if (keep_prim_data) pre_mat_ids.assign(triangles.size(), mat_id);

        LydraCGeomSubset* subsets = nullptr;
        uint32_t subset_count = keep_prim_data
            ? lydra_c_extract_geom_subsets(
                  reinterpret_cast<LusdLayer>(L),
                  reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
                  &subsets)
            : 0;
        if (subset_count > 0 && !face_to_tri_start.empty()) {
          for (uint32_t si = 0; si < subset_count; si++) {
            int32_t subset_mat_id = -1;
            if (subsets[si].material_path) {
              auto it = mat_map.find(subsets[si].material_path);
              if (it != mat_map.end()) subset_mat_id = it->second;
            }
            if (subset_mat_id < 0) continue;
            for (uint32_t fi_idx = 0; fi_idx < subsets[si].face_count; fi_idx++) {
              uint32_t fi = static_cast<uint32_t>(subsets[si].face_indices[fi_idx]);
              if (fi >= face_to_tri_start.size()) continue;
              int32_t fvc = mesh_data_c.face_vertex_counts[fi];
              uint32_t tri_start = face_to_tri_start[fi];
              uint32_t tri_count = (fvc >= 3) ? static_cast<uint32_t>(fvc - 2) : 0;
              for (uint32_t t = 0; t < tri_count; t++) {
                uint32_t tri_id = tri_start + t;
                if (tri_id < pre_mat_ids.size())
                  pre_mat_ids[tri_id] = subset_mat_id;
              }
            }
          }
          lydra_c_free_geom_subsets(subsets, subset_count);
        }

        std::multimap<CentroidKey, size_t> centroid_map;
        if (keep_prim_data) {
          for (size_t ti = 0; ti < triangles.size(); ti++)
            centroid_map.insert({makeCentroidKey(triangles[ti]), ti});
        }

        lightrt::AABB& lb = md.local_bounds;
        for (const auto& tri : triangles) {
          lb.expand(tri.v0); lb.expand(tri.v1); lb.expand(tri.v2);
        }
        md.bvh.build(triangles);

        const auto& reordered = md.bvh.getTriangles();
        size_t num_tris = reordered.size();
        if (keep_prim_data) {
          md.tri_material_ids.resize(num_tris);
          if (!pre_uvs.empty()) md.tri_uvs.resize(num_tris * 6);
          if (!pre_normals.empty()) md.tri_normals.resize(num_tris * 9);
        }

        for (size_t ti = 0; keep_prim_data && ti < num_tris; ti++) {
          CentroidKey key = makeCentroidKey(reordered[ti]);
          auto range = centroid_map.equal_range(key);
          size_t orig = (range.first != range.second) ? range.first->second : ti;
          if (range.first != range.second) centroid_map.erase(range.first);

          md.tri_material_ids[ti] = (orig < pre_mat_ids.size()) ? pre_mat_ids[orig] : mat_id;
          if (!pre_uvs.empty() && orig * 6 + 5 < pre_uvs.size())
            std::memcpy(&md.tri_uvs[ti * 6], &pre_uvs[orig * 6], 6 * sizeof(float));
          if (!pre_normals.empty() && orig * 9 + 8 < pre_normals.size())
            std::memcpy(&md.tri_normals[ti * 9], &pre_normals[orig * 9], 9 * sizeof(float));
        }

        scene::Instance inst;
        inst.mesh_id = static_cast<uint32_t>(mi);
        mat4d_to_3x4f(world_xform, inst.transform);
        scene::invert3x4(inst.transform, inst.inv_transform);
        std::memcpy(inst.transform_close, inst.transform, sizeof(inst.transform));
        std::memcpy(inst.inv_transform_close, inst.inv_transform, sizeof(inst.inv_transform));
        inst.has_motion = false;
        inst.world_bounds = scene::transformAABB(md.local_bounds, inst.transform);
        out_scene.scene_bounds.expand(inst.world_bounds);
        out_scene.instances.push_back(inst);
      }

      lydra_c_free_mesh_data(&mesh_data_c);
    }
  }

  if (P->type_name &&
      (strcmp(P->type_name, "BasisCurves") == 0 ||
       strcmp(P->type_name, "NurbsCurves") == 0 ||
       strcmp(P->type_name, "HermiteCurves") == 0)) {
    append_curve_prim(L, P, out_scene, mat_map, world_xform);
  }

  if (P->type_name && strcmp(P->type_name, "Points") == 0) {
    append_points_prim(L, P, out_scene, mat_map, world_xform);
  }

  if (P->type_name && std::strstr(P->type_name, "GaussianSplat")) {
    append_gaussian_prim(L, P, out_scene, world_xform);
  }

  // Keep authored spheres analytic. Tessellating every sphere was especially
  // costly in production scenes containing thousands of particle markers.
  if (P->type_name && strcmp(P->type_name, "Sphere") == 0) {
    float radius = 1.0f;
    lydra_c_read_float_attr(
        reinterpret_cast<LusdLayer>(L),
        reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
        "radius", &radius);
    if (radius > 1.0e-6f) {
      const uint32_t point_mesh_id =
          static_cast<uint32_t>(out_scene.point_meshes.size());
      out_scene.point_meshes.emplace_back();
      auto& pb = out_scene.point_meshes.back();
      std::vector<lightrt::Sphere> sphere = {
          lightrt::Sphere(lightrt::Vec3(0.0f, 0.0f, 0.0f), radius)};
      pb.build(sphere);
      pb.default_material_id = resolve_material_id(L, P, mat_map);
      pb.point_material_ids.assign(1, pb.default_material_id);
      scene::Instance inst = make_instance(world_xform, pb.local_bounds);
      inst.point_mesh_id = point_mesh_id;
      out_scene.scene_bounds.expand(inst.world_bounds);
      out_scene.instances.push_back(inst);
      if (loader_verbose())
        printf("  Sphere radius=%.6g -> analytic point primitive\n", radius);
    }
  }

  if (P->type_name && strcmp(P->type_name, "Cube") == 0) {
    float size = 2.0f;
    lydra_c_read_float_attr(
        reinterpret_cast<LusdLayer>(L),
        reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
        "size", &size);
    if (size <= 1.0e-6f) goto recurse;
    float h = size * 0.5f;

    int32_t mat_id = -1;
    {
      const char* mat_path = lydra_c_resolve_material_binding(
          reinterpret_cast<LusdLayer>(L),
          reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)));
      if (mat_path) {
        auto it = mat_map.find(mat_path);
        if (it != mat_map.end()) mat_id = it->second;
      }
    }

    struct FaceQuad {
      lightrt::Vec3 v[4];
      lightrt::Vec3 n;
      float uv[8];
    };
    FaceQuad faces[6] = {
      {{{h,-h,-h},{h,h,-h},{h,h,h},{h,-h,h}}, {1,0,0}, {0,0,1,0,1,1,0,1}},
      {{{-h,-h,h},{-h,h,h},{-h,h,-h},{-h,-h,-h}}, {-1,0,0}, {0,0,1,0,1,1,0,1}},
      {{{-h,h,-h},{-h,h,h},{h,h,h},{h,h,-h}}, {0,1,0}, {0,0,1,0,1,1,0,1}},
      {{{-h,-h,h},{-h,-h,-h},{h,-h,-h},{h,-h,h}}, {0,-1,0}, {0,0,1,0,1,1,0,1}},
      {{{-h,-h,h},{h,-h,h},{h,h,h},{-h,h,h}}, {0,0,1}, {0,0,1,0,1,1,0,1}},
      {{{h,-h,-h},{-h,-h,-h},{-h,h,-h},{h,h,-h}}, {0,0,-1}, {0,0,1,0,1,1,0,1}},
    };

    std::vector<lightrt::Triangle> triangles;
    std::vector<float> pre_uvs, pre_normals;
    triangles.reserve(12);
    for (auto& f : faces) {
      lightrt::Triangle t0; t0.v0 = f.v[0]; t0.v1 = f.v[1]; t0.v2 = f.v[2];
      triangles.push_back(t0);
      pre_uvs.insert(pre_uvs.end(), {f.uv[0], f.uv[1], f.uv[2], f.uv[3], f.uv[4], f.uv[5]});
      pre_normals.insert(pre_normals.end(), {f.n.x, f.n.y, f.n.z, f.n.x, f.n.y, f.n.z, f.n.x, f.n.y, f.n.z});
      lightrt::Triangle t1; t1.v0 = f.v[0]; t1.v1 = f.v[2]; t1.v2 = f.v[3];
      triangles.push_back(t1);
      pre_uvs.insert(pre_uvs.end(), {f.uv[0], f.uv[1], f.uv[4], f.uv[5], f.uv[6], f.uv[7]});
      pre_normals.insert(pre_normals.end(), {f.n.x, f.n.y, f.n.z, f.n.x, f.n.y, f.n.z, f.n.x, f.n.y, f.n.z});
    }

    {
      size_t mi = out_scene.meshes.size();
      out_scene.meshes.emplace_back();
      auto& md = out_scene.meshes.back();
      md.default_material_id = mat_id;

      std::multimap<CentroidKey, size_t> centroid_map;
      for (size_t ti = 0; ti < triangles.size(); ti++)
        centroid_map.insert({makeCentroidKey(triangles[ti]), ti});

      for (const auto& tri : triangles) {
        md.local_bounds.expand(tri.v0);
        md.local_bounds.expand(tri.v1);
        md.local_bounds.expand(tri.v2);
      }
      md.bvh.build(triangles);

      const auto& reordered = md.bvh.getTriangles();
      size_t num_tris = reordered.size();
      md.tri_material_ids.assign(num_tris, mat_id);
      md.tri_uvs.resize(num_tris * 6);
      md.tri_normals.resize(num_tris * 9);

      for (size_t ti = 0; ti < num_tris; ti++) {
        CentroidKey key = makeCentroidKey(reordered[ti]);
        auto range = centroid_map.equal_range(key);
        size_t orig = (range.first != range.second) ? range.first->second : ti;
        if (range.first != range.second) centroid_map.erase(range.first);
        if (orig * 6 + 5 < pre_uvs.size())
          std::memcpy(&md.tri_uvs[ti * 6], &pre_uvs[orig * 6], 6 * sizeof(float));
        if (orig * 9 + 8 < pre_normals.size())
          std::memcpy(&md.tri_normals[ti * 9], &pre_normals[orig * 9], 9 * sizeof(float));
      }

      scene::Instance inst;
      inst.mesh_id = static_cast<uint32_t>(mi);
      mat4d_to_3x4f(world_xform, inst.transform);
      scene::invert3x4(inst.transform, inst.inv_transform);
      std::memcpy(inst.transform_close, inst.transform, sizeof(inst.transform));
      std::memcpy(inst.inv_transform_close, inst.inv_transform, sizeof(inst.inv_transform));
      inst.has_motion = false;
      inst.world_bounds = scene::transformAABB(md.local_bounds, inst.transform);
      out_scene.scene_bounds.expand(inst.world_bounds);
      out_scene.instances.push_back(inst);
      if (loader_verbose())
        printf("  Cube size=%.3f -> %zu triangles\n", size, num_tris);
    }
  }

  if (P->type_name && strcmp(P->type_name, "Camera") == 0) {
    LydraCCameraData cam_data;
    lydra_c_extract_camera_at(
        reinterpret_cast<LusdLayer>(L),
        reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
        time_code, &cam_data);
    scene::Camera cam;
    cam.name = P->name ? P->name : "";
    cam.fov_y_rad = 2.0f * std::atan(0.5f * cam_data.vertical_aperture / cam_data.focal_length);
    cam.znear = cam_data.znear;
    cam.zfar = cam_data.zfar;
    cam.shutter_open = cam_data.shutter_open;
    cam.shutter_close = cam_data.shutter_close;
    mat4d_to_4x4f(world_xform, cam.transform);
    out_scene.cameras.push_back(cam);
  }

  if (P->type_name && (strcmp(P->type_name, "DistantLight") == 0 ||
                        strcmp(P->type_name, "SphereLight") == 0 ||
                        strcmp(P->type_name, "RectLight") == 0)) {
    LydraCLightData ld;
    lydra_c_extract_light_at(
        reinterpret_cast<LusdLayer>(L),
        reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
        time_code, &ld);
    float multiplier = ld.intensity * std::pow(2.0f, ld.exposure);
    scene::LightData light;
    light.color = lightrt::Vec3(ld.color[0] * multiplier,
                                ld.color[1] * multiplier,
                                ld.color[2] * multiplier);

    if (ld.type == LYDRA_C_LIGHT_DISTANT) {
      light.type = scene::LightData::Distant;
      float dir_x = -static_cast<float>(world_xform[0*4+2]);
      float dir_y = -static_cast<float>(world_xform[1*4+2]);
      float dir_z = -static_cast<float>(world_xform[2*4+2]);
      float len = std::sqrt(dir_x*dir_x + dir_y*dir_y + dir_z*dir_z);
      if (len > 1e-8f)
        light.direction = lightrt::Vec3(dir_x/len, dir_y/len, dir_z/len);
    } else if (ld.type == LYDRA_C_LIGHT_SPHERE) {
      light.type = scene::LightData::Sphere;
      light.position = lightrt::Vec3(
          static_cast<float>(world_xform[0*4+3]),
          static_cast<float>(world_xform[1*4+3]),
          static_cast<float>(world_xform[2*4+3]));
      light.radius = std::max(0.0f, ld.radius);
    } else if (ld.type == LYDRA_C_LIGHT_RECT) {
      light.type = scene::LightData::Rect;
      light.position = lightrt::Vec3(
          static_cast<float>(world_xform[0*4+3]),
          static_cast<float>(world_xform[1*4+3]),
          static_cast<float>(world_xform[2*4+3]));
      light.rect_axis_u = lightrt::Vec3(
          static_cast<float>(world_xform[0*4+0]),
          static_cast<float>(world_xform[1*4+0]),
          static_cast<float>(world_xform[2*4+0])).normalize();
      light.rect_axis_v = lightrt::Vec3(
          static_cast<float>(world_xform[0*4+1]),
          static_cast<float>(world_xform[1*4+1]),
          static_cast<float>(world_xform[2*4+1])).normalize();
      light.direction = lightrt::Vec3(
          -static_cast<float>(world_xform[0*4+2]),
          -static_cast<float>(world_xform[1*4+2]),
          -static_cast<float>(world_xform[2*4+2])).normalize();
      light.rect_half_width  = ld.width  * 0.5f;
      light.rect_half_height = ld.height * 0.5f;
    }
    out_scene.lights.push_back(light);
  }

  if (P->type_name && strcmp(P->type_name, "DomeLight") == 0) {
    LydraCDomeLightData dome;
    lydra_c_extract_dome_light(
        reinterpret_cast<LusdLayer>(L),
        reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
        &dome);
    if (dome.texture_file && !out_scene.envmap.valid()) {
      char resolved[1024];
      const char* rp = lydra_c_resolve_asset_path(
          usd_base_dir.c_str(), dome.texture_file, resolved, sizeof(resolved));
      std::string tex_path = rp ? rp : dome.texture_file;
      const char* prim_path = P->name ? P->name : "DomeLight";

      for (auto& c : tex_path) { if (c == '\\') c = '/'; }
      if (tex_path.size() >= 2 && tex_path[0] == '.' && tex_path[1] == '/')
        tex_path = tex_path.substr(2);

      float multiplier = dome.intensity * std::pow(2.0f, dome.exposure);
      int w = 0, h = 0, ch = 0;
      float* hdr_data = stbi_loadf(tex_path.c_str(), &w, &h, &ch, 0);
      if (!hdr_data && !usd_base_dir.empty() && tex_path[0] != '/') {
        std::string resolved2 = usd_base_dir + "/" + tex_path;
        hdr_data = stbi_loadf(resolved2.c_str(), &w, &h, &ch, 0);
        if (hdr_data) tex_path = resolved2;
      }
      if (!hdr_data) {
        printf("  DomeLight \"%s\": texture not found at \"%s\"\n", prim_path, tex_path.c_str());
      }
      if (hdr_data && w > 0 && h > 0) {
        bool is_ldr = !stbi_is_hdr(tex_path.c_str());
        scene::EnvmapData& env = out_scene.envmap;
        env.width = w;
        env.height = h;
        env.pixels.resize(static_cast<size_t>(w) * static_cast<size_t>(h) * 3);
        for (int y = 0; y < h; y++) {
          for (int x = 0; x < w; x++) {
            size_t si = (static_cast<size_t>(y) * w + x) * ch;
            size_t di = (static_cast<size_t>(y) * w + x) * 3;
            for (int c = 0; c < 3; c++) {
              float v = (c < ch) ? hdr_data[si + c] : 0.0f;
              if (is_ldr) v = std::pow(v, 2.2f);
              env.pixels[di + c] = v * multiplier * dome.color[c];
            }
          }
        }
        stbi_image_free(hdr_data);
        scene::shading::buildEnvmapCDF(env);
        printf("  DomeLight \"%s\": loaded envmap %dx%d from \"%s\"\n",
               prim_path, w, h, tex_path.c_str());
      }
    }
  }

recurse:
  for (uint32_t j = 0; j < P->child_count; j++) {
    walk_prim(L, &L->prim_nodes[P->child_spec_indices[j]], out_scene, mat_map,
              world_xform, usd_base_dir, time_code);
  }
}

bool loadUSDScene(const std::string& filename, double timecode, scene::Scene& out_scene) {
  LusdInstanceCreateInfo inst_info = {};
  inst_info.sType = LUSD_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
  inst_info.apiVersion = 1;
  inst_info.pApplicationName = "lightrt";
  inst_info.applicationVersion = 1;

  LusdInstance instance = LUSD_NULL_HANDLE;
  LusdResult r = lusdCreateInstance(&inst_info, nullptr, &instance);
  if (r != LUSD_SUCCESS) {
    fprintf(stderr, "lightusd-c: lusdCreateInstance failed: %s\n", lusdResultToString(r));
    return false;
  }

  const bool composed = loader_composition();
  FlattenedBuffer flattened;
  LusdFilesystemCallbacks flattened_fs = {};

  LusdLayerCreateInfo ci = {};
  ci.sType = LUSD_STRUCTURE_TYPE_LAYER_CREATE_INFO;
  ci.pIdentifier = filename.c_str();
  ci.pFilesystem = &kHostFilesystem;

  if (composed) {
    LusdFlattenOptions options = {};
    options.inputFormat = LUSD_FORMAT_AUTO;
    options.outputFormat = LUSD_FORMAT_USDC;
    options.loadPayloads = true;
    options.applyListOps = true;
    options.pFilesystem = &kHostFilesystem;
    LusdFlattenStats stats = {};
    r = lusdFlattenFileToBuffer(instance, filename.c_str(), &options,
                                &flattened.data, &flattened.size, &stats);
    if (r != LUSD_SUCCESS) {
      std::fprintf(stderr, "lightusd-c: composition failed: %s (%s)\n",
                   lusdResultToString(r), lusdGetLastError(instance));
      lusdDestroyInstance(instance, nullptr);
      return false;
    }
    std::printf("Composed USD: %llu prims, %llu properties, %.1f MiB flattened USDC\n",
                static_cast<unsigned long long>(stats.primCount),
                static_cast<unsigned long long>(stats.propertyCount),
                static_cast<double>(flattened.size) / (1024.0 * 1024.0));
    flattened_fs.pUserData = &flattened;
    flattened_fs.pfnReadFile = flattened_read_file;
    flattened_fs.pfnReleaseFile = flattened_release_file;
    flattened_fs.adoptReadFileBuffers = true;
    ci.pIdentifier = "lightrt-composed.usdc";
    ci.pFilesystem = &flattened_fs;
  }

  LusdLayer layer = LUSD_NULL_HANDLE;
  r = lusdCreateLayer(instance, &ci, &layer);
  if (r != LUSD_SUCCESS) {
    fprintf(stderr, "lightusd-c: lusdCreateLayer failed: %s (%s)\n",
            lusdResultToString(r), lusdGetLastError(instance));
    if (flattened.data) lusd_free(flattened.data);
    lusdDestroyInstance(instance, nullptr);
    return false;
  }

  LusdLayer_T* L = reinterpret_cast<LusdLayer_T*>(layer);
  out_scene.up_axis = L->metas.up_axis;
  const double sample_time = timecode < -1.0e20
                                 ? L->metas.start_time_code : timecode;

  std::string usd_base_dir;
  {
    const char* effective_id = composed ? filename.c_str()
                                        : (L->identifier ? L->identifier
                                                         : filename.c_str());
    std::string eid(effective_id);
    size_t slash_pos = eid.find_last_of("/\\");
    if (slash_pos != std::string::npos)
      usd_base_dir = eid.substr(0, slash_pos);
  }

  std::map<std::string, int> mat_map;
  std::map<std::string, int> tex_map;
  const char* geometry_only_env = std::getenv("LIGHTRT_USD_GEOMETRY_ONLY");
  const bool geometry_only = geometry_only_env && geometry_only_env[0] == '1';
  if (!geometry_only) {
    for (uint32_t i = 0; i < L->root_spec_count; i++) {
      collect_materials(L, &L->prim_nodes[L->root_spec_indices[i]], out_scene,
                        mat_map, usd_base_dir, tex_map);
    }
  }

  for (uint32_t i = 0; i < L->root_spec_count; i++) {
    walk_prim(L, &L->prim_nodes[L->root_spec_indices[i]], out_scene, mat_map,
              kIdentity4d, usd_base_dir, sample_time);
  }

  out_scene.buildAcceleration();

  size_t triangle_count = 0;
  size_t curve_count = 0;
  size_t point_count = 0;
  size_t gaussian_count = 0;
  for (const auto& mesh : out_scene.meshes)
    triangle_count += mesh.bvh.getTriangles().size();
  for (const auto& curves : out_scene.curve_meshes)
    curve_count += curves.curves.size();
  for (const auto& points : out_scene.point_meshes)
    point_count += points.points.size();
  for (const auto& gaussians : out_scene.gaussian_meshes)
    gaussian_count += gaussians.splats.size();

  printf("Loaded %zu meshes, %zu curve sets, %zu point sets, %zu Gaussian sets, %zu instances, "
         "%zu materials, %zu cameras, %zu lights (lightusd-c layer%s%s)\n",
         out_scene.meshes.size(), out_scene.curve_meshes.size(),
         out_scene.point_meshes.size(), out_scene.gaussian_meshes.size(),
         out_scene.instances.size(),
         out_scene.materials.size(), out_scene.cameras.size(),
         out_scene.lights.size(), composed ? ", composed" : "",
         geometry_only ? ", geometry only" : "");
  printf("Geometry: %zu triangles, %zu curves, %zu points, %zu Gaussian splats\n",
         triangle_count, curve_count, point_count, gaussian_count);
  printf("Scene bounds: [(%.6g, %.6g, %.6g) - (%.6g, %.6g, %.6g)]\n",
         out_scene.scene_bounds.min.x, out_scene.scene_bounds.min.y,
         out_scene.scene_bounds.min.z, out_scene.scene_bounds.max.x,
         out_scene.scene_bounds.max.y, out_scene.scene_bounds.max.z);
  lusdDestroyLayer(instance, layer);
  if (flattened.data) lusd_free(flattened.data);
  lusdDestroyInstance(instance, nullptr);
  return !out_scene.instances.empty();
}

static void walk_prim_mblur(LusdLayer_T* L, const LusdPrim_T* P,
                             scene::Scene& out_scene,
                             const double parent_xform[16],
                             double time_code,
                             uint32_t& instance_idx) {
  double local_xform[16];
  double world_xform[16];
  int has_local = lydra_c_extract_xform_at(
      reinterpret_cast<LusdLayer>(L),
      reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
      time_code, local_xform);
  if (has_local == 0) {
    mat4d_mul(parent_xform, local_xform, world_xform);
  } else {
    std::memcpy(world_xform, parent_xform, sizeof(world_xform));
  }

  if (P->type_name && strcmp(P->type_name, "Mesh") == 0) {
    // Non-mesh prims also occupy instance slots. Advance to the next mesh
    // slot so an interleaved curve/points instance is never treated as a mesh.
    while (instance_idx < out_scene.instances.size() &&
           out_scene.instances[instance_idx].mesh_id == lightrt::kInvalidIndex)
      instance_idx++;
    if (instance_idx < out_scene.instances.size()) {
      auto& inst = out_scene.instances[instance_idx];
      float close_xform[12];
      mat4d_to_3x4f(world_xform, close_xform);

      bool differs = false;
      for (int k = 0; k < 12; k++) {
        if (std::abs(close_xform[k] - inst.transform[k]) > 1e-7f) {
          differs = true;
          break;
        }
      }
      if (differs) {
        std::memcpy(inst.transform_close, close_xform, sizeof(close_xform));
        scene::invert3x4(inst.transform_close, inst.inv_transform_close);
        inst.has_motion = true;
        lightrt::AABB close_bounds = scene::transformAABB(
            out_scene.meshes[inst.mesh_id].local_bounds, inst.transform_close);
        inst.world_bounds.expand(close_bounds);
        out_scene.scene_bounds.expand(close_bounds);
      }
      instance_idx++;
    }
  }

  for (uint32_t j = 0; j < P->child_count; j++) {
    walk_prim_mblur(L, &L->prim_nodes[P->child_spec_indices[j]],
                    out_scene, world_xform, time_code, instance_idx);
  }
}

void applyMotionBlur(const std::string& filename,
                     double timecode,
                     double shutter_close_offset,
                     scene::Scene& scene) {
  if (shutter_close_offset == 0.0) return;

  LusdInstanceCreateInfo inst_info = {};
  inst_info.sType = LUSD_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
  inst_info.apiVersion = 1;
  inst_info.pApplicationName = "lightrt";
  inst_info.applicationVersion = 1;

  LusdInstance instance = LUSD_NULL_HANDLE;
  if (lusdCreateInstance(&inst_info, nullptr, &instance) != LUSD_SUCCESS) return;

  LusdLayerCreateInfo ci = {};
  ci.sType = LUSD_STRUCTURE_TYPE_LAYER_CREATE_INFO;
  ci.pIdentifier = filename.c_str();
  ci.pFilesystem = &kHostFilesystem;

  FlattenedBuffer flattened;
  LusdFilesystemCallbacks flattened_fs = {};
  if (loader_composition()) {
    LusdFlattenOptions options = {};
    options.inputFormat = LUSD_FORMAT_AUTO;
    options.outputFormat = LUSD_FORMAT_USDC;
    options.loadPayloads = true;
    options.applyListOps = true;
    options.pFilesystem = &kHostFilesystem;
    if (lusdFlattenFileToBuffer(instance, filename.c_str(), &options,
                                &flattened.data, &flattened.size,
                                nullptr) != LUSD_SUCCESS) {
      lusdDestroyInstance(instance, nullptr);
      return;
    }
    flattened_fs.pUserData = &flattened;
    flattened_fs.pfnReadFile = flattened_read_file;
    flattened_fs.pfnReleaseFile = flattened_release_file;
    flattened_fs.adoptReadFileBuffers = true;
    ci.pIdentifier = "lightrt-composed-mblur.usdc";
    ci.pFilesystem = &flattened_fs;
  }

  LusdLayer layer = LUSD_NULL_HANDLE;
  if (lusdCreateLayer(instance, &ci, &layer) != LUSD_SUCCESS) {
    if (flattened.data) lusd_free(flattened.data);
    lusdDestroyInstance(instance, nullptr);
    return;
  }

  LusdLayer_T* L = reinterpret_cast<LusdLayer_T*>(layer);
  const double open_time = timecode < -1.0e20
                               ? L->metas.start_time_code : timecode;
  double close_time = open_time + shutter_close_offset;

  uint32_t instance_idx = 0;
  for (uint32_t i = 0; i < L->root_spec_count; i++) {
    walk_prim_mblur(L, &L->prim_nodes[L->root_spec_indices[i]],
                    scene, kIdentity4d, close_time, instance_idx);
  }

  uint32_t motion_count = 0;
  for (const auto& inst : scene.instances)
    if (inst.has_motion) motion_count++;
  if (motion_count > 0)
    printf("Motion blur: %u/%zu instances have different close-shutter transforms\n",
           motion_count, scene.instances.size());

  scene.buildAcceleration();

  lusdDestroyLayer(instance, layer);
  if (flattened.data) lusd_free(flattened.data);
  lusdDestroyInstance(instance, nullptr);
}

#else // tinyusdz

#if defined(LIGHTRT_HAS_TINYUSDZ)

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

static bool isSrgbColorSpace(tinyusdz::tydra::ColorSpace cs) {
  using CS = tinyusdz::tydra::ColorSpace;
  return cs == CS::sRGB || cs == CS::sRGB_Texture || cs == CS::sRGB_DisplayP3;
}

static size_t componentBytes(tinyusdz::tydra::ComponentType t) {
  using CT = tinyusdz::tydra::ComponentType;
  switch (t) {
    case CT::UInt8:
    case CT::Int8:  return 1;
    case CT::UInt16:
    case CT::Int16: return 2;
    case CT::Float: return 4;
    default:        return 0;
  }
}

static bool decodeTextureImage(const tinyusdz::tydra::TextureImage& tex_img,
                               const tinyusdz::tydra::BufferData& buf,
                               bool want_srgb,
                               scene::ImageData& out_img) {
  if (tex_img.width <= 0 || tex_img.height <= 0 || tex_img.channels <= 0) return false;
  size_t bpc = componentBytes(buf.componentType);
  if (bpc == 0) return false;

  size_t pixel_count = static_cast<size_t>(tex_img.width) * static_cast<size_t>(tex_img.height);
  size_t needed = pixel_count * static_cast<size_t>(tex_img.channels) * bpc;
  if (buf.data.size() < needed) return false;

  out_img.width = tex_img.width;
  out_img.height = tex_img.height;
  out_img.pixels.resize(pixel_count * 4);

  bool apply_srgb = want_srgb && isSrgbColorSpace(tex_img.colorSpace);
  const uint8_t* src = buf.data.data();
  for (size_t i = 0; i < pixel_count; i++) {
    float rgba[4] = {0.0f, 0.0f, 0.0f, 1.0f};
    for (int c = 0; c < tex_img.channels && c < 4; c++) {
      float v = 0.0f;
      const uint8_t* p = src + (i * tex_img.channels + c) * bpc;
      switch (buf.componentType) {
        case tinyusdz::tydra::ComponentType::UInt8:
          v = (*p) / 255.0f;
          break;
        case tinyusdz::tydra::ComponentType::Int8:
          v = static_cast<const int8_t*>(static_cast<const void*>(p))[0] / 127.0f;
          break;
        case tinyusdz::tydra::ComponentType::UInt16:
          v = static_cast<const uint16_t*>(static_cast<const void*>(p))[0] / 65535.0f;
          break;
        case tinyusdz::tydra::ComponentType::Int16:
          v = static_cast<const int16_t*>(static_cast<const void*>(p))[0] / 32767.0f;
          break;
        case tinyusdz::tydra::ComponentType::Float:
          v = static_cast<const float*>(static_cast<const void*>(p))[0];
          break;
        default:
          break;
      }
      if (apply_srgb && c < 3) v = std::pow(std::max(0.0f, v), 2.2f);
      rgba[c] = v;
    }
    size_t di = i * 4;
    out_img.pixels[di + 0] = rgba[0];
    out_img.pixels[di + 1] = rgba[1];
    out_img.pixels[di + 2] = rgba[2];
    out_img.pixels[di + 3] = rgba[3];
  }
  return true;
}

static int loadTydraTexture(const tinyusdz::tydra::RenderScene& render_scene,
                            scene::Scene& out_scene,
                            std::unordered_map<int64_t, int>& img_map,
                            int32_t tex_id,
                            bool want_srgb) {
  if (tex_id < 0 || static_cast<size_t>(tex_id) >= render_scene.textures.size()) return -1;
  const auto& tex = render_scene.textures[static_cast<size_t>(tex_id)];
  if (tex.texture_image_id < 0 ||
      static_cast<size_t>(tex.texture_image_id) >= render_scene.images.size())
    return -1;

  auto it = img_map.find(tex.texture_image_id);
  if (it != img_map.end()) return it->second;

  const auto& tex_img = render_scene.images[static_cast<size_t>(tex.texture_image_id)];
  if (tex_img.buffer_id < 0 ||
      static_cast<size_t>(tex_img.buffer_id) >= render_scene.buffers.size())
    return -1;

  const auto& buf = render_scene.buffers[static_cast<size_t>(tex_img.buffer_id)];
  scene::ImageData img;
  if (!decodeTextureImage(tex_img, buf, want_srgb, img)) return -1;

  int img_idx = static_cast<int>(out_scene.images.size());
  out_scene.images.emplace_back(std::move(img));
  img_map[tex.texture_image_id] = img_idx;
  printf("    Texture[%d]: \"%s\" %dx%d%s\n", img_idx,
         tex_img.asset_identifier.c_str(), tex_img.width, tex_img.height,
         want_srgb ? "" : " [linear]");
  return img_idx;
}

static bool readFloat2(const tinyusdz::tydra::VertexAttribute& attr,
                       size_t data_index,
                       float out[2]) {
  size_t stride = attr.stride_bytes();
  if (stride == 0) return false;
  const uint8_t* base = attr.get_data().data() + data_index * stride;
  switch (attr.format) {
    case tinyusdz::tydra::VertexAttributeFormat::Vec2: {
      const float* f = reinterpret_cast<const float*>(base);
      out[0] = f[0]; out[1] = f[1];
      return true;
    }
    case tinyusdz::tydra::VertexAttributeFormat::Float: {
      const float* f = reinterpret_cast<const float*>(base);
      out[0] = f[0]; out[1] = f[0];
      return true;
    }
    default:
      return false;
  }
}

static bool readFloat3(const tinyusdz::tydra::VertexAttribute& attr,
                       size_t data_index,
                       float out[3]) {
  size_t stride = attr.stride_bytes();
  if (stride == 0) return false;
  const uint8_t* base = attr.get_data().data() + data_index * stride;
  switch (attr.format) {
    case tinyusdz::tydra::VertexAttributeFormat::Vec3: {
      const float* f = reinterpret_cast<const float*>(base);
      out[0] = f[0]; out[1] = f[1]; out[2] = f[2];
      return true;
    }
    default:
      return false;
  }
}

static bool resolveAttrIndex(const tinyusdz::tydra::VertexAttribute& attr,
                             size_t fv_idx,
                             uint32_t v_idx,
                             size_t tri_idx,
                             const std::vector<size_t>& fv_map,
                             size_t& out_index) {
  size_t mapped_fv = fv_idx;
  if (!fv_map.empty() && fv_idx < fv_map.size()) mapped_fv = fv_map[fv_idx];

  if (attr.is_constant()) {
    out_index = 0;
    return true;
  }
  if (attr.is_uniform()) {
    out_index = tri_idx;
    return true;
  }
  if (attr.is_vertex()) {
    out_index = v_idx;
    return true;
  }
  if (attr.is_facevarying()) {
    out_index = mapped_fv;
    return true;
  }
  if (attr.is_indexed()) {
    if (mapped_fv >= attr.indices.size()) return false;
    out_index = static_cast<size_t>(attr.indices[mapped_fv]);
    return true;
  }
  return false;
}

static void extractMaterials(const tinyusdz::tydra::RenderScene& render_scene,
                             scene::Scene& out_scene) {
  using V3 = lightrt::Vec3;
  auto v3 = [](const tinyusdz::value::float3& f) {
    return V3(f[0], f[1], f[2]);
  };

  std::unordered_map<int64_t, int> image_map;
  out_scene.materials.resize(render_scene.materials.size());
  for (size_t i = 0; i < render_scene.materials.size(); i++) {
    const auto& rm = render_scene.materials[i];
    scene::MaterialData& mat = out_scene.materials[i];

    if (rm.hasOpenPBR()) {
      const auto& p = rm.openPBRShader.value();
      mat.base_weight            = p.base_weight.value;
      mat.base_color             = v3(p.base_color.value);
      mat.base_roughness         = p.base_roughness.value;
      mat.base_metalness         = p.base_metalness.value;
      mat.base_diffuse_roughness = p.base_diffuse_roughness.value;

      mat.specular_weight        = p.specular_weight.value;
      mat.specular_color         = v3(p.specular_color.value);
      mat.specular_roughness     = p.specular_roughness.value;
      mat.specular_ior           = p.specular_ior.value;
      mat.specular_ior_level     = p.specular_ior_level.value;
      mat.specular_anisotropy    = p.specular_anisotropy.value;
      mat.specular_rotation      = p.specular_rotation.value;

      mat.transmission_weight    = p.transmission_weight.value;
      mat.transmission_color     = v3(p.transmission_color.value);
      mat.transmission_depth     = p.transmission_depth.value;
      mat.transmission_scatter   = v3(p.transmission_scatter.value);
      mat.transmission_scatter_anisotropy = p.transmission_scatter_anisotropy.value;
      mat.transmission_dispersion = p.transmission_dispersion.value;

      mat.subsurface_weight      = p.subsurface_weight.value;
      mat.subsurface_color       = v3(p.subsurface_color.value);
      mat.subsurface_radius      = p.subsurface_radius.value;
      mat.subsurface_radius_scale = v3(p.subsurface_radius_scale.value);
      mat.subsurface_scale       = p.subsurface_scale.value;
      mat.subsurface_anisotropy  = p.subsurface_anisotropy.value;

      mat.sheen_weight           = p.sheen_weight.value;
      mat.sheen_color            = v3(p.sheen_color.value);
      mat.sheen_roughness        = p.sheen_roughness.value;

      mat.fuzz_weight            = p.fuzz_weight.value;
      mat.fuzz_color             = v3(p.fuzz_color.value);
      mat.fuzz_roughness         = p.fuzz_roughness.value;

      mat.thin_film_weight       = p.thin_film_weight.value;
      mat.thin_film_thickness    = p.thin_film_thickness.value;
      mat.thin_film_ior          = p.thin_film_ior.value;

      mat.coat_weight            = p.coat_weight.value;
      mat.coat_color             = v3(p.coat_color.value);
      mat.coat_roughness         = p.coat_roughness.value;
      mat.coat_anisotropy        = p.coat_anisotropy.value;
      mat.coat_rotation          = p.coat_rotation.value;
      mat.coat_ior               = p.coat_ior.value;
      mat.coat_affect_color      = v3(p.coat_affect_color.value);
      mat.coat_affect_roughness  = p.coat_affect_roughness.value;

      mat.emission_luminance     = p.emission_luminance.value;
      mat.emission_color         = v3(p.emission_color.value);
      mat.opacity                = p.opacity.value;

      if (p.base_color.is_texture())
        mat.base_color_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                                 p.base_color.texture_id, true);
      if (p.base_metalness.is_texture())
        mat.metalness_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                                p.base_metalness.texture_id, false);
      if (p.base_roughness.is_texture())
        mat.roughness_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                                p.base_roughness.texture_id, false);
      if (p.normal.is_texture())
        mat.normal_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                             p.normal.texture_id, false);
      if (p.emission_color.is_texture())
        mat.emissive_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                               p.emission_color.texture_id, true);
      if (p.opacity.is_texture())
        mat.opacity_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                              p.opacity.texture_id, false);
    } else if (rm.hasUsdPreviewSurface()) {
      const auto& ps = rm.surfaceShader.value();
      mat.base_weight            = 1.0f;
      mat.base_color             = v3(ps.diffuseColor.value);
      mat.base_metalness         = ps.metallic.value;
      mat.specular_weight        = 1.0f;
      mat.specular_color         = v3(ps.specularColor.value);
      mat.specular_roughness     = ps.roughness.value;
      mat.specular_ior           = ps.ior.value;
      mat.coat_weight            = ps.clearcoat.value;
      mat.coat_roughness         = ps.clearcoatRoughness.value;
      mat.emission_color         = v3(ps.emissiveColor.value);
      float esum = ps.emissiveColor.value[0] + ps.emissiveColor.value[1]
                 + ps.emissiveColor.value[2];
      mat.emission_luminance     = (esum > 0.0f) ? 1.0f : 0.0f;
      mat.opacity                = ps.opacity.value;

      if (ps.diffuseColor.is_texture())
        mat.base_color_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                                 ps.diffuseColor.texture_id, true);
      if (ps.metallic.is_texture())
        mat.metalness_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                                ps.metallic.texture_id, false);
      if (ps.roughness.is_texture())
        mat.roughness_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                                ps.roughness.texture_id, false);
      if (ps.normal.is_texture())
        mat.normal_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                             ps.normal.texture_id, false);
      if (ps.emissiveColor.is_texture())
        mat.emissive_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                               ps.emissiveColor.texture_id, true);
      if (ps.opacity.is_texture())
        mat.opacity_tex_id = loadTydraTexture(render_scene, out_scene, image_map,
                                              ps.opacity.texture_id, false);
    }
  }
  if (!out_scene.materials.empty())
    printf("Extracted %zu materials\n", out_scene.materials.size());
}

static void extractLights(const tinyusdz::tydra::RenderScene& render_scene,
                          scene::Scene& out_scene) {
  for (size_t i = 0; i < render_scene.lights.size(); i++) {
    const auto& rl = render_scene.lights[i];
    if (rl.type == tinyusdz::tydra::RenderLight::Type::Dome) continue;

    scene::LightData light;
    float multiplier = rl.intensity * std::pow(2.0f, rl.exposure);
    light.color = lightrt::Vec3(rl.color[0] * multiplier, rl.color[1] * multiplier, rl.color[2] * multiplier);

    if (rl.type == tinyusdz::tydra::RenderLight::Type::Distant) {
      light.type = scene::LightData::Distant;
      float dir_x = -rl.transform.m[0][2];
      float dir_y = -rl.transform.m[1][2];
      float dir_z = -rl.transform.m[2][2];
      float len = std::sqrt(dir_x*dir_x + dir_y*dir_y + dir_z*dir_z);
      if (len > 1e-8f) {
        light.direction = lightrt::Vec3(dir_x/len, dir_y/len, dir_z/len);
      } else {
        light.direction = lightrt::Vec3(rl.direction[0], rl.direction[1], rl.direction[2]).normalize();
      }
    } else if (rl.type == tinyusdz::tydra::RenderLight::Type::Point) {
      light.type = scene::LightData::Point;
      light.position = lightrt::Vec3(
        static_cast<float>(rl.transform.m[3][0]),
        static_cast<float>(rl.transform.m[3][1]),
        static_cast<float>(rl.transform.m[3][2]));
    } else if (rl.type == tinyusdz::tydra::RenderLight::Type::Sphere) {
      light.type = scene::LightData::Sphere;
      light.position = lightrt::Vec3(
        static_cast<float>(rl.transform.m[3][0]),
        static_cast<float>(rl.transform.m[3][1]),
        static_cast<float>(rl.transform.m[3][2]));
      light.radius = std::max(0.0f, static_cast<float>(rl.radius));
    } else if (rl.type == tinyusdz::tydra::RenderLight::Type::Rect) {
      light.type     = scene::LightData::Rect;
      light.position = lightrt::Vec3(
        static_cast<float>(rl.transform.m[3][0]),
        static_cast<float>(rl.transform.m[3][1]),
        static_cast<float>(rl.transform.m[3][2]));
      light.rect_axis_u = lightrt::Vec3(
        static_cast<float>(rl.transform.m[0][0]),
        static_cast<float>(rl.transform.m[1][0]),
        static_cast<float>(rl.transform.m[2][0])).normalize();
      light.rect_axis_v = lightrt::Vec3(
        static_cast<float>(rl.transform.m[0][1]),
        static_cast<float>(rl.transform.m[1][1]),
        static_cast<float>(rl.transform.m[2][1])).normalize();
      light.direction = lightrt::Vec3(
        -static_cast<float>(rl.transform.m[0][2]),
        -static_cast<float>(rl.transform.m[1][2]),
        -static_cast<float>(rl.transform.m[2][2])).normalize();
      light.rect_half_width  = rl.width  * 0.5f;
      light.rect_half_height = rl.height * 0.5f;
    } else {
      continue;
    }
    out_scene.lights.push_back(light);
  }
  if (!out_scene.lights.empty())
    printf("Extracted %zu lights\n", out_scene.lights.size());
}

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
      const uint8_t* src = buf.data.data();
      size_t src_count = buf.data.size();
      for (int y = 0; y < h; y++) {
        for (int x = 0; x < w; x++) {
          size_t si = (static_cast<size_t>(y) * static_cast<size_t>(w) + static_cast<size_t>(x)) * static_cast<size_t>(ch);
          size_t di = (static_cast<size_t>(y) * static_cast<size_t>(w) + static_cast<size_t>(x)) * 3;
          for (int c = 0; c < 3 && si + static_cast<size_t>(c) < src_count; c++) {
            float v = src[si + static_cast<size_t>(c)] / 255.0f;
            if (is_srgb) v = std::pow(v, 2.2f);
            env.pixels[di + static_cast<size_t>(c)] = v * multiplier * rl.color[c];
          }
        }
      }
    }

    scene::shading::buildEnvmapCDF(env);
    printf("Loaded envmap %dx%d from dome light\n", w, h);
    break;
  }
}

bool loadUSDScene(const std::string& filename, double timecode, scene::Scene& out_scene) {
  std::string warn, err;
  tinyusdz::Stage stage;

  bool ret = tinyusdz::LoadUSDFromFile(filename, &stage, &warn, &err);
  if (!warn.empty()) fprintf(stderr, "USD warn: %s\n", warn.c_str());
  if (!ret) {
    fprintf(stderr, "USD load error: %s\n", err.c_str());
    return false;
  }

  {
    tinyusdz::Axis ax = stage.metas().upAxis.get_value();
    if (ax == tinyusdz::Axis::Z) out_scene.up_axis = 1;
    else if (ax == tinyusdz::Axis::X) out_scene.up_axis = 2;
    else out_scene.up_axis = 0;
  }

  if (timecode < -1e29) {
    timecode = stage.metas().startTimeCode.get_value();
  }

  tinyusdz::tydra::RenderScene render_scene;
  tinyusdz::tydra::RenderSceneConverter converter;
  tinyusdz::tydra::RenderSceneConverterEnv env(stage);
  env.mesh_config.triangulate = true;
  env.timecode = timecode;
  env.usd_filename = filename;
  {
    size_t slash_pos = filename.find_last_of("/\\");
    if (slash_pos != std::string::npos) {
      std::string usd_base_dir = filename.substr(0, slash_pos);
      env.set_search_paths({usd_base_dir});
    }
  }

  ret = converter.ConvertToRenderScene(env, &render_scene);
  if (!ret) {
    fprintf(stderr, "Failed to convert USD to render scene\n");
    return false;
  }

  extractMaterials(render_scene, out_scene);

  out_scene.meshes.resize(render_scene.meshes.size());
  for (size_t mi = 0; mi < render_scene.meshes.size(); mi++) {
    const auto& mesh = render_scene.meshes[mi];
    const auto& pts = mesh.points;
    const auto& idx = mesh.faceVertexIndices();
    const auto& fv_map = mesh.triangulatedToOrigFaceVertexIndexMap;

    const tinyusdz::tydra::VertexAttribute* uv_attr = nullptr;
    if (!mesh.texcoords.empty()) {
      auto it = mesh.texcoords.find(0);
      if (it != mesh.texcoords.end()) uv_attr = &it->second;
      else uv_attr = &mesh.texcoords.begin()->second;
    }
    const tinyusdz::tydra::VertexAttribute* normal_attr =
        mesh.normals.empty() ? nullptr : &mesh.normals;

    std::vector<lightrt::Triangle> triangles;
    std::vector<int32_t> mat_ids;
    std::vector<float> pre_uvs;
    std::vector<float> pre_normals;

    if (idx.size() % 3 != 0) {
      fprintf(stderr, "Warning: non-triangulated mesh %zu, skipping\n", mi);
      continue;
    }

    int32_t mesh_mat_id = mesh.material_id;
    out_scene.meshes[mi].default_material_id = mesh_mat_id;

    std::vector<int32_t> face_mat_ids(idx.size() / 3, mesh_mat_id);
    for (const auto& kv : mesh.material_subsetMap) {
      const auto& subset = kv.second;
      const auto& tri_indices = subset.indices();
      for (int ti : tri_indices) {
        if (ti >= 0 && static_cast<size_t>(ti) < face_mat_ids.size())
          face_mat_ids[static_cast<size_t>(ti)] = subset.material_id;
      }
    }

    bool uv_ok = (uv_attr && !uv_attr->empty());
    bool normal_ok = (normal_attr && !normal_attr->empty());
    for (size_t i = 0; i + 2 < idx.size(); i += 3) {
      uint32_t i0 = idx[i], i1 = idx[i + 1], i2 = idx[i + 2];
      if (i0 >= pts.size() || i1 >= pts.size() || i2 >= pts.size()) continue;
      lightrt::Triangle tri;
      tri.v0 = lightrt::Vec3(pts[i0][0], pts[i0][1], pts[i0][2]);
      tri.v1 = lightrt::Vec3(pts[i1][0], pts[i1][1], pts[i1][2]);
      tri.v2 = lightrt::Vec3(pts[i2][0], pts[i2][1], pts[i2][2]);
      triangles.push_back(tri);
      mat_ids.push_back(face_mat_ids[i / 3]);

      if (uv_ok) {
        float uv0[2], uv1[2], uv2[2];
        size_t tri_idx = i / 3;
        size_t di0, di1, di2;
        if (resolveAttrIndex(*uv_attr, i, i0, tri_idx, fv_map, di0) &&
            resolveAttrIndex(*uv_attr, i + 1, i1, tri_idx, fv_map, di1) &&
            resolveAttrIndex(*uv_attr, i + 2, i2, tri_idx, fv_map, di2) &&
            readFloat2(*uv_attr, di0, uv0) &&
            readFloat2(*uv_attr, di1, uv1) &&
            readFloat2(*uv_attr, di2, uv2)) {
          pre_uvs.insert(pre_uvs.end(), {uv0[0], uv0[1], uv1[0], uv1[1], uv2[0], uv2[1]});
        } else {
          uv_ok = false;
          pre_uvs.clear();
        }
      }

      if (normal_ok) {
        float n0[3], n1[3], n2[3];
        size_t tri_idx = i / 3;
        size_t di0, di1, di2;
        if (resolveAttrIndex(*normal_attr, i, i0, tri_idx, fv_map, di0) &&
            resolveAttrIndex(*normal_attr, i + 1, i1, tri_idx, fv_map, di1) &&
            resolveAttrIndex(*normal_attr, i + 2, i2, tri_idx, fv_map, di2) &&
            readFloat3(*normal_attr, di0, n0) &&
            readFloat3(*normal_attr, di1, n1) &&
            readFloat3(*normal_attr, di2, n2)) {
          pre_normals.insert(pre_normals.end(),
                             {n0[0], n0[1], n0[2],
                              n1[0], n1[1], n1[2],
                              n2[0], n2[1], n2[2]});
        } else {
          normal_ok = false;
          pre_normals.clear();
        }
      }
    }
    if (triangles.empty()) continue;

    std::multimap<CentroidKey, size_t> centroid_to_idx;
    for (size_t i = 0; i < triangles.size(); i++) {
      centroid_to_idx.emplace(makeCentroidKey(triangles[i]), i);
    }

    lightrt::AABB& lb = out_scene.meshes[mi].local_bounds;
    for (const auto& tri : triangles) {
      lb.expand(tri.v0);
      lb.expand(tri.v1);
      lb.expand(tri.v2);
    }

    out_scene.meshes[mi].bvh.build(triangles);

    const auto& bvh_tris = out_scene.meshes[mi].bvh.getTriangles();
    auto& remapped_ids = out_scene.meshes[mi].tri_material_ids;
    remapped_ids.resize(bvh_tris.size());
    if (!pre_uvs.empty()) out_scene.meshes[mi].tri_uvs.resize(bvh_tris.size() * 6);
    if (!pre_normals.empty()) out_scene.meshes[mi].tri_normals.resize(bvh_tris.size() * 9);
    for (size_t i = 0; i < bvh_tris.size(); i++) {
      CentroidKey key = makeCentroidKey(bvh_tris[i]);
      auto it = centroid_to_idx.find(key);
      size_t orig = (it != centroid_to_idx.end()) ? it->second : i;
      if (it != centroid_to_idx.end()) centroid_to_idx.erase(it);
      remapped_ids[i] = (orig < mat_ids.size()) ? mat_ids[orig] : mesh_mat_id;
      if (!pre_uvs.empty() && orig * 6 + 5 < pre_uvs.size())
        std::memcpy(&out_scene.meshes[mi].tri_uvs[i * 6],
                    &pre_uvs[orig * 6], 6 * sizeof(float));
      if (!pre_normals.empty() && orig * 9 + 8 < pre_normals.size())
        std::memcpy(&out_scene.meshes[mi].tri_normals[i * 9],
                    &pre_normals[orig * 9], 9 * sizeof(float));
    }
  }

  extractLights(render_scene, out_scene);
  loadEnvmap(render_scene, out_scene);

  std::vector<int> camera_node_indices;
  for (const auto& root_node : render_scene.nodes) {
    walkNodes(render_scene, root_node, out_scene, camera_node_indices);
  }

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
  out_scene.buildAcceleration();
  return !out_scene.instances.empty();
}

void applyMotionBlur(const std::string& filename, double timecode,
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
  scene.buildAcceleration();
}

#else

bool loadUSDScene(const std::string&, double, scene::Scene&) {
  fprintf(stderr, "USD loading not available (TinyUSDZ not found)\n");
  return false;
}

void applyMotionBlur(const std::string&, double, double, scene::Scene&) {}

#endif // LIGHTRT_HAS_TINYUSDZ

#endif // LIGHTRT_USE_LIGHTUSD_C

} // namespace lightrt_common
