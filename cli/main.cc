// LightRT CLI renderer with USD loading via TinyUSDZ or lightusd-c
// Usage: lightrt_cli input.usd [-o output.png] [-w 800] [-h 600] [-t timecode]
//        [--time-range start end step] [--camera name_or_index]
//        [--mblur-samples N] [--spp N]
//
// Build with -DLIGHTRT_USE_LIGHTUSD_C=ON to use lightusd-c + lydra backend.

#include "scene.hh"
#include "common/sss.hh"

#if defined(LIGHTRT_USE_LIGHTUSD_C)
// lightusd-c Layer API + lydra-c pure-C mesh utilities.
// Bypasses the Stage API (stubbed) and reads prims directly from the Layer.
#include "lightusd/lightusd-c.h"
#include "internal/lusd_layer_internal.h"
#include "lydra_c_scene.h"
#include "lydra_c_mesh.h"
#else
// tinyusdz + tydra backend (default)
#include "tinyusdz.hh"
#include "tydra/render-data.hh"
#include "tydra/scene-access.hh"
#endif

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

// ---------------------------------------------------------------------------
// Backend: shared helpers (BVH build + instance creation from render scene)
// ---------------------------------------------------------------------------

// Build BVH meshes and instances from a generic render scene representation.
// Called by both backends after they fill in a tydra/lydra RenderScene.

#if defined(LIGHTRT_USE_LIGHTUSD_C)
// =========================================================================
// lightusd-c + lydra backend (Layer API, bypasses Stage)
//
// Uses lusdCreateLayer() to parse USDC/USDA into flat prim tables, then
// walks the prim tree directly via LusdLayer_T/LusdPrim_T internals.
// lydra::extract_mesh() materializes mesh data from the layer fields.
// =========================================================================

// Collect all Material prims and extract UsdPreviewSurface data.
// Builds path→index map for material:binding resolution.
static void collect_materials(LusdLayer_T* L, const LusdPrim_T* P,
                              scene::Scene& out_scene,
                              std::map<std::string, int>& mat_map) {
  if (P->type_name && strcmp(P->type_name, "Material") == 0) {
    LydraCMaterialData mat_c;
    LusdResult r = lydra_c_extract_material(
        reinterpret_cast<LusdLayer>(L),
        reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
        &mat_c);
    if (r == LUSD_SUCCESS) {
      // Get prim path for map lookup
      const char* prim_path = nullptr;
      if (P->spec_index < L->spec_count) {
        uint32_t pi = L->specs[P->spec_index].path_index;
        if (pi < L->path_count) prim_path = L->paths[pi];
      }
      if (prim_path) {
        int idx = static_cast<int>(out_scene.materials.size());
        mat_map[prim_path] = idx;

        scene::MaterialData mat;
        mat.base_weight     = 1.0f;
        mat.base_color      = lightrt::Vec3(mat_c.diffuse_color[0], mat_c.diffuse_color[1], mat_c.diffuse_color[2]);
        mat.base_metalness  = mat_c.metallic;
        mat.specular_weight = 1.0f;
        mat.specular_color  = lightrt::Vec3(mat_c.specular_color[0], mat_c.specular_color[1], mat_c.specular_color[2]);
        mat.specular_roughness = mat_c.roughness;
        mat.specular_ior    = mat_c.ior;
        mat.coat_weight     = mat_c.clearcoat;
        mat.coat_roughness  = mat_c.clearcoat_roughness;
        mat.emission_luminance = (mat_c.emissive_color[0] + mat_c.emissive_color[1] + mat_c.emissive_color[2] > 0.0f) ? 1.0f : 0.0f;
        mat.emission_color  = lightrt::Vec3(mat_c.emissive_color[0], mat_c.emissive_color[1], mat_c.emissive_color[2]);
        mat.opacity         = mat_c.opacity;

        out_scene.materials.push_back(mat);
        printf("  Material[%d]: \"%s\" diffuse=(%.2f,%.2f,%.2f) metallic=%.2f roughness=%.2f\n",
               idx, prim_path,
               mat_c.diffuse_color[0], mat_c.diffuse_color[1], mat_c.diffuse_color[2],
               mat_c.metallic, mat_c.roughness);
      }
    }
  }
  for (uint32_t j = 0; j < P->child_count; j++)
    collect_materials(L, &L->prim_nodes[P->child_spec_indices[j]], out_scene, mat_map);
}

// Recursive DFS over prim tree, extracting Mesh prims
static void walk_prim(LusdLayer_T* L, const LusdPrim_T* P,
                      scene::Scene& out_scene,
                      const std::map<std::string, int>& mat_map) {
  // Check if this prim is a Mesh
  if (P->type_name && strcmp(P->type_name, "Mesh") == 0) {
    LydraCMeshData mesh_data_c;
    LusdResult r = lydra_c_extract_mesh(
        reinterpret_cast<LusdLayer>(L),
        reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
        &mesh_data_c);
    if (r == LUSD_SUCCESS) {
      // Triangulate
      uint32_t* tri_idx = nullptr;
      uint32_t  tri_idx_count = 0;
      bool owns_tri_idx = false;

      // Build face_to_tri_start mapping for GeomSubset support
      // face_to_tri_start[fi] = index of first triangle produced by face fi
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

        // Compute face-to-triangle start indices
        face_to_tri_start.resize(mesh_data_c.fvc_count);
        uint32_t tri_offset = 0;
        for (uint32_t fi = 0; fi < mesh_data_c.fvc_count; fi++) {
          face_to_tri_start[fi] = tri_offset;
          int32_t fvc = mesh_data_c.face_vertex_counts[fi];
          if (fvc >= 3) tri_offset += static_cast<uint32_t>(fvc - 2);
        }
      } else {
        // Already triangulated — cast int32_t* to uint32_t*
        tri_idx = reinterpret_cast<uint32_t*>(mesh_data_c.face_vertex_indices);
        tri_idx_count = mesh_data_c.fvi_count;
      }

      // Build lightrt triangles
      uint32_t pt_count = mesh_data_c.point_count;
      std::vector<lightrt::Triangle> triangles;
      triangles.reserve(tri_idx_count / 3);
      for (uint32_t i = 0; i + 2 < tri_idx_count; i += 3) {
        uint32_t i0 = tri_idx[i], i1 = tri_idx[i + 1], i2 = tri_idx[i + 2];
        if (i0 >= pt_count || i1 >= pt_count || i2 >= pt_count) continue;
        lightrt::Triangle tri;
        tri.v0 = lightrt::Vec3(mesh_data_c.points[i0*3], mesh_data_c.points[i0*3+1], mesh_data_c.points[i0*3+2]);
        tri.v1 = lightrt::Vec3(mesh_data_c.points[i1*3], mesh_data_c.points[i1*3+1], mesh_data_c.points[i1*3+2]);
        tri.v2 = lightrt::Vec3(mesh_data_c.points[i2*3], mesh_data_c.points[i2*3+1], mesh_data_c.points[i2*3+2]);
        triangles.push_back(tri);
      }

      if (owns_tri_idx) free(tri_idx);

      if (!triangles.empty()) {
        size_t mi = out_scene.meshes.size();
        out_scene.meshes.emplace_back();
        auto& md = out_scene.meshes.back();
        // Resolve material:binding
        int32_t mat_id = -1;
        const char* mat_path = lydra_c_resolve_material_binding(
            reinterpret_cast<LusdLayer>(L),
            reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)));
        if (mat_path) {
          auto it = mat_map.find(mat_path);
          if (it != mat_map.end()) mat_id = it->second;
        }
        md.default_material_id = mat_id;
        md.tri_material_ids.assign(triangles.size(), mat_id);

        // GeomSubset per-face material assignment
        LydraCGeomSubset* subsets = nullptr;
        uint32_t subset_count = lydra_c_extract_geom_subsets(
            reinterpret_cast<LusdLayer>(L),
            reinterpret_cast<LusdPrim>(const_cast<LusdPrim_T*>(P)),
            &subsets);
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
                if (tri_id < md.tri_material_ids.size())
                  md.tri_material_ids[tri_id] = subset_mat_id;
              }
            }
          }
          lydra_c_free_geom_subsets(subsets, subset_count);
        }

        lightrt::AABB& lb = md.local_bounds;
        for (const auto& tri : triangles) {
          lb.expand(tri.v0); lb.expand(tri.v1); lb.expand(tri.v2);
        }
        md.bvh.build(triangles);

        // Identity transform (xform not yet extracted from layer)
        scene::Instance inst;
        inst.mesh_id = static_cast<uint32_t>(mi);
        std::memset(inst.transform, 0, sizeof(inst.transform));
        inst.transform[0] = 1.0f; inst.transform[5] = 1.0f; inst.transform[10] = 1.0f;
        std::memcpy(inst.inv_transform,       inst.transform, sizeof(inst.transform));
        std::memcpy(inst.transform_close,     inst.transform, sizeof(inst.transform));
        std::memcpy(inst.inv_transform_close, inst.transform, sizeof(inst.transform));
        inst.has_motion  = false;
        inst.world_bounds = md.local_bounds;
        out_scene.scene_bounds.expand(inst.world_bounds);
        out_scene.instances.push_back(inst);
      }

      lydra_c_free_mesh_data(&mesh_data_c);
    }
  }

recurse:
  // Recurse into children
  for (uint32_t j = 0; j < P->child_count; j++) {
    walk_prim(L, &L->prim_nodes[P->child_spec_indices[j]], out_scene, mat_map);
  }
}

static bool loadUSDScene(const std::string& filename, double /*timecode*/,
                         scene::Scene& out_scene) {
  // Create lightusd-c instance
  LusdInstanceCreateInfo inst_info = {};
  inst_info.sType          = LUSD_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
  inst_info.pNext          = nullptr;
  inst_info.apiVersion     = 1;
  inst_info.pApplicationName   = "lightrt_cli";
  inst_info.applicationVersion = 1;

  LusdInstance instance = LUSD_NULL_HANDLE;
  LusdResult r = lusdCreateInstance(&inst_info, nullptr, &instance);
  if (r != LUSD_SUCCESS) {
    fprintf(stderr, "lightusd-c: lusdCreateInstance failed: %s\n",
            lusdResultToString(r));
    return false;
  }

  // Create layer (parses USDC/USDA into flat tables)
  LusdLayerCreateInfo ci = {};
  ci.sType     = LUSD_STRUCTURE_TYPE_LAYER_CREATE_INFO;
  ci.pNext     = nullptr;
  ci.pIdentifier = filename.c_str();

  LusdLayer layer = LUSD_NULL_HANDLE;
  r = lusdCreateLayer(instance, &ci, &layer);
  if (r != LUSD_SUCCESS) {
    fprintf(stderr, "lightusd-c: lusdCreateLayer failed: %s (%s)\n",
            lusdResultToString(r), lusdGetLastError(instance));
    lusdDestroyInstance(instance, nullptr);
    return false;
  }

  // Walk prim tree via internal Layer/Prim structs
  LusdLayer_T* L = reinterpret_cast<LusdLayer_T*>(layer);

  // Pass 1: Collect materials
  std::map<std::string, int> mat_map;
  for (uint32_t i = 0; i < L->root_spec_count; i++) {
    collect_materials(L, &L->prim_nodes[L->root_spec_indices[i]], out_scene, mat_map);
  }

  // Pass 2: Extract meshes with material binding
  for (uint32_t i = 0; i < L->root_spec_count; i++) {
    walk_prim(L, &L->prim_nodes[L->root_spec_indices[i]], out_scene, mat_map);
  }

  lusdDestroyLayer(instance, layer);
  lusdDestroyInstance(instance, nullptr);

  printf("Loaded %zu meshes, %zu instances, %zu materials (lightusd-c layer)\n",
         out_scene.meshes.size(), out_scene.instances.size(),
         out_scene.materials.size());
  return !out_scene.instances.empty();
}

// Motion blur: xform time-sample API not yet implemented in lightusd-c.
static void applyMotionBlur(const std::string& /*filename*/,
                            double /*timecode*/,
                            double /*shutter_close_offset*/,
                            scene::Scene& /*scene*/) {}

#else
// =========================================================================
// tinyusdz + tydra backend (default)
// =========================================================================

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

// Extract materials from RenderScene (full OpenPBR field mapping)
static void extractMaterials(const tinyusdz::tydra::RenderScene& render_scene,
                             scene::Scene& out_scene) {
  using V3 = lightrt::Vec3;
  auto v3 = [](const tinyusdz::value::float3& f) {
    return V3(f[0], f[1], f[2]);
  };

  out_scene.materials.resize(render_scene.materials.size());
  for (size_t i = 0; i < render_scene.materials.size(); i++) {
    const auto& rm = render_scene.materials[i];
    scene::MaterialData& mat = out_scene.materials[i];

    if (rm.hasOpenPBR()) {
      printf("  mat[%zu]: OpenPBR (sss_w=%.3f sss_r=%.3f base_color=(%.2f,%.2f,%.2f))\n",
             i, rm.openPBRShader->subsurface_weight.value,
             rm.openPBRShader->subsurface_radius.value,
             rm.openPBRShader->base_color.value[0],
             rm.openPBRShader->base_color.value[1],
             rm.openPBRShader->base_color.value[2]);
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
    } else if (rm.hasUsdPreviewSurface()) {
      printf("  mat[%zu]: UsdPreviewSurface (diffuse=(%.2f,%.2f,%.2f))\n",
             i, rm.surfaceShader->diffuseColor.value[0],
             rm.surfaceShader->diffuseColor.value[1],
             rm.surfaceShader->diffuseColor.value[2]);
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
    }
    // else: default OpenPBR material (grey dielectric from struct defaults)
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
        static_cast<float>(rl.transform.m[3][0]),
        static_cast<float>(rl.transform.m[3][1]),
        static_cast<float>(rl.transform.m[3][2]));
    } else if (rl.type == tinyusdz::tydra::RenderLight::Type::Rect) {
      light.type     = scene::LightData::Rect;
      light.position = lightrt::Vec3(
        static_cast<float>(rl.transform.m[3][0]),
        static_cast<float>(rl.transform.m[3][1]),
        static_cast<float>(rl.transform.m[3][2]));
      // matrix4f: m[row][col]. Local axis j = col j = (m[0][j], m[1][j], m[2][j]).
      light.rect_axis_u = lightrt::Vec3(           // col 0 = local +X
        static_cast<float>(rl.transform.m[0][0]),
        static_cast<float>(rl.transform.m[1][0]),
        static_cast<float>(rl.transform.m[2][0])).normalize();
      light.rect_axis_v = lightrt::Vec3(           // col 1 = local +Y
        static_cast<float>(rl.transform.m[0][1]),
        static_cast<float>(rl.transform.m[1][1]),
        static_cast<float>(rl.transform.m[2][1])).normalize();
      light.direction = lightrt::Vec3(             // -(col 2) = outward normal
        -static_cast<float>(rl.transform.m[0][2]),
        -static_cast<float>(rl.transform.m[1][2]),
        -static_cast<float>(rl.transform.m[2][2])).normalize();
      light.rect_half_width  = rl.width  * 0.5f;
      light.rect_half_height = rl.height * 0.5f;
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

#endif // LIGHTRT_USE_LIGHTUSD_C

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

// ─────────────────────────────────────────────────────────────────────────────
// Random-Walk Subsurface Scattering
//
// Algorithm:  Chiang, Kutz, Burley — SIGGRAPH 2016, with:
//   • Henyey-Greenstein anisotropic phase function  (g = subsurface_anisotropy)
//   • Luminance-weighted spectral channel MIS       (lower variance for chromatic)
//   • Correct throughput accounting for HG PDF      (see inline comments)
//   • Thin-shape guard via initial thickness probe
// ─────────────────────────────────────────────────────────────────────────────
struct SSSResult {
    lightrt::Vec3  exit_pos;           // world-space exit point
    lightrt::Vec3  exit_normal;        // world-space outward normal at exit
    lightrt::Vec3  throughput;         // spectral transport weight
    uint32_t       exit_instance_id;
    uint32_t       exit_triangle_id;
    bool           success;
};

// Compute the outward world-space normal for triangle `tri_id` in instance `inst`.
static lightrt::Vec3 computeWorldNormal(const scene::Scene& scene,
                                         uint32_t inst_id, uint32_t tri_id) {
    const auto& inst = scene.instances[inst_id];
    const auto& tris = scene.meshes[inst.mesh_id].bvh.getTriangles();
    const auto& tri  = tris[tri_id];
    lightrt::Vec3 local_n = (tri.v1 - tri.v0).cross(tri.v2 - tri.v0).normalize();
    return scene::transformNormal(inst.inv_transform, local_n).normalize();
}

static SSSResult randomWalkSSS(
        const scene::Scene&       scene,
        const lightrt::Vec3&      entry_pos,        // world entry point
        const lightrt::Vec3&      entry_N,           // outward normal at entry
        uint32_t                  entry_instance_id,
        const scene::MaterialData& mat,
        std::mt19937&             rng,
        std::uniform_real_distribution<float>& dist01)
{
    using namespace lightrt_common::sss;
    SSSResult result{};
    result.success = false;

    // ── 1. Compute volume coefficients ────────────────────────────────────────
    const SSSCoeffs c = computeCoeffsFromMaterial(mat);

    // If all channels are nearly opaque, fall back to surface shading.
    if (c.sigma_t.x > 1e14f && c.sigma_t.y > 1e14f && c.sigma_t.z > 1e14f)
        return result;

    float g = std::max(-0.99f, std::min(0.99f, mat.subsurface_anisotropy));

    // ── 2. Thin-shape thickness probe ─────────────────────────────────────────
    // Cast a probe ray along the inward normal to estimate the local slab
    // thickness.  This caps the first free-path sample and avoids spending
    // budget on nearly-transparent thick shapes.
    float thickness = kInfThickness;
    {
        lightrt::Vec3 inward = entry_N * -1.0f;
        lightrt::Ray probe(entry_pos + inward * 1e-3f, inward, 0.0f, 1000.0f);
        scene::HitInfo probe_hit = scene::traceScene(scene, probe);
        if (probe_hit.instance_id == entry_instance_id)
            thickness = probe_hit.t + 1e-3f;   // include the entry offset
    }

    // ── 3. Sample entry direction (Lambertian BTDF into the medium) ───────────
    lightrt::Vec3 inward_N = entry_N * -1.0f;   // points into the surface
    lightrt::Vec3 ray_dir  = sampleCosineHemisphere(inward_N,
                                                     dist01(rng), dist01(rng));
    // Ensure direction is into the surface
    if (ray_dir.dot(inward_N) <= 0.0f) ray_dir = ray_dir * -1.0f;

    lightrt::Vec3 ray_pos   = entry_pos + inward_N * 1e-3f;
    lightrt::Vec3 throughput(1.0f, 1.0f, 1.0f);

    constexpr int kMaxBounces = 512;

    // ── 4. Random walk ────────────────────────────────────────────────────────
    for (int bounce = 0; bounce < kMaxBounces; ++bounce) {

        // Channel selection + free-path sampling
        lightrt::Vec3 ch_pdf;
        int ch = sampleChannel(throughput, c.sigma_s, dist01(rng), ch_pdf);

        float t_max  = sampleFreePath(c.sigma_t, ch, dist01(rng));

        // On the first bounce, clamp to estimated thickness to avoid wasted
        // traversal deep inside thick shapes that are effectively opaque.
        if (bounce == 0) t_max = std::min(t_max, thickness);

        // Trace limited ray
        lightrt::Ray walk_ray(ray_pos, ray_dir, 1e-4f, t_max);
        scene::HitInfo hit = scene::traceScene(scene, walk_ray);

        if (hit.instance_id != lightrt::kInvalidIndex &&
            hit.instance_id == entry_instance_id)
        {
            // ── Exit surface found on the same object ─────────────────────────
            float t       = hit.t;
            lightrt::Vec3 tau = transmittance(c.sigma_t, t);

            // MIS weight:  balance estimator over the three channel PDFs
            float pdf_sum = ch_pdf.x * tau.x * c.sigma_t.x   // would use ch0
                          + ch_pdf.y * tau.y * c.sigma_t.y   // ch1
                          + ch_pdf.z * tau.z * c.sigma_t.z;  // ch2
            // For a surface event the PDF is transmittance (no sigma_t factor):
            float exit_pdf = ch_pdf.x * tau.x
                           + ch_pdf.y * tau.y
                           + ch_pdf.z * tau.z;
            if (exit_pdf < 1e-16f) break;

            throughput.x *= tau.x / exit_pdf;
            throughput.y *= tau.y / exit_pdf;
            throughput.z *= tau.z / exit_pdf;
            (void)pdf_sum;

            // Compute exit normal (world-space, oriented outward).
            // computeWorldNormal returns the geometric (winding-order) normal.
            // For a closed mesh the geometric normal points outward.  When the
            // walk exits from inside, ray_dir and the outward normal are in the
            // same hemisphere.  If they aren't (re-entrant geometry, degenerate
            // triangle), flip so exit_N always faces the same side as ray_dir
            // (i.e. outward from the surface toward the exterior world).
            lightrt::Vec3 exit_N = computeWorldNormal(scene,
                                                       hit.instance_id,
                                                       hit.triangle_id);
            if (exit_N.dot(ray_dir) < 0.0f) exit_N = exit_N * -1.0f;

            // Clamp throughput components: individual channels can grow before
            // Russian roulette suppresses them; cap to avoid firefly blowout.
            constexpr float kMaxTp = 1e4f;
            throughput.x = std::max(0.0f, std::min(throughput.x, kMaxTp));
            throughput.y = std::max(0.0f, std::min(throughput.y, kMaxTp));
            throughput.z = std::max(0.0f, std::min(throughput.z, kMaxTp));

            result.exit_pos          = ray_pos + ray_dir * t;
            result.exit_normal       = exit_N;
            result.throughput        = throughput;
            result.exit_instance_id  = hit.instance_id;
            result.exit_triangle_id  = hit.triangle_id;
            result.success           = true;
            return result;
        }

        // ── No surface hit: scatter inside the medium ─────────────────────────
        float t        = t_max;
        lightrt::Vec3 tau = transmittance(c.sigma_t, t);

        // Throughput update for a scatter event [Chiang16 §3]:
        //   weight *= (sigma_s * tau) / pdf_scatter
        // where pdf_scatter = sum_ch(ch_pdf[ch] * sigma_t[ch] * tau[ch])
        float pdf_scatter = ch_pdf.x * c.sigma_t.x * tau.x
                          + ch_pdf.y * c.sigma_t.y * tau.y
                          + ch_pdf.z * c.sigma_t.z * tau.z;
        if (pdf_scatter < 1e-16f) break;

        throughput.x *= c.sigma_s.x * tau.x / pdf_scatter;
        throughput.y *= c.sigma_s.y * tau.y / pdf_scatter;
        throughput.z *= c.sigma_s.z * tau.z / pdf_scatter;

        // Guard against nan/inf produced by a degenerate sigma_s or tau value.
        if (!std::isfinite(throughput.x) || !std::isfinite(throughput.y) ||
            !std::isfinite(throughput.z)) break;

        // Advance position
        ray_pos = ray_pos + ray_dir * t;

        // ── Russian roulette ──────────────────────────────────────────────────
        float lum = 0.2126f * throughput.x
                  + 0.7152f * throughput.y
                  + 0.0722f * throughput.z;
        lum = std::max(0.0f, std::min(1.0f, lum));
        if (dist01(rng) >= lum) break;
        throughput.x /= lum;
        throughput.y /= lum;
        throughput.z /= lum;

        // ── Sample new direction via Henyey-Greenstein ────────────────────────
        // Build ONB around current ray_dir (forward = ray_dir)
        lightrt::Vec3 T, B;
        buildONB(ray_dir, T, B);
        lightrt::Vec3 local_scatter = sampleHGLocal(g, dist01(rng), dist01(rng));
        ray_dir = toWorld(local_scatter, T, B, ray_dir).normalize();

        // Note: for HG, pdf(omega) == p(omega) (phase function = its own PDF),
        // so the direction weight = p / pdf = 1. No extra factor needed.
    }

    return result;   // absorbed or max bounces exceeded
}

// ─────────────────────────────────────────────────────────────────────────────

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

          // SSS: subsurface_weight blends BRDF ↔ random-walk SSS.
          // brdf_scale  = fraction of direct lighting from the surface BRDF.
          // sss_weight  = fraction routed through the subsurface walk.
          const float sss_weight  = (mat.subsurface_radius > 1e-8f)
                                      ? std::max(0.0f, std::min(1.0f, mat.subsurface_weight))
                                      : 0.0f;
          const float brdf_scale  = 1.0f - sss_weight;

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
            // ── Analytic light loop ─────────────────────────────────────────────
            for (const auto& light : scene.lights) {
              lightrt::Vec3 L;
              float light_dist = 1e20f;

              // Geometry factor for area lights (one-sided: front only)
              float geom_factor = 1.0f;

              if (light.type == scene::LightData::Distant) {
                L = light.direction * -1.0f;
              } else if (light.type == scene::LightData::Point) {
                lightrt::Vec3 to_light = light.position - hit_pos;
                light_dist = to_light.length();
                if (light_dist < 1e-6f) continue;
                L = to_light * (1.0f / light_dist);
              } else if (light.type == scene::LightData::Rect) {
                // Sample a random point on the rect surface
                float u = dist01(rng) * 2.0f - 1.0f; // [-1, 1]
                float v = dist01(rng) * 2.0f - 1.0f;
                lightrt::Vec3 sample_pos =
                  light.position
                  + light.rect_axis_u * (u * light.rect_half_width)
                  + light.rect_axis_v * (v * light.rect_half_height);
                lightrt::Vec3 to_light = sample_pos - hit_pos;
                light_dist = to_light.length();
                if (light_dist < 1e-6f) continue;
                L = to_light * (1.0f / light_dist);
                // Reject if shading point is behind the rect
                float cos_emit = light.direction.dot(L * -1.0f);
                if (cos_emit <= 0.0f) continue;
                // Geometry term: (1/r^2) * cos_emit * rect_area / pdf
                // pdf = 1/(width*height), area = width*height → area/pdf = 1
                float rect_area = (light.rect_half_width * 2.0f) * (light.rect_half_height * 2.0f);
                geom_factor = cos_emit * rect_area / (light_dist * light_dist);
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
              } else if (light.type == scene::LightData::Rect) {
                light_contribution = light_contribution * geom_factor;
              }

              color = color + lightrt::Vec3(
                brdf_ndl.x * light_contribution.x,
                brdf_ndl.y * light_contribution.y,
                brdf_ndl.z * light_contribution.z) * brdf_scale;
            }

            // ── Envmap MIS (if dome light exists) ───────────────────────────────
            if (has_envmap) {
              float alpha = std::max(0.001f, mat.specular_roughness * mat.specular_roughness);
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
                    lightrt::Vec3 H = (V + L).normalize();
                    float NdotH = std::max(0.0f, N.dot(H));
                    float VdotH = std::max(0.0f, V.dot(H));
                    float brdf_pdf = pdfGGX(NdotH, VdotH, alpha);
                    float combined_brdf_pdf = 0.5f * brdf_pdf + 0.5f * NdotL * kInvPi;
                    float w = misBalance(env_pdf, combined_brdf_pdf);
                    lightrt::Vec3 contrib(
                      brdf_ndl.x * env_col.x * w / env_pdf,
                      brdf_ndl.y * env_col.y * w / env_pdf,
                      brdf_ndl.z * env_col.z * w / env_pdf);
                    color = color + contrib * brdf_scale;
                  }
                }
              }

              // 2) BRDF sample
              {
                bool sample_diffuse = dist01(rng) < 0.5f;
                lightrt::Vec3 L;
                if (sample_diffuse) {
                  float r1 = dist01(rng), r2 = dist01(rng);
                  float cos_theta = std::sqrt(1.0f - r1);
                  float sin_theta = std::sqrt(r1);
                  float phi = 2.0f * kPi * r2;
                  lightrt::Vec3 local(sin_theta * std::cos(phi), sin_theta * std::sin(phi), cos_theta);
                  L = toWorld(local, N, T, B);
                } else {
                  lightrt::Vec3 H_local = sampleGGX(dist01(rng), dist01(rng), alpha);
                  lightrt::Vec3 H = toWorld(H_local, N, T, B);
                  L = V * -1.0f + H * (2.0f * V.dot(H));
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
                      color = color + contrib * brdf_scale;
                    }
                  }
                }
              }
            }

            // ── Random-Walk Subsurface Scattering ───────────────────────────────
            if (sss_weight > 1e-4f) {
              SSSResult sss_r = randomWalkSSS(scene, hit_pos, N,
                                              hit.instance_id, mat, rng, dist01);
              if (sss_r.success) {
                const lightrt::Vec3& eN      = sss_r.exit_normal;
                const lightrt::Vec3& eP      = sss_r.exit_pos;
                const lightrt::Vec3& tp      = sss_r.throughput;

                // At the exit surface use a Lambertian BRDF:
                //   f_exit = base_color * NdotL / π
                // The SSS walk's throughput already accounts for volume transport.

                // 1) Analytic lights at exit
                for (const auto& light : scene.lights) {
                  lightrt::Vec3 Lex;
                  float ld = 1e20f;
                  float sss_geom = 1.0f;
                  if (light.type == scene::LightData::Distant) {
                    Lex = light.direction * -1.0f;
                  } else if (light.type == scene::LightData::Point) {
                    lightrt::Vec3 tl = light.position - eP;
                    ld = tl.length();
                    if (ld < 1e-6f) continue;
                    Lex = tl * (1.0f / ld);
                  } else if (light.type == scene::LightData::Rect) {
                    float u = dist01(rng) * 2.0f - 1.0f;
                    float v = dist01(rng) * 2.0f - 1.0f;
                    lightrt::Vec3 sp = light.position
                      + light.rect_axis_u * (u * light.rect_half_width)
                      + light.rect_axis_v * (v * light.rect_half_height);
                    lightrt::Vec3 tl = sp - eP;
                    ld = tl.length();
                    if (ld < 1e-6f) continue;
                    Lex = tl * (1.0f / ld);
                    float cos_emit = light.direction.dot(Lex * -1.0f);
                    if (cos_emit <= 0.0f) continue;
                    float rect_area = (light.rect_half_width*2.0f)*(light.rect_half_height*2.0f);
                    sss_geom = cos_emit * rect_area / (ld * ld);
                  } else { continue; }

                  float NdotL_ex = std::max(0.0f, eN.dot(Lex));
                  if (NdotL_ex <= 0.0f) continue;

                  lightrt::Ray sh(eP + eN * bias, Lex, 0.0f, ld - bias);
                  if (scene::traceSceneAnyHit(scene, sh,
                        sss_r.exit_instance_id, sss_r.exit_triangle_id,
                        ray_time)) continue;

                  lightrt::Vec3 lc = light.color;
                  if (light.type == scene::LightData::Point)
                    lc = lc * (1.0f / (ld * ld));
                  else if (light.type == scene::LightData::Rect)
                    lc = lc * sss_geom;

                  // Lambert at exit ⊗ sss throughput ⊗ base_color
                  float lambert = NdotL_ex * kInvPi;
                  color = color + lightrt::Vec3(
                    lc.x * mat.base_color.x * lambert * tp.x,
                    lc.y * mat.base_color.y * lambert * tp.y,
                    lc.z * mat.base_color.z * lambert * tp.z) * sss_weight;
                }

                // 2) Envmap at exit (one sample, cosine-weighted)
                if (has_envmap) {
                  // Envmap importance sample
                  float env_pdf = 0.0f;
                  lightrt::Vec3 Lex = sampleEnvmap(scene.envmap,
                                                    dist01(rng), dist01(rng),
                                                    env_pdf);
                  float NdotL_ex = std::max(0.0f, eN.dot(Lex));
                  if (NdotL_ex > 0.0f && env_pdf > 1e-8f) {
                    lightrt::Ray sh(eP + eN * bias, Lex);
                    if (!scene::traceSceneAnyHit(scene, sh,
                          sss_r.exit_instance_id, sss_r.exit_triangle_id,
                          ray_time)) {
                      lightrt::Vec3 env_col = evalEnvmap(scene.envmap, Lex);
                      float lambert = NdotL_ex * kInvPi;
                      // MIS: combine envmap PDF with Lambert PDF
                      float lam_pdf = NdotL_ex * kInvPi;
                      float wm = misBalance(env_pdf, lam_pdf);
                      color = color + lightrt::Vec3(
                        env_col.x * mat.base_color.x * lambert * tp.x * wm / env_pdf,
                        env_col.y * mat.base_color.y * lambert * tp.y * wm / env_pdf,
                        env_col.z * mat.base_color.z * lambert * tp.z * wm / env_pdf) * sss_weight;
                    }
                  }

                  // BRDF sample (cosine-weighted hemisphere at exit)
                  {
                    lightrt::Vec3 eT, eB;
                    buildONB(eN, eT, eB);
                    float r1 = dist01(rng), r2 = dist01(rng);
                    float cos_t = std::sqrt(1.0f - r1);
                    float sin_t = std::sqrt(r1);
                    float phi   = 2.0f * kPi * r2;
                    lightrt::Vec3 local(sin_t * std::cos(phi), sin_t * std::sin(phi), cos_t);
                    lightrt::Vec3 Lex2 = toWorld(local, eN, eT, eB);
                    float NdotL2 = std::max(0.0f, eN.dot(Lex2));
                    if (NdotL2 > 0.0f) {
                      lightrt::Ray sh2(eP + eN * bias, Lex2);
                      if (!scene::traceSceneAnyHit(scene, sh2,
                            sss_r.exit_instance_id, sss_r.exit_triangle_id,
                            ray_time)) {
                        lightrt::Vec3 env_col2 = evalEnvmap(scene.envmap, Lex2);
                        float lam_pdf2 = NdotL2 * kInvPi;
                        float env_pdf2 = envmapPDF(scene.envmap, Lex2);
                        float wm2 = misBalance(lam_pdf2, env_pdf2);
                        if (lam_pdf2 > 1e-8f) {
                          float lambert2 = NdotL2 * kInvPi;
                          color = color + lightrt::Vec3(
                            env_col2.x * mat.base_color.x * lambert2 * tp.x * wm2 / lam_pdf2,
                            env_col2.y * mat.base_color.y * lambert2 * tp.y * wm2 / lam_pdf2,
                            env_col2.z * mat.base_color.z * lambert2 * tp.z * wm2 / lam_pdf2) * sss_weight;
                        }
                      }
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
