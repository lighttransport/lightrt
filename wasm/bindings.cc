// bindings.cc — Emscripten Embind bindings for LightRT WASM API
#ifdef __EMSCRIPTEN__

#include <emscripten/bind.h>
#include <emscripten/val.h>

#include <cstdint>
#include <cstring>
#include <vector>

#include "../lightrt.hh"

namespace {

using emscripten::val;
using namespace lightrt;

// ============================================================================
// Helper: Convert Float32Array (vertices: 9 floats per triangle) to
// std::vector<Triangle>
// ============================================================================

std::vector<Triangle> verticesToTriangles(const val& vertices) {
  std::vector<Triangle> triangles;

  if (vertices.isNull() || !vertices.instanceof(val::global("Float32Array"))) {
    return triangles;
  }

  unsigned length = vertices["length"].as<unsigned>();
  if (length == 0 || length % 9 != 0) {
    return triangles;
  }

  unsigned numTriangles = length / 9;
  triangles.reserve(numTriangles);

  // Get direct pointer to Float32Array buffer
  val heap = val::module_property("HEAPF32");
  unsigned byteOffset = vertices["byteOffset"].as<unsigned>();

  const float* data = reinterpret_cast<const float*>(
      heap["buffer"].as<uintptr_t>() + byteOffset);

  for (unsigned i = 0; i < numTriangles; i++) {
    const float* tri = data + i * 9;
    Vec3 v0(tri[0], tri[1], tri[2]);
    Vec3 v1(tri[3], tri[4], tri[5]);
    Vec3 v2(tri[6], tri[7], tri[8]);
    triangles.emplace_back(v0, v1, v2);
  }

  return triangles;
}

// ============================================================================
// Helper: Convert Uint8Array (raw Triangle data, 36 bytes each) to
// std::vector<Triangle>
// ============================================================================

std::vector<Triangle> rawTrianglesToVector(const val& data) {
  std::vector<Triangle> triangles;

  if (data.isNull() || !data.instanceof(val::global("Uint8Array"))) {
    return triangles;
  }

  unsigned length = data["length"].as<unsigned>();
  if (length == 0 || length % sizeof(Triangle) != 0) {
    return triangles;
  }

  unsigned numTriangles = length / sizeof(Triangle);
  triangles.reserve(numTriangles);

  val heap = val::module_property("HEAPU8");
  unsigned byteOffset = data["byteOffset"].as<unsigned>();

  const uint8_t* ptr = reinterpret_cast<const uint8_t*>(
      heap["buffer"].as<uintptr_t>() + byteOffset);

  const Triangle* tris = reinterpret_cast<const Triangle*>(ptr);
  for (unsigned i = 0; i < numTriangles; i++) {
    triangles.push_back(tris[i]);
  }

  return triangles;
}

// ============================================================================
// Helper: Convert std::vector<uint8_t> to ArrayBuffer
// ============================================================================

val vectorToArrayBuffer(const std::vector<uint8_t>& buffer) {
  if (buffer.empty()) {
    return val::global("ArrayBuffer").new_(0);
  }

  val array = val::global("Uint8Array").new_(buffer.size());
  val heap = val::module_property("HEAPU8");
  uintptr_t dest = heap["buffer"].as<uintptr_t>();

  std::memcpy(reinterpret_cast<void*>(dest), buffer.data(), buffer.size());

  return val::global("ArrayBuffer").new_(buffer.size());
}

// ============================================================================
// Helper: Convert ArrayBuffer to std::vector<uint8_t>
// ============================================================================

std::vector<uint8_t> arrayBufferToVector(const val& buffer) {
  std::vector<uint8_t> result;

  if (buffer.isNull() || !buffer.instanceof(val::global("ArrayBuffer"))) {
    return result;
  }

  val bytes = buffer.call<val>("slice");
  unsigned length = bytes["length"].as<unsigned>();

  if (length == 0) {
    return result;
  }

  result.resize(length);

  val heap = val::module_property("HEAPU8");
  unsigned byteOffset = bytes["byteOffset"].as<unsigned>();

  std::memcpy(result.data(),
              reinterpret_cast<const void*>(heap["buffer"].as<uintptr_t>() + byteOffset),
              length);

  return result;
}

// ============================================================================
// HitResult wrapper (used by trace methods)
// ============================================================================

struct TraceResult {
  bool hit;
  float t;
  float u;
  float v;
  uint32_t prim_id;

  TraceResult() : hit(false), t(0.0f), u(0.0f), v(0.0f), prim_id(kInvalidIndex) {}
  TraceResult(bool h, float tt, float uu, float vv, uint32_t id)
      : hit(h), t(tt), u(uu), v(vv), prim_id(id) {}
};

// ============================================================================
// Helper: convert to Ray for traversal
// ============================================================================

Ray valToRay(float ox, float oy, float oz,
             float dx, float dy, float dz,
             float tmin = 0.0f, float tmax = kInfinity) {
  return Ray(Vec3(ox, oy, oz), Vec3(dx, dy, dz), tmin, tmax);
}

}  // anonymous namespace

// ============================================================================
// Embind bindings
// ============================================================================

EMSCRIPTEN_BINDINGS(lightrt_wasm) {

  // --------------------------------------------------------------------------
  // Basic types
  // --------------------------------------------------------------------------

  emscripten::value_object<Vec3>("Vec3")
      .field("x", &Vec3::x)
      .field("y", &Vec3::y)
      .field("z", &Vec3::z);

  emscripten::value_object<Ray>("Ray")
      .field("origin", &Ray::origin)
      .field("direction", &Ray::direction)
      .field("tmin", &Ray::tmin)
      .field("tmax", &Ray::tmax);

  emscripten::value_object<AABB>("AABB")
      .field("min", &AABB::min)
      .field("max", &AABB::max);

  emscripten::value_object<TraceResult>("TraceResult")
      .field("hit", &TraceResult::hit)
      .field("t", &TraceResult::t)
      .field("u", &TraceResult::u)
      .field("v", &TraceResult::v)
      .field("prim_id", &TraceResult::prim_id);

  // --------------------------------------------------------------------------
  // Build Configuration: BVHBuildConfig
  // --------------------------------------------------------------------------

  emscripten::class_<BVHBuildConfig>("BVHBuildConfig")
      .constructor<>()
      .property("max_leaf_size", &BVHBuildConfig::max_leaf_size)
      .property("min_leaf_size", &BVHBuildConfig::min_leaf_size)
      .property("traversal_cost", &BVHBuildConfig::traversal_cost)
      .property("intersection_cost", &BVHBuildConfig::intersection_cost)
      .property("use_sah", &BVHBuildConfig::use_sah)
      .property("use_binning", &BVHBuildConfig::use_binning)
      .property("num_bins", &BVHBuildConfig::num_bins)
      .property("force_max_leaf_size", &BVHBuildConfig::force_max_leaf_size)
      .property("use_lbvh", &BVHBuildConfig::use_lbvh)
      .property("use_parallel_build", &BVHBuildConfig::use_parallel_build)
      .class_function("fast", &BVHBuildConfig::fast)
      .class_function("quality", &BVHBuildConfig::quality);

  // --------------------------------------------------------------------------
  // Build Configuration: SBVHBuildConfig
  // --------------------------------------------------------------------------

  emscripten::class_<SBVHBuildConfig>("SBVHBuildConfig")
      .constructor<>()
      .property("max_leaf_size", &SBVHBuildConfig::max_leaf_size)
      .property("traversal_cost", &SBVHBuildConfig::traversal_cost)
      .property("intersection_cost", &SBVHBuildConfig::intersection_cost)
      .property("num_spatial_bins", &SBVHBuildConfig::num_spatial_bins)
      .property("num_object_bins", &SBVHBuildConfig::num_object_bins)
      .property("alpha", &SBVHBuildConfig::alpha)
      .property("max_split_factor", &SBVHBuildConfig::max_split_factor)
      .property("compute_leaf_obbs", &SBVHBuildConfig::compute_leaf_obbs)
      .property("obb_volume_threshold", &SBVHBuildConfig::obb_volume_threshold);

  // --------------------------------------------------------------------------
  // Build Configuration: MMapBVHConfig
  // --------------------------------------------------------------------------

  emscripten::class_<MMapBVHConfig>("MMapBVHConfig")
      .constructor<>()
      .property("use_compact_nodes", &MMapBVHConfig::use_compact_nodes)
      .property("use_ordered_traversal", &MMapBVHConfig::use_ordered_traversal)
      .property("build", &MMapBVHConfig::build)
      .class_function("minMemory", &MMapBVHConfig::minMemory)
      .class_function("maxSpeed", &MMapBVHConfig::maxSpeed);

  // --------------------------------------------------------------------------
  // Traversal Configuration
  // --------------------------------------------------------------------------

  emscripten::class_<TraversalConfig>("TraversalConfig")
      .constructor<>()
      .property("max_prim_tests", &TraversalConfig::max_prim_tests)
      .property("exclude_prim_id", &TraversalConfig::exclude_prim_id)
      .property("use_mailboxing", &TraversalConfig::use_mailboxing)
      .property("early_termination", &TraversalConfig::early_termination)
      .class_function("fast", &TraversalConfig::fast)
      .class_function("anyHit", &TraversalConfig::anyHit)
      .class_function("shadowRay", &TraversalConfig::shadowRay)
      .class_function("secondaryRay", &TraversalConfig::secondaryRay);

  // --------------------------------------------------------------------------
  // TriangleBVH
  // --------------------------------------------------------------------------

  emscripten::class_<TriangleBVH>("TriangleBVH")
      .constructor<>()
      .function("build", +[](TriangleBVH& bvh, const val& vertices, const val& config) -> bool {
        auto triangles = verticesToTriangles(vertices);
        if (triangles.empty()) return false;
        BVHBuildConfig cfg;
        if (!config.isNull()) {
          cfg = config.as<BVHBuildConfig>();
        }
        return bvh.build(triangles, cfg);
      })
      .function("buildWithConfig", +[](TriangleBVH& bvh, const val& vertices, const BVHBuildConfig& cfg) -> bool {
        auto triangles = verticesToTriangles(vertices);
        if (triangles.empty()) return false;
        return bvh.build(triangles, cfg);
      })
      .function("trace", +[](TriangleBVH& bvh, const Ray& ray) -> TraceResult {
        float hit_t = kInfinity, hit_u = 0.0f, hit_v = 0.0f;
        uint32_t prim_id = bvh.traverse(ray, hit_t, hit_u, hit_v);
        return TraceResult(prim_id != kInvalidIndex, hit_t, hit_u, hit_v, prim_id);
      })
      .function("trace", +[](TriangleBVH& bvh, float ox, float oy, float oz,
                              float dx, float dy, float dz,
                              float tmin, float tmax) -> TraceResult {
        Ray ray = valToRay(ox, oy, oz, dx, dy, dz, tmin, tmax);
        float hit_t = kInfinity, hit_u = 0.0f, hit_v = 0.0f;
        uint32_t prim_id = bvh.traverse(ray, hit_t, hit_u, hit_v);
        return TraceResult(prim_id != kInvalidIndex, hit_t, hit_u, hit_v, prim_id);
      })
      .function("traceAnyHit", +[](TriangleBVH& bvh, const Ray& ray, uint32_t exclude_prim_id) -> bool {
        return bvh.traverseAnyHit(ray, exclude_prim_id);
      })
      .function("traceAnyHit", +[](TriangleBVH& bvh, float ox, float oy, float oz,
                                    float dx, float dy, float dz,
                                    float tmin, float tmax,
                                    uint32_t exclude_prim_id) -> bool {
        Ray ray = valToRay(ox, oy, oz, dx, dy, dz, tmin, tmax);
        return bvh.traverseAnyHit(ray, exclude_prim_id);
      })
      .function("saveToMemory", +[](const TriangleBVH& bvh) -> val {
        std::vector<uint8_t> buffer;
        bvh.saveToMemory(buffer);
        return vectorToArrayBuffer(buffer);
      })
      .function("loadFromMemory", +[](TriangleBVH& bvh, const val& buffer) -> bool {
        auto data = arrayBufferToVector(buffer);
        if (data.empty()) return false;
        return bvh.loadFromMemory(data.data(), data.size());
      })
      .function("getNumPrimitives", &TriangleBVH::getNumPrimitives);

  // --------------------------------------------------------------------------
  // SBVH (no serialization - uses internal split references)
  // --------------------------------------------------------------------------

  emscripten::class_<SBVH>("SBVH")
      .constructor<>()
      .function("build", +[](SBVH& sbvh, const val& vertices, const val& sbvh_config) -> bool {
        auto triangles = verticesToTriangles(vertices);
        if (triangles.empty()) return false;
        SBVHBuildConfig cfg;
        if (!sbvh_config.isNull()) {
          cfg = sbvh_config.as<SBVHBuildConfig>();
        }
        return sbvh.build(triangles, cfg);
      })
      .function("buildWithConfig", +[](SBVH& sbvh, const val& vertices, const SBVHBuildConfig& cfg) -> bool {
        auto triangles = verticesToTriangles(vertices);
        if (triangles.empty()) return false;
        return sbvh.build(triangles, cfg);
      })
      .function("trace", +[](SBVH& sbvh, const Ray& ray) -> TraceResult {
        float hit_t = kInfinity, hit_u = 0.0f, hit_v = 0.0f;
        uint32_t prim_id = sbvh.traverse(ray, hit_t, hit_u, hit_v);
        return TraceResult(prim_id != kInvalidIndex, hit_t, hit_u, hit_v, prim_id);
      })
      .function("trace", +[](SBVH& sbvh, float ox, float oy, float oz,
                              float dx, float dy, float dz,
                              float tmin, float tmax) -> TraceResult {
        Ray ray = valToRay(ox, oy, oz, dx, dy, dz, tmin, tmax);
        float hit_t = kInfinity, hit_u = 0.0f, hit_v = 0.0f;
        uint32_t prim_id = sbvh.traverse(ray, hit_t, hit_u, hit_v);
        return TraceResult(prim_id != kInvalidIndex, hit_t, hit_u, hit_v, prim_id);
      })
      .function("traceAnyHit", +[](SBVH& sbvh, const Ray& ray, uint32_t exclude_prim_id) -> bool {
        return sbvh.traverseAnyHit(ray, exclude_prim_id);
      })
      .function("traceAnyHit", +[](SBVH& sbvh, float ox, float oy, float oz,
                                    float dx, float dy, float dz,
                                    float tmin, float tmax,
                                    uint32_t exclude_prim_id) -> bool {
        Ray ray = valToRay(ox, oy, oz, dx, dy, dz, tmin, tmax);
        return sbvh.traverseAnyHit(ray, exclude_prim_id);
      })
      .function("getNumPrimitives", &SBVH::getNumPrimitives);

  // --------------------------------------------------------------------------
  // MMapTriangleBVH (no serialization - zero-copy over external data)
  // --------------------------------------------------------------------------

  emscripten::class_<MMapTriangleBVH>("MMapTriangleBVH")
      .constructor<>()
      .function("build", +[](MMapTriangleBVH& bvh, const val& vertices, const val& config) -> bool {
        auto triangles = verticesToTriangles(vertices);
        if (triangles.empty()) return false;
        MMapBVHConfig cfg;
        if (!config.isNull()) {
          cfg = config.as<MMapBVHConfig>();
        }
        return bvh.build(triangles.data(), static_cast<uint32_t>(triangles.size()), cfg);
      })
      .function("buildFromTriangles", +[](MMapTriangleBVH& bvh, const val& data, const val& config) -> bool {
        auto triangles = rawTrianglesToVector(data);
        if (triangles.empty()) return false;
        MMapBVHConfig cfg;
        if (!config.isNull()) {
          cfg = config.as<MMapBVHConfig>();
        }
        return bvh.build(triangles.data(), static_cast<uint32_t>(triangles.size()), cfg);
      })
      .function("trace", +[](MMapTriangleBVH& bvh, const Ray& ray) -> TraceResult {
        float hit_t = kInfinity, hit_u = 0.0f, hit_v = 0.0f;
        uint32_t prim_id = bvh.traverse(ray, hit_t, hit_u, hit_v);
        return TraceResult(prim_id != kInvalidIndex, hit_t, hit_u, hit_v, prim_id);
      })
      .function("trace", +[](MMapTriangleBVH& bvh, float ox, float oy, float oz,
                              float dx, float dy, float dz,
                              float tmin, float tmax) -> TraceResult {
        Ray ray = valToRay(ox, oy, oz, dx, dy, dz, tmin, tmax);
        float hit_t = kInfinity, hit_u = 0.0f, hit_v = 0.0f;
        uint32_t prim_id = bvh.traverse(ray, hit_t, hit_u, hit_v);
        return TraceResult(prim_id != kInvalidIndex, hit_t, hit_u, hit_v, prim_id);
      })
      .function("getTriangleCount", &MMapTriangleBVH::getTriangleCount)
      .function("getBVHMemoryUsage", &MMapTriangleBVH::getBVHMemoryUsage);

  // --------------------------------------------------------------------------
  // Constants
  // --------------------------------------------------------------------------

  emscripten::constant("kInvalidIndex", kInvalidIndex);
  emscripten::constant("kInfinity", kInfinity);
  emscripten::constant("kEpsilon", kEpsilon);
}

#endif  // __EMSCRIPTEN__
