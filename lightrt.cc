// Copyright (c) 2026 Light Transport Entertainment, Inc.
// SPDX-License-Identifier: MIT
//
// lightrt.cc - Lightweight ray tracing and BVH kernel implementation

#include "lightrt.hh"

namespace lightrt {

// ============================================================================
// AABB Ray Intersection (Scalar)
// ============================================================================

bool AABB::intersect(const Ray& ray, float& tmin_out, float& tmax_out) const noexcept {
  float tmin = ray.tmin;
  float tmax = ray.tmax;
  
  for (int i = 0; i < 3; i++) {
    float inv_d = 1.0f / (i == 0 ? ray.direction.x : i == 1 ? ray.direction.y : ray.direction.z);
    float t0 = ((i == 0 ? min.x : i == 1 ? min.y : min.z) - 
                (i == 0 ? ray.origin.x : i == 1 ? ray.origin.y : ray.origin.z)) * inv_d;
    float t1 = ((i == 0 ? max.x : i == 1 ? max.y : max.z) - 
                (i == 0 ? ray.origin.x : i == 1 ? ray.origin.y : ray.origin.z)) * inv_d;
    
    if (inv_d < 0.0f) {
      float temp = t0;
      t0 = t1;
      t1 = temp;
    }
    
    tmin = t0 > tmin ? t0 : tmin;
    tmax = t1 < tmax ? t1 : tmax;
    
    if (tmax < tmin) {
      return false;
    }
  }
  
  tmin_out = tmin;
  tmax_out = tmax;
  return true;
}

// ============================================================================
// AABB Ray Intersection (SIMD Optimized)
// ============================================================================

bool AABB::intersectSIMD(const Ray& ray, float& tmin_out, float& tmax_out) const noexcept {
#if defined(LIGHTRT_HAS_SSE2) || defined(LIGHTRT_HAS_AVX)
  // SSE2/AVX optimized version
  __m128 ray_orig = _mm_set_ps(0.0f, ray.origin.z, ray.origin.y, ray.origin.x);
  __m128 ray_dir = _mm_set_ps(0.0f, ray.direction.z, ray.direction.y, ray.direction.x);
  __m128 ray_inv_dir = _mm_div_ps(_mm_set1_ps(1.0f), ray_dir);
  
  __m128 box_min = _mm_set_ps(0.0f, min.z, min.y, min.x);
  __m128 box_max = _mm_set_ps(0.0f, max.z, max.y, max.z);
  
  __m128 t0 = _mm_mul_ps(_mm_sub_ps(box_min, ray_orig), ray_inv_dir);
  __m128 t1 = _mm_mul_ps(_mm_sub_ps(box_max, ray_orig), ray_inv_dir);
  
  __m128 tmin_v = _mm_min_ps(t0, t1);
  __m128 tmax_v = _mm_max_ps(t0, t1);
  
  // Horizontal max of tmin
  float tmin = ray.tmin;
  alignas(16) float tmin_arr[4];
  _mm_store_ps(tmin_arr, tmin_v);
  tmin = std::max(tmin, std::max(tmin_arr[0], std::max(tmin_arr[1], tmin_arr[2])));
  
  // Horizontal min of tmax
  float tmax = ray.tmax;
  alignas(16) float tmax_arr[4];
  _mm_store_ps(tmax_arr, tmax_v);
  tmax = std::min(tmax, std::min(tmax_arr[0], std::min(tmax_arr[1], tmax_arr[2])));
  
  if (tmax < tmin) {
    return false;
  }
  
  tmin_out = tmin;
  tmax_out = tmax;
  return true;
  
#elif defined(LIGHTRT_HAS_NEON)
  // ARM NEON optimized version
  float32x4_t ray_orig = {ray.origin.x, ray.origin.y, ray.origin.z, 0.0f};
  float32x4_t ray_inv_dir = {
    1.0f / ray.direction.x,
    1.0f / ray.direction.y,
    1.0f / ray.direction.z,
    0.0f
  };
  
  float32x4_t box_min_v = {min.x, min.y, min.z, 0.0f};
  float32x4_t box_max_v = {max.x, max.y, max.z, 0.0f};
  
  float32x4_t t0 = vmulq_f32(vsubq_f32(box_min_v, ray_orig), ray_inv_dir);
  float32x4_t t1 = vmulq_f32(vsubq_f32(box_max_v, ray_orig), ray_inv_dir);
  
  float32x4_t tmin_v = vminq_f32(t0, t1);
  float32x4_t tmax_v = vmaxq_f32(t0, t1);
  
  // Horizontal max of tmin
  float tmin = ray.tmin;
  float tmin_arr[4];
  vst1q_f32(tmin_arr, tmin_v);
  tmin = std::max(tmin, std::max(tmin_arr[0], std::max(tmin_arr[1], tmin_arr[2])));
  
  // Horizontal min of tmax
  float tmax = ray.tmax;
  float tmax_arr[4];
  vst1q_f32(tmax_arr, tmax_v);
  tmax = std::min(tmax, std::min(tmax_arr[0], std::min(tmax_arr[1], tmax_arr[2])));
  
  if (tmax < tmin) {
    return false;
  }
  
  tmin_out = tmin;
  tmax_out = tmax;
  return true;
  
#else
  // Fallback to scalar version
  return intersect(ray, tmin_out, tmax_out);
#endif
}

// ============================================================================
// BVH Builder Implementation
// ============================================================================

bool BVH::build(const std::vector<AABB>& prim_aabbs, const BVHBuildConfig& config) noexcept {
  if (prim_aabbs.empty()) {
    return false;
  }
  
  prim_aabbs_ = prim_aabbs;
  config_ = config;
  
  // Initialize primitive indices
  prim_indices_.resize(prim_aabbs.size());
  for (uint32_t i = 0; i < prim_aabbs.size(); i++) {
    prim_indices_[i] = i;
  }
  
  // Reserve space for nodes (estimate)
  nodes_.clear();
  nodes_.reserve(prim_aabbs.size() * 2);
  
  // Build recursively
  buildRecursive(prim_indices_.data(), static_cast<uint32_t>(prim_aabbs.size()), 0);
  
  return true;
}

uint32_t BVH::buildRecursive(uint32_t* indices, uint32_t num_prims, uint32_t depth) noexcept {
  // Allocate new node
  uint32_t node_idx = static_cast<uint32_t>(nodes_.size());
  nodes_.emplace_back();
  BVHNode& node = nodes_[node_idx];
  
  // Compute bounds of all primitives
  AABB bounds;
  for (uint32_t i = 0; i < num_prims; i++) {
    bounds.expand(prim_aabbs_[indices[i]]);
  }
  node.bounds = bounds;
  
  // Check if we should create a leaf
  if (num_prims <= config_.max_leaf_size) {
    // Create leaf node
    uint32_t offset = static_cast<uint32_t>(prim_indices_.size());
    
    // Move primitives to end of array
    std::vector<uint32_t> leaf_prims(indices, indices + num_prims);
    prim_indices_.insert(prim_indices_.end(), leaf_prims.begin(), leaf_prims.end());
    
    node.setLeaf(offset, num_prims);
    return node_idx;
  }
  
  // Compute centroid bounds
  AABB centroid_bounds;
  for (uint32_t i = 0; i < num_prims; i++) {
    centroid_bounds.expand(prim_aabbs_[indices[i]].center());
  }
  
  // Find best split
  SplitResult split;
  if (config_.use_binning && num_prims > 64) {
    split = findBestSplitBinned(indices, num_prims, centroid_bounds);
  } else if (config_.use_sah) {
    split = findBestSplit(indices, num_prims, centroid_bounds);
  } else {
    // Simple midpoint split
    split.axis = centroid_bounds.longestAxis();
    split.pos = (centroid_bounds.min.x + centroid_bounds.max.x) * 0.5f;
    if (split.axis == 1) {
      split.pos = (centroid_bounds.min.y + centroid_bounds.max.y) * 0.5f;
    } else if (split.axis == 2) {
      split.pos = (centroid_bounds.min.z + centroid_bounds.max.z) * 0.5f;
    }
    split.cost = 0.0f;
  }
  
  // Partition primitives
  auto getAxisValue = [&](uint32_t idx) -> float {
    Vec3 c = prim_aabbs_[idx].center();
    return split.axis == 0 ? c.x : split.axis == 1 ? c.y : c.z;
  };
  
  uint32_t* mid = std::partition(indices, indices + num_prims,
    [&](uint32_t idx) { return getAxisValue(idx) < split.pos; });
  
  uint32_t left_count = static_cast<uint32_t>(mid - indices);
  
  // Handle degenerate case where all primitives go to one side
  if (left_count == 0 || left_count == num_prims) {
    left_count = num_prims / 2;
  }
  
  // Check if split is worth it (SAH cost)
  if (config_.use_sah && split.cost >= config_.intersection_cost * num_prims) {
    // Don't split, create leaf
    uint32_t offset = static_cast<uint32_t>(prim_indices_.size());
    std::vector<uint32_t> leaf_prims(indices, indices + num_prims);
    prim_indices_.insert(prim_indices_.end(), leaf_prims.begin(), leaf_prims.end());
    node.setLeaf(offset, num_prims);
    return node_idx;
  }
  
  // Build children
  uint32_t left_child = buildRecursive(indices, left_count, depth + 1);
  uint32_t right_child = buildRecursive(mid, num_prims - left_count, depth + 1);
  
  // Update node (it may have been reallocated)
  nodes_[node_idx].setInterior(left_child, right_child);
  
  return node_idx;
}

BVH::SplitResult BVH::findBestSplit(
    const uint32_t* indices,
    uint32_t num_prims,
    const AABB& centroid_bounds) noexcept {
  
  SplitResult best;
  best.cost = kInfinity;
  best.axis = 0;
  best.pos = 0.0f;
  
  // Try each axis
  for (int axis = 0; axis < 3; axis++) {
    // Sort primitives by centroid along axis
    std::vector<uint32_t> sorted_indices(indices, indices + num_prims);
    
    std::sort(sorted_indices.begin(), sorted_indices.end(), [&](uint32_t a, uint32_t b) {
      Vec3 ca = prim_aabbs_[a].center();
      Vec3 cb = prim_aabbs_[b].center();
      float va = axis == 0 ? ca.x : axis == 1 ? ca.y : ca.z;
      float vb = axis == 0 ? cb.x : axis == 1 ? cb.y : cb.z;
      return va < vb;
    });
    
    // Try splits between primitives
    for (uint32_t i = 1; i < num_prims; i++) {
      // Compute bounds for left and right
      AABB left_bounds, right_bounds;
      
      for (uint32_t j = 0; j < i; j++) {
        left_bounds.expand(prim_aabbs_[sorted_indices[j]]);
      }
      
      for (uint32_t j = i; j < num_prims; j++) {
        right_bounds.expand(prim_aabbs_[sorted_indices[j]]);
      }
      
      // Compute SAH cost
      float left_area = left_bounds.surfaceArea();
      float right_area = right_bounds.surfaceArea();
      float cost = config_.traversal_cost + 
                   config_.intersection_cost * (i * left_area + (num_prims - i) * right_area);
      
      if (cost < best.cost) {
        best.cost = cost;
        best.axis = axis;
        
        // Split position is between primitives
        Vec3 c1 = prim_aabbs_[sorted_indices[i - 1]].center();
        Vec3 c2 = prim_aabbs_[sorted_indices[i]].center();
        best.pos = (axis == 0 ? (c1.x + c2.x) : axis == 1 ? (c1.y + c2.y) : (c1.z + c2.z)) * 0.5f;
      }
    }
  }
  
  return best;
}

BVH::SplitResult BVH::findBestSplitBinned(
    const uint32_t* indices,
    uint32_t num_prims,
    const AABB& centroid_bounds) noexcept {
  
  SplitResult best;
  best.cost = kInfinity;
  best.axis = 0;
  best.pos = 0.0f;
  
  // Try each axis
  for (int axis = 0; axis < 3; axis++) {
    float min_val = axis == 0 ? centroid_bounds.min.x : 
                    axis == 1 ? centroid_bounds.min.y : centroid_bounds.min.z;
    float max_val = axis == 0 ? centroid_bounds.max.x : 
                    axis == 1 ? centroid_bounds.max.y : centroid_bounds.max.z;
    
    if (max_val - min_val < kEpsilon) {
      continue;
    }
    
    // Initialize bins
    struct Bin {
      AABB bounds;
      uint32_t count;
      
      Bin() : count(0) {}
    };
    
    std::vector<Bin> bins(config_.num_bins);
    
    // Put primitives into bins
    float scale = config_.num_bins / (max_val - min_val);
    for (uint32_t i = 0; i < num_prims; i++) {
      Vec3 centroid = prim_aabbs_[indices[i]].center();
      float val = axis == 0 ? centroid.x : axis == 1 ? centroid.y : centroid.z;
      
      uint32_t bin_idx = static_cast<uint32_t>((val - min_val) * scale);
      bin_idx = std::min(bin_idx, config_.num_bins - 1);
      
      bins[bin_idx].bounds.expand(prim_aabbs_[indices[i]]);
      bins[bin_idx].count++;
    }
    
    // Compute costs for each split
    for (uint32_t i = 1; i < config_.num_bins; i++) {
      AABB left_bounds, right_bounds;
      uint32_t left_count = 0, right_count = 0;
      
      for (uint32_t j = 0; j < i; j++) {
        left_bounds.expand(bins[j].bounds);
        left_count += bins[j].count;
      }
      
      for (uint32_t j = i; j < config_.num_bins; j++) {
        right_bounds.expand(bins[j].bounds);
        right_count += bins[j].count;
      }
      
      if (left_count == 0 || right_count == 0) {
        continue;
      }
      
      float left_area = left_bounds.surfaceArea();
      float right_area = right_bounds.surfaceArea();
      float cost = config_.traversal_cost + 
                   config_.intersection_cost * (left_count * left_area + right_count * right_area);
      
      if (cost < best.cost) {
        best.cost = cost;
        best.axis = axis;
        best.pos = min_val + (max_val - min_val) * (static_cast<float>(i) / config_.num_bins);
      }
    }
  }
  
  return best;
}

// ============================================================================
// BVH Traversal Implementation
// ============================================================================

uint32_t BVH::traverse(const Ray& ray, float& hit_t) const noexcept {
  if (nodes_.empty()) {
    return kInvalidIndex;
  }
  
  uint32_t hit_prim = kInvalidIndex;
  hit_t = ray.tmax;
  
  // Stack-based traversal
  struct StackEntry {
    uint32_t node_idx;
  };
  
  StackEntry stack[64];
  int stack_ptr = 0;
  
  stack[stack_ptr++].node_idx = 0;
  
  while (stack_ptr > 0) {
    uint32_t node_idx = stack[--stack_ptr].node_idx;
    const BVHNode& node = nodes_[node_idx];
    
    float tmin, tmax;
    if (!node.bounds.intersect(ray, tmin, tmax) || tmin > hit_t) {
      continue;
    }
    
    if (node.isLeaf()) {
      // Test primitives in leaf
      for (uint32_t i = 0; i < node.prim_count; i++) {
        uint32_t prim_idx = prim_indices_[node.prim_offset + i];
        
        // Simple AABB intersection as primitive test
        float prim_tmin, prim_tmax;
        if (prim_aabbs_[prim_idx].intersect(ray, prim_tmin, prim_tmax)) {
          if (prim_tmin < hit_t && prim_tmin > ray.tmin) {
            hit_t = prim_tmin;
            hit_prim = prim_idx;
          }
        }
      }
    } else {
      // Add children to stack
      if (stack_ptr < 63) {
        stack[stack_ptr++].node_idx = node.left_child;
        stack[stack_ptr++].node_idx = node.right_child;
      }
    }
  }
  
  return hit_prim;
}

uint32_t BVH::traverseSIMD(const Ray& ray, float& hit_t) const noexcept {
  if (nodes_.empty()) {
    return kInvalidIndex;
  }
  
  uint32_t hit_prim = kInvalidIndex;
  hit_t = ray.tmax;
  
  // Stack-based traversal with SIMD intersection
  struct StackEntry {
    uint32_t node_idx;
  };
  
  StackEntry stack[64];
  int stack_ptr = 0;
  
  stack[stack_ptr++].node_idx = 0;
  
  while (stack_ptr > 0) {
    uint32_t node_idx = stack[--stack_ptr].node_idx;
    const BVHNode& node = nodes_[node_idx];
    
    float tmin, tmax;
    if (!node.bounds.intersectSIMD(ray, tmin, tmax) || tmin > hit_t) {
      continue;
    }
    
    if (node.isLeaf()) {
      // Test primitives in leaf
      for (uint32_t i = 0; i < node.prim_count; i++) {
        uint32_t prim_idx = prim_indices_[node.prim_offset + i];
        
        // Simple AABB intersection as primitive test
        float prim_tmin, prim_tmax;
        if (prim_aabbs_[prim_idx].intersectSIMD(ray, prim_tmin, prim_tmax)) {
          if (prim_tmin < hit_t && prim_tmin > ray.tmin) {
            hit_t = prim_tmin;
            hit_prim = prim_idx;
          }
        }
      }
    } else {
      // Add children to stack
      if (stack_ptr < 63) {
        stack[stack_ptr++].node_idx = node.left_child;
        stack[stack_ptr++].node_idx = node.right_child;
      }
    }
  }
  
  return hit_prim;
}

BVH::Stats BVH::getStats() const noexcept {
  Stats stats = {};
  
  if (nodes_.empty()) {
    return stats;
  }
  
  // Count nodes and compute depth
  std::vector<uint32_t> depths(nodes_.size(), 0);
  
  for (uint32_t i = 0; i < nodes_.size(); i++) {
    const BVHNode& node = nodes_[i];
    stats.num_nodes++;
    
    if (node.isLeaf()) {
      stats.num_leaves++;
      stats.avg_leaf_size += node.prim_count;
      stats.max_depth = std::max(stats.max_depth, depths[i]);
    } else {
      depths[node.left_child] = depths[i] + 1;
      depths[node.right_child] = depths[i] + 1;
    }
  }
  
  if (stats.num_leaves > 0) {
    stats.avg_leaf_size /= stats.num_leaves;
  }
  
  // Compute SAH cost
  stats.sah_cost = 0.0f;
  for (uint32_t i = 0; i < nodes_.size(); i++) {
    const BVHNode& node = nodes_[i];
    float area = node.bounds.surfaceArea();
    
    if (node.isLeaf()) {
      stats.sah_cost += area * node.prim_count * config_.intersection_cost;
    } else {
      stats.sah_cost += area * config_.traversal_cost;
    }
  }
  
  return stats;
}

// ============================================================================
// Two-Level BVH (TLAS) Implementation
// ============================================================================

bool TLAS::build(const std::vector<BLASInstance>& instances, const BVHBuildConfig& config) noexcept {
  if (instances.empty()) {
    return false;
  }
  
  instances_ = instances;
  
  // Build BVH over instance AABBs
  std::vector<AABB> instance_aabbs;
  instance_aabbs.reserve(instances.size());
  
  for (const auto& inst : instances) {
    instance_aabbs.push_back(inst.bounds);
  }
  
  return bvh_.build(instance_aabbs, config);
}

TLAS::TraceResult TLAS::trace(const Ray& ray, const std::vector<BLAS>& blas_array) const noexcept {
  TraceResult result;
  result.instance_id = kInvalidIndex;
  result.primitive_id = kInvalidIndex;
  result.t = ray.tmax;
  
  if (instances_.empty() || blas_array.empty()) {
    return result;
  }
  
  // Traverse TLAS to find instances
  float tlas_hit_t;
  uint32_t instance_idx = bvh_.traverse(ray, tlas_hit_t);
  
  if (instance_idx == kInvalidIndex) {
    return result;
  }
  
  // For simplicity, we test all instances (in full implementation, we'd traverse TLAS properly)
  for (uint32_t i = 0; i < instances_.size(); i++) {
    const BLASInstance& inst = instances_[i];
    
    if (inst.blas_id >= blas_array.size()) {
      continue;
    }
    
    // Transform ray to instance local space
    Ray local_ray;
    local_ray.origin = inst.worldToLocal(ray.origin);
    local_ray.direction = inst.worldToLocalDir(ray.direction).normalize();
    local_ray.tmin = ray.tmin;
    local_ray.tmax = result.t;
    
    // Traverse BLAS
    const BLAS& blas = blas_array[inst.blas_id];
    float hit_t;
    uint32_t prim_idx = blas.bvh.traverse(local_ray, hit_t);
    
    if (prim_idx != kInvalidIndex && hit_t < result.t) {
      result.instance_id = i;
      result.primitive_id = prim_idx;
      result.t = hit_t;
    }
  }
  
  return result;
}

} // namespace lightrt
