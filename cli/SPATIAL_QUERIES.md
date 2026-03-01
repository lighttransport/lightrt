# Spatial Queries Documentation

## Overview

BVH provides efficient spatial indexing for broad-phase collision detection and frustum culling.

## AABB Query

### Collect Primitives within Bounding Box

```cpp
// Query all triangles within a bounding box
AABB query_box(Vec3(0, 0, 0), Vec3(10, 10, 10));
std::vector<uint32_t> results;
bvh.queryAABB(query_box, results);

// Results contains indices of intersecting triangles
for (uint32_t tri_idx : results) {
  // Process triangle tri_idx
}
```

## Sphere Query

### Collect Primitives within Sphere Radius

```cpp
// Query all triangles within sphere
Vec3 center(5.0f, 5.0f, 5.0f);
float radius = 3.0f;
std::vector<uint32_t> results;
bvh.querySphere(center, radius, results);
```

## Frustum Culling

### Collect Primitives Visible within View Frustum

```cpp
// Create frustum from view-projection matrix (column-major)
float mvp[16] = { ... };  // projection * view
Frustum frustum = Frustum::fromMatrix(mvp);

// Or construct planes manually
Frustum frustum;
frustum.planes[0] = Frustum::Plane(nx, ny, nz, d);  // Left
frustum.planes[1] = Frustum::Plane(...);            // Right
// ... near, far, top, bottom

// Query visible primitives
std::vector<uint32_t> visible;
bvh.queryFrustum(frustum, visible);
```

## K-Nearest Neighbor (KNN)

### Find K Closest Primitives to Query Point

```cpp
// Find 10 nearest triangles to a point
Vec3 query_point(5.0f, 0.0f, 5.0f);
std::vector<KNNResult> results;
bvh.queryKNN(query_point, 10, results);

// Results sorted by distance (nearest first)
for (const auto& r : results) {
  uint32_t tri_idx = r.prim_id;
  float dist_sq = r.distance_sq;
}

// For single nearest neighbor
float dist_sq;
uint32_t nearest = bvh.queryNearest(query_point, dist_sq);
```

## Performance

### Time Complexity

Spatial queries traverse the BVH tree, testing nodes against the query volume:
- **Time complexity**: O(log N + K) where K is the result count
- **Stack-based traversal**: No recursion overhead
- **Early culling**: Skips entire subtrees when bounds don't intersect
- **KNN uses priority queue**: Visits nodes in distance order for optimal pruning

### Use Cases

- **Frustum culling**: Use AABB query with view frustum bounds
- **Broad-phase collision**: Find potential collision candidates
- **Area-of-effect**: Find entities within explosion/effect radius
- **Spatial indexing**: Range queries for nearest neighbor search

