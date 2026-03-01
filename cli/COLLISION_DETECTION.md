# Collision Detection Examples

## BVH-BVH Collision

### Find All Colliding Primitive Pairs Between Two BVHs

```cpp
// Check if any collision exists (fast early-out)
if (bvh_a.hasCollision(bvh_b)) {
  // Find all colliding pairs
  std::vector<CollisionPair> pairs;
  bvh_a.findCollisions(bvh_b, pairs);

  for (const auto& p : pairs) {
    // p.prim_a from bvh_a, p.prim_b from bvh_b
    handleCollision(p.prim_a, p.prim_b);
  }
}
```

### Near-Collision with Distance Threshold

```cpp
// Find all collisions within distance threshold
std::vector<CollisionPair> near_pairs;
bvh_a.findCollisions(bvh_b, 0.5f, near_pairs);  // Within 0.5 units
```

## Self-Collision

### Detect Collisions Within a Single BVH (e.g., Cloth Simulation)

```cpp
// Check if any self-collision exists
if (bvh.hasSelfCollision()) {
  std::vector<CollisionPair> self_pairs;
  bvh.findSelfCollisions(self_pairs);
  // Pairs are deduplicated: only (a, b) where a < b
}
```

## Swept Collision (Continuous Collision Detection)

### Find Collisions as an Object Moves Along a Velocity Vector

```cpp
Vec3 velocity(10.0f, 0.0f, 0.0f);  // Movement for this frame

// Find first collision
SweptCollisionResult result;
if (moving_bvh.findSweptCollision(static_bvh, velocity, result)) {
  // result.t_first: time of first contact [0, 1]
  // result.t_last: time of last contact
  // result.normal: collision normal
  Vec3 safe_pos = original_pos + velocity * result.t_first;
}

// Find all collisions along path
std::vector<SweptCollisionResult> all_results;
moving_bvh.findAllSweptCollisions(static_bvh, velocity, all_results);
// Results sorted by t_first (earliest first)
```

## AABB Utilities

### Additional AABB Methods for Collision Detection

```cpp
// Swept AABB intersection
float t_first, t_last;
if (aabb_a.intersectSwept(aabb_b, velocity, t_first, t_last)) {
  // Collision during interval [t_first, t_last]
}

// Penetration depth and normal for overlapping AABBs
Vec3 normal;
float depth;
if (aabb_a.computePenetration(aabb_b, normal, depth)) {
  // Resolve by pushing aabb_a along normal by depth
  position += normal * depth;
}

// Minkowski operations
AABB sum = aabb_a.minkowskiSum(aabb_b);       // For configuration space
AABB diff = aabb_a.minkowskiDifference(aabb_b);  // For GJK-style tests

// Point containment
if (aabb.contains(point)) { ... }
```

