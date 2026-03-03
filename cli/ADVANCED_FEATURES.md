# Advanced BVH Features Documentation

## SBVH (Split BVH)

### Overview

SBVH (Split BVH) provides spatial splits for handling problematic geometry like long/large triangles that regular BVH struggles with.

### Usage Example

```cpp
// Build SBVH with spatial splits
SBVH sbvh;
sbvh.build(triangles, sbvh_config);

// Trace ray through SBVH
float hit_t, hit_u, hit_v;
uint32_t hit = sbvh.traverse(ray, hit_t, hit_u, hit_v);
```

### Configuration

```cpp
SBVHBuildConfig config;
config.use_sah = true;        // Use SAH for spatial split evaluation
config.use_binning = false;   // Disable binning for faster builds
config.max_leaf_size = 4;      // Maximum primitives per leaf
```

## AutoTuner

### Overview

AutoTuner automatically selects optimal BVH construction and traversal parameters by sampling primitives and measuring performance.

### Usage Example

```cpp
// Auto-tune and get best configuration
auto result = AutoTuner::tune(triangles);

// Build with tuned config
if (result.best_method == BVHBuildMethod::TriangleBVH) {
  bvh.build(triangles, result.best_bvh_config);
} else {
  sbvh.build(triangles, result.best_sbvh_config);
}
```

### Configuration Presets

```cpp
AutoTuneConfig::throughput()      // Optimize for ray throughput
AutoTuneConfig::interactive()     // Balance build/traversal
AutoTuneConfig::memory()          // Optimize for memory-constrained scenes
AutoTuneConfig::quick()           // Fast tuning with fewer samples
```

## MMapBVH (Zero-Copy BVH)

### Overview

MMapBVH provides zero-copy BVH construction over external primitive data, optimized for low memory and bandwidth.

### Usage Example

```cpp
// Triangle data from memory-mapped file or external source
const Triangle* triangles = reinterpret_cast<const Triangle*>(mmap_data);
uint32_t count = file_size / sizeof(Triangle);

// Build BVH over external data (zero-copy)
MMapTriangleBVH bvh;
bvh.build(triangles, count);

// Traverse
float hit_t, hit_u, hit_v;
uint32_t hit = bvh.traverse(ray, hit_t, hit_u, hit_v);
```

### Configuration

```cpp
MMapBVHConfig config = MMapBVHConfig::minMemory();
config.max_leaf_size = 8;  // More primitives per leaf
bvh.build(triangles, count, config);
```

## Collision Detection Examples

### BVH-BVH Collision

```cpp
// Find all colliding primitive pairs between two BVHs
std::vector<CollisionPair> pairs;
bvh_a.findCollisions(bvh_b, pairs);

for (const auto& p : pairs) {
  handleCollision(p.prim_a, p.prim_b);
}
```

### Swept Collision (Continuous Collision Detection)

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
```

## Heatmap Writer Usage

### Overview

HeatmapWriter provides zero-dependency image writer for BVH traversal visualization with multiple colormaps.

### Usage Example

```cpp
// Render image with profiling
TraversalProfile* profiles = renderImageProfiled(
    bvh, width, height,
    camera_pos, camera_dir, camera_up, fov_y);

// Write heatmap
HeatmapWriter::writeHeatmap("nodes.bmp", profiles, width, height,
                             HeatmapWriter::Metric::NodesVisited,
                             Colormap::Viridis);
```

### Available Metrics

| Metric | Description |
|--------|-------------|
| `NodesVisited` | Nodes visited per ray |
| `LeafVisits` | Leaf nodes visited |
| `PrimsTested` | Primitive tests per ray |
| `MaxDepth` | Traversal depth |

### Colormaps

```cpp
Colormap::Grayscale     // Black to white
Colormap::Heat          // Black → Red → Yellow → White
Colormap::Jet          // Blue → Cyan → Green → Yellow → Red
Colormap::Viridis      // Purple → Blue → Green → Yellow
Colormap::Turbo        // Google's improved rainbow
Colormap::Plasma      // Purple → Pink → Orange → Yellow
Colormap::Inferno     // Black → Purple → Red → Yellow
Colormap::Cool        // Cyan to Magenta
Colormap::Hot         // Black → Red → Yellow → White
```

## Memory-Mapped BVH Examples

### Compact BVH (Zero-Copy)

```cpp
// Build compact BVH with minimal memory overhead
MMapBVHConfig config = MMapBVHConfig::minMemory();
config.max_leaf_size = 8;
bvh.build(triangles, count, config);

// Get BVH memory usage (excludes external primitive data)
size_t bvh_memory = bvh.getBVHMemoryUsage();
```

### Memory Optimization

```cpp
// Compact nodes (16-bit quantized bounds)
MMapBVHConfig config = MMapBVHConfig::minMemory();

// Full precision nodes (32-bit bounds)
MMapBVHConfig config = MMapBVHConfig::maxSpeed();
```

