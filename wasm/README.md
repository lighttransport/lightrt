# LightRT WebAssembly

Lightweight ray tracing BVH library compiled to WebAssembly for browser and Node.js usage.

## Installation

```bash
npm install @lighttransport/lightrt-wasm
```

## Quick Start

```javascript
import loadLightRT from '@lighttransport/lightrt-wasm';

const lightrt = await loadLightRT();

// Build BVH from triangle mesh
// vertices: Float32Array of [x0,y0,z0, x1,y1,z1, ...] (9 floats per triangle)
const bvh = new lightrt.TriangleBVH();
const vertices = new Float32Array([
  0, 0, 0,  1, 0, 0,  0.5, 1, 0,  // triangle 1
  0, 0, 0,  0.5, 1, 0,  0, 1, 0,  // triangle 2
]);
bvh.build(vertices);

// Trace a ray
const hit = bvh.trace(0.5, 0.5, 5, 0, 0, -1); // origin, direction
if (hit.hit) {
  console.log(`Hit triangle ${hit.prim_id} at t=${hit.t}`);
}

// Serialize/deserialize BVH for caching
const buffer = bvh.saveToMemory();
const bvh2 = new lightrt.TriangleBVH();
bvh2.loadFromMemory(buffer);
```

## API

### TriangleBVH

Standard SAH-based BVH for triangle meshes.

```javascript
const bvh = new lightrt.TriangleBVH();

// Build with default config
bvh.build(vertices);  // Float32Array, 9 floats per triangle

// Build with explicit config
bvh.buildWithConfig(vertices, lightrt.BVHBuildConfig.quality());

// Trace ray (closest hit)
const result = bvh.trace(ox, oy, oz, dx, dy, dz, tmin = 0, tmax = infinity);
// result: { hit: boolean, t: number, u: number, v: number, prim_id: number }

// Trace ray (any-hit, for shadows)
const isOccluded = bvh.traceAnyHit(ox, oy, oz, dx, dy, dz, tmin, tmax, excludePrimId);

// Serialize to ArrayBuffer
const buffer = bvh.saveToMemory();

// Deserialize from ArrayBuffer
bvh.loadFromMemory(buffer);
```

### SBVH

Split BVH - handles large/spanning triangles better but uses more memory.

```javascript
const sbvh = new lightrt.SBVH();
sbvh.build(vertices);  // Uses SBVHBuildConfig by default
sbvh.buildWithConfig(vertices, customSBVHConfig);

const hit = sbvh.trace(ox, oy, oz, dx, dy, dz);
```

### MMapTriangleBVH

Zero-copy BVH for memory-mapped triangle data.

```javascript
const mmap = new lightrt.MMapTriangleBVH();

// Build from vertices (copies data)
mmap.build(vertices);

// Build from pre-formatted triangle data (36 bytes each, zero-copy)
// vertices must be Uint8Array of Triangle struct data
mmap.buildFromTriangles(triangleData);

const hit = mmap.trace(ox, oy, oz, dx, dy, dz);
```

### Configuration

#### BVHBuildConfig

```javascript
const config = lightrt.BVHBuildConfig.fast();    // LBVH: fast build
const config = lightrt.BVHBuildConfig.quality(); // SAH: best traversal
```

#### SBVHBuildConfig

```javascript
const config = new lightrt.SBVHBuildConfig();
config.max_leaf_size = 4;
config.num_spatial_bins = 64;
config.alpha = 1e-5;
```

#### TraversalConfig

```javascript
const config = lightrt.TraversalConfig.anyHit();           // Stop on first hit
const config = lightrt.TraversalConfig.shadowRay(exclude);  // Shadow ray
const config = lightrt.TraversalConfig.fast(128);          // Limit primitive tests
```

#### MMapBVHConfig

```javascript
const config = lightrt.MMapBVHConfig.minMemory();  // Compact 16-bit bounds
const config = lightrt.MMapBVHConfig.maxSpeed();  // Full precision bounds
```

## License

MIT
