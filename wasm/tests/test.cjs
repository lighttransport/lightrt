const createModule = require('../dist/lightrt.js');

async function test() {
  const lightrt = await createModule();

  console.log('Module loaded successfully');
  console.log('TriangleBVH:', typeof lightrt.TriangleBVH);
  console.log('Ray:', typeof lightrt.Ray);
  console.log('Vec3:', typeof lightrt.Vec3);
  console.log('kInvalidIndex:', lightrt.kInvalidIndex);

  // Create a simple cube mesh (12 triangles, 36 vertices, 108 floats)
  const vertices = new Float32Array([
    // Front face
    -1, -1,  1,   1, -1,  1,   1,  1,  1,
    -1, -1,  1,   1,  1,  1,  -1,  1,  1,
    // Back face
    -1, -1, -1,  -1,  1, -1,   1,  1, -1,
    -1, -1, -1,   1,  1, -1,   1, -1, -1,
    // Left face
    -1, -1, -1,  -1, -1,  1,  -1,  1,  1,
    -1, -1, -1,  -1,  1,  1,  -1,  1, -1,
    // Right face
     1, -1, -1,   1,  1, -1,   1,  1,  1,
     1, -1, -1,   1,  1,  1,   1, -1,  1,
    // Top face
    -1,  1, -1,   1,  1, -1,   1,  1,  1,
    -1,  1, -1,   1,  1,  1,  -1,  1,  1,
    // Bottom face
    -1, -1, -1,  -1, -1,  1,   1, -1,  1,
    -1, -1, -1,   1, -1,  1,   1, -1, -1,
  ]);

  // Test TriangleBVH
  const bvh = new lightrt.TriangleBVH();
  let success = bvh.build(vertices);
  if (!success) throw new Error('TriangleBVH build failed');
  console.log('TriangleBVH built successfully, primitives:', bvh.getNumPrimitives());

  // Trace using Ray struct
  const ray = new lightrt.Ray();
  ray.origin = new lightrt.Vec3();
  ray.origin.x = 0;
  ray.origin.y = 0;
  ray.origin.z = 5;
  ray.direction = new lightrt.Vec3();
  ray.direction.x = 0;
  ray.direction.y = 0;
  ray.direction.z = -1;
  ray.tmin = 0;
  ray.tmax = lightrt.kInfinity;

  let result = bvh.trace(ray);
  if (!result.hit) throw new Error('Ray should hit cube');
  if (result.prim_id >= 12) throw new Error('Prim ID should be valid');
  console.log('TriangleBVH trace hit (with Ray):', result.prim_id, 'at t=', result.t.toFixed(4));

  // Also test trace with individual floats (backwards compatible)
  result = bvh.trace(0, 0, 5, 0, 0, -1, 0, lightrt.kInfinity);
  if (!result.hit) throw new Error('Ray should hit cube');
  console.log('TriangleBVH trace hit (with floats):', result.prim_id, 'at t=', result.t.toFixed(4));

  // Trace a ray that misses
  result = bvh.trace(10, 10, 10, 0, 0, -1, 0, lightrt.kInfinity);
  if (result.hit) throw new Error('Ray should miss');
  console.log('TriangleBVH trace miss: OK');

  // Test serialization
  const buffer = bvh.saveToMemory();
  console.log('Serialized size:', buffer.byteLength, 'bytes');

  const bvh2 = new lightrt.TriangleBVH();
  success = bvh2.loadFromMemory(buffer);
  if (!success) throw new Error('TriangleBVH loadFromMemory failed');

  result = bvh2.trace(ray);
  if (!result.hit) throw new Error('Restored BVH should hit');
  console.log('TriangleBVH serialization: OK');

  // Test SBVH
  const sbvh = new lightrt.SBVH();
  success = sbvh.build(vertices);
  if (!success) throw new Error('SBVH build failed');
  console.log('SBVH built successfully, primitives:', sbvh.getNumPrimitives());

  result = sbvh.trace(ray);
  if (!result.hit) throw new Error('SBVH should hit');
  console.log('SBVH trace hit:', result.prim_id, 'at t=', result.t.toFixed(4));

  // Test MMapTriangleBVH
  const mmap = new lightrt.MMapTriangleBVH();
  success = mmap.build(vertices);
  if (!success) throw new Error('MMapTriangleBVH build failed');
  console.log('MMapTriangleBVH built successfully, triangles:', mmap.getTriangleCount());

  result = mmap.trace(ray);
  if (!result.hit) throw new Error('MMapTriangleBVH should hit');
  console.log('MMapTriangleBVH trace hit:', result.prim_id, 'at t=', result.t.toFixed(4));

  // Test traceAnyHit
  const isOccluded = bvh.traceAnyHit(ray, lightrt.kInvalidIndex);
  if (!isOccluded) throw new Error('traceAnyHit should return true');
  console.log('traceAnyHit: OK');

  console.log('\nAll tests passed!');
}

test().catch(err => {
  console.error('Test failed:', err);
  process.exit(1);
});
