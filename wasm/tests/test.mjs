import assert from 'node:assert/strict';
import loadLightRT from '../dist/lightrt.js';

const lightrt = await loadLightRT();
const bvh = new lightrt.TriangleBVH();
try {
  const vertices = new Float32Array([0, 0, 0, 1, 0, 0, 0, 1, 0]);
  assert.equal(bvh.build(vertices, null), true);
  assert.equal(bvh.getNumPrimitives(), 1);
  const hit = bvh.trace(0.25, 0.25, 1, 0, 0, -1, 0, 10);
  assert.equal(hit.hit, true);
  assert.equal(hit.prim_id, 0);
  assert.equal(hit.t, 1);
} finally {
  bvh.delete();
}
