const assert = require('node:assert/strict');
const lightrt = require('..');

const bounds = [
  [-1, -1, -1, 1, 1, 1],
  [3, -1, -1, 5, 1, 1],
];

function boxIntersect(org, dir, tmin, tmax, prim) {
  const lo = bounds[prim].slice(0, 3);
  const hi = bounds[prim].slice(3, 6);
  let near = tmin;
  let far = tmax;
  for (let axis = 0; axis < 3; axis++) {
    if (dir[axis] === 0) {
      if (org[axis] < lo[axis] || org[axis] > hi[axis]) return null;
      continue;
    }
    const inv = 1 / dir[axis];
    let t0 = (lo[axis] - org[axis]) * inv;
    let t1 = (hi[axis] - org[axis]) * inv;
    if (t0 > t1) [t0, t1] = [t1, t0];
    near = Math.max(near, t0);
    far = Math.min(far, t1);
    if (far < near) return null;
  }
  return [near, 0, 0];
}

const scene = new lightrt.Scene(bounds, boxIntersect);
scene.build();
assert.deepEqual(scene.intersect([0, 0, -5], [0, 0, 1]).slice(0, 2), [0, 4]);
assert.deepEqual(scene.intersect([4, 0, -5], [0, 0, 1]).slice(0, 2), [1, 4]);
assert.equal(scene.intersect([10, 0, -5], [0, 0, 1]), null);
assert.match(lightrt.backendName(), /C11/);

