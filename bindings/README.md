# LightRT C Bindings

These bindings wrap the pure C11 CPU callback API in `lightrt_c.h`.

GPU/Vulkan support is intentionally deferred. The public binding shape keeps
the CPU backend explicit so a future GPU backend can be added as a sibling
module or constructor option without changing the CPU callback API.

## Python

```bash
cd bindings/python
python3 setup.py build_ext --inplace
PYTHONPATH=. python3 tests/test_smoke.py
```

```python
import lightrt_c

bounds = [[-1, -1, -1, 1, 1, 1]]

def intersect(org, direction, tmin, tmax, prim):
    return 4.0  # return None/False for miss, or t / (t, u, v) for hit

scene = lightrt_c.Scene(bounds, intersect)
scene.build()
print(scene.intersect([0, 0, -5], [0, 0, 1]))
```

## Node.js

```bash
cd bindings/node
npm run build
npm test
```

```js
const lightrt = require('@lighttransport/lightrt-c');

const bounds = [[-1, -1, -1, 1, 1, 1]];
const scene = new lightrt.Scene(bounds, (org, dir, tmin, tmax, prim) => {
  return 4.0; // return null/false for miss, or t / [t, u, v] for hit
});
scene.build();
console.log(scene.intersect([0, 0, -5], [0, 0, 1]));
```

