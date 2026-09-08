# LightRT USD work — resume notes

## Current state

- Branch: `main`, tracking `origin/main`.
- Push range: two WIP commits, currently `0 behind / 2 ahead`:
  - `17210b0 Add CPU USD composition and splat rendering`
  - `6597fa0 Improve USD curve loading and motion rendering`
- Gitleaks and TruffleHog found no credentials, secrets, or tokens in the push range.
- `resume.md` is a handoff file only; keep it uncommitted.
- Preserve unrelated untracked paths: `data/`, `lightrt_c_test`,
  `lightrt_c_tri_test_new`, `tests/tests.md`, `third_party/`, and `wasm/dist/`.

## Remaining work

### 1. Fix motion-blur instance matching (confirmed blocker)

`common/usd_loader.cc::walk_prim_mblur` matches Mesh and Curve instances with
independent ordinal counters. Initial loading creates an instance only when a
prim produces renderable geometry, but the motion walk consumes a counter slot
for every typed prim. An empty or invalid Mesh/BasisCurves/NurbsCurves/
HermiteCurves prim before valid geometry therefore shifts or drops subsequent
motion samples.

Confirmed mesh reproducer:

1. Author an empty `Mesh "Empty"` before a valid `Mesh "MovingTriangle"`.
2. Animate `MovingTriangle` from x=0 at time 0 to x=5 at time 1.
3. Give the camera shutter `[0, 1]` and run with `--mblur-samples 8`.
4. The scene loads one mesh/instance, but no `Motion blur: 1/1 ...` message is
   printed because the empty mesh consumes the valid instance's slot.

Replace ordinal matching with stable USD prim identity, preferably a prim-path
to instance mapping recorded by the initial walk. Apply the same mechanism to
meshes and all supported curve schemas. Add regression fixtures for an empty
mesh and empty curve preceding animated valid geometry.

Relevant code:

- Initial mesh instance creation: `common/usd_loader.cc` around line 1137.
- Curve append: `common/usd_loader.cc` around line 1153.
- Motion walk and ordinal counters: `common/usd_loader.cc` around line 1554.

### 2. Correct mixed Gaussian/opaque compositing

When the nearest scene hit is Gaussian, `common/renderer.cc` calls
`traceGaussianRadiance`, composites every Gaussian hit over the environment,
and returns. `traceGaussianRadiance` does not stop at the nearest opaque mesh
depth or use the opaque surface radiance as its background. Mixed mesh+splat
scenes can therefore show splats through opaque surfaces or replace a mesh
behind transparent splats with the environment.

Limit Gaussian collection to the nearest opaque hit distance and composite the
remaining transmittance over that surface's shaded radiance. Add a small mixed
mesh/splat occlusion render test.

Relevant code:

- `common/renderer.cc` around line 239.
- `common/scene.hh::traceGaussianRadiance` around line 454.

### 3. Add automated CLI/USD regression tests

The standalone CLI currently registers zero CTest tests. Wire the committed
fixtures into smoke/regression tests:

- `tests/curves_points.usda`
- `tests/curve_matrix.usda`
- `tests/advanced_curves.usda`
- `tests/animated_curves.usda`
- `tests/composition_root.usda`
- New empty-prim motion fixtures from item 1.
- New mixed Gaussian/mesh fixture from item 2.

Tests should verify load counts, curve/segment counts, motion-instance counts,
successful CPU rendering, and nonempty output rather than relying only on a
process exit code.

### 4. Make ordinary-clone dependencies reproducible

Do not add submodules. `scripts/setup_deps.sh` currently clones a developer's
local lightusd_c checkout when available and otherwise clones floating public
`main`; TinyUSDZ follows the floating `lightusd` branch. Record and checkout
known-good revisions after ordinary `git clone`, or provide an equivalent lock
file/check step.

Audit revisions:

- Local `dep/lightusd_c`: `78ab8685591bbf076588c90463979fc98c0c161c`
- Public lightusd-c `main` during audit: `58b368f0707d17e33a557396177a2c2cb2a20057`
- Local `dep/lightusd_c/ref/tinyusdz`: `9cef021c1ffefab3435a0fb3ebe6d81d733ae27d`

The public lightusd-c revision successfully built and rendered the curve and
composition fixtures during the audit, so this is reproducibility hardening,
not a current build failure.

### 5. Documentation cleanup

Update stale `deps/lightusd-c/` references in `TASKS.md` to `dep/lightusd_c/`.

### 6. Follow-up quality item

Review moving mesh/point normal transforms. Intersection uses an interpolated
motion transform, while some shading paths still use the shutter-open inverse
transform. Non-rigid or rotating motion may produce incorrect normals.

## Validation baseline already passed

- Clean Release build with the lightusd_c CPU backend.
- Clean Release build with the TinyUSDZ fallback backend.
- Core CTest: 5/5.
- lightusd-c: 228/228 tests.
- lydra-c: 291/291 tests.
- flatten: 6/6 tests.
- ASAN and UBSAN query/animated-curve checks.
- Direct renders for curves, points, NURBS, Hermite, composition, and motion.
- A-Lab Gaussian scene: 2,274,589 splats, about 1.93 s load and 1.48 GiB RSS.
- A-Lab hair scene: 1,652 curves / 24,780 segments.
- Caldera scene: about 38.8M triangles plus 1M points, 23.5 s and 7.64 GB RSS.
- `git diff --check origin/main...HEAD` passed.

Re-run focused tests after each fix, then repeat clean Release builds, CTest,
sanitizers, and at least one A-Lab plus Caldera stress test before the final
non-WIP push.

## Resuming prompt

```text
Continue the LightRT USD CPU loader/rendering work in
/mnt/nvme02/work/lightrt using resume.md as the handoff. Inspect the repository
and current git state first, preserve all unrelated untracked files, and do not
add submodules. Start by fixing the confirmed motion-blur ordinal-instance bug
in common/usd_loader.cc using stable USD prim identity for both meshes and
BasisCurves/NurbsCurves/HermiteCurves. Add committed CLI regression fixtures and
CTest coverage for empty geometry preceding valid animated geometry. Then fix
mixed Gaussian/opaque compositing, add its regression test, make ordinary-clone
lightusd_c/TinyUSDZ dependency revisions reproducible, and clean up stale docs.
Use the CPU backend and validate composition, points, curves, NURBS, Hermite,
Gaussian splats, motion blur, and the public A-Lab/Caldera stress scenes listed
in resume.md. Run clean Release builds, tests, ASAN/UBSAN, and git diff checks.
Do not modify or commit resume.md. Report findings before committing; only
commit implementation changes when explicitly requested.
```
