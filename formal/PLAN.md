# LightRT formal verification — PLAN (document of record)

Status: 2026-11-17. Branch `formal-lean` (local commits ahead of `origin/formal-lean`, not pushed), tree clean.
`make formal`: PASS end-to-end. `count_sorry --max 0`: 0 sorry.
Axioms: only `propext`, `Quot.sound`, `Classical.choice`. No `native_decide`.

This file is the **document of record**, not a changelog. The milestone history
(M0–M22) remains in git history (`git log --oneline formal-lean`); do not
re-add narrative history here. Update this file when a theorem, a gate, or a
decision changes. `resume-lean.md` points here; it is not a second source of
truth.

## 1. Scope and coverage map

**Verified (Lean theorems, C-equivalent via `c2lean` + `cdiff`):**

| C kernel / concept | Lean counterpart (representative theorems) |
|---|---|
| ray setup, robust slab | `C/Proofs/RaySetupRefines.lean`, `C/Proofs/SlabRobustRefines.lean`, `Robust/Slab.fpT_abs_err_total` (range-free), `Robust/SlabTotal.slab_no_false_miss_total_of_floor` (conditional) |
| Möller–Trumbore gap / scalar triangle | `C/Proofs/MTGap.lean` (`mt_not_watertight`), `Geom/MTReal.lean` (soundness/completeness over ℝ), `Robust/MTT.lean` (`mt_t_fl_err_total_model`) |
| Woop watertight leaf (scalar) | `C/Proofs/WoopRefines.lean`, `WoopWatertight.lean` (`woop_no_gap_bits`, `woop_det_ne_zero`), `Robust/Woop.lean` |
| `EXACT_NEAREST` pruning key | `BVH/ExactPruneTotal.lean` (`key_le_total`, `woop_key_le_t_total_model`, both edge-sign classes) |
| BVH build / traversal / K-nearest / refit | `BVH/Tree.lean`, `BVH/Flat.lean`, `BVH/KBest.lean`, `BVH/Check.lean`, `BVH/TwoLevel.lean` |
| SIMD watertight leaf (lane model) | `C/Proofs/SimdLanes.lean` (`vWoopK_lane`, `blockBest_woop`), `C/Proofs/SimdLeafISA.lean` (`simd_leaf_eq_scalar_of_isa`, conditional) |
| Bézier curve, tube, signed distance | `Geom/BezTube.lean` (`infDist_bezTubeSet`, `samDist_le_bezPhiMin_add`, `stTrace3_bezTube_le_root`) |
| Newton foot-point / contact system | `Geom/Newton2D.lean`, `Geom/BezNewton.lean` (`ofCubic_newton_quadratic`), `Geom/SafeguardedNewton.lean` (`bracket_root`), `Geom/BezNewtonGuards.lean` (domain-of-attraction theorem) |

**Empirical gates only (no Lean theorem):** CUDA/HIP/Vulkan/d3d kernels
(trusted ports of the C; **out of scope for formalization for now**); the
floating-point solve of the Bézier Newton minimizer (`primhitcheck`); the
intrinsic→model ISA step (`wtcheck` leaf fuzz). These are documented boundaries,
not axioms.

## 2. Invariants — what is actually proved

- **FP**: executable binary32 RNE with subnormals/NaN; range-free absolute error
  `|fl x − x| ≤ u|x| + η` (`η = 2⁻¹⁵⁰`); Woop `t` bounds in both sign classes;
  1e-37 TLAS dilation floor; conditional non-tangent slab completeness.
- **Geometry**: MT soundness/completeness over ℝ and the concrete gap witness;
  Woop watertightness for every bit pattern; hull containment for curve/patch/
  point primitives; 1D/3D sphere-trace no-overshoot; Bézier tube `infDist` identity,
  sampled/exact distance sandwich, interior nearest-point classification.
- **BVH**: build/refit containment, traversal = brute force (ordered and
  k-nearest), two-level world-hit bound, `EXACT_NEAREST` conservativity where proved.
- **Newton/Bez**: local quadratic contraction of the 2D contact system;
  safeguarded bracket convergence to a critical point of `φ`; algebraic bridge
  (`F = 0` at a critical contact); guarded-step model and two conditional
  convergence theorems (`newtonIter_tendsto_of_basin`,
  `newtonIter_tendsto_of_basin_ball`).

## 3. Gates (manual only — no CI workflow by decision)

`make formal` = `lake build` (9000+ jobs, cached) → `c2lean --check` →
`count_sorry.sh --max 0` → `check_axioms.py` (allowlist above) → `cdiff` →
`bvhcheck.py` → `tlascheck(_exn)` → `wtcheck` (default + `EXACT_NEAREST`) →
`mtcheck 500000` → `primboxcheck` → `primhitcheck`. All must PASS to commit.
`formal/tools/` is gitignored; add new tools with `git add -f`.
GPU/CUDA/HIP/VK validation is required only after C changes (correctness only
on the miner nodes); no C changes in the formalization-only milestones.

## 4. Boundaries and decisions (do not attempt without new tooling)

- **Item 4 / SIMD ISA**: `PackedOps` makes the intrinsic→model hypothesis
  machine-checked, and `simd_leaf_eq_scalar_of_isa` is conditional on it. No
  vendor SSE4.1/AVX2/SVE semantics model exists; `wtcheck` is the empirical gate.
- **Item 3 / slab no-false-miss**: unprovable at tangency (no error-dominating
  K); the conditional non-tangent form is proved. `tlas_instance_margin` fp64
  stays out of scope (`tlascheck` covers it).
- **GPU kernels**: out of scope for formalization for now; trusted ports of C,
  validated by the C suites and `cdiff`-family checks.
- **M14 remainder**: the Newton basin hypotheses are discharged conditionally
  (see §5); `det0` (a lower bound on `|det J|`) is data, not an axiom, since it
  cannot be proved for arbitrary control points. Floating point of the
  minimizer remains `primhitcheck`-gated.

## 5. Roadmap

The open roadmap is organized into three tiers. Tier 1 is actionable formalization
work; Tier 2 records boundaries that must not be attempted without new tooling or
a decision change; Tier 3 is closed or maintenance.

### Tier 1 — Open formalization work

1. **Primitive intersector soundness over ℝ.** The C kernel exposes ~20 non-triangle
   scalar intersectors (sphere, quad/tetra, point, round-linear/flat curves, cubic
   Bézier, SDF, bilinear/Bézier/NURBS/trimmed-NURBS surfaces). `Geom/Hull.lean`
   proves their box containment, but none has a soundness/completeness/nearest
   theorem over ℝ, and none is `c2lean`-translated. `Geom/PrimReal.lean` now
   proves soundness+completeness+nearest over ℝ for ray–sphere (analytic nearest
   root) and quad/tetra (nearest of two/four MT triangle hits, composing
   `Geom/MTReal.lean`), with a `Sanity.lean` non-vacuity example. Next: expand
   family by family (points, round-linear/flat/cubic-Bézier curves, SDF, and the
   parametric surfaces). `Geom/PointReal.lean` now covers point discs (ray-facing
   and oriented; point spheres reuse `sphereReal`). Next: curves (round-linear,
   flat via `quadReal`, cubic Bézier), SDF, surfaces. Acceptance: for each family, a
   soundness+completeness+nearest theorem over ℝ and non-vacuity examples; a
   `*_refines` theorem once the scalar C function is translated.
   Coverage so far: triangle/MT (`MTReal`), sphere + quad/tetra (`PrimReal`),
   point sphere (via `sphereReal`), ray-facing/oriented point discs
   (`PointReal`), flat curve (ray-facing ribbon = quad via `quadReal`), SDF
   sphere/box (via `sphereReal` / `SlabReal` respectively). `CylinderReal`
   adds finite ray-cylinder side soundness/completeness; `CapsuleReal`
   composes it with two end spheres (nearest of three components, with
   soundness/completeness) and `Geom/EllipseReal.lean` covers ellipse points
   (plane intersection + elliptical-bound test, soundness/completeness).
   `Geom/RoundLinear.lean` defines swept-ball round-linear and ray-facing flat
   ribbon tube sets with hit soundness (completeness/nearest pending).
   `Geom/BezCurveReal.lean` gives the cubic-Bezier curve hit API: sampled
   acceptance soundness, completeness (boundary existence) and nearest-hit
   existence (closedness hypothesis), composing BezTube/BezFirstContact.
   `Geom/BezFirstContact.lean` composes the chain into a first-contact contract
   (`HitsBezTubeRay`, sampled acceptance sound, exact/sampled no-overshoot,
   boundary existence). `Geom/SphereTraceConvergence.lean` adds the convergence
   half (`stTrace_tendsto_contact`: an SDF-like 1-Lipschitz trace converges to
   a contact `L` with `f L = 0`). `Geom/BilinearSurface.lean` begins the
   parametric-surface family: the `tri_bilin_one` coplanarity quadratic +
   Cramer solve, with soundness (a reported hit is a genuine surface point
   in the unit square) and the dual-basis reconstruction identity.
   `bilinReal_complete` closes the other half: a geometric hit (point on the
   surface with `(u,v)` in the unit square, nondegenerate ruling) implies
   `bilinReal` reports a genuine hit. `Geom/BezPatchReal.lean` starts the
   bicubic Bezier patch: tensor Bernstein evaluation, control-hull containment,
   continuity and u-partial derivative, ray/patch hit soundness, and culling
   soundness (a ray missing the control hull cannot hit the patch) and culling
   completeness (`bezpatch_cull_complete`: a true hit is never culled; together
   the two make the subdivision AABB cull exact). `bez3Vec` and
   `bez3Vec_decasteljau_left` give the vector-valued de Casteljau split of each
   patch control row, and bicubicEval_eq_rows / bicubic_split_left give the
   full tensor de Casteljau split (Fin 16 reindexed as Fin 4 x Fin 4 via
   finProdFinEquiv, avoiding the slow global simp), and
   bezpatch_exists_nearest_hit (a hit implies a minimal hit parameter exists,
   via compactness of the closed hit-parameter set with a cheap finite-sum
   continuity proof). Full subdivision-plus-Newton completeness (Newton2D
   instantiation) and NURBS/trimmed-NURBS surfaces remain open. The Newton-to-
   hit bridge is in place: `newton2Step_at_root` (Newton is a fixed point at a
   root), `bezPatchContact` (the patch contact residual), and
   `newton_patch_hit_of_contact_zero` / `newton_patch_contact_ge_nearest` tie
   a converged Newton contact to a genuine hit no smaller than the nearest.
   `bezpatch_newton_quadratic` instantiates Newton2D contraction at the patch
   contact system (`patchF`/`patchG`). The control-point bound chase is now
   complete: Bernstein derivative bounds (`abs_bern3'_le ≤ 3`,
   `abs_bern3''_le ≤ 12`), componentwise partial/second-partial bounds
   (du/dv ≤48M, uv ≤144M, duu/dvv ≤192M), pd1/pd2 formulas and their
   second-order HasDerivAt lemmas for both patchF and patchG, full `patchF_C2Seg`
   / `patchG_C2Seg` assembly (K = 192·M), and
   `bezpatch_newton_quadratic_of_controls`, which supplies B = 48·M and K from
   the control net. The determinant lower bound δ remains necessarily data (as
   M14's `det0`): no lower bound on |det J| is provable for arbitrary control
   points. Full subdivision-plus-Newton completeness and NURBS/trimmed-NURBS
   surfaces remain open; `Geom/NURBSReal.lean` models the rational bicubic
   patch produced by NURBS Bezier extraction (positive-weight denominator,
   convex-combination identity, control-hull containment, hit soundness /
   culling, continuity, uniform-weight reduction to the Bezier patch), but
   `Geom/Trim.lean` models (u,v) trim loops (outer + holes) with the even–odd
   crossing rule and proves the trim invariant, hole rejection, edge-cross
   bound and the unit-square crossing parity (Jordan case); the full
   nearest-untrimmed-hit search and knot insertion are not yet formalized
   (subdivision-plus-Newton completeness is now covered abstractly above).
   `Geom/NURBSKnots.lean` lays the B-spline foundation: Cox–de Boor basis,
   knot insertion (`insertKnot`) with the degree-0 refinement equation and
   degree-1 Boehm curve preservation (`boehm1_preserves`), and the surface
   Bezier-extraction identity (`bezKnot_ratEval`: rational B-spline evaluation
   over the Bezier knot vector equals `ratEval` of NURBSReal),
   the cubic Bezier knot vector giving exactly the Bernstein basis, partition
   of unity, and B-spline-curve = Bezier-curve on `[0,1)` (the right endpoint
   is excluded by the half-open knot convention). Full knot insertion /
   Bezier extraction remains open.
2. **`c2lean` coverage expansion.** `C/Gen*.lean` currently translates the
   scalar triangle core (`tri_minf/maxf`, `tri_slab_scalar`, `tri_mt_one`,
   `tri_ray_setup`, `tri_woop_one`, `tri_exn_key`) plus `tri_sphere_dist_f`
   (the ray/sphere distance helper that exercises `sqrtf`), `tri_surface_area`
   and `tri_longest_axis` (box helpers). Their `*_refines` theorems are in
   `C/Proofs/{SphereDist,SmallKernels}Refines.lean`. `sqrtf` support is
   now in place: the C kernel uses `lrt_sqrtf` (`lrt_sqrtf.h`, the ISA's
   correctly-rounded SQRTSS on x86 SSE2/AVX/AVX2 and `vsqrt.f32` on ARM64 NEON,
   no libm call; `make test_lrt_sqrtf` checks bit-exactness vs libm over 200k+
   patterns); c2lean maps `sqrtf`/`lrt_sqrtf` to MiniC `Expr.sqrt`; the semantics
   executes `FP.Binary32.sqrtBits` (integer algorithm, `#guard`-checked);
   `EvE.sqrt'` is the refinement lemma; `cdiff.py` includes `sph` vectors that
   compare the real C sqrt with the MiniC model end-to-end (0 mismatches).
   Translate additional *scalar* kernels (e.g. `tri_woop_one_hp`, the primitive
   scalar intersectors from item 1) and prove their `*_refines` theorems.
   Acceptance: each new translated function has a passing `c2lean --check` and a
   refinement theorem. `tri_sphere_dist_f_refines` is proved in
   `C/Proofs/SphereDistRefines.lean` (ExS symbolic execution with an explicit
   post-`set` witness state, plus a `callFunc` wrapper); the model, translation
   and differential test are all covered.
3. **Bézier/patch intersector contract (M15/M16).** The cubic-Bézier and surface
   intersectors use adaptive subdivision + bounded Newton. Formalize the abstract
   contract (sampled acceptance sound; no missed nearest) analogous to the M14
   chain (`Geom/BezTube.lean`, `Geom/BezNewton*.lean`, `Geom/BezData.lean`,
   `Geom/BezKBounds.lean`). High effort; scope each surface kind before starting.
   Acceptance: an abstract soundness theorem per intersector strategy; FP of the
   solve itself remains the Tier 2 empirical boundary.

### Tier 2 — Documented boundaries (do not attempt without new tooling/a decision)

- **SIMD ISA semantics**: `PackedOps` makes the intrinsic→model hypothesis machine-checked, and `simd_leaf_eq_scalar_of_isa` is conditional on it. No vendor SSE4.1/AVX2/SVE semantics model exists; `wtcheck` is the empirical gate.
- **GPU formalization**: CUDA/HIP/Vulkan kernels are trusted ports of C, validated by the C suites and `cdiff`-family checks; out of scope for formalization for now.
- **`tlas_instance_margin` fp64 ρ/σ bound**: unproved, covered by `tlascheck` empirically.
- **Slab completeness at tangency**: unprovable (no error-dominating K); the conditional non-tangent form (`slab_no_false_miss_total_of_floor`) is proved.
- **Bézier Newton minimizer floating point**: remains `primhitcheck`-gated.

### Tier 3 — Closed / maintenance

- **M14 (Newton/basin verification)**: complete under the conditional-convergence acceptance criterion. Local quadratic contraction, safeguarded bracket, algebraic bridge, guarded basin convergence, `exists_radius_of_data`, control-point supply of `B0` (`ofCubicB0`) and `K` (`ofCubicK`/`ofCubic_PddBounds`/`ofCubicK_pos`), and `ofCubic_newton_tendsto_of_control_points`. `Sanity.lean` covers non-vacuity. `det0` stays data (no provable lower bound for arbitrary control points).
- **Sanity and doc consistency**: `Sanity.lean` examples and this document-of-record are maintained as part of each milestone, not tracked as separate roadmap items.

## 6. Conventions

- Namespaces mirror directories; `<algo>_<property>` theorem names; each
  translated C function `foo` has `foo_refines`.
- No sorry, no new axioms, no `native_decide`, no CI Actions (manual gates).
- Every commit: `make formal` green, `Co-Authored-By:` trailer, no force-push.
