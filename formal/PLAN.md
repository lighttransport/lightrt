# LightRT formal verification — PLAN (document of record)

Status: 2026-11-17. Branch `formal-lean` (`origin/formal-lean`), tree clean.
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
- **M14 remainder**: the quantitative verification of the Newton basin
  hypotheses (see §5); floating point of the minimizer remains `primhitcheck`-gated.

## 5. Roadmap (open)

1. **M14 basin verification (F)** — the one open deep item. Done: local
   contraction (`ofCubic_newton_quadratic`), safeguarded bracket (`bracket_root`),
   guard model, algebraic bridge, and two conditional convergence theorems
   (`newtonIter_tendsto_of_basin` with per-iterate hypotheses,
   `newtonIter_tendsto_of_basin_ball` with a single neighbourhood check).
   Progress: `jacDet_variation_bound` (Lipschitz variation of the Jacobian),
   `basin_ball_of_data`, and `newtonIter_tendsto_of_root_data` (guarded
   convergence from explicit root data `B0, det0, R` plus `PddBounds`) are
   proved; `exists_radius_of_data` proves the radius conditions are
   satisfiable whenever `4(B0+1)² < det0` (non-vacuity sanity example in
   `Sanity.lean`). Remaining: supply `B0, det0` for `ofCubic` from a
   nondegenerate root (control-point bound chase).
2. **Item 4 instance** (blocked): needs vendor ISA semantics; stays conditional.
3. **GPU formalization** (deferred by decision): would require a device-kernel
   semantics and codegen verification; not scheduled.

## 6. Conventions

- Namespaces mirror directories; `<algo>_<property>` theorem names; each
  translated C function `foo` has `foo_refines`.
- No sorry, no new axioms, no `native_decide`, no CI Actions (manual gates).
- Every commit: `make formal` green, `Co-Authored-By:` trailer, no force-push.
