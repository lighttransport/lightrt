# LightRT Lean formalization: remaining items and resume prompt

State as of 2026-11-20, branch `formal-lean` (local commits ahead of
`origin/formal-lean`, not pushed).
The formalization document of record is `formal/PLAN.md` (scope, coverage map,
invariants, gates, boundaries, roadmap). Milestone history is in git history.
Repo guidance: `CLAUDE.md`, section "Formal verification".
See also the PLAN entries for the negative-key / tighter-key / `hp_subpatch`
decisions and item-3's `tlas_dil_origins` `1e-37` floor.

## Current state

`make formal` passes with 0 `sorry` and 889 theorems closed, axioms limited to
`propext`, `Quot.sound` and `Classical.choice`. It runs:

- `lake build` (includes `C/GenExn.lean`, `C/Proofs/ExnKeyRefines.lean`,
  `BVH/KBest.lean`, `FP/TotalErr.lean`, and the new `Geom/{BezPatchConvergence,
  BezPatchSubdivision,NURBSKnots,NURBSReal,Trim,RoundLinear,BezCurveReal,
  SDFReal,IntersectorContract}.lean`)
- `c2lean --check` (`Gen.lean` legacy, `GenRobust.lean` default, `GenExn.lean`
  with `-DLRT_TRI_EXACT_NEAREST`)
- the sorry and axiom checks
- `cdiff` (incl. `sph` vectors: real C hardware sqrt vs MiniC `sqrtBits`)
- `bvhcheck.py`: Lean mirror of the MT leaf; every variant opts out of the
  watertight leaf
- `tlascheck`, with and without `EXACT_NEAREST`
- `wtcheck`, the default and `EXACT_NEAREST` builds (also the SVE leaf fuzz
  under aarch64)
- `primboxcheck` and `primhitcheck`

Defaults in `lightrt_c_tri.h`, each with an `-DLRT_TRI_NO_*` opt-out:

- `SLAB_ROBUST`
- `SLAB_INFLATE` (with `SLAB_ROBUST`)
- `LEAF_BOX_EXACT`
- `BITEXACT`
- `WATERTIGHT_TRI` (vertex-format leaves, LRTS flag 4)

`EXACT_NEAREST` is opt-in. It prunes by the best hit on scenes with
`wbox_exact` (LRTS flag 8).

GPU nodes for CUDA tests:

- **zen5** (RTX 3070, `CUDA_ARCH=sm_86`) and **b550** (RTX 5060 Ti,
  `sm_120`), at `~/work/lightrt`.
- Sync with `rsync` (exclude `formal/.lake`, `.git`, `deps`, `data`,
  `third_party`, `build*`, `wasm`, `*.o`), then run
  `PATH=/usr/local/cuda/bin:$PATH make cuda_full_test CUDA_ARCH=...`.
- A GPU miner runs on these nodes, so run correctness tests only, no
  benchmarks.
- The local GPU is an RX 9070 XT: run `make hip_test`, then
  `timeout 600 ./lightrt_c_hip_test`.

ARM validation under qemu (clang cross builds; see `/tmp/opencode/build_a64.sh`
pattern): `clang --target=aarch64-linux-gnu --sysroot=/usr/aarch64-linux-gnu
-fuse-ld=lld -B/usr/lib/gcc-cross/aarch64-linux-gnu/13 ...` then
`qemu-aarch64 [-cpu max] -L /usr/aarch64-linux-gnu ./test`. `wtcheck` has
`leaf_fuzz_sve(8/16)` and the SVE leaf dispatch; `-march=armv8.2-a` for NEON,
`-march=armv8.2-a+sve` for SVE.

## Completed since `7fd2bf7`

- 5: `tri_exn_key` translated (`GenExn`) and `tri_exn_key_refines`.
- 2: `woop_t_err` / `woop_t_upper` (+ neg variants), `quot_err`.
- 1: `plane_t_incidence`, `hit_point_in_dilated_box`,
  `tlas_hit_point_in_box_incidence` (composed, dilated).
- 11: SIMD Woop leaf on the NEON shim (qemu-validated).
- 13: versioned ROCm root search in `lrt_hipew`; `make hip_rtc_test` green.
- 6: refit containment (`refit_contains`, `refit_prims`,
  `refit_traverse_eq_brute`) at the algorithm level.
- 9: fp64 Woop leaf (`tri_woop_one_hp`) + robust fp64 slab.
- 8: `BVH/KBest.lean`: `intersect_n` model, `kbest_omitted`, `runN_sound`,
  `runN_KInv`, `runN_complete` (soundness + completeness below the k-th).
- 10: SVE watertight Woop leaves for BVH8 and BVH16 (qemu SVE validated).
- 12: tighter-key attempt benchmarked; no gain, reverted and recorded.
- 14: `occluded1N` AUTO pipeline is now size-adaptive (per-ray < 300k
  triangles, interleaved above); benchmarked with `make bench_occ`.
- 15/16/17: decisions recorded in PLAN.md (keep `hp_subpatch`; accept the
  Bézier exact-solve cost; keep degenerate triangles).
- 3: `FP/TotalErr.lean` range-free rounding error and `1e-37` floor margin;
  `Robust/Total.lean` `num_err_total` / `den_bounds_total` /
  `quot_bounds_total(_tight)` / `woop_t_err_total(_model)(_tight)`;
  `BVH/ExactPruneTotal.lean` `key_le_total` / `woop_key_le_t_total_model`.
- 3a: `Robust/SlabTotal.fpT_abs_err_total` (range-free slab-parameter error).
- 7: `Geom/Hull.lean` box containment; `Geom/SphereTrace.lean` 1D no-overshoot
  + 1-Lipschitz + one-step contraction; `Geom/Newton2D.lean` general 2D Newton
  quadratic contraction; `Geom/BezNewton.lean` `tri_bez_newton` specialization;
  `Geom/SphereTrace3.lean` 3D no-overshoot via `Metric.infDist`.

Explicitly deferred/recorded (see PLAN.md):
- 3b (range-free MT `t` error): **done** — `Robust/MTTotal.lean`, `MTLeaf.lean`,
  `MTCross2.lean`, `MTDot.lean`, `MTT.lean` compose `mt_t_fl_err_total_model`
  (range-free, no `InRange`; `a0 ≤ |det_exact|` and det-error bound as data).
- 3c: `tlas_instance_margin` fp64 `ρ/σ` bound — unproved, `tlascheck` empirical.
- 4: ISA/intrinsics semantics gap — documented model boundary; `wtcheck` leaf
  fuzz incl. SVE 8/16; `mtcheck.c` fuzzes SIMD == scalar (2M blocks / 8M lanes
  / 642k hits, 0 differences); not an axiom.

## Completed in the 2026-11-20 Tier 1 push (commits `0163b1b`–`6a632e6`)

- **c2lean / sqrt**: `lrt_sqrtf.h` (ISA sqrt on SSE2/AVX2/NEON), `sqrtf` → MiniC
  `Expr.sqrt`, `FP.Binary32.sqrtBits` (integer RNE model, `#guard`-checked),
  `EvE.sqrt'`, `cdiff` `sph` vectors; `C/Proofs/SphereDistRefines.lean`
  (`tri_sphere_dist_f_refines`), `SmallKernelsRefines.lean`
  (`tri_surface_area`, `tri_longest_axis`).
- **Patch basin from control points**: `Geom/BezPatchConvergence.lean` —
  `patch_basin_ball_of_data`, `patch_newtonIter_tendsto_of_basin_ball`,
  `patch_newtonIter_tendsto_of_root_data`,
  `patch_subdivision_no_missed_nearest_of_root_data`, `cell_center_in_basin`.
  the seed is now the LOCAL center (1/2,1/2) and its distance to the local root
  is derived from the cell-size condition via cell_center_in_basin; only δ
  (determinant lower bound) stays data.
- **Patch subdivision**: `Geom/BezPatchSubdivision.lean` — `transposeCP`,
  `bicubicEval_transpose`, `splitBicubicV`, `PatchCell` / `Represents` with u/v
  split preservation, `cell_not_culled_of_hit`, `cell_contact_eq`.
- **NURBS foundation**: `Geom/NURBSKnots.lean` — Cox–de Boor `bsplineBasis`,
  Bezier-knot = Bernstein identity (degree 3), partition of unity, B-spline =
  Bezier curve, `insertKnot` + degree-0 refinement, degree-1 Boehm
  (`boehm1_preserves`), surface Bezier extraction (`bezKnot_ratEval`, now with
  the denominator also a B-spline sum, removing the circular statement).
- **Trimmed NURBS**: `Geom/Trim.lean` — even-odd crossing, unit-square Jordan
  parity, `nearestVisibleT` finite scan + reject-and-continue and its main
  spec theorem (returned parameter is a minimal visible hit).
- **Curves / SDF**: `Geom/RoundLinear.lean` (round/flat tube hit soundness;
  tube sets proved closed as compact images, nearest-hit existence unconditional),
  `Geom/BezCurveReal.lean` (cubic-Bezier soundness/completeness/nearest, bezTubeSet
  closed, unconditional nearest-hit existence), `Geom/SDFReal.lean` (trace
  soundness/no-overshoot/boundary). RoundLinear.lean additionally has rlcReal /
  flatReal nearest-hit models, tapered box containment and the flat-ribbon to
  two-MT-triangle connection.
- **M15/M16 contracts**: `Geom/IntersectorContract.lean` — curve and surface
  abstract contract APIs.

## Remaining items

The authoritative roadmap is `formal/PLAN.md` §5 (three tiers). Concrete
remaining sub-items from the 2026-11-20 push:

- **Tier 1, patch surfaces**: the seed-distance hypothesis is now supplied from
  the cell size (local center (1/2,1/2)); δ stays data for arbitrary control
  points by decision. A local-curvature bound that shrinks with cell size would
  remove the residual `1 <= R` side condition.
- **Tier 1, NURBS**: general-degree Boehm insertion / Cox–de Boor refinement
  equation (only degree 0 and degree 1 are proved; degree 3 Bezier extraction
  via `bezKnot_ratEval` is done); full tensor-product general knot insertion.
- **Tier 1, trimmed NURBS**: general crossing-number parity: far-right zero,
  edgeCrossX betweenness and the general rectangle are now proved; loop bridge
  additivity and cyclic rotation invariance remain (the latter needs a
  closed-loop crossingNumber definition). Swept-tube closedness is proved;
  trim loops beyond the finite candidate list remain.
- **Tier 1, curves/SDF**: completeness for round-linear / flat curves (only
  soundness + nearest-hit existence are proved; tube-set closedness is now
  established for round/flat/Bezier curves); real rlc/flat intersector models.
- **Tier 1, c2lean**: translate further scalar kernels and prove `*_refines`.
- **Tier 2 (boundaries, do not attempt without new tooling/decision)**: SIMD ISA
  semantics (`wtcheck` gate), GPU formalization, fp64 `tlas_instance_margin`
  (`tlascheck` gate), slab completeness at tangency (unprovable), Bézier-minimizer
  FP (`primhitcheck` gate).
- **Tier 3 (closed)**: M14 basin verification is complete (conditional
  convergence); `B0`, `K`, radii, and the convergence theorem are supplied from
  control points in `Geom/Bez{Data,KBounds,...}.lean`. Sanity/doc consistency is
  maintenance. No CI by decision; formal gates are manual.

## Resuming prompt

> Continue the LightRT Lean formalization on branch `formal-lean` in
> `/mnt/nvme02/work/lightrt` (local commits ahead of `origin/formal-lean`, not pushed). Read
> `formal/PLAN.md` (document of record) first, then this file. Run
> `make formal` to confirm the baseline (0 sorry, all gates PASS, axiom allowlist unchanged).
>
> The 2026-11-20 Tier 1 push is committed through `6a632e6`: patch Newton basin
> from control points (δ data), Bezier subdivision + cull safety + abstract
> no-missed contract, NURBS foundation (degree-0/1 knot insertion, surface
> Bezier extraction), trim loops + finite nearest-visible scan, curve/SDF soundness
> APIs, and M15/M16 contracts. The concrete remaining sub-items are listed above
> under "Remaining items" — start with the most tractable (e.g. round/flat tube
> closedness, general-degree Boehm refinement, general crossing parity). Everything
> else is a recorded boundary (ISA, tangency, fp64 margins, GPU) or empirical gate
> (`wtcheck`, `primhitcheck`).
>
> For every C change: SIMD bit-identical to scalar (`wtcheck`, incl. SVE under
> qemu), rerun `make formal`, the C suites, `make hip_test` (local RX 9070 XT,
> use `timeout`), `make hip_rtc_test`, `make vk_test`, and
> `make cuda_full_test` on zen5 (`sm_86`) and b550 (`sm_120`) — correctness
> only there (GPU miner). Measure speed on a quiet machine; keep negative
> results in `formal/PLAN.md`. Commit only when `make formal` passes, ending
> messages with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
> `formal/tools` is gitignored (`git add -f`). Do not push unless asked;
> never submit Perforce changelists.
