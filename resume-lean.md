# LightRT Lean formalization: remaining items and resume prompt

State as of 2026-11-15, branch `formal-lean` at `b736431` (35 commits on top of
`7fd2bf7`). Nothing is pushed. The plan and history are in `formal/PLAN.md`
(milestones M1–M21); repo guidance is in `CLAUDE.md`, section "Formal
verification".
See also the PLAN entries for the negative-key / tighter-key / `hp_subpatch`
decisions and item-3's `tlas_dil_origins` `1e-37` floor.

## Current state

`make formal` passes with 0 `sorry` and axioms limited to `propext`,
`Quot.sound` and `Classical.choice`. It runs:

- `lake build` (now includes `C/GenExn.lean`, `C/Proofs/ExnKeyRefines.lean`,
  `BVH/KBest.lean`, `FP/TotalErr.lean`)
- `c2lean --check` (`Gen.lean` legacy, `GenRobust.lean` default, `GenExn.lean`
  with `-DLRT_TRI_EXACT_NEAREST`)
- the sorry and axiom checks
- `cdiff`
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
- 3: `FP/TotalErr.lean` range-free `|rneR x − x| ≤ u|x| + 2⁻¹⁵⁰` and the
  `1e-37` dilation-floor margin (`fl_add_margin_ge`, `fl_sub_margin_le`);
  `Robust/Total.lean` `num_err_total` / `den_bounds_total` /
  `quot_bounds_total(_tight)` / `woop_t_err_total(_model)(_tight)` (full
  range-free Woop `t` error, `η/a0` slack); `BVH/ExactPruneTotal.lean`
  `key_le_total` and `woop_key_le_t_total_model` (the C `EXACT_NEAREST`
  call-site instantiation, now both edge-sign classes, `hsign`,
  `a0 ≤ |e0+e1+e2|`).
- 3a: `Robust/SlabTotal.fpT_abs_err_total` — range-free error bound for one
  scalar slab parameter (`fl(fl(x−o)·fl(1/d))`), no `InRange`.
- 7: `Geom/Hull.lean` proves box containment; `Geom/SphereTrace.lean`
  proves the 1D no-overshoot core, the distance-to-point 1-Lipschitz atom,
  and the one-Newton-step quadratic contraction (`newton_step_quadratic`);
  `Geom/Newton2D.lean` proves the general 2D Newton quadratic contraction
  (7b-1); `Geom/BezNewton.lean` proves the `tri_bez_newton` specialization
  (7b-2: Jacobian as polynomial sums + `1/|R|` entries, `jacDet` = the C's
  `det`, rectangle `C2Seg` with `|R|² > 0`, contraction corollary
  `bez_newton_quadratic`, and the `BezSys.ofCubic` control-point-polynomial
  instance); `Geom/SphereTrace3.lean` proves the 3D no-overshoot via
  `Metric.infDist` (7a). The signed-distance Bézier model itself
  (PLAN M14) is not formalized. Patch/NURBS stay measured against
  `primhitcheck` (item 16 decision).

Explicitly deferred/recorded (see PLAN.md):
- 3b: range-free Möller–Trumbore `t` error bound — out of scope. The TLAS
  world-hit incidence theorem instantiates `ε := woop_t_err` (watertight BLAS
  only); MT scenes are unsupported by it.
- 3c: `tlas_instance_margin`'s fp64 `ρ/σ` bound — unproved, covered by
  `tlascheck` empirically.
- 4: ISA/intrinsics semantics gap — documented model boundary (packed ops are
  `FP.Binary32` lane ops); exhaustively checked for this kernel by
  `wtcheck`'s leaf fuzz (incl. SVE 8/16), not an axiom.
  `BITEXACT` SIMD == scalar for MT: new `formal/tools/mtcheck.c` fuzzes
  `tri_packet4_tri` vs the scalar per-lane `tri_isect_lane` — 2M blocks /
  8M lanes / 642k hits, 0 differences (`make formal` gate, 500k iterations).
  Item 3b (range-free MT `t` error bound): **done.** `Robust/MTTotal.lean`
  and `Robust/MTLeaf.lean` prove the leaf/stage bounds (`fl_mul_err_total`,
  `fl_mul_ops_err_total`, `fl_sub/add_err_total`, `fl_abs_le`, `add2/sub2_fl_err_total`,
  ...); `Robust/MTCross2.lean` proves `cross2_fl_err_total` (the cross-product
  component: `|fl(fl a·fl c − fl b·fl d) − (a·c − b·d)| ≤ 7u(AC+BD) + 4η(A+B+C+D+2)`);
  `Robust/MTDot.lean` proves `dot3_fl_err_total`, `cross_component_err`,
  `mt_det_err_total` and `mt_num_err_total` (the determinant and numerator
  stages of `tri_mt_one`, in C op order); `Robust/MTT.lean` composes them
  into `mt_t_fl_err_total_model` (range-free, no `InRange`):
  `|t_model − t_exact| ≤ (12u·BMA + (2u+2)·mtNumErr M A B) / a0 + η + 12·BMA·mtDetErr M A B / a0²`,
  with hypotheses `a0 ≤ |det_exact|` and `mtDetErr M A B ≤ a0/2` (a0 keeps the
  exact determinant away from zero; the same theorem with `d ↦ −d` covers the
  negative-det class). Constants reflect the F-model op order of the C; the
  bound degrades like `1/a0` as det → 0, which is correct for a non-watertight
  kernel — MT's `t` bound buys no conservativity for `EXACT_NEAREST`-style
  pruning (MT is not watertight), and `mtcheck` remains the empirical check.

## Remaining items

### Proofs (Lean), large

3. **Rounding-model hypotheses (done for Woop/key/slab/MT bounds).** Woop `t`
   error and the `EXACT_NEAREST` key are range-free (both sign classes).
   `Robust/SlabTotal.lean` now proves the range-free scalar slab-parameter
   error bound `fpT_abs_err_total` (`|fpT − q/d| ≤ 4u|q/d| + 4(1+u)(|q| +
   |1/d|)η + 2(1+u)η² + η`, no `InRange`). 3b (MT error bound) is **done**
   (`Robust/MTCross2.lean`, `MTDot.lean`, `MTT.lean`; MT is not watertight,
   so it buys no `EXACT_NEAREST` conservativity — `mtcheck` remains the check);
   3c (`tlas_instance_margin` fp64) is **out of scope** —
   `tlascheck` covers it. The `1e-37` dilation floor is proved
   (`fl_add_margin_ge`/`fl_sub_margin_le`); a range-free `slab_no_false_miss`
   needs a non-degeneracy floor and is not attempted (tangent rays admit no
   absolute-error-dominating `K`). `fpT_rel`/`slab_t_err_fma` keep their
   `InRange` versions.
4. **A refinement proof for the SIMD watertight leaf (model done; ISA gap
   recorded).** `C/Proofs/SimdLanes.lean` gives the per-lane model (packed lane
   ops, `vWoopK` mirroring `Ref.woopK`, `vWoopK_lane`, `blockBest_*`). The
   ISA/intrinsics semantics is a documented model boundary (see PLAN.md), not
   an axiom; `wtcheck`'s leaf fuzz (400k blocks / 2.7M lanes, incl. SVE 8/16) is
   the empirical check for the watertight kernel, and the new `mtcheck`
   fuzz (`make formal` gate) covers the BITEXACT MT packet path vs scalar.
7. **Curve, patch and point hit correctness (started).** `Geom/Hull.lean`
   proves box containment; `Geom/SphereTrace.lean` proves the 1D no-overshoot
   core, the distance-to-point 1-Lipschitz atom, and
   `newton_step_quadratic`. Remaining (in order):
   - 7b-1 `Geom/Newton2D.lean`: general 2D Newton quadratic contraction.
     **Done** (`residual_bound`, `pd1/pd2_diff_bound`, `newton2_step_quadratic`;
     note the honest `2 B² E` term for the second component in absence of a
     `B ≤ K E`-style extra hypothesis; with `B ≤ K·E` the constant is
     `(10 B K/δ) E²` for both).
   - 7b-2 `Geom/BezNewton.lean`: Bézier specialization of the `F(u, t)` system
     (`tri_bez_newton`). **Done** — `BezSys` bundles the curve/radius
     derivative chains; `pd1_bezF`/`pd2_bezF`/`pd1_bezG`/`pd2_bezG` identify
     the C's `dFdu`/`dFdt`/`dGdu`/`dGdt` as polynomial sums (plus the `1/|R|`
     entries), `jacDet_bez` is the C's `det`; `bezF_C2Seg`/`bezG_C2Seg` prove
     the rectangle differentiability parts of `C2Seg` (with
     `|R|² > 0` from the C's `lenR > 1e-30` guard as hypothesis) and take the
     eight second-derivative bounds as `PddBounds` hypotheses;
     `bez_newton_quadratic` is the final contraction corollary and
     `BezSys.ofCubic` instantiates everything for the actual cubic control-point
     polynomials (`tri_bez_eval`'s `P`/`dP`/`ddP` expressions, proved via the
     `bezPoly` polynomial representation); `ofCubic_newton_quadratic` is the
     monic specialization. Honest limits, mirroring the C: the radius row is
     modeled unclamped (`max r 0` is not `C²` at the kink), the `dF/du < 0`
     front-facing-minimum selection and the eps-convergence test are not
     modeled, `K`/`B` stay hypotheses, and no floating-point analysis of the
     step is claimed.
   - 7a `Geom/SphereTrace3.lean`: 3D no-overshoot via `Metric.infDist`.
     **Done** (`infDist_lipschitz`, `absLipschitz_infDist`,
     `infDist_line_lipschitz` (‖v‖ ≤ 1 ray restriction),
     `lipschitz1_infDist_line`, `stTrace3_le_root` (via `stTrace_le_root`),
     `stTrace3_tube_le_root` (`r`-tube form), and the `AbsLipschitz`
     atoms `lipschitz1_min` / `lipschitz1_dist_of_mem` for the *sampled*
     `tri_bez_leaf_dist` fold). Not modeled: the leaf's distance is a
     sampled estimate, not exact `infDist`; `primhitcheck` covers it.
   - M14 signed-distance model: `Geom/BezTube.lean` now proves (working in
     `EuclideanSpace ℝ (Fin 3)`): `bezPhi` (φ(u) = dist x C(u) − r(u)),
     `bezQ`, `curvePt` (notation `!₂[gx, gy, gz]`), `bezQ_eq_dist_sq` /
     `bezPhi_eq_dist` (bridges to `Metric.dist`), `hasDerivAt_bezQ` /
     `hasDerivAt_bezPhi` / `deriv_bezPhi`, `continuous_bezPhi`,
     `phi_min_attained` (min on `Icc a b`), `bezPhiMin` /
     `bezPhiMin_eq` (the attained minimum value), `bezPhiMin_le`, and —
     **the linchpin** — `infDist_bezTubeSet`:
     `Metric.infDist x (bezTubeSet S a b) = max 0 (bezPhiMin S x a b)`
     for `a ≤ b` and `0 ≤ r(u)` on the interval (the `x` inside tube /
     perpendicular-foot cases), plus `stTrace3_bezTube_le_root` (the
     exact-distance no-overshoot trace corollary: root with
     `bezPhiMin ≤ 0` ⇒ iterate never passes it, `‖v‖ ≤ 1`), plus the
     sampled rule: `samDist` models the C's `tri_bez_leaf_dist` fold
     (min over sample sites of `dist x (C u) − r(u)`, empty site list is
     degenerate at `0`), proved `AbsLipschitz` by induction
     (`absLipschitz_bezContact`, `absLipschitz_samDist_foldr`), giving
     `lipschitz1_samDist_line` and `stTrace3_samDist_le_root` (the
     sampled trace never passes a root where the sampled min is ≤ 0,
     i.e. some site's ball covers the root — the honest analogue for the
     C's actual stepping function), and
     `samDist_nonpos_mem_tube` (sampled acceptance is sound: `samDist ≤ 0`
     ⇒ `x` inside the true tube — the C's leaf never accepts outside it;
     overshoot remains the sampling-density question), its
     contrapositive `samDist_pos_of_bezPhiMin_pos`, and
     `exists_bezTube_boundary_point` (IVT: along any segment from an
     outside point to a point in/touching the tube, some intermediate `s`
     has `infDist · (bezTubeSet) = 0` — the trace's boundary-existence
     companion to `stTrace3_bezTube_le_root`). Also done: the interior nearest
     point is a critical point of `φ` — `interior_min_bezPhi_deriv`
     (Fermat), `interior_min_bezPhi_envelope` (the foot-point equation
     `⟨x − C, C′⟩/|x − C| = −r′`), and `bezPhi_min_critical` (min of φ
     on `[a,b]` is attained at an endpoint, an interior critical point,
     or on the curve), `bezPhiMin_le_samDist` (for nonempty sites in
     `[a,b]`, the continuous min bounds the sampled fold below — the
     sampled fold is an over-estimate of the true distance-to-tube, the
     sign that makes the C's stepping by it safe in the no-overshoot
     sense), and the quantitative sandwich `samDist_le_bezPhiMin_add`:
     `bezPhiMin ≤ samDist ≤ bezPhiMin + (√3·Mx + Mr)·R` for sites with
     covering radius `R` and per-component derivative bounds `Mx` (curve)
     and `Mr` (radius), via MVT (`abs_sub_le_of_deriv_bound`),
     `curve_dist_le`, `rad_dist_le`, `foldr_min_le_mem`, `samDist_le_mem`.
     The Newton contraction core already landed as
     `ofCubic_newton_quadratic` (M7/M22 addendum 4). M14's remaining
   - Global safeguarded-Newton argument is now proved (Newton from an arbitrary
  seed, not just near a root): new `Geom/SafeguardedNewton.lean` —
  `fsplit`/`seqIter`, monotone `seqLo`/`seqHi` bracket sequences,
  `seqIter_width` (width halves: bisection alone suffices), convergence to
  a common limit (`seqLo_tendsto`/`seqHi_tendsto`/`limit_unique`),
  `bracket_root` (the bracket converges to a root of the sign-changing
  `ContinuousOn` function). Instantiated to the Bézier envelope:
  `envelope_continuousOn`, `bracket_envelope_bezPhi` / `'` (both sign
  conventions) — whenever `φ′` changes sign on `[a, b]` with `x` off the
  curve, there is a critical point of `φ`, and the C's sample-detected
  bracket converges to it from an arbitrary seed. Newton acceleration is the
  local half (`ofCubic_newton_quadratic`, M7/M22 addendum 4).
  M14's remaining bulk: the full 2D `(u, t)` basin-of-attraction refinement
  for `tri_bez_newton` with damped-step/`det > 0` guards (the local
  contraction core is done; the global 2D refinement is the one open deep
  item), and floating point of the minimizer (`primhitcheck` covers it).
   Patch/NURBS stay measured against `primhitcheck` (item 16 decision).

## Resuming prompt

> Continue the LightRT Lean formalization on branch `formal-lean` in
> `/mnt/nvme02/work/lightrt`. Read `resume-lean.md` and `formal/PLAN.md`
> (M14–M21) first. Run `make formal` to confirm the baseline (0 sorry, all
> checks PASS). Remaining large items: 4
> (BITEXACT SIMD == scalar for MT; ISA boundary recorded and **audited** —
> see PLAN.md addendum 11: every intrinsic in the Woop leaf is mapped to a
> model op; the residual ISA assumptions are enumerated and stay empirical
> via `wtcheck`; closing the boundary would need a vendor ISA semantics
> model). 3a (slab chain) is **done** (`fpT_abs_err_total`), 3b (MT error
> bound) is **done** (`MTT.lean`). 3c (`tlas_instance_margin` fp64) is
> **out of scope** by decision; do not attempt it. Item 7 is complete:
> `Geom/Newton2D.lean` (7b-1), `Geom/BezNewton.lean` (7b-2, the
> `tri_bez_newton` specialization: Jacobian as polynomial sums, C2Seg on a
> rectangle with `|R|² > 0`, contraction corollary `bez_newton_quadratic`),
> and `Geom/SphereTrace3.lean` (7a, 3D no-overshoot via `Metric.infDist`). For every C change: keep
> SIMD bit-identical to scalar (`wtcheck`, incl. the SVE leaf fuzz under
> qemu), rerun `make formal`, the C suites (`make c_tri_test c_tri_seam_test
> c_tri_parallel_test`, plus `tests/test_lightrt_c_quadtetra.c` and
> `tests/test_lightrt_c_surfaces.c` built by hand), `make hip_test` (local RX
> 9070 XT, use `timeout`), `make hip_rtc_test`, `make vk_test`, and
> `make cuda_full_test` on zen5 (`sm_86`) and b550 (`sm_120`). Those nodes run
> a GPU miner, so do correctness checks only there. Measure speed on a quiet
> machine (best of 9, interleaved; `make bench_occ` for the any-hit pipeline).
> Report measured costs honestly; keep negative results in PLAN.md. Commit
> when `make formal` passes, ending messages with `Co-Authored-By: Claude 5.5
> <noreply@anthropic.com>`. `formal/tools` is gitignored (`git add -f`). Do not
> push. Never submit Perforce changelists.
