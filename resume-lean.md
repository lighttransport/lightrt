# LightRT Lean formalization: remaining items and resume prompt

State as of 2026-11-13, branch `formal-lean` at `a4d92b6` (18 commits on top of
`7fd2bf7`). Nothing is pushed. The plan and history are in `formal/PLAN.md`
(milestones M1–M21); repo guidance is in `CLAUDE.md`, section "Formal
verification".

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
- 3: `FP/TotalErr.lean` range-free `|rneR x − x| ≤ u|x| + 2⁻¹⁵⁰`, and
  `Robust/Total.lean` `num_err_total` / `den_bounds_total` /
  `quot_bounds_total` / `woop_t_err_total` / `woop_t_err_total_model`
  (full range-free Woop `t` error, `η/a0` slack). C-range instantiation and
  the `1e-37` floor remain.

## Remaining items

### Proofs (Lean), large

3. **Rounding-model hypotheses (core done).** `FP/TotalErr.lean` gives the
   range-free primitive bound and `Robust/Total.lean` the full range-free Woop
   `t` bound (`woop_t_err_total_model`), with `η/a0` slack. Remaining:
   instantiate the ranges for the C call sites (slab/MT too), and the `1e-37`
   floor in `tlas_instance_margin`.
4. **A refinement proof for the SIMD watertight leaf.** `tri_woop4/8_block`
   and the new SVE `tri_woop_sve_*` are bit-identical to `tri_woop_one` by
   testing (`wtcheck` leaf fuzz, incl. SVE 8/16), not by proof. A Lean model of
   the SSE/AVX/SVE intrinsics, or a per-lane refinement argument, would close
   it. Same for `BITEXACT` SIMD == scalar for MT.
7. **Curve, patch and point hit correctness (started).** `Geom/Hull.lean`
   proves box containment; `Geom/SphereTrace.lean` now proves the 1D core of
   the first-contact argument (1-Lipschitz `f`: no overshoot of a surface
   point, monotone trace). Remaining: the full Bézier signed-distance model and
   the Newton refinement; patch/NURBS still measured against `primhitcheck`.

## Resuming prompt

> Continue the LightRT Lean formalization on branch `formal-lean` in
> `/mnt/nvme02/work/lightrt`. Read `resume-lean.md` and `formal/PLAN.md`
> (M14–M21) first. Run `make formal` to confirm the baseline (0 sorry, all
> checks PASS). Then work through the three remaining large items: 3
> (range-free slab/MT/Woop bounds from `model_abs_err_total`), 4 (per-lane
> SIMD refinement), 7 (Bézier first-contact model). For every C change: keep
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
