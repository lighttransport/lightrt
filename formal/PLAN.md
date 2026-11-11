# LightRT formal verification plan (Lean 4 + Mathlib)

Status as of 2026-11-10. Everything below builds with `make formal`. The codebase has **0 `sorry`s** (`tools/count_sorry.sh`; `FORMAL_SORRY_MAX = 0`). Every stated theorem is closed, including `tri_ray_setup_refines` (loop + struct stores), the Higham γₙ product lemmas, Möller–Trumbore soundness/completeness/Cramer over ℝ, the Woop vertex fan, and the BVH build/traversal theorems. **337 theorems are closed** with axioms limited to {`propext`, `Classical.choice`, `Quot.sound`}. That count includes 52 MiniC logic lemmas ported from tinygltf; 117 are new to this project, including the full M1 Ize slab bound (`slab_no_false_miss`, `slab_t_err`, `slab_t_err_fma`, `ize_constant_sufficient`/`_gamma3_insufficient`). The binary32 instance `Binary32.model` is now sorry-free (`rneR_rel`, `rneR_mono`, `rneR_neg`, `rneR_idem`, `rne_cast`, `mul_num_refines`), so `slab_no_false_miss` holds for real binary32 RNE. No closed theorem uses `native_decide`.

## 1. Repo layout

```
formal/
  lean-toolchain        leanprover/lean4:v4.35.0   (= latest stable Mathlib tag v4.35.0)
  lakefile.lean         require mathlib @ v4.35.0; lib LightRT (+submodules); exe cdiff
  LightRT/Geom/         Stage 1  Basic (Ray, Box, HitsBox, InTriangle), SlabReal, MTReal
  LightRT/FP/           Stage 2  Model (RoundingModel), Gamma (γₙ), Binary32 (executable RNE)
  LightRT/Robust/       Stage 3/4  Slab (no-false-miss, Ize), Woop (watertightness)
  LightRT/BVH/Tree.lean Stage 5  containment invariant, traversal = brute force
  LightRT/C/            Stage 6  MiniC Semantics/Logic/Hoare (ported from tinygltf),
                                 Gen (GENERATED from lightrt_c_tri.c), Ref (bit-level oracle),
                                 Proofs/Refines, Proofs/SlabMiss
  LightRT/Sanity.lean   non-vacuity examples (§4)
  CDiff.lean            MiniC + Ref runner for differential testing
  tools/                c2lean.py, cdiff.py, cdiff_c.c, count_sorry.sh, check_axioms.py
```

Naming conventions:
- Namespaces follow the directories (`LightRT.Geom`, `LightRT.FP`, …).
- Theorems are named `<algo>_<property>` (for example `slab_no_false_miss` or `woop_edge_antisymm`).
- Each translated C function `foo` has a `foo_refines`.

## 2. Floating-point dependency decision

Each library was cloned and read on 2026-11-10. The `sorry` counts are real tokens; every matching word inside a comment was ignored.

| | FloatSpec | Flean | FloatLib | **custom (chosen)** |
|---|---|---|---|---|
| Last commit | 2026-09-13 | 2026-04-07 | 2026-11-07 | — |
| Toolchain | v4.34.0-rc2 | v4.27.0-rc1 | v4.35.0 ✓ | v4.35.0 |
| License | Apache-2.0 | Apache-2.0 | MIT | MIT (LightRT) |
| `sorry` / `axiom` | 0 / 0 | 0 / 0 | 0 / 0 | 15 (ours, tracked) |
| Size | 80 files | 9 files | 1451 files, `native_decide` in 6 | 3 files |
| Executable bit-exact binary32 for cdiff | unclear | partial | yes | yes |

**Decision: a minimal custom model.** `FP/Model.lean` defines an abstract `RoundingModel`: one fresh δ per operation, monotone, odd, idempotent, with an explicit `InRange` predicate. `FP/Binary32.lean` is a computable RNE with subnormals, ±0, ±∞ and x86 NaN propagation. One generic `rne` definition serves both ℚ (executed) and ℝ (`model`).

Reasons:
1. MiniC needs an executable, bit-exact semantics that agrees with compiled C. None of the theorems need Flocq-scale generality.
2. No toolchain lag: FloatSpec and Flean pin older Lean versions.
3. FloatLib is compatible (MIT, v4.35.0), but adds about 1.4k modules and uses `native_decide` internally. It remains the fallback for lemmas such as `rneR_rel` if proving them ourselves stalls (risk R1).

## 3. Stages: main statements

All statements below compile. A † marks a theorem that is already proved.

**Stage 1 (ℝ³):**
- `slabReal_iff (hd : ∀ i, r.d i ≠ 0) : slabReal r b ↔ HitsBox r b`
- `hitsBox_parallel`†
- `mtReal_sound` (needs `0 < ε`: with `ε = 0` a zero determinant is not rejected and the division by zero yields a bogus hit, so the original `0 ≤ ε` statement was false), `mtReal_complete`, `mt_cramer`
- Helpers: `slab_axis_iff`, `mt_cramer`

**Stage 2:**
- `gamma_nonneg`†, `gamma_mono`
- `prod_one_add_le` (Higham Lemma 3.1, with independent `δ : Fin n → ℝ`) and its inverse-factor variant
- `gamma_compose`, `abs_err`
- `sub_antisymm`†
- The binary32 obligations `rneR_rel`, `rneR_mono`, `rneR_neg`, `rneR_idem`, plus the bridges `rne_cast` and `mul_num_refines`
- Eleven `#guard` tests: ties-to-even, subnormal tie, 1/±0, overflow, NaN.

**Stage 3 (slab):**
- `slab_t_err`: scalar order, |t̃ − t| ≤ γ₃|t|.
- `slab_t_err_fma`: the FMA order used by the SIMD kernels has an *absolute* error, ≤ γ₃(|x−o|+|o|)/|d|.
- `slab_no_false_miss (hK : InflationOK u K) (hrange : SlabInRange …) : HitsBox r b → fpSlab R r b K`. The implication runs from a geometric hit to an algorithm hit.
- **Derived finding.** I derived this condition myself; Ize's constant is still UNVERIFIED against the paper. When `tfar·K` is itself rounded, the requirement is `1+γ₃ ≤ (1−γ₃)(1−u)K`. The real number K = 1+2γ₃ does *not* meet it (`ize_constant_gamma3_insufficient`), while 1+2γ₄ does (`ize_constant_sufficient`). Empirically, either constant rounded *up* to binary32 (1+8u or 1+10u) removed all 2,908 observed misses.
- **The real C misses hits.** `tri_slab_scalar_false_miss`† is kernel-checked with `decide +kernel` on the c2lean translation. In exact ℚ the ray meets the box, yet `tri_slab_scalar` returns 0. A seeded search found 2,908 such false misses among 73,412 exact-hit grazing rays (4%).

**Stage 4 (Woop):**
- Reference implementation over any `RoundingModel`.
- `woop_edge_antisymm`† (**M1**) and `woop_shared_edge_W`†: adjacent triangles compute exactly opposite W.
- `woop_no_gap`†: no ray passes between two triangles sharing an edge.
- `edgeFn_sign_weak`, and `woop_vertex_fan` (under an exact-sector hypothesis).
- Not modelled: the paper's double-precision tie fallback. Its absence can only duplicate a hit, never lose one.

**Stage 5 (BVH):**
- `build_contains`† holds for every split strategy.
- `build_prims_perm`.
- `traverse_eq_brute (hcons : Conservative …)` and `traverseOrdered_eq_brute`, which models the LightRT loop with t_best culling.
- Stage 3 discharges `Conservative`: the box test receives a box that encloses a hit primitive's bound, so `HitsBox` holds.

**Stage 6 (C):** `tri_ray_setup_refines`, `tri_slab_scalar_refines` and `tri_mt_one_refines` cover every input, including NaN, ∞ and subnormals, and include frame conditions. `slab_ref_eq_fpSlab` connects these bit-level results to Stage 3.

Helper lemmas still needed:
- evaluation lemmas for `binF32`, `loadF32` and `storeF32`, in the style of tinygltf's `varLoad`
- (done) decode/encode round-trip `decode_encode_num`, `propagate` identity on finite inputs, `fmin`/`fmax` = `min`/`max` (`C/Proofs/SlabFP.lean`)

Full verification of the SIMD and GPU kernels is out of scope. They are byte-for-byte ports already tested against the scalar oracle (`tests/test_lightrt_c_tri.c`).

## 4. Specification review checklist (human)

1. **Direction of the implication.** Conservativeness must read `HitsBox → algorithm hit`. Reject `algorithm hit → HitsBox` (that would be soundness, a different claim) and any `↔` stated for FP code.
2. **Ground truth independent of the algorithm.** Postconditions should mention `HitsBox` / `InTriangle`, never `fpSlab` on both sides. A spec built from the algorithm's own output is trivially true.
3. **Hypotheses are satisfiable.** Each main theorem should have an `example` in `Sanity.lean` that inhabits its premises. `RoundingModel.exact` shows the class is consistent. Look for range hypotheses that silently exclude the interesting cases; for example, `InRange` must not exclude 0.
4. **The conclusion is not trivial.** There should be a negative example: a miss, a rejected `Accept`, or a violated `Contains`.
5. **Unintended hypotheses.** Check against the C. `0 ≤ tmin` is required, so state it explicitly. `d i ≠ 0` changes semantics, because C clamps `invd` to ±1e18. The NaN inputs needed for `refines` must cover every bit pattern.
6. **Constants come from the code or the paper.** `1e18f`, `1e37f` and `1e-12f` are taken from `lightrt_c_tri.c`. Ize's constant is UNVERIFIED (§3).
7. **Per-operation δ.** No statement may use a single shared `δ` across operations.
8. **Generated code is fresh.** `c2lean.py --check` must pass, and `Gen.lean` must never be edited by hand.

## 5. Agent workflow

- **Human-owned:** every statement in §3, edits to `Model.lean`, `Semantics.lean` and `c2lean.py` (all part of the trusted base), and the checklist. The agent never edits a theorem statement. If one looks false, it escalates with a counterexample from `cdiff.py` or `#eval`.
- **Delegated to the agent through lean-lsp-mcp:** closing `sorry`s, one theorem per task, with ≤30-line lemmas.
  - The agent first writes a `have`-skeleton with sub-`sorry`s and checks the goal states.
  - It then closes the leaves.
  - Preferred tactics: `simp`, `linarith`, `nlinarith`, `positivity`, `gcongr`, and `decide +kernel` for concrete bits.
- **Splitting:**
  - Refinement proofs go statement by statement through `Logic.lean` (`EvE`/`ExS`), with one lemma per C basic block.
  - FP bounds go one operation at a time through `RoundingModel.rel`, then `prod_one_add_le`.
- **Retry and escalation:** 3 attempts per lemma, each with a different strategy. After that the agent posts the goal state, the attempted tactics and a minimal `example` to the human. If the agent believes the statement is false, it searches for a counterexample with cdiff before escalating.
- **CI gates (`make formal`):**
  - `lake build`
  - `c2lean --check`
  - the `sorry` budget (`FORMAL_SORRY_MAX`, monotonically decreasing)
  - `check_axioms.py`: allowlist enforced, no `native_decide`/`bv_decide` under `Robust/` and `C/Proofs/`
  - `cdiff --n 1000`, three-way: compiled C under ASan/UBSan, MiniC, and Ref
  - Build budget: ≤15 min cold with the Mathlib cache. The current incremental build takes about 1 min, and the `decide +kernel` witness takes about 9 s.

## 6. Risk register

| # | Risk | Mitigation / fallback |
|---|---|---|
| R1 | `rneR_rel`/`mono` take long to prove over `Int.log` | Cite FloatLib's lemmas, or prove only the normal range |
| R2 | MiniC binary32 ≠ hardware | Three-way cdiff (60k vectors, 0 mismatches). NaN sign/payload follows x86 SSE (IEEE leaves it unspecified) and is visible through `copysignf`. ARM may differ, so cdiff must run there before any ARM claim. |
| R3 | `-ffp-contract` | The verified object is the code compiled with `-ffp-contract=off`. GCC's default `fast` contracts to FMA, so production builds need the flag, or `slab_t_err_fma` must be the bound that applies. |
| R4 | `decide +kernel` blowups | Keep concrete witnesses small; never use `native_decide` |
| R5 | The Ize constant is misremembered | Read the JCGT 2013 paper and its FMA note, then update §3. The derived condition is the safe one. |
| R6 | Woop is not in LightRT C | Port `tri_woop_one` to C behind a flag, extend `c2lean` `FUNCTIONS`, and reuse Stage 4 |
| R7 | Translator bugs (trusted base) | Reject unsupported syntax (`die`), audit diffs of `c2lean.py`, and rely on cdiff against the compiled binary |

## 7. Milestones

- **M0 (done):** Project, pinned toolchain, Stage 1–6 statements, c2lean port, three-way cdiff, CI gates.
  - c2lean was ported with f32 support, `copysignf`, scalar replacement of constant-indexed local arrays, and fixes for loop-variable ordering and enums.
- **M1:** Woop edge antisymmetry (✅ done: `woop_edge_antisymm`, `woop_no_gap`), plus Ize's slab bound (✅ done: `slab_t_err`, `slab_t_err_fma`, `slab_no_false_miss` under `6u<1`, `InflationOK`; spec fix: `slab_axis_iff`/`slabReal_iff` needed `lo ≤ hi`).
- **M2:** binary32 model obligations (`rneR_*`) and `slab_ref_eq_fpSlab`.
- **M3:** ✅ `tri_slab_scalar_refines`, `tri_mt_one_refines` (all inputs, eventual-fuel form), `tri_slab_scalar_false_miss_exists` (over ℝ, `Binary32.model`), add/sub/mul/div value bridges, and the opt-in C patch `LRT_TRI_SLAB_INFLATE` (`tfar *= 0x3f800005`). `slab_ref_eq_fpSlab` ✅ (via `decode_encode_num`). `tri_ray_setup_refines` ✅ (3-iteration loop unrolled; arbitrary initial `*rc` contents).
- **M4:** ✅ Woop vertex fan and `tri_mt_one_refines`. `mt_not_watertight` ✅ (`C/Proofs/MTGap.lean`): a ray through the shared edge of two adjacent triangles hits one of them in exact arithmetic but binary32 `tri_mt_one` rejects both (kernel-checked). C port of Woop ✅: `tri_woop_one` in `lightrt_c_tri.c`, used by the CPU quad/tetra leaves under `-DLRT_TRI_WATERTIGHT` (default off; GPU `hp_mt` unchanged). Proved: `tri_woop_one_refines` (C = `Ref.woop`, all inputs, 8-way axis selection + one symbolic run of the fp body), `woop_no_gap_bits` (bit-level watertightness for EVERY input, NaN/∞/underflow/overflow included: the shared edge function has exactly opposite sign in the two triangles, so the sign test of at least one passes), `woop_no_gap_det` / `woop_det_ne_zero` (`WoopDet.lean`: after the sign test, `det ≠ 0` for every input once some edge value is strictly signed, because a same-sign binary32 sum never rounds to zero; so the only remaining per-triangle rejection is the `t` range), and `woop_closes_mt_gap` (Woop accepts the triangle on `mt_not_watertight`'s witness). cdiff covers `woop` vectors; the quad seam test in `tests/test_lightrt_c_quadtetra.c` leaks 5/3000 diagonal rays with MT and 0 with the flag.
- **M5:** ✅ BVH `build_prims_perm`, `traverse_eq_brute` / `traverseOrdered_eq_brute` (generic in the box test; instantiate with the Stage 3 inflated slab).
- **M6 (flat BVH of the C kernel):** ✅ `BVH/Flat.lean` models `tri_intersect_scalar`'s data and loop: an array of wide nodes with `(box, ref)` children, leaf refs as block ranges, a `(ref, tnear)` stack, `tnear ≥ best` culling, and pushing the box hits in any order. The semantics `den`/`visits` are total, by recursion on increasing child indices. Proved:
  - `den_inside`: global containment follows from the local check `WF` (child indices increase, each child box contains its children's boxes and its leaf primitives).
  - `run_spec` / `run_root`: with fuel `visits root + 1`, the loop terminates and returns exactly the brute-force nearest `t`, given conservativity C1 (an enclosed hit `t < best` passes the box test) and C2 (`tnear ≤ t`).
  - `run_approx`: if `tnear ≤ g t` for a slack `g ≥ id`, the result `r` satisfies `brute ≤ r` and `r ≤ g t` for every hit, so it is at most `g` farther than the nearest hit.
  - `checkWF` / `checkWF_sound`: an executable checker for `WF`. `BVH/Check.lean` instantiates it with exact-rational containment of the *stored* triangle `v0 + u·e1 + v·e2` (`insideQ`); `checked_run_root` is the result.
- **M6 validation (`make formal` → `tools/bvhcheck.py`):** `tools/bvhdump.c` dumps real C-built BVH4/BVH8 trees (LBVH and SAH; random soup and a jittered heightfield, with rays aimed at grid vertices and edges, including axis-parallel rays). The `checkbvh` executable runs `checkWF` and a Lean mirror of the loop that uses the verified `Ref.raySetup`/`Ref.slab`. It compares the mirror with the C scalar traversal (t and prim_id) and with brute force. Findings:
  1. **The mirror equals the C scalar traversal bit for bit** on every ray tested.
  2. **Default leaf boxes do not contain the tested triangle.** `e1 = fl(v1−v0)` is stored rounded, so `v0+e1` can exceed the box by up to ~10 ulp, and `checkWF` fails on every tree. Refit's `tri_leaf_prim_aabb` has the same issue. Fix `LRT_TRI_LEAF_BOX_EXACT` (default on since this milestone; opt out `-DLRT_TRI_NO_LEAF_BOX_EXACT`): TwoSum-bracketed corners in `tri_leaf_prim_aabb`, plus a bottom-up `tri_refit_propagate` after the build (not SBVH/HQ, whose clipped boxes need a different invariant). With it, `checkWF` passes on every tree.
  3. **C2 fails at the ulp level.** On shared-edge rays the rounded box `tnear` can exceed the rounded triangle `t`, so the BVH returns a hit 1–4 ulp farther (another prim) than brute force. This is exactly `run_approx` with `g t = t + few ulp`.
  4. **Parallel-ray false miss** (`C/Proofs/SlabParallel.lean`, `slab_parallel_false_miss`, decide +kernel): with `d_k = ±0` and the origin exactly on a box face, the clamp `1/±0 → ±1e18` gives `0·1e18 = 0` as the far bound, so the box is rejected although the ray lies in it. Vertical rays along the scene's boundary edge miss the scene. This is outside the `|d| ≥ 1e-18` hypothesis of the Stage 3 theorems. A fix must touch every slab implementation (scalar/SSE/AVX2/NEON/SVE/GPU), so it is left open.
  The SIMD-dispatched traversal (`lrt_tri_intersect1`, not bit-identical to scalar) differs by ≤ 10 ulp on most rays, with rare different-prim hits.
- **M7 (open items closed; opt-in compile flags, of which `SLAB_ROBUST` and `LEAF_BOX_EXACT` became the default in M8):**
  - **Parallel-ray false miss → `LRT_TRI_SLAB_ROBUST` (default on; opt out `-DLRT_TRI_NO_SLAB_ROBUST`).** The slab reciprocal is `+∞` (not the `1e18` clamp) for `d = ±0`, the entry bound is `min(th, tl)`, and the SIMD node tests use the sub-mul form instead of the FMA form. A ray lying on a slab plane then gives `0·∞ = NaN`, which the operand order of the min/max chain drops (`+∞` for both signs of zero means only two NaN placements can occur, and both are dropped). Lean: `Ref.slabRobust`, plus `slabRobust_parallel_hit` / `_lo` (decide +kernel) on the witness that `slab_parallel_false_miss` rejects. Validation: 0 hit/miss differences against brute force on the heightfield trees, where the default kernel had 3–4 per 400 rays. Coverage of the other backends (ARM, quantized nodes, GPU) is listed under "Robust slab on every backend" below.
  - **SIMD/scalar parity → `-DLRT_TRI_BITEXACT`.** The AVX2 leaf (`TRI_X8`/`TRI_DOT8`) uses scalar `tri_isect_lane` order without FMA. The det-epsilon test uses scalar association `(EPS·s)·s` and the scalar predicate `!(−rel < det < rel)`. With `LRT_TRI_SLAB_ROBUST` (sub-mul slabs), `lrt_tri_intersect1` (SSE BVH4 / AVX2 BVH8) equals `tri_intersect_scalar` in (t, prim) on every validation ray, asserted by `bvhcheck.py`.
  - **Watertight main triangle leaf → `-DLRT_TRI_WATERTIGHT_TRI`.** The scene keeps the exact input vertices (`wverts`, refreshed by refit). The scalar leaf `tri_isect_lane_s` runs `tri_woop_one`, which is proved to refine `Ref.woop` and to be watertight on shared edges (`woop_no_gap_bits`, `woop_no_gap_det`). Triangle queries route to the scalar kernels. `tests/test_lightrt_c_tri_seam.c` (`make c_tri_seam_test`) shoots 400k rays at shared heightfield edges: default MT leaks 10–13%, the watertight leaf leaks 0. Serialized/mmapped scenes carry no `wverts` and fall back to MT.
  - **SBVH (HQ) correctness → `Flat.run_cover` / `run_cover_root`.** Containment is replaced by per-ray coverage: every hit primitive has a reference whose whole box path contains the hit point (`goodN`/`goodRef`), and C1/C2 are stated for hit points. The loop then terminates with `brute ≤ r ≤ tmax` and `r ≤ g t` for every hit (`g = id`: exactly the nearest). This needs only the index part of well-formedness (`WFidx`; `WF.idx`). The validator checks the Lean mirror against C scalar on SBVH trees too.
  - **Exactly nearest → `-DLRT_TRI_EXACT_NEAREST` + `Flat.run_exact`.** With pruning that depends on the current best, C2 with `g = id` cannot hold in general, because the MT/Woop `t` error is unbounded for grazing triangles. In exact-nearest mode the closest-hit node test uses `tmax` instead of the current best and pushes children with `tnear = tmin`, so C2 holds trivially. `run_exact` then proves the loop returns EXACTLY the brute-force nearest hit, given containment and a conservative box test. Implemented for scalar, SSE BVH4 (and the NEON shim) and AVX2/SVE BVH8. Validation (`bvhcheck.py` "exactn", and aarch64 under qemu with 512-bit SVE): t equals brute force, and SIMD equals scalar, on every ray. Without the flag, `run_approx`/`run_cover` still bound the slack (≤ 4 ulp measured). The cost is losing early-out pruning.
  - **Robust slab on every backend.**
    - *ARM:* the NEON shim maps `_mm_min/max_ps` to exact x86 semantics (`vbslq(vcltq)`) under `SLAB_ROBUST`/`BITEXACT`. The SVE BVH8/BVH16 slabs use `sinv` and select-based min/max, and the SVE leaves use separate mul+add under `BITEXACT`. Under qemu, NEON BVH4 and SVE BVH8 match scalar in (t, prim) with 0 hit/miss differences against brute force.
    - *Quantized nodes (BVH8Q / QF8 / Q4):* boxes are decoded to floats and run through the robust float slab (`tri_slab8_robust_q`). The qnode kernels' leaf takes the watertight path under `WATERTIGHT_TRI`. `tests/test_lightrt_c_tri_parallel.c` (`make c_tri_parallel_test`) fires 20k vertical rays exactly on box faces: the default build misses 649 / 18 / 18 / 18 (BVH4 / BVH8Q / QF8 / Q4), the robust build 0 on every format.
    - *GPU:* the hiprtc kernel (`hip/trace_bvh_hip.h`, `-DLRT_TRI_SLAB_ROBUST` passed to hiprtc), the CUDA port, the stale `.hip` source and the Vulkan `trace_bvh.comp` (specialization constant 2, SPIR-V regenerated). GPU `fminf`/GLSL `min` IGNORE the on-plane NaN and keep the infinite bound, so explicit selects are used. On an RX 9070 XT the same vertical-ray set gives HIP 547 → 16 misses and Vulkan 547 → 8 with the robust slab alone.
    - *GPU watertight leaf:* the hiprtc kernel and `trace_bvh.comp` include a line-for-line port of `tri_woop_one` (`woop_one`; the GLSL edge functions are `precise`, i.e. not contracted, so the antisymmetry the proof uses still holds). The host uploads the exact vertices from the LRTS aux region: HIP passes a kernel argument, Vulkan uses binding 4 plus `pc.nwverts`. Only `LRT_TRI_WATERTIGHT_TRI` scenes carry that data, so default behaviour is unchanged. With all three flags, both HIP and Vulkan have **0 misses**. HIP is also bit-identical to the CPU in (t, prim) on every ray. Vulkan is not, because RADV's arithmetic outside the precise edge functions may fuse, as in the default build. `make vk_test` still passes, 0 mismatches. The precompiled resident HIP backend (`lightrt_c_hip.hip`: `hp_woop_lane` in `k_trace`/`k_occluded`, `d_wverts` uploaded from the aux region and refreshed by `refit_core`) also reaches 0 misses on the parallel-ray set, bit-identical to the CPU. The CUDA twin (`lightrt_c_cuda.cu`) has the same code. Verified on hardware (2026-11-11, `make cuda_full_test`): RTX 3070 (sm_86) and RTX 5060 Ti (sm_120) give identical results: triangles 0 mismatches; every primitive kind and the shading normals 100% vs the CPU oracle (Bézier curves 99.93%, as on HIP); parallel-ray test with the watertight leaf 0 GPU misses and GPU == CPU bit for bit on BVH4 and BVH8.
  - **HIP build fixed.** Commit `44e178e` had replaced `lightrt_c_hip.h` with a 6-function header for the new hiprtc path. That broke the resident HIP backend (`lightrt_c_hip.hip`), `tests/test_lightrt_c_hip.c`, `benchmark_hip/` and the CUDA port, all of which use the device-resident API. The new path's `lightrt_c_hip.c` was also unbuildable: no `hipew.h`, and no build target.
    - Restored the resident-API header. It is a superset of the hiprtc path's API, plus `LRT_HIP_CAP_POINTS`. `make hip_test` passes on gfx1201 again.
    - Added `lightrt_hipew.{h,c}`, a minimal dlopen loader in the style of `lightrt_vkew` for the 21 HIP/hiprtc entry points the hiprtc path uses (no ROCm SDK at build time).
    - Added `make hip_rtc_test` (`tests/test_lightrt_c_hip_rtc.c`). It skips without a runtime.
    - The hiprtc kernel is now compiled with `-ffp-contract=off`: hiprtc contracts by default, which broke parity with the CPU and the exact antisymmetry of the Woop edge functions. With all flags it is bit-identical to the CPU with 0 misses.
- **M8 (robust defaults):** `LRT_TRI_SLAB_ROBUST` and `LRT_TRI_LEAF_BOX_EXACT` are on by default (`lightrt_c_tri.h`; opt out with `-DLRT_TRI_NO_SLAB_ROBUST` / `-DLRT_TRI_NO_LEAF_BOX_EXACT`). Every backend includes that header, so the CPU SIMD paths, hiprtc, the resident HIP and CUDA kernels and Vulkan follow the same default.
  - *Two translated configurations.* `c2lean.py` now emits `C/Gen.lean` (legacy kernel, both opt-outs; the Stage 6 refinement theorems and the `tri_slab_scalar_false_miss` witness are about this code, which is still built with the opt-outs) and `C/GenRobust.lean` (the default build). `--check` checks both.
  - *Default-build refinement.* `tri_slab_scalar_robust_refines` (`C/Proofs/SlabRobustRefines.lean`): for every input, the compiled default `tri_slab_scalar` returns exactly `Ref.slabRobust` on the 68-byte context `tri_ray_setup` builds (`sinv = +∞` for `d = ±0`, else `invd`). With `slabRobust_parallel_hit` this closes the parallel-ray false miss at the C level for the shipped kernel.
  - *cdiff.* New `slabr` vectors run the default-build C against `GenRobust` and `Ref.slabRobust`; half put the ray parallel to and exactly on a face plane. The legacy `slab`/`mt`/`woop` vectors run against a legacy C build. 20k vectors: 0 mismatches.
  - *Cost* (1 thread, mandelbulb 128k tris, 4 interleaved pinned runs, best of each): trace within noise (−3%..+2% on BVH4/BVH8/LBVH8, primary/incoherent/shadow), build +7% (SAH BVH4) to +29% (LBVH8), all from `LEAF_BOX_EXACT` (TwoSum bracketing + the refit pass). No memory change. The unloaded-machine caveat applies: the host had load average 15–24 while measuring.
  - Still opt-in: `BITEXACT`, `WATERTIGHT_TRI` (extra vertex copy, scalar leaf), `EXACT_NEAREST` (no early-out pruning).
- **M9 (any-hit, SBVH coverage check, two-level):**
  - *Any-hit* (`BVH/AnyHit.lean`): `Flat.runAny` models `tri_occluded_scalar` (box test against fixed `tmax`, stop at the first leaf hit, any push order). `runAny_root`: with `WF` and a conservative box test it returns exactly whether any reachable primitive hits. `runAny_cover_root`: the SBVH form, needing only `WFidx` and per-node coverage (`skip`). Not modelled: C returns 0 on stack overflow (`sp + nchildren > TRI_STACK_SIZE`).
  - *Validation* (`bvhcheck.py`): the validator runs the proven `Flat.runAny` itself, with the bit-level C box test, and compares it with `tri_occluded_scalar`, the dispatched `lrt_tri_occluded1` and brute force. It also checks the coverage hypothesis bit-exactly: every hitting primitive must have a reference whose whole box path passes the test. SBVH trees now also run under the default flags. Result: Lean == C scalar on every ray of every variant; default flags (robust/exactn/SBVH-robust): 0 differences from SIMD or brute force and 0 uncovered hits; legacy flags: 32 (BVH) / 29 (SBVH) uncovered hits, the parallel-ray false miss.
  - *Two-level* (`BVH/TwoLevel.lean`): `runT` models `lrt_tlas_intersect1` (leaf = per-instance BLAS query with `tmax = best`). `runT_eq_run`: if each BLAS query from `best` is the fold of its primitives (`blas_fold`, from `run_root`), the TLAS loop equals `run` over (instance, primitive) pairs; `tlas_root` then gives brute force over every reachable pair. `hit_iff`: over ℝ the affine world→object map preserves the ray parameter exactly (`HitsTriangleAt` in object space ⇔ in world space on the obj2world image). `xform_point_err` / `xform_vec_err`: rounding of `tlas_xform_point` / `tlas_xform_vec` in any `RoundingModel`, as `u·Σ|products| + u·Σ|partial sums|`. Open: discharging the TLAS conservativity conditions (C1/C2 for pairs) from `tlas_transform_aabb` rounding, and a bound on the world-space `t` error of the whole pipeline.
  - *Validation* (`tools/tlascheck.c`, in `make formal`): random BLAS (BVH4/BVH8, LBVH/SAH) and 60 instances with random rotation, non-uniform scale and translation, plus masks. TLAS `t` == brute-force minimum over instances, bit for bit (with and without `EXACT_NEAREST`); any-hit == brute force; 0 hit/miss differences against an fp64 world-space Möller–Trumbore over the transformed triangles; max relative `t` error 1.4e-5–2.5e-5.
- **M10 (curve / patch / point boxes; hit-accuracy reference):**
  - *Hull theorems* (`Geom/Hull.lean`): `hull_of_balls` (a convex combination of points, each within `r k` of `P k`, lies in every box containing all `P k ± r k`) and its instances `bezier_tube_in_box`, `linear_tube_in_box` (round-linear and flat curves: hull of the end balls), `bilinear_in_box`, `bicubic_in_box`, `rational_in_box` (positive weights, box of the projected CPs `x/w`), `ball_in_box`; Bernstein nonnegativity / partition of unity (`bern3_*`, `bern33_*`); `decasteljau_left/right` (the pre-subdivided sub-arc CPs describe exactly that sub-arc).
  - *Exact C check* (`tools/primboxcheck.c`, in `make formal`): every BVH4 child box contains the control-point hull of the STORED leaf data (exact in double; `x/w ≥ lo` tested as `x ≥ lo·w`), and every inner box contains its children. **Found:** every `c ± r` box (round-linear, flat, Bézier curves, sphere/disc points; also ellipse and SDF primitives, same code shape) missed the stored primitive by up to 0.5 ulp on 2–10% of the checks, and NURBS `x·fl(1/w)` boxes by up to 10 ulp. **Fix** (under `LRT_TRI_LEAF_BOX_EXACT`, default): `tri_box_sub/add` (TwoSum bracket) and `tri_box_div_lo/hi` (exact rounding-direction test) at every such site, including the curve refit box and the NURBS intersector's own subdivision cull (also in the HIP/CUDA ports, `hp_div_lo/hi` via `fmaf`). After: 0 failures.
  - *Hit accuracy* (`tools/primhitcheck.c`, in `make formal`): C hits against a double-precision reference: the residual on the exact stored geometry (union-of-balls distance for tubes/points, `|S(u,v) − (o + t d)|` for patches) and an independent nearest-hit reference (sphere tracing on the exact union-of-balls distance; MT on a 128×128 double tessellation of each patch). **Found:** the patch Newton loops (bicubic, rational, and the fp64 refinement `tri_patch_newton_hp`) and the Bézier-curve Newton tested convergence on the residual BEFORE the final update but returned the point AFTER it, so an ill-conditioned last step produced false hits (one bicubic hit 0.17 from any surface; Bézier-curve hits up to ~a radius off). **Fix:** the convergence test is on the returned point; patches take one more step and keep it only if its residual is smaller (accuracy unchanged, ~1e-6). Mirrored in HIP/CUDA; GPU-vs-CPU agreement unchanged (patches 100%, Bézier 99.93%).
  - *Measured* (8 seeds × 3000 rays per kind): round-linear, sphere points, bilinear, bicubic, NURBS: 0 hit/miss and 0 `t` disagreements with the reference beyond the tessellation tolerance, residual ≤ 2.4e-5 (curves) / ≤ 4e-6 (patches). Cubic Bézier curves: residual p99.9 ≈ 3e-4 (the Newton tolerance `1e-5·(1+|R|)` and the normal-plane-circle surface model vs the union of balls), ≤ 0.1% of hits above 1e-3 (the documented cone fallback for ill-conditioned Newton), and 0–3 per 3000 rays where the adaptive sweep returns a farther hit than the nearest. These are thresholds in the tool, not zero; improving the sweep's pruning is open.
  - *Cost* (1 thread, `dea7d73^` vs this, interleaved pinned runs, best of 3–6; 28k-segment hair, 20k Bézier curves, 50k sphere points, 4k bicubic patches, 39×39-span NURBS, 400k rays): trace within ±0.5% for every kind except NURBS −2.8%; hit counts identical except one bicubic hit (the Newton fix). Build: round-linear +1.7 ms (+37%), flat +2.2 ms (+11%), Bézier +6.9 ms (+20%), points +2 ms (+5%), bicubic 0, NURBS +1.1 ms (+81%, exact `x/w` box per extracted patch). The first version cost NURBS −80% trace: the exact per-point `x/w` rounding ran inside the intersector's subdivision cull. That hot path now uses the original arithmetic plus an 8u widening of the finished bounds (conservative for the ≤ 2 roundings of `x·fl(1/w)`); `nextafterf` was replaced by an inline bit step and the TwoSum `volatile` dropped.
- **M11 (refit / serialization, more kinds, stack overflow):**
  - *Box check coverage* (`tools/primboxcheck.c`): every scene is also checked after `lrt_tri_scene_save_to_memory` → `load_from_memory` and `save` → `open_mmap`, and the curve and patch scenes after refit (`lrt_curve_refit`, `lrt_tri_surface_refit` with moved control data). New kinds: ellipses, built-in SDF primitives (sphere/box/torus, including the ray-interval clip radius `brad`), planar quads, tetrahedra, and quantized triangles in all four formats, lossy and conservative (no serialization: they refuse to save).
  - *Found* (against the previous kernel): SDF boxes and clip radii missed the shape by up to 2 ulp (99 failures/seed: the torus extent `|R| + |r|` and `br = sqrt(…)` rounded inward). Quantized-triangle leaf boxes missed the tested triangle by up to 8 ulp, including in CONSERVATIVE mode: the box was built from the decoded vertices, but the intersector tests `v0 + u·fl(v1−v0) + v·fl(v2−v0)`. *Fix* (under `LEAF_BOX_EXACT`): torus extent via `tri_box_add`, `br` widened by 4u, quantized-triangle box corners via `tri_sum_bracket` like plain triangles. After: 0 failures on 3 seeds for every kind and every reload / mmap / refit variant.
  - *Stack overflow* (`BVH/AnyHit.lean`): `runAnyB` models `tri_occluded_scalar`'s `if (sp + nchildren > TRI_STACK_SIZE) return 0`. `need i = (#children − 1) + max(1, max over children of need)` (order-independent). `runAnyB_eq`: under the invariant "each entry's need plus the entries below it fits" (`Good`, preserved by every push via `need_child` / `good_append`) the check never fires; `runAnyB_root`: if `needRef root ≤ cap`, the bounded C loop equals brute force. The closest-hit check uses the number of children that pass the box test, at most `#children`, so the same bound covers it (not separately formalized). The validator computes `need` on every C-built tree and asserts it ≤ 1024 (max 17 measured) and runs `runAnyB` itself against the C any-hit.
- **M12 (pathological geometry, degenerate triangles, NaN and boundary semantics):**
  - *Pathological scenes* in `bvhcheck.py` (`--only-patho` to run alone): every vertex at one point (all triangles degenerate) and 500 distinct triangles overlapping in one plane, BVH4/BVH8. The builder's median fallback and depth cap keep the stack requirement small (`need` ≤ 18).
  - *Found:* the SIMD any-hit leaves (SSE BVH4 and the NEON shim, AVX2 BVH8, SVE BVH8/BVH16) accepted `t <= tmax` (closed), the scalar leaf and every closest-hit / GPU path `t < tmax` (half-open), so a blocker exactly at the light distance was occluded only on SIMD. Now half-open everywhere; robust/bitexact any-hit SIMD == scalar on every ray. (The closest-hit "hit/miss vs brute" on the coplanar scene are rays whose exact hit is at `t = tmax`, i.e. a miss under `[tmin, tmax)`; brute force's rounded `t` is one ulp below.)
  - *Degenerate triangles* (`Robust/Degenerate.lean`, any `RoundingModel`): MT computes `det = 0` exactly when `e1 = 0` or `e2 = 0` and its threshold `rel ≥ 1e-12 > 0` rejects it (`mt_rejects_degenerate`); Woop gets `det = 0` exactly when any two vertices coincide (`woop_det_ab/ac/bc`, from `mul_comm'` + `sub_antisymm` + `fl_idem`). They are kept by the builder because the spatial queries (closest point, kNN, region) do see them; for ray queries they never contribute.
  - *Found* (cdiff `degenerate` vectors, bit level): the scalar MT accepted NaN results as hits. A 0·∞ (infinite vertex or ray component, or overflow) gives `det = NaN`, and `uu < 0 || uu > 1`, `tt < tmin || tt >= tbest`, `-eps < det < eps` are all false for NaN, so `t = u = v = NaN` was returned (and poisoned `best_t`). The SIMD masks already rejected NaN. *Fix:* every scalar acceptance test is now NaN-rejecting (`!(uu >= 0 && uu <= 1)`, `!(vv >= 0 && uu + vv <= 1)`, `!(tt >= tmin && tt < tbest)`, `!(det <= -eps || det >= eps)`), identical for numbers, in the CPU kernel and the HIP, CUDA, hiprtc and Vulkan kernels (SPIR-V regenerated). `Ref.mtRej1–4` updated; `tri_mt_one_refines` re-proved (`EvE.lnot'` moved to `Eval.lean`). On 4000 random MT/Woop vectors with special values: 410 of 450 old MT "hits" were NaN/∞ results and are gone, no finite hit lost or gained; Woop unchanged. 4000/4000 degenerate vectors miss in C, MiniC and Ref. CUDA (RTX 3070, RTX 5060 Ti), HIP, hiprtc and Vulkan suites unchanged.
- **M13 (instance boxes):**
  - *Lean* (`BVH/TwoLevel.lean`): `aff_in_corner_box`: the affine image of every point of a box lies in any per-axis interval that contains the images of its 8 corners (each coordinate is affine; its minimum over the box is attained at the corner that picks, per input axis, the bound minimizing `L a j · p j`). With `hit_iff` this gives: an exact object-space hit inside the BLAS root box is a world-space hit inside the instance box built from the transformed corners.
  - *Found* (`tools/tlascheck.c`, new exact check, double): `tlas_transform_aabb` takes min/max of `fl(m0 c0 + m1 c1 + m2 c2 + m3)`; with cancellation that misses the exact corner by many ulps of the result. ~2% of the checks failed, by up to 47 ulp. *Fix* (under `LEAF_BOX_EXACT`): each transformed corner is widened by `4u · (Σ|products| + Σ|partial sums|)` (+tiny), i.e. 4× the bound proved in `xform_point_err`. After: 0 failures on 5 seeds; TLAS results unchanged (TLAS == brute bit for bit, 0 hit/miss vs fp64 world).
  - *Open:* the BLAS query runs on the rounded object-space ray `fl(W o) + t·fl(W d)`, not the exact one; the world point of a reported hit is within `|L_O|·(|e_o| + t |e_d|)` of the exact transformed box (grows with `t`), so containment of the world hit itself is not proved; measured: 0 hit/miss vs the fp64 world-space reference.
- **M14 (cubic Bézier curve intersector):** the three weaknesses `primhitcheck` measured had separate causes, all fixed (CPU kernel and the HIP/CUDA device port, regenerated from the C):
  - *Wrong surface model:* Newton solved a normal-plane circle sweep (foot `R·T = 0`, `|R⊥| = r`); a round curve is the union of balls, whose envelope is `F = R·C′ + r r′ = 0`, `G = |R| − r = 0`. Now that, plus the second-order condition `∂F/∂u < 0` (a minimum of the distance along u; a maximum lies inside the tube on the concave side of a bend). Residual 3e-4 → ~3e-6.
  - *Approximate fallback hits:* when Newton failed the cone seed (on the inflated bounding cone) was reported as the hit. Never now.
  - *Missed nearest:* nothing checked that Newton's root was this leaf's entry. Now the fast path is accepted only if converged, front-facing (`R·dir ≤ 0`) and inside the leaf's u-range; otherwise `tri_bez_leaf_trace` sphere-traces the exact leaf-tube distance (u restricted to the leaf, so end balls — where `F ≠ 0` and Newton cannot converge — are included) from the entry of a capsule that encloses the leaf tube, so the first contact is found, then polishes with Newton. Every leaf thus returns its own nearest contact below the current best, so the minimum over leaves is the nearest hit. A converged front contact elsewhere on the curve is kept as a candidate (it is a real surface point) and lowers `best` for the remaining search. Bugs found on the way, each by a specific failing ray: the sub-interval capsule used the distance to the chord LINE where the cull measures against the SEGMENT; a warm-started foot point slid to an interior local minimum and overestimated the distance near end balls (now the interval ends are also tried, and overshoot bisects back to the last point a full search verified outside).
  - *Reference fix:* `primhitcheck`'s tube distance refined only around its best sample and could pick the wrong basin (it reported a spurious miss / residual on a correct C hit); it now refines around every sampled local minimum. Bézier curves are checked with the strict criterion (no farther hit, residual ≤ 2e-4); "C nearer with a tiny residual" is no longer a failure (it is the patch tessellation missing a silhouette sliver).
  - *Result* (24 seeds × 2000 rays): 0 hit/miss, 0 farther-than-nearest, worst residual 3.8e-6. HIP GPU vs CPU agreement 99.930% → 99.975%. *Cost* (1 thread, 20k curves, 400k rays): closest 0.221 → 0.182 Mray/s, occluded 0.258 → 0.211 (−18%), after replacing the leaf distance's 28-step golden-section refinement by a bracketed Newton on φ′(u) (~5 evaluations); profile: the remaining leaf work is mostly sphere traces that end in a miss.
  - *Patch follow-up (M15 below).*
- **M15 (bicubic / NURBS patch intersector):**
  - *Reference first:* both "farther than the reference" rays of M14 were tessellation artifacts. Near a silhouette a 128×128 tessellation triangle pokes past the surface (no exact root exists), and at a grazing angle its `t` is off by more than the tolerance. `primhitcheck` now adjudicates every patch disagreement (farther hit, or a miss where the tessellation hits) with an exact double multi-start Newton over every patch the ray's box admits; only a confirmed nearer exact root counts as a C failure.
  - *Found* (24 seeds, and an old-vs-new diff on a 4000-patch scene judged by a tessellation + exact-polish oracle): (1) a real miss. The per-cell Newton (seeded at the cell centre, undamped) jumped from a corner cell to (0.71, −0.41) at a grazing root and converged outside the domain. (2) Several old false hits and farther hits.
  - *Fix* (CPU `tri_bezpatch_newton` / `tri_rbezpatch_newton` and drivers; HIP/CUDA `hp_patch_newton2<RAT>` / `hp_patch_fold<RAT>`): Newton is cell-bounded (steps ≤ one cell, iterate clamped to the cell ± half a cell, roots accepted only there) and returns 0 = failed, 1 = hit, 2 = converged to an in-domain root outside [tmin, best). A depth-4 cell whose box is hit is refined (to depth 7) when Newton fails. A root of the analytically extended surface just outside [0,1]² is NOT settled: a different in-domain root can sit next to it, which was a regression of the first version. After a hit, the cell is also refined when the surface folds against the ray inside it (n·dir changes sign at its corners/centre: a silhouette, the only way to have a nearer second root in a small cell), which was the second regression, a farther root picked in a folded cell.
  - *Result:* 24 seeds × 3 patch kinds: 0 confirmed C misses/farther hits (5 tessellation artifacts adjudicated away), worst residual 3.7e-5. On the 18 disputed rays of the 4000-patch scene the oracle rates old {ok 4, farther 2, miss 1, nearer 11} and new {ok 6, nearer 12} ("nearer" = C found a root nearer than the tessellation-seeded polish). HIP GPU vs CPU still 100% on all patch kinds. *Cost* (1 thread, 300k rays): bicubic 0.034 → 0.031 Mray/s (−9%), NURBS 0.071 → 0.059 (−17%).
