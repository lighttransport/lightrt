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

**Range-free binary32 error (resume-lean item 3, first step).** `FP/TotalErr.lean` proves `|rneR x − x| ≤ u |x| + 2⁻¹⁵⁰` for **every** `x` (subnormals, zero, and values beyond the finite range), from the per-rounding `q/2` bound and the quantum clamp at `2⁻¹⁴⁹`; `model_abs_err_total` exposes it for the model. `Robust/Total.lean` re-derives the whole Woop `t` chain with `u|x| + η` per rounding, without any `InRange` hypothesis: `num_err_total` (`≤ 4u(b0+b1+b2) + 8η`), `den_bounds_total` (`(1−u)²(Σe) − 4η ≤ D ≤ (1+u)²(Σe) + 4η`), `quot_bounds_total` (`|fl(N/D) − E/A| ≤ 40uM + 100η(1+M)/a0 + 4η` given `0 < a0 ≤ Σe` and `4η ≤ a0/2`), and `woop_t_err_total` / `woop_t_err_total_model` (the `_model` version discharges the per-operation hypotheses with `model_abs_err_total`). The price is the `η/a0` term, which degrades exactly when the projected area is tiny. A tighter quotient/vs assembly (`quot_bounds_total_tight`, `woop_t_err_total_tight`) reduces the constants to `29.1uM + 49η(1+M)/a0 + η`.

**Item 3, C-call-site instantiation.** `BVH/ExactPruneTotal.lean` proves the `InRange`-free replacement for the `EXACT_NEAREST` pruning theorem:
- `key_le_total`: the float node key is `≤ m − 30uM + 3η` (the total rounding model only adds `3η` to `key_le`);
- `woop_key_le_t_total_model`: for an accepted triangle whose *computed* dominant-axis depths lie in `[m, M]`, `fl(m − fl(2⁻¹⁹M)) ≤ t`, in **both** edge-sign classes (`hsign : (0 ≤ e0 ∧ 0 ≤ e1 ∧ 0 ≤ e2) ∨ (e0 ≤ 0 ∧ e1 ≤ 0 ∧ e2 ≤ 0)`), provided the extra slack fits: `49η(1+M)/a0 + 4η ≤ 0.9uM`. The negative class uses `woop_t_err_total_model_tight_neg` (numerator/denominator flip sign, same bound). For a real scene (`M` not subnormal) that is a projected area `a0 ≳ 50·2⁻¹²⁶(1+M)/M`, the same `1e-37`-scale regime as the dilation floor.

**Item 3, the `1e-37` floor.** `FP/TotalErr.fl_add_margin_ge` / `fl_sub_margin_le` prove that `tlas_dil_origins`' margin `mk = (m + 2⁻²³|o| + 1e-37)(1 + 2⁻²⁰)` is conservative: `o + m ≤ fl(o + fl mk)` and `fl(o − fl mk) ≤ o − m`. The `2⁻²³|o|` term covers the add with `o`, `1 + 2⁻²⁰` the double→float conversion plus that add, and `1e-37` the subnormal absolute error (`η = 2⁻¹⁵⁰`); the C's `mk < 1e38` guard covers overflow with the conservative infinite-origin box. The negative edge-sign class of `woop_key_le_t_total_model` is proved (`ExactPruneTotal.lean`); the range-free scalar slab-parameter error is proved (`Robust/SlabTotal.lean` `fpT_abs_err_total`); the MT `t` error bound is proved (`Robust/MTT.lean` `mt_t_fl_err_total_model`); `tlas_instance_margin` fp64 stays out of scope (`tlascheck` covers it); a range-free `slab_no_false_miss` is unprovable as stated (a tangent ray admits no absolute-error-dominating `K`); the conditional non-tangent form is now proved: `SlabTotal.slab_no_false_miss_total_of_floor` (parameters `κ ≤ |t_exact|` per slab endpoint, `κT ≤ t`, `θ` from `fpT_rel_of_floor`, and `1 + θ + η/κT ≤ (1 - θ)(1 - u)K`).

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
- `refit_contains`: the bottom-up refit (`tri_refit_propagate`) re-establishes containment for any new primitive bounds, `refit_prims` keeps the primitive lists, and `refit_traverse_eq_brute` re-derives traversal = brute force after a refit. This is the algorithm-level counterpart of `tri_leaf_prim_aabb(vf = 1)` (exact vertex min/max) plus the parent union; the C function's translation is not part of c2lean.
- `KBest` (`BVH/KBest.lean`): the multi-hit (`lrt_tri_intersect_n`) model. `ins`/`kbest` are the sorted insertion buffer and its fold (`kbest_sorted`, `kbest_length_le`, `kbest_mem`); `runN` mirrors the C loop (best-first stack, prune by the k-th buffer value, leaf fold) and `runN_sound` proves every reported hit is a real hit. `KInv`/`kbest_omitted` give the k-best-by-value specification: the k-th buffer value is nonincreasing under insertion (`prune_take_ins_le`), and every element omitted from `kbest k l` is at least the k-th kept value (`kbest_omitted`). The buffer step `stepN` mirrors the C leaf test (`t < prune_t`); `stepN_KInv`/`foldN_KInv` carry `KInv` through a leaf fold, and `runN_prune_le` proves the prune never increases along the traversal. `KInv_add_ge` extends the invariant with hits above the prune (the dropped-child case) and `mem_hitList` characterises the folded hits. `runN_KInv` threads `KInv` through the stack (skipped entries, leaf folds, and the node's `order`/`filter` permutation bookkeeping, with `filterMap_facts`/`den_wf` and the C1/C2 conditions), and `runN_complete` concludes: every hit of the root's primitives strictly below the returned k-th value is in the result (no false misses). With `runN_sound` this is the multi-hit completeness/soundness pair; the C's `max_hits == 0` early return is outside the model (k > 0).
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
    - Added `lightrt_hipew.{h,c}`, a minimal dlopen loader in the style of `lightrt_vkew` for the 21 HIP/hiprtc entry points the hiprtc path uses (no ROCm SDK at build time). It searches the versioned ROCm roots (`/opt/rocm/core-*/lib`, newest numeric version first) as well as `/opt/rocm/lib` and `LRT_HIP_LIB`/`LRT_HIPRTC_LIB`, so the hiprtc path works with Ubuntu's `rocm` metapackage layout; `make hip_rtc_test` is green again on gfx1201.
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
  - *Two-level* (`BVH/TwoLevel.lean`): `runT` models `lrt_tlas_intersect1` (leaf = per-instance BLAS query with `tmax = best`). `runT_eq_run`: if each BLAS query from `best` is the fold of its primitives (`blas_fold`, from `run_root`), the TLAS loop equals `run` over (instance, primitive) pairs; `tlas_root` then gives brute force over every reachable pair. `hit_iff`: over ℝ the affine world→object map preserves the ray parameter exactly (`HitsTriangleAt` in object space ⇔ in world space on the obj2world image). `xform_point_err` / `xform_vec_err`: rounding of `tlas_xform_point` / `tlas_xform_vec` in any `RoundingModel`, as `u·Σ|products| + u·Σ|partial sums|`. (The pair conservativity conditions and the world-space `t` error, open here, are closed in M16.)
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
  - *Degenerate triangles* (`Robust/Degenerate.lean`, any `RoundingModel`): MT computes `det = 0` exactly when `e1 = 0` or `e2 = 0` and its threshold `rel ≥ 1e-12 > 0` rejects it (`mt_rejects_degenerate`); Woop gets `det = 0` exactly when any two vertices coincide (`woop_det_ab/ac/bc`, from `mul_comm'` + `sub_antisymm` + `fl_idem`). They are kept by the builder because the spatial queries (closest point, kNN, region) do see them; for ray queries they never contribute. *Decision (resume-lean item 17):* keep them. Dropping them would silently change the point/kNN/region answers, and the ray path is already provably unaffected; the extra nodes are bounded by the median fallback and depth cap.
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
  - *First-contact core (resume-lean item 7):* `Geom/SphereTrace.lean` proves the 1D sphere-trace no-overshoot lemma for a 1-Lipschitz distance `f`: if `f root ≤ 0` and `y ≤ root`, then `y + f y ≤ root` (`stStep_le_root`), so every iterate stays left of a surface point (`stTrace_le_root`), and the trace is monotone where `f ≥ 0` (`stStep_ge`/`stTrace_mono`). The full model (the actual Bézier signed distance and the Newton refinement) remains.
  - *Result* (24 seeds × 2000 rays): 0 hit/miss, 0 farther-than-nearest, worst residual 3.8e-6. HIP GPU vs CPU agreement 99.930% → 99.975%. *Cost* (1 thread, 20k curves, 400k rays): closest 0.221 → 0.182 Mray/s, occluded 0.258 → 0.211 (−18%), after replacing the leaf distance's 28-step golden-section refinement by a bracketed Newton on φ′(u) (~5 evaluations); profile: the remaining leaf work is mostly sphere traces that end in a miss. Any-hit (`lrt_tri_occluded1`) now passes `anyhit` down to the leaf solve, which accepts the first converged, residual-verified Newton contact in range (front or back, any u) and the sweeps stop at the first hit: occluded 0.258 → 0.304 Mray/s (+18% over the pre-rewrite sweep). `primhitcheck` checks any-hit against the exact reference for every tube/point kind (`occ-bad`). *Decision (resume-lean item 16):* accept the closest-hit cost. The exact solve removed false hits (one bicubic hit 0.17 off any surface); the remaining time is conservative sphere traces that end in a miss. The next candidate is a cheaper miss-side bound (a tighter interval or an early AABB reject inside the trace), not a return to the golden-section refinement.
  - *Patch follow-up (M15 below).*
- **M15 (bicubic / NURBS patch intersector):**
  - *Reference first:* both "farther than the reference" rays of M14 were tessellation artifacts. Near a silhouette a 128×128 tessellation triangle pokes past the surface (no exact root exists), and at a grazing angle its `t` is off by more than the tolerance. `primhitcheck` now adjudicates every patch disagreement (farther hit, or a miss where the tessellation hits) with an exact double multi-start Newton over every patch the ray's box admits; only a confirmed nearer exact root counts as a C failure.
  - *Found* (24 seeds, and an old-vs-new diff on a 4000-patch scene judged by a tessellation + exact-polish oracle): (1) a real miss. The per-cell Newton (seeded at the cell centre, undamped) jumped from a corner cell to (0.71, −0.41) at a grazing root and converged outside the domain. (2) Several old false hits and farther hits.
  - *Fix* (CPU `tri_bezpatch_newton` / `tri_rbezpatch_newton` and drivers; HIP/CUDA `hp_patch_newton2<RAT>` / `hp_patch_fold<RAT>`): Newton is cell-bounded (steps ≤ one cell, iterate clamped to the cell ± half a cell, roots accepted only there) and returns 0 = failed, 1 = hit, 2 = converged to an in-domain root outside [tmin, best). A depth-4 cell whose box is hit is refined (to depth 7) when Newton fails. A root of the analytically extended surface just outside [0,1]² is NOT settled: a different in-domain root can sit next to it, which was a regression of the first version. After a hit, the cell is also refined when the surface folds against the ray inside it (n·dir changes sign at its corners/centre: a silhouette, the only way to have a nearer second root in a small cell), which was the second regression, a farther root picked in a folded cell.
  - *Result:* 24 seeds × 3 patch kinds: 0 confirmed C misses/farther hits (5 tessellation artifacts adjudicated away), worst residual 3.7e-5. On the 18 disputed rays of the 4000-patch scene the oracle rates old {ok 4, farther 2, miss 1, nearer 11} and new {ok 6, nearer 12} ("nearer" = C found a root nearer than the tessellation-seeded polish). HIP GPU vs CPU still 100% on all patch kinds. *Cost* (1 thread, 300k rays): bicubic 0.034 → 0.031 Mray/s (−9%), NURBS 0.071 → 0.059 (−17%); then *more than recovered*: the profile showed ~55% of patch time in re-deriving every cell's control net from the root net (`tri_bezpatch_subpatch` / `tri_rbezpatch_subpatch`: per-row/column `subcurve` = two de Casteljau splits each). The CPU drivers now carry each cell's net on the stack and split it once at the midpoint (`tri_patch_split4`), with a 16u widening of the cull box for the accumulated split rounding (Newton still uses the original net and global (u,v)). Bicubic 0.031 → 0.117 Mray/s (3.5× the original), NURBS 0.059 → 0.088 (+24% over the original); results unchanged (24-seed strict check clean, oracle unchanged, GPU vs CPU 100%). The GPU kernels keep the per-cell re-derivation (carrying 48–64 floats per stack entry would cost KB of per-thread stack).
- **M16 (defaults, closest-hit stack bound, TLAS pair conservativity, world `t` error):**
  - *Defaults:* `LRT_TRI_BITEXACT` is on by default (opt out: `-DLRT_TRI_NO_BITEXACT`). Cost, 1 thread, 131k-triangle bumpy sphere, 400k rays: −1% to −3% (within noise). `WATERTIGHT_TRI` and `EXACT_NEAREST` stay opt-in for now. Measured on the same scene, `WATERTIGHT_TRI` traces 1.5–2.4× slower (the leaf is scalar Woop), `EXACT_NEAREST` 2.2× slower on BVH8 primary rays, and all three together 4–5× slower on closest-hit. They become defaults once a SIMD watertight leaf and a pruning `EXACT_NEAREST` exist.
  - *Closest-hit stack* (`BVH/AnyHit.lean`): `runB` models `tri_intersect_scalar`'s `if (sp + nhit > TRI_STACK_SIZE) return 0`. `runB_eq`: under the same `need` invariant as any-hit, the check never fires and `runB = run`. `runB_root`: if `needRef root ≤ TRI_STACK_SIZE`, the bounded C loop returns `run_root`'s brute-force answer. `bvhcheck.py` already checks `need` on real trees (max 18 ≤ 1024).
  - *TLAS pair conservativity* (`BVH/TwoLevel.lean`): the BLAS traces the rounded object ray `õ + s d̃`. `world_near_obj` maps that ray's point back with the stored `obj2world` `A`, not the exact inverse of the float `world2obj` `W`. Its distance to the world ray point `o + s d` is at most `ρ|o + s d|₁ + σ + Σ_j |A_kj| (e_o + |s| e_d)_j`. Here `ρ, σ` bound the residual of `A ∘ W − id` (`hres_of_entries`, from the entries of `L_A L_W − I` and `L_A c_W + c_A`). `xform_point_err_simple` / `xform_vec_err_simple` give `e ≤ 5u Σ|products|`. Together the margin is `α(|o|₁ + |s||d|₁) + β` per instance. `world_in_dilated_box`: if the BLAS point lies in the BLAS box, the world point lies in the instance box dilated by that margin (with `aff_in_corner_box`). `s_bound`: before the first hit `best = tmax`, so the per-ray margin is capped by `|s| ≤ (|o_k| + R + a)/(|d_k| − b)` on the dominant axis, R being the root box half-extent. The pair conditions C1/C2 of `tlas_root` thus reduce to the conservative slab test on the dilated box, with the BLAS's own slack.
  - *C* (under `LEAF_BOX_EXACT`, default): `tlas_instance_margin` computes α, β per instance in double with explicit rounding terms. β widens the instance box outward, and the TLAS keeps `max α` and the root half-extent. `lrt_tlas_intersect1` / `lrt_tlas_occluded1` test each node against the dilated box. To keep the cost low, the dilation shifts the ray origin rather than the faces: `oL = fl(o + m_f) ≥ o + m` and `oH ≤ o − m`. Then `(lo − oL)·sinv` is the usual robust slab arithmetic against the plane `lo − (oL − o)`. The shifted origins are recomputed only when `best` changes. Cost (2000 instances of small BLASes, 300k incoherent rays, 1 thread): closest −4%, occluded −4%. Hits are identical. A first version that dilated each face in double with `nextafterf` was 2.7× slower.
  - *Validation* (`tools/tlascheck.c`, in `make formal`): for every brute-force (instance, BLAS) hit it checks `|o + s d − A(õ + s d̃)| ≤ α(|o|₁ + |s||d|₁) + β` in long double, and also `|s| ≤ s_bound`. 4 seeds, ~1700 pair hits each: 0 over the bound, worst use of the bound 0.22, 0 over `s_bound`. TLAS == brute force and any-hit == brute force, unchanged; 0 hit/miss against the fp64 world reference.
  - *World `t` error* (`plane_t_perturb`, `plane_t_perturb_abs`): the mapped-back BLAS ray `A õ + s L_A d̃` meets the world triangle `A T` at the BLAS's own parameter (`hit_iff`). On the triangle's plane `n·x = h` it differs from the exact world ray by `t₂ − t₁ = (n·(o − o') + t₁ n·(d − d'))/(n·d')`. That gives `|Δt| ≤ Σ_j |n_j| (|δo_j| + |t₁||δd_j|) / |n·d'|`, with `δo, δd` from `world_near_obj`. The reported `t` adds the BLAS kernel's own `t` error. Grazing rays (`n·d' → 0`) are unbounded, as for any ray/plane solve. Measured max relative `t` error against fp64 world: 2.5e-5.
  - *World hit point, conditioned on incidence* (`TwoLevel.tlas_hit_point_in_box_incidence`, 0 sorry): `plane_t_incidence` bounds `|s − t*|` by `planePerturb(n,o,d,o',d',t*)/c` when `0 < c ≤ |n⬝ᵥd'|`; `hit_point_in_dilated_box` turns a parameter error `δ` into `δ|dⱼ|` per axis; the composed theorem places the reported point `o + t·d` in the instance box (already dilated by the `world_in_dilated_box` transform margin `m`) dilated by `mⱼ + (planePerturb/c + ε)|dⱼ|`, with `ε` the BLAS's own `t` error (`ExactPrune.woop_t_err`). Grazing rays (`|n⬝ᵥd'| → 0`) are outside the bound, as any ray/plane solve must be. The closest-hit result was already covered: C1/C2 use the BLAS's exact parameter, as in the single-level `run_cover`.

  - *GPU patch drivers, negative result:* porting the CPU's stack-carried cell nets (`tri_patch_split4`) to `hp_bezpatch_one` / `hp_rbez_one` kept agreement at 100% but was about 2× slower on an RX 9070 XT (`bench_hip --normals`, 20k bicubic patches): primary 6.4 → 3.8 Mray/s, incoherent 0.7 → 0.3. 32 stack entries × 192–256 B per thread spill to local memory, which costs more than recomputing each cell's net from the root in registers. The GPU keeps `hp_subpatch`. *Decision (resume-lean item 15):* keep `hp_subpatch`; a shared-memory cell net per warp is the only plausible retry, and it is not worth the complexity without a measured win.
- **M17 (SIMD watertight leaf):**
  - *Per-lane model (resume-lean item 4, first step):* `C/Proofs/SimdLanes.lean` models the SIMD watertight leaf lane-wise. `vmul`/`vadd`/`vsub`/`vdiv`/`vlt` are the packed binary32 operations; `vWoopK` mirrors `Ref.woopK` expression for expression (same order, no FMA, no reassociation), so `vWoopK_lane` proves lane `i` is exactly the scalar reference on lane `i`'s vertices (definitional). On top of that, `bstep`/`blockBest` mirror the C driver's fold (`NO_HIT` slots skipped, strict `t < best`), with `blockBest_sound` (a changed block result is a real lane hit with the reported `t,u,v` and id), `blockBest_all_skip` (all-padding block leaves the caller's best), and `blockBest_woop` (the reported prim id belongs to a lane whose scalar `woop` returns the reported `(t,u,v)`). The model *assumes* the ISA's packed ops are the binary32 lane ops of `FP.Binary32`; mapping the intrinsics to that (and the C to the intrinsics) remains the trust gap, covered exhaustively for this kernel by `wtcheck`'s leaf fuzz (400k blocks / 2.7M lanes, bit-identical incl. SVE 8/16).
  - *Leaf:* `tri_woop4_block` (SSE, BVH4) and `tri_woop8_block` (AVX2, BVH8) are generated from one template. They perform `tri_woop_one`'s operations in its order, with no FMA and the same association. Comparisons keep the scalar NaN behaviour: ordered `<`, `>`, `>=`, and an unordered `!=` for the `det == 0` reject. The closest lane is the minimum `t`, lowest lane on ties, which is what the scalar lane loop with a strict `t < best` update returns. So every lane equals `tri_woop_one` bit for bit, and `tri_woop_one_refines` / `woop_no_gap_bits` carry over unchanged. Exact vertices sit in a self-contained SoA side block `wblk` (`10·W` words per leaf block: v0, v1, v2, then the prim ids). It is derived from `wverts` by `tri_build_wblk` after build, load and refit, and prefetched in place of the edge block.
  - *Dispatch:* `lrt_tri_intersect1` / `occluded1` now run the SIMD kernels when the leaf exists (`TRI_WBLK_SIMD`: BVH4 on SSE, BVH4/BVH8 on AVX2, not quantized nodes). The interleaved `intersect1N` pipeline is used only for BVH4 closest-hit; elsewhere it measured slower than per-ray with this leaf. *Found:* the Ray4/Ray8 packet kernels (`lrt_tri_intersect4/8`, `occluded4/8`, and the coherent `intersect1N` that calls them) ran Möller–Trumbore even in watertight builds. They now fall back per ray when the scene carries exact vertices. BVH8Q builds keep the scalar watertight kernels; the NEON shim dispatches the SIMD Woop leaf for BVH4 (validated under `qemu-aarch64`: `wtcheck` leaf 400k blocks / 1.37M lanes bit-identical, traversal/batch/save-load/refit 0 differences, `c_tri_seam_test_wt` 0 leaks).
  - *SVE watertight leaves (resume-lean item 10):* `tri_woop_sve_setup`/`tri_woop_sve_core` implement the fp32 Woop test with SVE intrinsics on the exact-vertex `wblk` (separate mul/sub, no FMA, scalar axis/shear), one kernel for width 8 (BVH8) and 16 (BVH16), plus the half-open any-hit variant. `TRI_WBLK_SIMD` now includes SVE layouts 8/16, and the four SVE traversals (`intersect`/`occluded` × BVH8/BVH16) dispatch the Woop leaf when `s->wblk` is set; the edge-format MT SVE leaves are unchanged. Validation under `qemu-aarch64 -cpu max` (`-march=armv8.2-a+sve`): new `leaf_fuzz_sve(8/16)` 400k blocks / 2.74M lanes bit-identical to `tri_woop_one` (including any-hit), layout-8 traversal/batch/save-load/refit 0 differences, `c_tri_seam_test_wt` 0 leaks and the C tri test passes. The 16-wide wblk kernel is leaf-validated; the scalar traversal reference does not support layout 16, so the traversal-level bit check is BVH8 only (pre-existing scalar limitation). NEON (no SVE) and x86 builds are unchanged and pass; the SVE code is `#if LRT_TRI_HAS_SVE` only.
  - *Validation* (`tools/wtcheck.c`, in `make formal`):
    - Leaf fuzz: 1.2M blocks, a third with special values (±0, ±inf, NaN, subnormal, 1e30) and a third with rays through vertices/edges and lanes sharing edges. Every lane and the chosen hit equal the scalar test: 0 differences.
    - Traversal: BVH4/BVH8 × LBVH/SAH × soup / shared-edge heightfield / coplanar, 54k rays. Dispatched `intersect1` / `occluded1` == `tri_intersect_scalar` / `tri_occluded_scalar` bit for bit (t, u, v, prim).
    - Also checked: `intersect1N` / `occluded1N` (both hints), `intersect4`, and the scene after save → load and after refit: 0 differences.
    - SSE-only build: same, 0 differences.
    - `c_tri_seam_test_wt`: 0 leaks. The full C suite passes when built watertight.
  - *Cost* (1 thread, 131k-tri bumpy sphere, 400k rays), against the default MT build. Before this change the watertight build was 1.5–2.4× slower everywhere.

    | | BVH4 | BVH8 |
    |---|---|---|
    | Primary | +24% | −3% |
    | Incoherent | −9% | +3% |
    | Shadow | −8% | −2% |

    Memory is now the obstacle to making it the default: exact vertices `wverts` (36 B/tri) plus `wblk` (40 B per lane slot) add 145–155% to nodes + leaves on this mesh. The MT edge blocks are still kept, for the GPU upload, shading reconstruction and serialization. Dropping one copy (leaf blocks storing exact vertices, or `wverts` reconstructed from `wblk`) is the next step before a default switch.
- **M18 (one exact-vertex copy):** watertight scenes kept the exact vertices twice: prim-ordered `wverts` (36 B/tri) and the SoA `wblk`. `wverts` is gone and `wblk` is the only copy.
  - `tri_build_wblk(s, src, n)` fills it from the caller's vertices at build (a temporary prim-ordered array, freed right after), from the LRTS aux vertices at load, and from the new vertices at refit.
  - The scalar lane test `tri_isect_lane_s` reads the lane's vertices from `wblk` by block index. That covers BVH8Q and the quantized-node kernels, and NEON/SVE/scalar targets now build `wblk` too.
  - The serializer regenerates the prim-ordered aux array from `wblk` (`tri_wblk_to_prims`). The file format is unchanged, so the HIP/CUDA/Vulkan watertight kernels still receive `d_wverts` from the blob.
  - *Independent check:* `wtcheck` previously compared SIMD against a scalar oracle that now reads the same `wblk`. So it also checks that every reported hit equals `tri_woop_one` on the caller's input vertices of that prim, bit for bit, after build, load and refit: 0 differences. All `wtcheck` sections pass, also under ASan/UBSan. `c_tri_seam_test_wt` has 0 leaks, the full C suite passes built watertight, and `c_tri_parallel_test_rb` passes.
  - *Memory:* the overhead over nodes + leaves on the 131k-tri mesh drops from +145–155% to +78–84%. *Speed* is unchanged from M17 relative to the default build: BVH4 +23 / −8 / −5%, BVH8 −3 / +3 / −3% (primary / incoherent / shadow). The rest of the overhead is `wblk` sitting beside the MT edge blocks. The SIMD traversal no longer reads those blocks, but they remain the source for the GPU upload, `lrt_tri_get_verts` and serialization. Dropping them would mean a watertight-specific leaf format through the GPU and LRTS paths.
- **M19 (watertight scenes without edge blocks):** for BVH4/BVH8 watertight scenes the leaf blocks themselves store the exact `v0 v1 v2`, replacing `v0 e1 e2`. The size is the same (`10·W` words), so `wblk` aliases `s->blocks` (`tri_vfmt`). Watertight scenes now take the same memory as default ones: on the 131k-tri mesh BVH4 is 7.0 MB in both, BVH8 6.7 MB.
  - *Edge readers:* the build stores `e1 = fl(v1 − v0)`, so readers that still want edges recompute them bit-identically. That is the fp64 path `tri_block_isect_hp` for non-vertex-format blocks; on the vertex format it now runs a double Woop leaf (`tri_woop_one_hp`) on the exact vertices, replacing the double Möller–Trumbore. The fp64 slab also mirrors the robust `+∞` reciprocal and inflation, so its node tests match the fp32 ones. `lrt_tri_get_verts` returns the exact vertices. *Found:* it used to return `v0 + e1` in watertight scenes too, which differs from the input on 544 of the checked prims. `tri_leaf_verts` / `tri_leaf_prim_aabb` (node boxes under `LEAF_BOX_EXACT`, region queries, refit) take the exact vertices, so node boxes now contain the triangles the watertight test actually tests, rather than the MT triangle `v0 + e`. The SSE/AVX2/SVE MT edge leaves are never dispatched for these scenes. `wtcheck` compares every entry point against the scalar oracle and against `tri_woop_one` on the input vertices, which would show a misroute.
  - *Format:* LRTS header flag bit 2 (value 4) marks vertex-format leaves. A build without `WATERTIGHT_TRI` rejects such a file instead of misreading it. Vertex-format files load directly, including when mmapped, read-only. Legacy watertight files (edge blocks + aux vertices) are converted on load, or keep a separate `wblk` when mmapped. BVH16 also keeps a separate `wblk`. The aux vertex array is still written, so the HIP/CUDA/Vulkan watertight kernels are unchanged.
  - *Validation* (`wtcheck`, in `make formal`): all sections from M17/M18, plus readers. `get_verts` equals the input exactly. `intersect_n` agrees with `intersect1` on hit/miss on every ray. Its first `t` differs on 2468 of 36000 rays, by at most 11 ulp, all on the shared-edge and coplanar scenes. That is the node-pruning slack of the two searches (`Flat.run_approx`): each prunes by a rounded `tnear` against its own running bound, so either can miss the true nearest by a few ulp, or pick another prim at a tie. It is the same count with the previous library. The ≤4-ulp figure from M7 was measured on ordinary scenes; in-plane rays on overlapping coplanar triangles reach 11. The fp64 path uses a watertight Woop leaf in double on vertex-format blocks (MT otherwise). It still differs from the fp32 hit/miss on ~4% of the vertex- and edge-aimed rays (1456 of 36000, down from 1562). The cause is the test construction, not the leaf: `ray.dir = p − org` is rounded in fp32, so the exact real fp64 ray can pass one fp32 ulp to the side of the vertex and genuinely miss, while the fp32 arithmetic lands inside. A caller supplying double rays (`lrt_ray_hp` is double) gets the watertight double leaf. Reported, not failed; the fp64 leaf is scalar on SVE (the 8-wide double MT loop is bypassed for vertex-format blocks). SSE-only and ASan/UBSan runs pass, `c_tri_seam_test_wt` has 0 leaks, and the full C suite built watertight passes.
  - *Speed* vs the default build (1 thread, 131k tris, load ~4 while measuring): BVH4 about +20% primary, −8 to −10% incoherent, −10% shadow; BVH8 0% primary, +1–2% incoherent, about −10% shadow.
- **M20 (shadow retune; `WATERTIGHT_TRI` on by default):**
  - *Retune:* measured best of 9 on a quiet machine (load < 0.5). Under load the earlier "−10% shadow" was mostly noise: the real loss was BVH4 −4%, BVH8 −1%. Two changes, neither altering any result:
    - The Woop leaf returns before the `t` divide when no lane passes the edge-sign / det test (≈ +3% everywhere).
    - The per-ray Woop setup (three divides) is lazy: done at the first leaf visit. Rays that reach no leaf skip it. This applies to the single-ray kernels and all four pipelines.
    - The BVH4 shadow interleaved pipeline was re-measured with the Woop leaf and stays slower than per-ray (7.7 vs 7.9 Mray/s), so watertight any-hit batches remain per ray.
  - *Result* (1 thread, 131k tris, 400k rays), watertight vs the MT build:

    | | BVH4 | BVH8 |
    |---|---|---|
    | Primary | +20% | 0% |
    | Incoherent | −2% | +9% |
    | Shadow | +3% | +14% |

    Memory is the same (M19).
  - *Default:* `LRT_TRI_WATERTIGHT_TRI` is now set in `lightrt_c_tri.h`; opt out with `-DLRT_TRI_NO_WATERTIGHT_TRI`. The Lean mirror in `bvhcheck.py` models the Möller–Trumbore leaf, so its variants, `cdiff`'s legacy build, c2lean's `Gen`, and the "report" builds of the seam and parallel-ray tests opt out explicitly. The default watertight leaf is validated by `wtcheck.c` (bit-identical to `tri_woop_one`, which `tri_woop_one_refines` / `woop_no_gap_bits` cover) and by `c_tri_seam_test_wt` (0 leaks). Full C suite, quad/tetra, surfaces, HIP (RX 9070 XT), Vulkan and CUDA (RTX 3070, RTX 5060 Ti) pass with the new default.
  - *Any-hit pipeline heuristic, benchmarked and fixed* (`make bench_occ`, `benchmark_c/bench_occ.c`): on the 131k-triangle scene the batched `occluded1N` interleaved pipeline is slower than per-ray `occluded1` (7.7 vs 8.5 Mray/s), as noted in M17. A larger, cache-cold sweep (1M incoherent shadow rays, BVH8, 0 differences in hit bits; best of 9, alternated) shows the crossover: per-ray wins below ~245k triangles (−11 to −14%) and the interleaved pipeline wins above ~500k (+7 to +16%). The BVH8 AUTO hint now uses per-ray below 300k triangles and the interleaved pipeline above; explicit `LRT_TRI_BATCH_INCOHERENT` always interleaves and `_COHERENT` always runs per-ray. Re-measured AUTO: 180-grid (65k tris) +0.4% vs per-ray (was −11 to −14%), 700-grid (980k tris) +14.8% vs per-ray. Watertight scenes always take the per-ray path (`wblk`), so this affects only non-watertight builds.
- **M21 (exact nearest with pruning; slab false misses at vertices):**
  - *Key* (`BVH/ExactPrune.lean`, 0 sorry): the Woop leaf's `t = fl(N/D)` is a weighted mean of the vertex depths `z_i = fl(sz · fl(v_i[kz] − o[kz]))` along the dominant axis, with all edge values of one sign. `woop_t_lower` / `woop_t_lower_neg` prove `t ≥ m − 16u M` for `m ≤ z_i`, `|z_i| ≤ M`, `|m| ≤ M`. `depth_bounds` gives such `m, M` from the box's two `kz` faces, because rounding is monotone. `key_le` shows the float key `fl(m − fl(2⁻¹⁹ M))` is below that bound. Together (`woop_key_le_t`), pushing `max(key, tmin)` satisfies `Flat.run_root`'s C2 for every accepted triangle whose exact vertices lie in the node box. The box test against the fixed `tmax` is C1, as in `run_exact`. So the traversal returns exactly the brute-force nearest `t` while still pruning by `best`.
  - *Tighter key attempt (resume-lean item 12), negative:* adding the child box's slab entry to the key (`max(old, tnear − 2⁻²⁰|tnear| − 2⁻¹⁹M)`, suggested by the `slab_no_false_miss` relative bound and the Woop `t` error) gave no measurable gain: on 131k triangles / 400k incoherent rays the `EXACT_NEAREST` rate stayed at 0.5–0.6 vs 0.7 Mray/s for the default build (was 0.5). The slab entry is the box entry, which for incoherent rays is not much tighter than the dominant-axis box extent at leaf scale; a useful tighter key would need a leaf-level bound, not a node-slab bound. Reverted (the exact-nearest pruning gap remains the known −24%/−12% cost).
  - *C refinement of the key* (`C/Proofs/ExnKeyRefines.lean`, 0 sorry): `c2lean.py` gained a `GenExn` configuration (`-DLRT_TRI_EXACT_NEAREST`) that translates `tri_exn_key` (and maps `fabsf` to `copysignf(x, +1)`). `tri_exn_key_refines` proves the compiled scalar function returns exactly `exnKey` — the bit-level `fl(m − fl(2⁻¹⁹ M))` with `m = fmin(z_lo, z_hi)`, `M = fmax(|z_lo|, |z_hi|)` (and `tmin` when `on == 0`) — closing the C-to-Lean gap for the key computation itself.
  - *Two-sided `t` error* (`ExactPrune.woop_t_err`, `woop_t_err_neg`, 0 sorry): the same numerator/denominator analysis gives `|t − (Σ eᵢzᵢ)/(Σ eᵢ)| ≤ 16u M` for both edge-sign classes; since the exact ratio is a convex combination of the depths, `woop_t_upper` (`t ≤ Z + 16u M` when all `zᵢ ≤ Z`, both signs) follows. `quot_err` holds the generic quotient algebra. This complements `woop_t_lower` (`t ≥ m − 16u M`) and is the C-level `t` error needed by the TLAS world-hit bound.
  - *C* (`-DLRT_TRI_EXACT_NEAREST`, watertight scenes with `wbox_exact`, i.e. node boxes that are the exact min/max of the exact vertices): `tri_exn_key` in the scalar, SSE BVH4 and AVX2 BVH8 closest-hit kernels. `wbox_exact` is set at build (not SBVH, not quantized nodes) and refit, and saved as LRTS flag 8. Other scenes (MT leaves, SBVH, quantized nodes) keep the unpruned rule. *Found:* `intersect1N`'s interleaved pipelines and the Ray4/Ray8 packets ignored `EXACT_NEAREST` and pruned by `best`; under the flag they now run the per-ray kernels.
  - *Found while validating — slab false misses on vertex-aimed rays:* comparing every ray against brute force (`tri_woop_one` over all input triangles) showed 26–27 rays aimed at shared vertices of the heightfield missing entirely, in the default build since watertight became the default (and in the scalar kernel). The node slab test rejects a box the ray touches exactly at an edge or corner. This is the false miss proved to exist in `Robust/SlabMissReal.lean`; random rays almost never hit it, so `bvhcheck` never flagged it.
  - *Fix:* `LRT_TRI_SLAB_INFLATE` (far value `× (1 + 10u)`, `Robust/Slab.lean` `ize_constant_sufficient`) is now on by default with `SLAB_ROBUST` (opt out: `-DLRT_TRI_NO_SLAB_INFLATE`). It is mirrored in every CPU node slab (scalar, SSE, AVX2 incl. BVH8Q / fp8 / q4 nodes, SVE, the Ray4 packet, the TLAS) and in the HIP, CUDA and hiprtc kernels and the Vulkan shader (specialization constant 2 is now a bit mask: bit 1 = inflate; SPIR-V regenerated). `Ref.slabRobust` now includes the inflation, and `tri_slab_scalar_robust_refines` and `slabRobust_parallel_hit` re-check against it.
  - *Result* (`wtcheck`, both builds in `make formal`):
    - Default: 0 misses against brute force (was 26), with `t` within 13 ulp (pruning slack); misses now fail the check.
    - `EXACT_NEAREST`: `t` equal to brute force bit for bit on all 36000 rays.
    - All earlier sections still pass. The full C suite also passes built with `EXACT_NEAREST`. Cost of the inflation: 1–3%.
  - *Cost of the pruning key* (1 thread, 131k tris, best of 9; load 3–4):

    | | Default | New `EXACT_NEAREST` | Old `EXACT_NEAREST` |
    |---|---|---|---|
    | BVH4 primary | 6.47 | 4.91 (−24%) | 2.95 (−55%) |
    | BVH8 primary | 6.89 | 6.05 (−12%) | 3.42 (−52%) |
    | BVH4 incoherent | 5.15 | 3.19 | 5.16 |
    | BVH8 incoherent | 5.58 | 4.66 (−17%) | 3.75 |

    The old BVH4 incoherent figure came from the non-exact pipeline. The key uses only the dominant-axis extent of the box, so diagonal rays prune less. `EXACT_NEAREST` stays opt-in.


- **M22 (formalization tail, items 3/4/7):**
  - *Item 3, negative edge-sign class and the C-call-site instantiation:* `Robust/Total.lean` adds `woop_t_err_total_model_tight_neg` (numerator/denominator flip sign, same bound); `BVH/ExactPruneTotal.woop_key_le_t_total_model` now takes `hsign : (0 ≤ eᵢ) ∨ (eᵢ ≤ 0)` and `a0 ≤ |e0+e1+e2|`, dispatching both classes. `ExactPrune.woop_key_le_t` (InRange) is fully replaced by the range-free version for the C `EXACT_NEAREST` call site.
  - *Item 3, the slab chain (3a):* `Robust/SlabTotal.lean` proves
    `fpT_abs_err_total`: for the binary32 model, the scalar slab parameter
    `fpT = fl(fl(x−o)·fl(1/d))` satisfies `|fpT − (x−o)/d| ≤ 4u|(x−o)/d| + 4(1+u)(|x−o| + 1/|d|)η + 2(1+u)η² + η`
    with **no** `InRange` hypothesis (η = 2⁻¹⁵⁰). The `η·(|q| + 1/|d|)` slack is
    the same subnormal regime as the Woop `t` bound; the `tangent ray`
    degenerate case admits no absolute-error-dominating `K`, so a range-free
    `slab_no_false_miss` needs a non-degeneracy floor and is not attempted.
    `slab_t_err_fma` and the FMA-order slab keep their `InRange` forms.
  - *Item 3c (`tlas_instance_margin`'s fp64 `ρ/σ`):* **not proved**, covered empirically by `tlascheck`; recorded as out of scope. The `1e-37` dilation floor itself is proved (`FP/TotalErr.fl_add_margin_ge` / `fl_sub_margin_le`, matching the C's `mk = (m + 2⁻²³|o| + 1e-37)(1 + 2⁻²⁰)` and the `mk < 1e38` guard).
  - *Item 3b (range-free Möller–Trumbore `t` error bound): deferred.* `BVH/TwoLevel.tlas_hit_point_in_box_incidence` takes the BLAS's own `t` error `ε`; the instantiation is `ExactPrune.woop_t_err`, i.e. the watertight Woop leaf only. The MT leaf has no error bound (MT is not watertight, `mt_not_watertight`, so a bound would buy no conservativity); MT scenes are **not** supported by the world-hit incidence theorem. The C's `tlas_dil_origins` dilation carries only the transform margin (`α = (ρ + u5·pmax)(1+2⁻⁴⁰)` plus the `1e-37` subnormal floor) — no `ε|d|` term; a C change to add it was not taken.
  - *Item 4 (SIMD watertight leaf):* per-lane model (`SimdLanes.lean`) done; the ISA/intrinsics semantics gap is a **documented model boundary** (packed ops assumed to be the `FP.Binary32` lane ops), not an axiom. The MT packet path (`tri_packet4_tri` via `tri_isect_det_parallel4`, `LRT_TRI_BITEXACT` scalar order/predicate) is **not exercised by `wtcheck`** (it builds WATERTIGHT_TRI, packets fall back to per-ray). New `formal/tools/mtcheck.c` fuzzes `tri_packet4_tri` vs the scalar per-lane `tri_isect_lane` (fabricated bw=4 block, qNaN/inf/subnormal/special inputs, vertex-aimed mode): 2M blocks / 8M lanes / 642k hits, **0 differences** (added to `make formal`, 500k iterations); this is the empirical check that BITEXACT MT packet == scalar MT. The same reasoning applies to `tri_mt4_decoded_sse` (same det predicate + arithmetic order), not separately fuzzed.
  - *Item 7 (sphere trace and Newton):* `Geom/SphereTrace.lean` proves the 1D no-overshoot/monotonicity core; the distance-to-point 1-Lipschitz atom; and `newton_step_quadratic` (one Newton step squares the error under a Lipschitz Jacobian and bounded inverse). The Bézier *curve* and *patch* signed-distance models are not yet formalized; patch/NURBS remain adjudicated by `primhitcheck` (item 16 decision).
  - *Decisions (mirroring resume-lean.md):* 3b deferred; 3c out of scope; item 4 ISA gap = model boundary; item 7 full-2D Newton is the next formalization item (7b-1 `Geom/Newton2D.lean`, 7b-2 `Geom/BezNewton.lean`), then the 3D `Metric.infDist` no-overshoot (`Geom/SphereTrace3.lean`).
- **M22 (addendum):** the full 2D Newton quadratic contraction (resume-lean
  item 7b-1) is proved as `Geom/Newton2D.lean`: general `C2`
  `F : ℝ² → ℝ²` with second-derivative bound `K`, `|det J(x)| ≥ δ > 0` (the C's
  own acceptance guard), `K·|e|₁ ≤ B`, `|partials| ≤ B` at both points — then
  one Newton step `x' = x - J(x)⁻¹F(x)` has `|x'_i - x*_i| ≤ (10BK/δ)·|e|₁²`
  (first component) and `≤ (8BK·|e|₁² + 2B²|e|)/δ` (second; the `2B²E` term is
  the same-point partial-product contribution, unavoidable without more
  hypotheses). The file also has `residual_bound` (`|R| ≤ 3K‖e‖₁²`) and
  `pd1/pd2_diff_bound` (`|Δpartials| ≤ K‖e‖₁`). `tri_bez_newton`
  instantiation is the remaining step (7b-2).
- **M22 (addendum 2):** 7b-2 (Bézier specialization of the 2D Newton) is
  **deferred**, not attempted this pass. The remaining work is large and
  specific: (i) polynomial differentiability bounds for the stationarity
  `f = ⟨R, C′⟩ + r·r′` (tractable via Mathlib's polynomial/`deriv` API) and
  (ii) for `g(u, t) = |R| - r(u)`, `R = o + t·d − C(u)` — `g` is not
  polynomial (involves `√`); second derivatives need Mathlib's `deriv` of
  `sqrt` machinery plus an explicit second bound, and a
  `C2Seg`-bundle packaging, and (iii) the `δ ≤ |det J|` side condition
  (front-facing/simple contacts) and the `E ≤ B/K` ball establishment.
  Until those are done, 7b-1's `newton2_step_quadratic` is the
  contraction core to instantiate.

- **M22 (addendum 3):** item 3b (range-free Möller–Trumbore `t` error
  bound): leaf bounds proved in new `Robust/MTTotal.lean` — `fl_sub_err_total` /
  `fl_add_err_total`, `fl_abs_le`, `fl_mul_err_total` (`|fl(fl a·fl b) − a·b| ≤
  7uAB + 9η(A+B+1)`), `fl_mul_ops_err_total` (product of operands each with an
  absolute operand error), no `InRange` anywhere. `Robust/MTLeaf.lean` adds
  `add2_fl_err_total` / `sub2_fl_err_total` (range-free bounds for fl-sum and
  fl-diff of two already-rounded operands). **Not done**: the cross-product
  component lemma `cross2_fl_err_total` and the full composition
  `mt_t_fl_err_total` — the F-model's `model.fl` unification cost makes the
  elaboration of those impossible to bound in this environment; the scratch
  attempts time out at 4+ CPU-minutes without producing a clean build. MT is
  not watertight so a `t` bound would buy no conservativity anyway. The
  verified leaf + stage lemmas stand as the bound toolkit; `mtcheck` remains
  the empirical check. `LightRT.lean` imports MTTotal and MTLeaf.
- **M22 (addendum 4):** 7b-2 (Bézier specialization of the 2D Newton) is
  **done**: `LightRT/Geom/BezNewton.lean` (~700 lines) proves the concrete
  contact system `F = (⟨R, C′⟩ + r·r′, |R| − r)` of `tri_bez_newton` for an
  abstract round-Bézier `BezSys` (curve components `gx..qz`, unclamped radius
  row `rad..ddr`, `HasDerivAt` hypotheses). The Jacobian entries are the C's
  own `dFdu`/`dFdt`/`dGdu`/`dGdt` polynomial sums (`pd1_bezF`, `pd2_bezF`,
  `pd1_bezG`, `pd2_bezG`, the `1/|R|` entries needing `|R| ≠ 0` like the C's
  `lenR > 1e-30` guard); `jacDet_bez` is literally the C's
  `det = dFdu·dGdt − dFdt·dGdu`. `bezF_C2Seg` / `bezG_C2Seg`
  prove the rectangle differentiability halves of `C2Seg` and take the eight
  second-derivative bounds as `PddBounds` hypotheses (f and g share one `K`,
  the C's `ddP` scale); second-derivative `K` and Jacobian `B` are *not*
  derived from the control points (that coefficient chase is out of scope).
  `bez_newton_quadratic` is the final contraction corollary (via
  `newton2_step_quadratic`), and `BezSys.ofCubic` instantiates the system for
  the actual cubic control-point polynomials of `tri_bez_eval`
  (`P`/`dP`/`ddP` proved equal to derivative polynomials via a `bezPoly`
  `Polynomial` representation, so no hand-differentiated monomial soup);
  `ofCubic_newton_quadratic` is the monic specialization. Honest limits:
  radius row unclamped (the C's `max r 0` is not `C²` at the kink), `dF/du < 0`
  selection and eps-convergence not modeled, `|R|² > 0` on the rectangle and
  `K`, `B`, `δ ≤ |det|`, `E ≤ B/K` are hypotheses — the same standing as
  `newton2_step_quadratic`. Supersedes addendum 2's deferral note.
  `LightRT.lean` imports `Geom.BezNewton`.

- **M22 (addendum 14):** M14 phases 1-2 (modeling the C's `tri_bez_newton`
  guards). New `Geom/BezNewtonGuards.lean`: `uLo/uHi = [-0.05, 1.05]`,
  `clampU`, `dampDu` (wild `|du| >= 1` steps become ±0.25), `rawStep`
  (identical to `newton2Step`), `guardedStep` (damp + advance + clamp) and
  `accepted` (C's residual / `dF/du < 0` minimum / `[tmin, best) × [0,1]`
  acceptance). Lemmas: `accepted_residual`, `accepted_minimum`,
  `accepted_range`, `jacDet_ne_zero_of_guard` (det guard), `dampDu_of_small`,
  `dampDu_le`, `clampU_mem`, `clampU_eq_of_mem`, `damped_step_range`. The
  float epsilons and the 12-iteration cap remain parameters/outside the
  model; the radius kink stays excluded (interval ends are handled by
  `bezPhi_min_critical`). M14 phase 3 (first step): `bezF_eq_zero_of_critical_of_contact`
  — at a ray point where the curve parameter is a critical point of `φ` and
  `G = 0` (tube boundary), the system's first equation vanishes (`F = 0`),
  so the bracket limit pairs with a genuine root `(u, t)` of the 2D system
  when the ray parameter is the contact. The remaining phase 3-4 work: verify
  the local hypotheses (`E ≤ B/K`, `δ ≤ |det|`, rectangle containment) at that
  root and prove guarded convergence; phase 3-4 first slice landed:
  `newtonIter_tendsto_of_basin` — guarded Newton converges to the root when
  the local hypotheses hold at every iterate, with
  `E_{n+1} ≤ (2B²/δ)E_n + (18BK/δ)E_n²` and `Tendsto E atTop (𝓝 0)`;
  verifying those hypotheses at the bracket-derived root remains the open gap;
  global 2D refinement stays open.

- **M22 (addendum 13):** the ISA boundary is now a **machine-checked
  hypothesis**, not just prose (item 4). New `C/Proofs/SimdLeafISA.lean`:
  `PackedOps` packages the audited per-intrinsic semantics (mul/add/sub/div
  and ordered/equality compares and mask and/or, each with an equation field
  tying it to the corresponding `FP.Binary32` lane op), the Woop kernel is
  re-run over abstract ops (`kWoopK`), `kWoopK_eq_model` proves it equals
  `SimdLanes.vWoopK` under those equations, and
  `simd_leaf_eq_scalar_of_isa` composes this with `blockBest_woop`: a block
  result differing from caller's best is a genuine scalar Woop hit in some
  lane, **conditional on the vendor ops satisfying PackedOps**. The actual
  SSE4.1/AVX2/SVE `PackedOps` instance is still not supplied (needs a vendor
  ISA semantics model); `wtcheck`'s fuzz remains the empirical evidence.
  The assumption boundary is now explicit in Lean, with the audit table in
  addendum 11 giving the intrinsic → field correspondence.

- **M22 (addendum 12):** conditional range-free slab completeness (item 3).
  `Robust/SlabTotal.lean`: `fpT_eta_slack` (the absolute-error slack of
  `fpT_abs_err_total`), `fpT_rel_of_floor` (a floor `κ ≤ |t_exact|` converts
  the absolute bound into `|fpT − t| ≤ θ|t|`, `θ = 4u + slack/κ`) and
  `slab_no_false_miss_total_of_floor`: with per-endpoint floor κ, a ray-length
  floor `κT ≤ tmin ≤ t`, θ < 1, and the explicit inflation condition
  `1 + θ + η/κT ≤ (1−θ)(1−u)K`, every geometric hit is reported by
  `fpSlab` — **no `InRange`**. The unconditioned statement is unprovable
  (tangency); this theorem states exactly the hypothesis under which it is
  true. `LightRT.lean` now imports `Robust.SlabTotal`.

- **M22 (addendum 11):** **SIMD leaf ISA audit** — the exact boundary of
  the model. The watertight leaf kernels in `lightrt_c_tri.c`
  (`tri_woop4_lanes` SSE4, `tri_woop8_lanes` AVX2, `tri_woop_sve_core`
  SVE 8/16) are structurally identical (same expression tree, same
  association, explicit mul/sub separation, no FMA anywhere in the leaf;
  `-ffp-contract=off`), and so are the block wrappers' scalar folds.
  Every intrinsic in the leaf maps to a model operation:
  - `_mm_loadu_ps`/`_mm256_loadu_ps`/`svld1_f32`, `_mm_store_ps|u_ps`/`_mm256_store_ps`/`svst1_f32`
    → register load/store; the model abstracts inputs as
    `v : Fin w → Fin 3 → F` and the C spills `tt, ve, we, det` to scalar memory
    for the final fold — modeled by `blockBest`;
  - `_mm_setzero_ps`/`_mm256_setzero_ps`/`svdup_f32(0)`, `_mm_set1_ps`/`svdup_f32`
    → `vconst`;
  - `_mm_sub_ps|mul_ps|add_ps|div_ps`/`_mm256_*`/`sv{sub,mul,add,div}_f32_x`
    → `vsub`/`vmul`/`vadd`/`vdiv` (per-lane binary32, RNE, no FMA);
  - `_mm_or_ps`/`_mm256_or_ps`/`svorr_b_z` → `vor`; `_mm_and_ps`/`_mm256_and_ps`/`svand_b_z` → `vand`;
    `_mm_andnot_ps(a, b)` (= `b & ~a`) → `vnot` then `vand`;
    `svbic_b_z(pg, svcmpne_f32(pg, det, z), svand_b_z(pg, neg, pos))` → same polarity as `(det ≠ 0) ∧ ¬(neg ∧ pos)`;
  - `_mm_cmplt_ps`/`_mm_cmpgt_ps`/`_mm_cmpge_ps`/`_mm_cmpneq_ps`
    and AVX2 `_mm256_cmp_ps(_CMP_LT_OQ|_CMP_GT_OQ|_CMP_GE_OQ|_CMP_NEQ_UQ)`
    and SVE `svcmplt_f32`/`svcmpgt_f32`/`svcmpge_f32`/`svcmpne_f32`
    → `vlt` (with operand order swapped for the greater-than case, as the
    model does), `vle`, `veq`;
  - `_mm_movemask_ps`/`_mm256_movemask_ps`/`svptest_any`
    → the C bit-packing `(m >> l & 1)` of the per-lane bool into the
    block-acceptance integer index — lane order 0…w−1 matches `Fin w`;
    the all-reject early return (`!em` before the divide) is not modeled,
    but it only short-circuits what the masks would reject anyway;
  - `_mm256_fmadd_ps`/`_mm256_fmsub_ps`/SSE `_mm_fmadd_ps` — **not used in
    this leaf** (they appear only in the MT/Bezier paths, under
    `-ffp-contract=off`); the model's no-FMA assumption holds here by
    inspection.
  Ordered comparisons are false on NaN (both ISA `_OQ` and SSE `cmplt`);
  `_CMP_NEQ_UQ` and SVE `svcmpne_f32` are true on NaN — the same atoms as
  `FP.Binary32.ltBits/leBits/eqF` (decoded-compare on RNE bit patterns).
  The fold (`if ((m >> l) & 1 && T[l] < bt) { bt = T[l]; bl = l; }`) is the
  model's `blockBest` (NO_HIT lanes skipped, strictly-smaller-`t` wins,
  first/lowest lane on ties), with `*best_u = V[bl] / D[bl]` computed
  scalar after selection — same operands, same op order, same result.
  **Residual ISA assumptions (not formalized, vendor guarantee, recorded
  here as the boundary):** (1) per-element packed ops compute exactly the
  binary32 lane ops (`mulBits`/`addBits`/`subBits`/`divBits`), RNE;
  (2) ordered compares are NaN-false; unordered NEQ is NaN-true;
  (3) movemask/predicates preserve lane-bit order;
  (4) the compiler contracted nothing and reassociated nothing (guaranteed
  by `-ffp-contract=off` and single-op expressions; verified bitwise by
  `wtcheck`, incl. SVE, every `make formal`).
  **Empirical backstop:** `wtcheck` (in `make formal`) compares
  `tri_woop4_block`, `tri_woop8_block`, `tri_woop_sve_block` (SVE 8 and 16)
  plus `_occ` variants against scalar `tri_woop_one` **bit for bit**,
  including SVE, on edge/degenerate/NaN-ish inputs and bit patterns;
  ASan/UBSan runs pass. Closing the boundary needs a vendor ISA semantics
  model (SSE4.1/AVX2/SVE packed ops), which no current tooling provides;
  item stays empirical.

- **M22 (addendum 10):** the global safeguarded-Newton argument (the C's
  `tri_bez_leaf_dist` bracket). New `Geom/SafeguardedNewton.lean`:
  `fsplit`/`seqIter` (bracket split + `n`-fold iteration), `seqLo`/`seqHi`
  (monotone bracket-end sequences), invariants `seqIter_sign`,
  `seqIter_in_interval`, `seqIter_width` (width halves: bisection alone
  suffices), convergence to a common limit `c` (`seqLo_tendsto` via
  `tendsto_atTop_ciSup`, `seqHi_tendsto`, `limit_unique` via
  width → 0), and `bracket_root`: from a sign-changing bracket with
  `ContinuousOn g [a, b]`, the bracket converges to a root of `g`.
  Instantiated to the Bézier envelope equation: `envelope_continuousOn`
  (`φ′` continuous where `bezQ ≠ 0`), `bracket_envelope_bezPhi` /
  `bracket_envelope_bezPhi'` (both sign conventions): whenever `φ′` changes
  sign on `[a, b]` (the C's sample-detected bracket) and `x` is off the
  curve, there is a critical point of `φ` — the C's safeguarded loop
  converges to one from an arbitrary seed. Newton acceleration (quadratic
  contraction near the limit) is the local half (`ofCubic_newton_quadratic`,
  M7/M22 addendum 4). The 2D `(u, t)` `tri_bez_newton` polish is the same
  argument applied to the envelope component of the system plus the
  existing local contraction theorem. Remaining: the basin-of-attraction
  refinement for the 2D Newton in full generality (the C's damped-step /
  `det > 0` guards are modeled but not theorem'd).

- **M22 (addendum 9):** two more M14 slices for the tube model:
  (1) the sampled rule is modeled end-to-end — `samDist` (the `tri_bez_leaf_dist`
  fold, min of `dist x (C u) − r(u)` over `List ℝ` sites; empty list maps
  to `0`), proved `AbsLipschitz` by list induction
  (`absLipschitz_bezContact`, `absLipschitz_samDist_foldr`,
  `absLipschitz_samDist`), then `lipschitz1_samDist_line` along unit
  rays and `stTrace3_samDist_le_root` (the sampled trace never passes a
  root where the sampled min is ≤ 0 — some site's ball covers the root).
  What's *not* shown: sampled-min ≥ continuous inf is not relaxed —
  a root of the sampled fold need not lie inside the true tube without a
  density bound on `sites`; `primhitcheck` remains the empirical gate.
  (addendum 9 cont.) `samDist_nonpos_mem_tube`: the C's leaf can never
  accept outside the true tube — `samDist ≤ 0` ⇒ `x ∈ bezTubeSet`
  (contrapositive: `samDist_pos_of_bezPhiMin_pos`); overshoot remains the
  sampling-density question.
  (addendum 9 cont.) `exists_bezTube_boundary_point`: along any segment
  from an outside point to a point in/touching the tube, some intermediate
  `s` has `Metric.infDist (x₀ + s • v) tube = 0` (IVT; the trace's
  boundary-existence companion to `stTrace3_bezTube_le_root`).
  `bezPhiMin_le_samDist`: for nonempty site lists in
  `[a, b]`, `bezPhiMin ≤ samDist` — the sampled fold is an
  *over-estimate* of the true distance-to-tube (the correct sign for the
  C stepping by it). And the **quantitative** density bound:
  `samDist_le_bezPhiMin_add` — for sites covering `[a, b]` with radius
  `R` and per-component derivative bounds `Mx` (curve) and `Mr` (radius),
  `samDist x ≤ bezPhiMin S x a b + (√3·Mx + Mr)·R`, via
  `abs_sub_le_of_deriv_bound` (MVT), `curve_dist_le`, `rad_dist_le`,
  `foldr_min_le_mem`, `samDist_le_mem`. Together with
  `bezPhiMin_le_samDist` this sandwiches the sampled fold:
  `bezPhiMin ≤ samDist ≤ bezPhiMin + (√3·Mx + Mr)·R`.
  (2) the interior nearest point is a critical point of `φ`:
  `interior_min_bezPhi_deriv` (Fermat: at an interior min of `φ` with
  `bezQ ≠ 0`, `φ′ = 0`), `interior_min_bezPhi_envelope` (the foot-point
  equation `⟨x − C, C′⟩ / |x − C| = −r′`, the C's Newton solve shape),
  and `bezPhi_min_critical` (the min of `φ` on `[a,b]` is attained at an
  endpoint, an interior critical point, or on the curve itself). These
  are the soundness direction of the `tri_bez_newton` model; the
  contraction core (`ofCubic_newton_quadratic`) was already done in M7/M22
  addendum 4. Remaining M14 work: the Newton convergence's global
  argument (basin of attraction / existence of the nearest foot with a
  nondegenerate Jacobian), which is substantial.

- **M22 (addendum 8):** the linchpin of M14 is done: `Geom/BezTube.lean`
  (all in `EuclideanSpace ℝ (Fin 3)`, where Mathlib's `dist` is Euclidean)
  now proves `bezQ_eq_dist_sq` / `bezPhi_eq_dist`, `phi_min_attained`,
  `bezPhiMin` / `bezPhiMin_eq` / `bezPhiMin_le`, the closed-ball-based
  `bezTubeSet` with `mem_bezTubeSet_iff`, and **`infDist_bezTubeSet`**:
  `Metric.infDist x (bezTubeSet S a b) = max 0 (bezPhiMin S x a b)`.
  Proof strategy: nonpositive-φ case puts `x` inside the tube
  (`Metric.infDist_zero_of_mem`); positive case shows every tube point
  is at distance `≥ min φ` (via the triangle inequality and
  `bezPhi_eq_dist`) and exhibits the perpendicular foot at the
  minimizing parameter `C(u₀) + (r(u₀)/d) • (x − C(u₀))` as a witness.
  Added (same milestone): `stTrace3_bezTube_le_root` — the
  exact-distance no-overshoot trace corollary for `bezTubeSet`
  (`bezPhiMin root ≤ 0` ⇒ iterate never passes it; via
  `stTrace3_le_root (bezTubeSet ...)` and `infDist_bezTubeSet`).
  Added (same milestone): `samDist` — the sampled-distance fold of
  `tri_bez_leaf_dist` (min of `dist x (C u) − r(u)` over `List ℝ` sites,
  empty list maps to `0`) — proved `AbsLipschitz` by list induction
  (`absLipschitz_bezContact`, `absLipschitz_samDist_foldr`,
  `absLipschitz_samDist`), then `lipschitz1_samDist_line` along unit
  rays, and `stTrace3_samDist_le_root` (the sampled trace never passes a
  root where the sampled min is ≤ 0). What's *not* shown: the sampled
  fold's zero set need not align with the true tube without a density
  bound on `sites`; `primhitcheck` remains the empirical gate there.
  Remaining M14 work: the Newton foot-point convergence proof.

- **M22 (addendum 7):** the M14 signed-distance model got its first
  slice: `LightRT/Geom/BezTube.lean` proves `hasDerivAt_bezQ` /
  `hasDerivAt_bezPhi` (φ(u) = ‖x − C(u)‖ − r(u) differentiable off the
  curve, derivative `⟨R, C′⟩ / |R| − r′`, the C's `dGdu`-shaped formula),
  `deriv_bezPhi`, `continuous_bezPhi`, and `phi_min_attained` (the min of
  φ on `Icc a b` is attained, via `IsCompact_Icc.exists_isMinOn`).
  Definitions `bezPhi` / `bezQ` / `bezTubeSet` (union of balls
  `B(C(u), r(u))` over the interval). Not done: `inf_u φ = infDist` to
  the tube set, the tube trace guarantee through the sampled rule, and
  the Newton foot-point convergence proof. `LightRT.lean` imports
  `Geom.BezTube`.

- **M22 (addendum 6):** item 3b (range-free Möller–Trumbore `t` error
  bound) is **done, end-to-end**: `Robust/MTTotal.lean` + `Robust/MTLeaf.lean`
  (leaf/stage bounds: `fl_mul_err_total`, `fl_mul_ops_err_total`,
  `fl_sub/add_err_total`, `fl_abs_le`, `add2/sub2_fl_err_total`), `Robust/MTCross2.lean`
  (`fl_pair_mul_bound`, `cross_mul_abs_err`, `cross2_fl_err_total` — the
  cross-product component as the C rounds it), `Robust/MTDot.lean` (`dot3_fl_err_total`
  via `num_err_total` with a padded operand bound; `cross_component_err`;
  `mt_det_err_total` / `mt_num_err_total` with `|dᵢ|,|tvᵢ| ≤ M`, `|e1ᵢ| ≤ A`, `|e2ᵢ| ≤ B`),
  and `Robust/MTT.lean` (`mt_t_fl_err_total_model`: the composed `t` bound
  `|t_model − t_exact| ≤ (12u·BMA + (2u+2)·mtNumErr M A B)/a0 + η + 12·BMA·mtDetErr M A B / a0²`,
  with `a0 ≤ det_exact` and `mtDetErr M A B ≤ a0/2` hypotheses; negative-det
  class via the sign-flipped ray). All range-free, zero `sorry`; the bound
  degrades like `1/a0` near det = 0, which is correct for a non-watertight
  kernel — it buys no conservativity for pruning; `mtcheck` remains the
  empirical check. `LightRT.lean` imports MTDot and MTT.

- **M22 (addendum 5):** 7a (3D no-overshoot) is **done**:
  `LightRT/Geom/SphereTrace3.lean` proves `infDist_lipschitz` (distance to a
  set is 1-Lipschitz), `infDist_line_lipschitz` (the ray restriction
  `infDist (x₀ + t•v) S` has Lipschitz constant `‖v‖`, so ≤ 1-Lipschitz on a
  unit ray), `stTrace3_le_root` (starting at `t ≤ root`, the distance-driven
  trace never passes a `root` with `infDist (x₀ + root • v) S ≤ 0`, via the
  1D `stTrace_le_root`), `stTrace3_tube_le_root` (the `r`-tube variant for
  the round Bézier tube), plus the `AbsLipschitz` atoms `lipschitz1_min`
  (min of two 1-Lipschitz functions) and `lipschitz1_dist_of_mem` — the
  building blocks of the *sampled* `tri_bez_leaf_dist` fold (repeated
  `min` closes the sample fold). Not modeled: the leaf's distance is a
  sampled estimate, not exact `infDist`; `primhitcheck` covers the sampled
  rule. `LightRT.lean` imports `Geom.SphereTrace3`.

