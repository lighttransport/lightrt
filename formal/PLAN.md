# LightRT formal verification plan (Lean 4 + Mathlib)

Status as of 2026-11-10. Everything below builds with `make formal`. The codebase has **21 `sorry`s** (`tools/count_sorry.sh`). **84 theorems are closed** with axioms limited to {`propext`, `Classical.choice`, `Quot.sound`}. That count includes 52 MiniC logic lemmas ported from tinygltf; 32 are new to this project, including the full M1 Ize slab bound (`slab_no_false_miss`, `slab_t_err`, `slab_t_err_fma`, `ize_constant_sufficient`/`_gamma3_insufficient`). No closed theorem uses `native_decide`.

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
| `sorry` / `axiom` | 0 / 0 | 0 / 0 | 0 / 0 | 21 (ours, tracked) |
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
- `mtReal_sound`, `mtReal_complete`
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
- decode/encode round-trip
- `propagate` is the identity on non-NaN inputs
- `fmin`/`fmax` equal `min`/`max` on non-NaN inputs

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
- **M3:** `tri_ray_setup_refines` and `tri_slab_scalar_refines`. Together with the kernel-checked witness these yield `tri_slab_scalar_false_miss_exists`. Then patch the C: inflate `tfar` by `0x3f800005` (1+10u) behind a flag, and re-verify.
- **M4:** Woop vertex fan, optional C port, and `tri_mt_one_refines`. Möller–Trumbore *non*-watertightness would be shown with a cdiff witness.
- **M5:** BVH `traverse_eq_brute` / `traverseOrdered_eq_brute`, instantiated with the Stage 3 box test.
