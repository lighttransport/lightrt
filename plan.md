# Task: Plan a Lean 4 formal verification project for ray tracing primitives

## Goal
Produce a concrete, staged PLAN (do not write the proofs yet) for formally verifying
core ray-tracing algorithms in Lean 4 + Mathlib, with floating-point robustness as the
main research target. The plan must be executable by an LLM proof agent working with
lean-lsp-mcp, with a human reviewing specifications.

## Context
- Lean 4 + Mathlib. Check the latest stable toolchain and pin it in `lean-toolchain`.
- Floating-point: Lean's built-in `Float` is opaque to the kernel, so it cannot be reasoned
  about directly. Evaluate these candidates and recommend ONE (or a minimal custom
  rounding model) with reasons: FloatSpec (Flocq port), Flean, FloatLib. Check their
  current `sorry` counts, Mathlib version compatibility, and license (project must stay
  Apache-2.0 compatible, no GPL dependencies).
- Reference papers for the algorithms to verify:
  - Woop, Benthin, Wald, "Watertight Ray/Triangle Intersection" (JCGT 2013)
  - Ize, "Robust BVH Ray Traversal" (JCGT 2013) and its FMA correction note
  - Williams et al., slab-method ray/AABB
  - Möller–Trumbore ray/triangle (as a baseline, non-watertight)

## Scope (staged; plan each stage separately)
1. Real-number geometric specs over ℝ³ (Mathlib inner-product / affine spaces):
   ray/AABB and ray/triangle intersection, "algorithm returns hit ⇔ geometric intersection".
2. Rounding-error model (standard model fl(x∘y) = (x∘y)(1+δ), |δ| ≤ u) and a
   reusable lemma library (γₙ composition, FMA, monotonicity of rounding).
3. Conservative robustness theorems:
   - Slab ray/AABB: no false misses, with an explicit t_max inflation factor.
   - Reproduce Ize's FMA-corrected error bound (each operation has its own δᵢ; do not
     assume every operation contributes exactly ε).
4. Watertightness of Woop's ray/triangle test: consistent decisions on shared edges
   and vertices.
5. BVH level: containment invariant of the build, and traversal returns the same nearest
   hit as brute force (induction over the tree).
6. Bridge to implementation: Lean reference implementation used as a differential-testing
   oracle for a C/Rust/SIMD implementation (full verification of C is out of scope unless
   justified).

## Deliverables of the plan
1. Repo layout (lakefile, module tree, naming conventions, `lean-toolchain` pin).
2. Dependency decision for floating point, with a comparison table and risks.
3. For each stage: formal statements of the main definitions and top-level theorems in Lean
   syntax, written with `sorry` bodies, and a list of the helper lemmas needed. The
   statements must compile.
4. Specification review checklist for the human: how to catch vacuous or weak specs
   (trivially true postconditions, wrong direction of the false-miss implication,
   unintended hypotheses).
5. Agent workflow: which tasks are delegated to a proof agent, how to split the work into
   small lemmas, the retry/escalation policy, and CI gates (no `sorry`, `#print axioms`
   allowlist, no `native_decide` in core theorems, build time budget).
6. Risk register and fallbacks (for example, if the floating-point library is too incomplete,
   prove only the needed lemmas ourselves).
7. A milestone list with a minimal first result. Suggested first milestone: Woop
   watertight edge-function antisymmetry on shared edges, then Ize's slab error bound.

## Constraints
- Do not write full proofs in this phase. Skeleton statements with `sorry` are fine, but they must
  typecheck (`lake build`), and you must report the exact count of `sorry`s.
- Verify every external claim (library status, versions, theorem statements in the papers) by
  reading the source or repo. If you cannot verify, mark it as UNVERIFIED.
- Ask me before choosing between real-first versus rounding-model-first if the trade-offs are
  close. Otherwise proceed with your recommendation and state the assumption.
- Keep the final plan under about 2000 words, plus the Lean skeleton files.
