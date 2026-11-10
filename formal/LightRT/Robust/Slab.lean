/-
  Stage 3: conservative floating-point slab test (no false misses).

  Two evaluation orders appear in LightRT:
  * scalar `tri_slab_scalar`:   t = fl(fl(bound - org) * invd)        (relative error)
  * SIMD  `*_slab_avx/sse`:     t = fl(bound * invd - oinv)  (FMA)    (absolute error!)
  where `invd = fl(1 / d)` and `oinv = fl(org * invd)`.

  Every rounding has its own δ (via `RoundingModel.rel`); nothing below assumes
  all operations contribute the same ε.

  Note (derived here, Ize's exact constant is UNVERIFIED against the paper):
  if the far value is inflated by a *rounded* multiply `fl(tfar * K)`, the
  sufficient condition is `(1 + γ₃) ≤ (1 - γ₃)(1 - u) K`; `K = 1 + 2γ₃` does
  NOT satisfy it, `K = 1 + 2γ₄` does (`ize_constant_sufficient`).
-/
import LightRT.FP.Gamma
import LightRT.FP.Binary32
import LightRT.Geom.SlabReal

namespace LightRT.Robust
open LightRT.FP LightRT.Geom
noncomputable section

variable (R : RoundingModel)

/-- `invd = fl(1/d)` (direction components assumed nonzero here). -/
def fpInvd (r : Ray) (i : Fin 3) : ℝ := R.div 1 (r.d i)

/-- Scalar order: `fl(fl(x - o) * invd)`. -/
def fpT (r : Ray) (x : ℝ) (i : Fin 3) : ℝ := R.mul (R.sub x (r.o i)) (fpInvd R r i)

/-- FMA order: `fl(x * invd - fl(o * invd))` (one rounding for the fused op). -/
def fpTfma (r : Ray) (x : ℝ) (i : Fin 3) : ℝ :=
  R.fma x (fpInvd R r i) (-(R.mul (r.o i) (fpInvd R r i)))

def fpNear (r : Ray) (b : Box) (i : Fin 3) : ℝ := min (fpT R r (b.lo i) i) (fpT R r (b.hi i) i)
def fpFar (r : Ray) (b : Box) (i : Fin 3) : ℝ := max (fpT R r (b.lo i) i) (fpT R r (b.hi i) i)

/-- Floating-point slab test with the far value inflated by a rounded multiply by `K`.
    `K = 1` is exactly the current `tri_slab_scalar` (min/max are exact in FP). -/
def fpSlab (r : Ray) (b : Box) (K : ℝ) : Prop :=
  max (max (fpNear R r b 0) (fpNear R r b 1)) (max (fpNear R r b 2) r.tmin) ≤
    R.mul (min (min (fpFar R r b 0) (fpFar R r b 1)) (min (fpFar R r b 2) r.tmax)) K

/-- Every intermediate exact result lies where the standard model applies. -/
def SlabInRange (r : Ray) (b : Box) (K : ℝ) : Prop :=
  (∀ i, R.InRange (1 / r.d i)) ∧
  (∀ i, ∀ x ∈ ({b.lo i, b.hi i} : Set ℝ),
    R.InRange (x - r.o i) ∧ R.InRange (R.sub x (r.o i) * fpInvd R r i)) ∧
  R.InRange (min (min (fpFar R r b 0) (fpFar R r b 1)) (min (fpFar R r b 2) r.tmax) * K)

/-- Per-operation error of one slab parameter (scalar order): three roundings. -/
theorem slab_t_err (r : Ray) (x : ℝ) (i : Fin 3) (hd : r.d i ≠ 0)
    (hu : (3 : ℝ) * R.u < 1)
    (h1 : R.InRange (1 / r.d i)) (h2 : R.InRange (x - r.o i))
    (h3 : R.InRange (R.sub x (r.o i) * fpInvd R r i)) :
    |fpT R r x i - (x - r.o i) / r.d i| ≤ gamma R.u 3 * |(x - r.o i) / r.d i| := by
  sorry

/-- Ize's FMA observation: the FMA order has an *absolute* error that scales
    with `|o|/|d|`, not with `|t|` (catastrophic cancellation in `x·invd - oinv`). -/
theorem slab_t_err_fma (r : Ray) (x : ℝ) (i : Fin 3) (hd : r.d i ≠ 0)
    (hu : (3 : ℝ) * R.u < 1)
    (h1 : R.InRange (1 / r.d i)) (h2 : R.InRange (r.o i * fpInvd R r i))
    (h3 : R.InRange (x * fpInvd R r i - R.mul (r.o i) (fpInvd R r i))) :
    |fpTfma R r x i - (x - r.o i) / r.d i| ≤
      gamma R.u 3 * (|x - r.o i| + |r.o i|) / |r.d i| := by
  sorry

/-- The inflation condition needed when `tfar * K` is itself rounded. -/
def InflationOK (u K : ℝ) : Prop := 1 + gamma u 3 ≤ (1 - gamma u 3) * (1 - u) * K

/-- `K = 1 + 2γ₄` is sufficient for every `u ≤ 2⁻²⁴`. -/
theorem ize_constant_sufficient {u : ℝ} (hu0 : 0 < u) (hu : u ≤ (2 : ℝ) ^ (-24 : ℤ)) :
    InflationOK u (1 + 2 * gamma u 4) := by
  sorry

/-- `K = 1 + 2γ₃` is NOT sufficient once the final multiply is rounded. -/
theorem ize_constant_gamma3_insufficient {u : ℝ} (hu0 : 0 < u) (hu : u ≤ (2 : ℝ) ^ (-24 : ℤ)) :
    ¬ InflationOK u (1 + 2 * gamma u 3) := by
  sorry

/-- **Stage 3 main theorem: no false misses.** If the exact ray segment meets the
    box, the inflated floating-point slab test reports a hit. Direction of the
    implication: geometric hit ⇒ algorithm hit (conservativeness). -/
theorem slab_no_false_miss (r : Ray) (b : Box) (K : ℝ)
    (hd : ∀ i, r.d i ≠ 0) (htmin : 0 ≤ r.tmin)
    (hu : (3 : ℝ) * R.u < 1) (hK : InflationOK R.u K)
    (hrange : SlabInRange R r b K) :
    HitsBox r b → fpSlab R r b K := by
  sorry

/-- Without inflation the scalar LightRT test can miss a real hit in binary32.
    To be discharged by an explicit witness found with `tools/cdiff.py --search-miss`. -/
theorem tri_slab_scalar_false_miss_exists :
    ∃ (r : Ray) (b : Box), (∀ i, r.d i ≠ 0) ∧ 0 ≤ r.tmin ∧
      (∀ i, Binary32.model.Repr (r.o i) ∧ Binary32.model.Repr (r.d i) ∧
            Binary32.model.Repr (b.lo i) ∧ Binary32.model.Repr (b.hi i)) ∧
      HitsBox r b ∧ ¬ fpSlab Binary32.model r b 1 := by
  sorry

end
end LightRT.Robust
