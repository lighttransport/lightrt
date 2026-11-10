/-
  Stage 2: the standard rounding-error model.

  `fl (x ∘ y) = (x ∘ y)(1 + δ)`, `|δ| ≤ u`, for every exact result `x ∘ y`
  that lies in the model's `InRange` set (normal range or zero). Each
  operation gets its *own* δ (the existential is per call), so no theorem may
  assume that all operations contribute the same error.
-/
import Mathlib

namespace LightRT.FP

/-- An abstract rounding to a floating-point format with unit roundoff `u`. -/
structure RoundingModel where
  /-- Rounding of an exact real result. -/
  fl : ℝ → ℝ
  /-- Unit roundoff (binary32 RNE: `2⁻²⁴`). -/
  u : ℝ
  /-- Results for which the relative-error bound holds (zero or normal range). -/
  InRange : ℝ → Prop
  u_pos : 0 < u
  u_lt_one : u < 1
  /-- Standard model, one fresh `δ` per rounding. -/
  rel : ∀ x, InRange x → ∃ δ, |δ| ≤ u ∧ fl x = x * (1 + δ)
  /-- Rounding is monotone (holds for all IEEE rounding modes). -/
  mono : Monotone fl
  /-- Rounding is odd (holds for RNE / RTZ, not for directed modes). -/
  neg : ∀ x, fl (-x) = -fl x
  /-- Representable values are fixed points; `0` is representable. -/
  fl_zero : fl 0 = 0
  fl_idem : ∀ x, fl (fl x) = fl x

namespace RoundingModel
noncomputable section
variable (R : RoundingModel)

/-- `x` is a representable value of the format. -/
def Repr (x : ℝ) : Prop := R.fl x = x

def add (x y : ℝ) : ℝ := R.fl (x + y)
def sub (x y : ℝ) : ℝ := R.fl (x - y)
def mul (x y : ℝ) : ℝ := R.fl (x * y)
def div (x y : ℝ) : ℝ := R.fl (x / y)
/-- Fused multiply-add: one rounding. -/
def fma (a b c : ℝ) : ℝ := R.fl (a * b + c)

theorem mul_comm' (x y : ℝ) : R.mul x y = R.mul y x := by
  simp [mul, _root_.mul_comm]

theorem sub_antisymm (x y : ℝ) : R.sub x y = -R.sub y x := by
  simp only [sub, ← R.neg]; congr 1; ring

/-- Helper (to prove): rounding preserves sign. -/
theorem fl_nonneg {x : ℝ} (h : 0 ≤ x) : 0 ≤ R.fl x := by
  simpa [R.fl_zero] using R.mono h

theorem fl_nonpos {x : ℝ} (h : x ≤ 0) : R.fl x ≤ 0 := by
  simpa [R.fl_zero] using R.mono h

/-- Helper: the relative bound in absolute-error form. -/
theorem abs_err {x : ℝ} (hx : R.InRange x) : |R.fl x - x| ≤ R.u * |x| := by
  sorry

/-- Non-vacuity: exact arithmetic is a rounding model for any `0 < u < 1`, so the
    class's axioms are consistent (a contradictory model would make every
    theorem over `RoundingModel` vacuously true). -/
def exact (u : ℝ) (h0 : 0 < u) (h1 : u < 1) : RoundingModel where
  fl := id
  u := u
  InRange := fun _ => True
  u_pos := h0
  u_lt_one := h1
  rel := fun x _ => ⟨0, by simp [h0.le], by simp⟩
  mono := monotone_id
  neg := fun _ => rfl
  fl_zero := rfl
  fl_idem := fun _ => rfl

end
end RoundingModel
end LightRT.FP
