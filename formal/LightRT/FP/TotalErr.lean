/-
  Total (range-free) rounding error for the concrete binary32 RNE.

  `RoundingModel.rel` only bounds `fl` on `InRange` (zero or normal, no
  overflow). The proofs in `Robust/` therefore carry `InRange` hypotheses.
  For the concrete `Binary32.model` a range-free absolute bound holds:

      |rneR x − x| ≤ u |x| + 2⁻¹⁵⁰                       (u = 2⁻²⁴)

  where `2⁻¹⁵⁰` is half the smallest subnormal quantum. `rneR_abs_err_half`
  is the per-rounding error (`q/2`, `q = 2^qexp x`), valid for every `x`;
  the two branches below just split `x` at the normal threshold. This does
  not by itself re-prove the Woop/MT bounds without `InRange` (their absolute
  terms gain `η/|D|`, which is only useful when the denominator is not tiny),
  but it gives the primitive `model.abs_err_total` those re-derivations need.
-/
import LightRT.FP.Binary32

namespace LightRT.FP.Binary32

/-- Per-rounding error for positive `x`: half the quantum `2^qexp x`. -/
theorem rneR_abs_err_half_pos (x : ℝ) (hx : 0 < x) :
    |rneR x - x| ≤ (2:ℝ)^(qexp x) / 2 := by
  set q : ℝ := (2:ℝ) ^ qexp x with hqdef
  have qpos : 0 < q := by positivity
  have h1 : rneR x = (roundEven (x / q) : ℝ) * q := by
    unfold rneR; rw [rne_pos hx]
  have h2 : (roundEven (x / q) : ℝ) * q - x =
      q * ((roundEven (x / q) : ℝ) - x / q) := by
    field_simp [qpos.ne']
  rw [h1, h2, abs_mul, abs_of_pos qpos]
  have := roundEven_err (x / q)
  nlinarith

/-- Per-rounding error for every `x` (oddness handles negatives). -/
theorem rneR_abs_err_half (x : ℝ) : |rneR x - x| ≤ (2:ℝ)^(qexp x) / 2 := by
  by_cases hx0 : x = 0
  · simp [hx0, rneR, rne]
    positivity
  · rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have hx : x = -|x| := by rw [abs_of_neg hneg]; simp
      rw [hx, rneR_neg, show -rneR |x| - -|x| = -(rneR |x| - |x|) by ring, abs_neg]
      have hq : qexp (-|x|) = qexp |x| := by simp [qexp]
      rw [hq]
      exact rneR_abs_err_half_pos |x| (abs_pos.2 hx0)
    · have hx : x = |x| := by rw [abs_of_pos hpos]
      rw [hx]
      exact rneR_abs_err_half_pos |x| (abs_pos.2 hx0)

/-- **Range-free binary32 absolute error**: `u |x| + 2⁻¹⁵⁰`, including
    subnormals, zero and values beyond the finite range. -/
theorem rneR_abs_err_total (x : ℝ) :
    |rneR x - x| ≤ (2:ℝ)^(-24:ℤ) * |x| + (2:ℝ)^(-150:ℤ) := by
  have h := rneR_abs_err_half x
  by_cases hx : |x| < (2:ℝ)^(-126:ℤ)
  · by_cases hx0 : x = 0
    · simp [hx0, rneR, rne]
    · have ha : 0 < |x| := abs_pos.2 hx0
      have hlog : Int.log 2 |x| ≤ -126 := by
        by_contra hlt
        push Not at hlt
        have h1 := two_zpow_log_le ha
        have h2 : (2:ℝ)^(-126:ℤ) < (2:ℝ)^(Int.log 2 |x|) := by
          apply zpow_lt_zpow_right₀ (by norm_num : (1:ℝ) < 2)
          omega
        linarith
      have hq : qexp x = (-149 : ℤ) := by
        rw [qexp_eq, max_eq_right (by omega)]
        norm_num
      have hq2 : (2:ℝ)^(qexp x) / 2 = (2:ℝ)^(-150:ℤ) := by
        rw [hq]
        rw [show (-149:ℤ) = -150 + 1 by norm_num, zpow_add₀ (by norm_num)]
        ring
      rw [hq2] at h
      calc |rneR x - x| ≤ (2:ℝ)^(-150:ℤ) := h
        _ ≤ (2:ℝ)^(-24:ℤ) * |x| + (2:ℝ)^(-150:ℤ) := by
          have : (0:ℝ) ≤ (2:ℝ)^(-24:ℤ) * |x| := by positivity
          linarith
  · push Not at hx
    have ha : 0 < |x| := lt_of_lt_of_le (by positivity) hx
    have hE : (-126 : ℤ) ≤ Int.log 2 |x| :=
      (Int.zpow_le_iff_le_log (b := 2) (by norm_num) ha).1 (by simpa using hx)
    have hq : qexp x = Int.log 2 |x| - 23 := by rw [qexp_eq, max_eq_left hE]
    have hqx : (2:ℝ)^(qexp x) / 2 ≤ (2:ℝ)^(-24:ℤ) * |x| := by
      have h2 := two_zpow_log_le ha
      have e : (2:ℝ)^(qexp x) / 2 =
          (2:ℝ)^(-24:ℤ) * (2:ℝ)^(Int.log 2 |x|) := by
        rw [hq, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
          zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0),
          zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
        norm_num
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    calc |rneR x - x| ≤ (2:ℝ)^(qexp x) / 2 := h
      _ ≤ (2:ℝ)^(-24:ℤ) * |x| := hqx
      _ ≤ (2:ℝ)^(-24:ℤ) * |x| + (2:ℝ)^(-150:ℤ) := by
        have : (0:ℝ) ≤ (2:ℝ)^(-150:ℤ) := by positivity
        linarith

/-- The model instance's total error, ready for range-free re-derivations. -/
theorem model_abs_err_total (x : ℝ) :
    |model.fl x - x| ≤ model.u * |x| + (2:ℝ)^(-150:ℤ) :=
  rneR_abs_err_total x

end LightRT.FP.Binary32
