/-
  Range-free (subnormal-safe) numerator bound for the Woop `t`.

  `num_err` in `BVH/ExactPrune.lean` bounds the rounded numerator through
  `RoundingModel.abs_err`, which needs `InRange`. Here each of the five
  roundings (three products, two sums) is instead bounded by
  `u |x| + eta` (`TotalErr.model_abs_err_total`, `eta = 2^-150`), giving the
  same `4 u (b0+b1+b2)` term plus `8 eta`. This is the first building block
  for a Woop `t` bound that does not assume `InRange`; the denominator bound
  and the quotient assembly are the next steps.
-/
import LightRT.FP.TotalErr
import LightRT.Robust.Slab

namespace LightRT.Robust
open LightRT.FP LightRT.FP.Binary32

/-- Half the smallest subnormal quantum. -/
noncomputable def eta : ℝ := (2:ℝ)^(-150:ℤ)

theorem eta_pos : 0 < eta := by unfold eta; positivity

variable (R : RoundingModel)

set_option maxHeartbeats 800000 in
/-- `num_err` with the range-free absolute error: five roundings (3 products,
    2 sums) each gain at most `eta`. -/
theorem num_err_total (hu : R.u ≤ 1 / 1000) (p0 p1 p2 E0 E1 E2 b0 b1 b2 : ℝ)
    (b0n : 0 ≤ b0) (b1n : 0 ≤ b1) (b2n : 0 ≤ b2)
    (q0 : |p0 - E0| ≤ R.u * b0 + eta) (q1 : |p1 - E1| ≤ R.u * b1 + eta)
    (q2 : |p2 - E2| ≤ R.u * b2 + eta)
    (a0 : |p0| ≤ (1 + R.u) * b0 + eta) (a1 : |p1| ≤ (1 + R.u) * b1 + eta)
    (a2 : |p2| ≤ (1 + R.u) * b2 + eta)
    (e1 : |R.fl (p0 + p1) - (p0 + p1)| ≤ R.u * |p0 + p1| + eta)
    (eN : |R.fl (R.fl (p0 + p1) + p2) - (R.fl (p0 + p1) + p2)| ≤
      R.u * |R.fl (p0 + p1) + p2| + eta) :
    |R.fl (R.fl (p0 + p1) + p2) - (E0 + E1 + E2)| ≤
      4 * R.u * (b0 + b1 + b2) + 8 * eta := by
  have u0 := R.u_pos
  have hu' : R.u ≤ (0.001 : ℝ) := by linarith
  have un : R.u ≤ 1 := by linarith
  have en := eta_pos
  have ub0 : R.u * b0 ≤ 0.001 * b0 := mul_le_mul_of_nonneg_right hu' b0n |>.trans (by linarith)
  have ub1 : R.u * b1 ≤ 0.001 * b1 := mul_le_mul_of_nonneg_right hu' b1n |>.trans (by linarith)
  have ub2 : R.u * b2 ≤ 0.001 * b2 := mul_le_mul_of_nonneg_right hu' b2n |>.trans (by linarith)
  have as1 : |p0 + p1| ≤ 1.001 * (b0 + b1) + 2 * eta := by
    have := abs_add_le p0 p1
    have e0 : (1 + R.u) * b0 = b0 + R.u * b0 := by ring
    have e1 : (1 + R.u) * b1 = b1 + R.u * b1 := by ring
    linarith
  have es1 : |R.fl (p0 + p1) - (p0 + p1)| ≤ R.u * (1.001 * (b0 + b1) + 2 * eta) + eta := by
    have := mul_le_mul_of_nonneg_left as1 u0.le
    linarith
  have hb01 : 0 ≤ b0 + b1 := by linarith
  have h1 : R.u * (b0 + b1) ≤ 0.001 * (b0 + b1) := mul_le_mul_of_nonneg_right hu' hb01
  have h2 : R.u * eta ≤ eta := by nlinarith [u0.le, un, en]
  have small : R.u * (1.001 * (b0 + b1) + 2 * eta) + eta ≤
      0.002 * (b0 + b1) + 3 * eta := by nlinarith [h1, h2, hb01]
  have hf : |R.fl (p0 + p1)| ≤ 1.003 * (b0 + b1) + 6 * eta := by
    have := abs_sub_abs_le_abs_sub (R.fl (p0 + p1)) (p0 + p1)
    nlinarith [as1, es1, small]
  have hb2 : (1 + R.u) * b2 ≤ 1.001 * b2 := by nlinarith [hu', b2n]
  have a2p : |p2| ≤ 1.001 * b2 + 6 * eta := by nlinarith [a2, hb2, en]
  have as2 : |R.fl (p0 + p1) + p2| ≤
      1.003 * (b0 + b1) + 1.001 * b2 + 12 * eta := by
    have := abs_add_le (R.fl (p0 + p1)) p2
    nlinarith [this, hf, a2p]
  have eN' : |R.fl (R.fl (p0 + p1) + p2) - (R.fl (p0 + p1) + p2)| ≤
      R.u * (1.003 * (b0 + b1) + 1.001 * b2 + 12 * eta) + eta := by
    have := mul_le_mul_of_nonneg_left as2 u0.le
    linarith
  have eP : |(p0 - E0) + (p1 - E1) + (p2 - E2)| ≤
      R.u * b0 + R.u * b1 + R.u * b2 + 3 * eta := by
    have := abs_add_three (p0 - E0) (p1 - E1) (p2 - E2)
    linarith
  have key : |R.fl (R.fl (p0 + p1) + p2) - (E0 + E1 + E2)| ≤
      (R.u * (1.001 * (b0 + b1) + 2 * eta) + eta) +
      (R.u * (1.003 * (b0 + b1) + 1.001 * b2 + 12 * eta) + eta) +
      (R.u * b0 + R.u * b1 + R.u * b2 + 3 * eta) := by
    calc |R.fl (R.fl (p0 + p1) + p2) - (E0 + E1 + E2)|
        = |(R.fl (R.fl (p0 + p1) + p2) - (R.fl (p0 + p1) + p2)) +
            (R.fl (p0 + p1) - (p0 + p1)) +
            ((p0 - E0) + (p1 - E1) + (p2 - E2))| := by ring_nf
      _ ≤ |R.fl (R.fl (p0 + p1) + p2) - (R.fl (p0 + p1) + p2)| +
            |R.fl (p0 + p1) - (p0 + p1)| +
            |(p0 - E0) + (p1 - E1) + (p2 - E2)| := abs_add_three _ _ _
      _ ≤ _ := by linarith [eN', es1, eP]
  nlinarith [key, ub0, ub1, ub2, un, en]

theorem den_bounds_total (e0 e1 e2 : ℝ) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (h1 : |R.fl (e0 + e1) - (e0 + e1)| ≤ R.u * (e0 + e1) + eta)
    (h2 : |R.fl (R.fl (e0 + e1) + e2) - (R.fl (e0 + e1) + e2)| ≤
      R.u * |R.fl (e0 + e1) + e2| + eta) :
    0 ≤ R.fl (R.fl (e0 + e1) + e2) ∧
      (1 - R.u) * ((1 - R.u) * (e0 + e1 + e2)) - 4 * eta ≤
        R.fl (R.fl (e0 + e1) + e2) ∧
      R.fl (R.fl (e0 + e1) + e2) ≤ (1 + R.u) * ((1 + R.u) * (e0 + e1 + e2)) + 4 * eta := by
  have u0 := R.u_pos
  have un : R.u ≤ 1 := R.u_lt_one.le
  have en := eta_pos
  have huη : R.u * eta ≤ eta := by nlinarith [u0.le, un, en]
  have hun : 0 ≤ 1 - R.u := by linarith
  have hup : 0 ≤ 1 + R.u := by linarith
  have hsum : 0 ≤ e0 + e1 := by linarith
  set A := e0 + e1 + e2 with hA
  set d1 := R.fl (e0 + e1) with hd1
  have hd1lo : (1 - R.u) * (e0 + e1) - eta ≤ d1 := by
    have := (abs_le.1 h1).1; linarith
  have hd1hi : d1 ≤ (1 + R.u) * (e0 + e1) + eta := by
    have := (abs_le.1 h1).2; linarith
  have hs : 0 ≤ d1 + e2 := by
    have : 0 ≤ d1 := by rw [hd1]; exact R.fl_nonneg hsum
    linarith
  have hDlo : (1 - R.u) * (d1 + e2) - eta ≤ R.fl (d1 + e2) := by
    have := (abs_le.1 h2).1
    rw [abs_of_nonneg hs] at this
    linarith
  have hDhi : R.fl (d1 + e2) ≤ (1 + R.u) * (d1 + e2) + eta := by
    have := (abs_le.1 h2).2
    rw [abs_of_nonneg hs] at this
    linarith
  have lower : (1 - R.u) * ((1 - R.u) * A) - 4 * eta ≤ R.fl (d1 + e2) := by
    have hl : (1 - R.u) * ((1 - R.u) * (e0 + e1) + e2) - eta ≤ (1 - R.u) * (d1 + e2) := by
      have := mul_le_mul_of_nonneg_left hd1lo hun
      have : (1 - R.u) * ((1 - R.u) * (e0 + e1) - eta + e2) =
          (1 - R.u) * ((1 - R.u) * (e0 + e1) + e2) - (1 - R.u) * eta := by ring
      nlinarith [this, mul_nonneg hun en.le]
    have he2 : (1 - R.u) * ((1 - R.u) * A) ≤ (1 - R.u) * ((1 - R.u) * (e0 + e1) + e2) := by
      apply mul_le_mul_of_nonneg_left _ hun
      have h1m : (1 - R.u) * e2 ≤ e2 := by nlinarith
      have : (1 - R.u) * (e0 + e1 + e2) = (1 - R.u) * (e0 + e1) + (1 - R.u) * e2 := by ring
      rw [hA, this]; linarith
    have heta : (1 - R.u) * eta ≤ eta := by nlinarith [huη, hun, en]
    linarith [hDlo, hl, he2, heta, mul_nonneg hun (le_of_lt en)]
  have upper : R.fl (d1 + e2) ≤ (1 + R.u) * ((1 + R.u) * A) + 4 * eta := by
    have hh : d1 + e2 ≤ (1 + R.u) * (e0 + e1) + e2 + eta := by linarith [hd1hi]
    have hu2 : R.fl (d1 + e2) ≤ (1 + R.u) * ((1 + R.u) * (e0 + e1) + e2 + eta) + eta := by
      have := mul_le_mul_of_nonneg_left hh hup
      linarith [hDhi, this]
    have he2 : (1 + R.u) * ((1 + R.u) * (e0 + e1) + e2 + eta) + eta ≤
        (1 + R.u) * ((1 + R.u) * A) + 4 * eta := by
      have h1p : e2 ≤ (1 + R.u) * e2 := by nlinarith
      have h2m : (1 + R.u) * eta ≤ 2 * eta := by nlinarith [huη, hup, en]
      have : (1 + R.u) * ((1 + R.u) * (e0 + e1) + e2 + eta) + eta =
          (1 + R.u) * ((1 + R.u) * (e0 + e1)) + (1 + R.u) * e2 +
            (1 + R.u) * eta + eta := by ring
      have hAe : (1 + R.u) * ((1 + R.u) * A) =
          (1 + R.u) * ((1 + R.u) * (e0 + e1)) + (1 + R.u) * ((1 + R.u) * e2) := by
        rw [hA]; ring
      have hcoef : (1 + R.u) * e2 ≤ (1 + R.u) * ((1 + R.u) * e2) := by
        have := mul_le_mul_of_nonneg_left h1p hup
        linarith
      linarith
    linarith
  exact ⟨R.fl_nonneg (by linarith), lower, upper⟩


end LightRT.Robust
