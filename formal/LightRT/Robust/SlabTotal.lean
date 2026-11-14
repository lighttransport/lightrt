/-
  Range-free analog of `Robust/Slab.fpT_rel` / `slab_t_err`: the error of one
  scalar slab parameter `fl(fl(x − o) · fl(1/d))` with **no** `InRange`
  hypotheses, by the same `η = 2⁻¹⁵⁰` absolute-error method as `Robust/Total.lean`
  (Woop `t` bound).

  The proven bound is

    |fpT − (x − o)/d| ≤ 4u·|(x − o)/d| + 4(1 + u)(|x − o| + 1/|d|)·η
      + 2(1 + u)η² + η.

  The price vs. the `InRange` bound (`γ₃·|t|`) is the `η·(|q| + 1/|d|)` slack:
  for tiny `d` the absolute error dominates, exactly the `η/a0` regime of the
  Woop `t` bound and of the `1e-37` dilation floor. Note the degenerate
  `tangent ray` case: no `K` can make the *inflated* slab test exact when the
  segment only touches the box's plane at grazing angle, so a range-free
  `slab_no_false_miss` needs an explicit non-degeneracy floor and is NOT
  attempted here (see PLAN.md M22).
-/
import LightRT.Robust.Slab
import LightRT.Robust.Total
import LightRT.FP.TotalErr

namespace LightRT.Robust
open LightRT.FP LightRT.FP.Binary32 Geom

set_option maxHeartbeats 1600000 in
/-- **Total (range-free) error of one scalar slab parameter.** For the binary32
    model: each rounding contributes at most `u|x| + η`. -/
theorem fpT_abs_err_total (r : Ray) (x : ℝ) (i : Fin 3) (hd : r.d i ≠ 0) :
    |fpT model r x i - (x - r.o i) / r.d i| ≤
      4 * model.u * |(x - r.o i) / r.d i| +
      4 * (1 + model.u) * (|x - r.o i| + 1 / |r.d i|) * eta +
      2 * (1 + model.u) * eta ^ 2 + eta := by
  set q := x - r.o i with hqX
  set A := |q| with hA
  set B := |1 / r.d i| with hB
  set u := model.u
  have hu0 : 0 < u := model.u_pos
  have hu1 : u ≤ 1 := le_of_lt (lt_of_lt_of_le model.u_lt_one (by norm_num))
  have u2 : 0 ≤ u := hu0.le
  have en : 0 < eta := eta_pos
  have en0 : 0 ≤ eta := en.le
  have hB' : 0 ≤ B := abs_nonneg _
  have hd' : 0 < |r.d i| := abs_pos.2 hd
  have hBo : B = 1 / |r.d i| := by rw [hB, abs_div, abs_one]
  -- the three roundings, range-free
  have hs : |model.fl q - q| ≤ u * A + eta := by
    have h := model_abs_err_total q
    rw [show (2:ℝ)^(-150:ℤ) = eta from rfl, ← hA] at h
    exact h
  have hi : |model.fl (1 / r.d i) - 1 / r.d i| ≤ u * B + eta := by
    have h := model_abs_err_total (1 / r.d i)
    rw [show (2:ℝ)^(-150:ℤ) = eta from rfl, abs_div, abs_one, ← hBo] at h
    exact h
  have hu' : u ≤ 1 / 1000 := by
    show model.u ≤ 1 / 1000
    unfold model; norm_num [zpow_neg]
  have hsA : |model.fl q| ≤ (1 + u) * A + eta := by
    have hadd := abs_add_le q (model.fl q - q)
    rw [show q + (model.fl q - q) = model.fl q by ring] at hadd
    rw [← hA] at hadd
    linarith [hadd, hs, hA]
  have hiB : |model.fl (1 / r.d i)| ≤ (1 + u) * B + eta := by
    have hadd := abs_add_le (1 / r.d i) (model.fl (1 / r.d i) - 1 / r.d i)
    rw [show 1 / r.d i + (model.fl (1 / r.d i) - 1 / r.d i) = model.fl (1 / r.d i) by ring] at hadd
    rw [← hB] at hadd
    linarith [hadd, hi, hB]
  have h1 : |model.fl q * model.fl (1 / r.d i)| ≤
      ((1 + u) * A + eta) * ((1 + u) * B + eta) := by
    rw [abs_mul]
    apply mul_le_mul hsA hiB (abs_nonneg _) (by positivity)
  have hp : |model.fl (model.fl q * model.fl (1 / r.d i)) -
        model.fl q * model.fl (1 / r.d i)| ≤
        u * ((1 + u) * A + eta) * ((1 + u) * B + eta) + eta := by
    have h := model_abs_err_total (model.fl q * model.fl (1 / r.d i))
    rw [show (2:ℝ)^(-150:ℤ) = eta from rfl] at h
    have hb := mul_le_mul_of_nonneg_left h1 u2
    linarith [h, hb]
  have hsq : |model.fl q * model.fl (1 / r.d i) - q * (1 / r.d i)| ≤
      (u * A + eta) * ((1 + u) * B + eta) + A * (u * B + eta) := by
    have e : (model.fl q * model.fl (1 / r.d i) - q * (1 / r.d i)) =
        (model.fl q - q) * model.fl (1 / r.d i) + q * (model.fl (1 / r.d i) - 1 / r.d i) := by ring
    rw [e]
    have h1' : |(model.fl q - q) * model.fl (1 / r.d i)| ≤ (u * A + eta) * ((1 + u) * B + eta) := by
      rw [abs_mul]
      exact mul_le_mul hs hiB (abs_nonneg _) (by positivity)
    have h2 : |q * (model.fl (1 / r.d i) - 1 / r.d i)| ≤ A * (u * B + eta) := by
      rw [abs_mul]
      exact mul_le_mul (le_refl A) hi (abs_nonneg _) (by positivity)
    have hadd := abs_add_le ((model.fl q - q) * model.fl (1 / r.d i))
      (q * (model.fl (1 / r.d i) - 1 / r.d i))
    linarith [h1', h2, hadd]
  -- expanded products
  have e1 : u * ((1 + u) * A + eta) * ((1 + u) * B + eta) =
      u * (1 + u) ^ 2 * (A * B) + u * (1 + u) * (A * eta) + u * (1 + u) * (B * eta) +
        u * eta ^ 2 := by ring
  have e2 : (u * A + eta) * ((1 + u) * B + eta) =
      u * (1 + u) * (A * B) + u * (A * eta) + (1 + u) * (B * eta) + eta ^ 2 := by ring
  have e3 : A * (u * B + eta) = u * (A * B) + A * eta := by ring
  have e4 : u * (3 + 3 * u + u ^ 2) ≤ 4 * u := by nlinarith [hu', u2]
  have e5 : (1 + u) ^ 2 ≤ 4 * (1 + u) := by
    have h : 0 ≤ 4 * (1 + u) - (1 + u) ^ 2 := by nlinarith [hu1, u2]
    linarith [h]
  have e7 : u * (1 + u) ^ 2 + u * (1 + u) + u ≤ 4 * u := by
    have : u * (1 + u) ^ 2 + u * (1 + u) + u = u * (3 + 3 * u + u ^ 2) := by ring
    linarith [e4]
  have e8 : u * (1 + u) + u + 1 ≤ 4 * (1 + u) := by
    have : u * (1 + u) + u + 1 = (1 + u) ^ 2 := by ring
    linarith [e5]
  have e9 : u * (1 + u) + (1 + u) ≤ 4 * (1 + u) := by
    have : u * (1 + u) + (1 + u) = (1 + u) ^ 2 := by ring
    linarith [e5]
  have e10 : (1 + u) ≤ 2 * (1 + u) := by nlinarith [u2]
  have hp' : |model.fl (model.fl q * model.fl (1 / r.d i)) -
        model.fl q * model.fl (1 / r.d i)| ≤
        u * (1 + u) ^ 2 * (A * B) + u * (1 + u) * (A * eta) + u * (1 + u) * (B * eta) +
          u * eta ^ 2 + eta := by
    rw [e1] at hp; linarith [hp]
  have hsq' : |model.fl q * model.fl (1 / r.d i) - q * (1 / r.d i)| ≤
      u * (1 + u) * (A * B) + u * (A * eta) + (1 + u) * (B * eta) + eta ^ 2 +
        u * (A * B) + A * eta := by
    rw [e2, e3] at hsq; linarith [hsq]
  set X := model.fl q * model.fl (1 / r.d i) with hX
  have hpT : fpT model r x i = model.fl X := by
    simp only [fpT, fpInvd, RoundingModel.mul, RoundingModel.sub, RoundingModel.div]
    rw [← hqX, hX]
  have hBi : B = |r.d i|⁻¹ := by rw [hB, abs_div, abs_one, one_div]
  have habs : A * B = |q / r.d i| := by
    rw [div_eq_mul_inv q, abs_mul, abs_inv, hA, hBi]
  have hsubs : q / r.d i = q * (1 / r.d i) := by rw [div_eq_mul_inv q, one_div]
  have htri : |model.fl X - q * (1 / r.d i)| ≤
      |model.fl X - X| + |X - q * (1 / r.d i)| := by
    have e : model.fl X - q * (1 / r.d i) =
        (model.fl X - X) + (X - q * (1 / r.d i)) := by ring
    rw [e]
    exact abs_add_le _ _
  have hAB' : u * (1 + u) ^ 2 * (A * B) + u * (1 + u) * (A * B) + u * (A * B) ≤
      4 * u * (A * B) := by
    have hm : 0 ≤ A * B := mul_nonneg (abs_nonneg _) hB'
    nlinarith [e7, hm]
  have hAe' : u * (1 + u) * (A * eta) + u * (A * eta) + A * eta ≤ 4 * (1 + u) * (A * eta) := by
    have hm : 0 ≤ A * eta := mul_nonneg (abs_nonneg _) en.le
    nlinarith [e8, hm]
  have hBe' : u * (1 + u) * (B * eta) + (1 + u) * (B * eta) ≤ 4 * (1 + u) * (B * eta) := by
    have hm : 0 ≤ B * eta := mul_nonneg hB' en.le
    nlinarith [e9, hm]
  have he' : u * eta ^ 2 + eta ^ 2 ≤ 2 * (1 + u) * eta ^ 2 := by
    have hm : 0 ≤ eta ^ 2 := sq_nonneg _
    nlinarith [e10, hm]
  calc |fpT model r x i - (x - r.o i) / r.d i|
      = |model.fl X - q / r.d i| := by rw [hpT, ← hqX]
    _ = |model.fl X - q * (1 / r.d i)| := by rw [hsubs]
    _ ≤ |model.fl X - X| + |X - q * (1 / r.d i)| := htri
    _ ≤ 4 * u * (A * B) + 4 * (1 + u) * (A + B) * eta + 2 * (1 + u) * eta ^ 2 + eta := by
        nlinarith [hp', hsq', hAB', hAe', hBe', he', hu1, en0]
    _ = 4 * u * |(x - r.o i) / r.d i| +
        4 * (1 + model.u) * (|x - r.o i| + 1 / |r.d i|) * eta +
        2 * (1 + model.u) * eta ^ 2 + eta := by
        rw [← habs, hA, hqX, hBo]

end LightRT.Robust
