/-
  The Möller–Trumbore `t`-error bound (item 3b, final composition).

  Composes `mt_det_err_total` and `mt_num_err_total` (the determinant and
  numerator stages of `tri_mt_one`/`tri_packet4_tri`, op order
  `-ffp-contract=off`) with the division rounding to a range-free error
  bound for

    t = (e2 ⬝ᵥ q) / det,   q = tv × e1,   det = e1 · (d × e2),   tv = o − v0.

  Side conditions (hypotheses, mirroring `woop_t_err_total_model`'s):

  * the coordinate magnitudes are bounded (`|dᵢ|, |tvᵢ| ≤ M`, `|e1ᵢ| ≤ A`,
    `|e2ᵢ| ≤ B`);
  * the exact determinant is bounded below by `a0 > 0` (the positive-det
    class; the negative class is the same theorem with the ray's direction
    flipped, `det ↦ −det` under `d ↦ −d`);
  * the F-model's determinant stays within `a0/2` of the exact one
    (`hεD : mtDetErr M A B ≤ a0 / 2`) — so the rounded `det` is positive and
    within a factor of 2 of the exact one.

  The bound is

      |t_model − t_exact| ≤ (12u·BMA + (2u+2)·mtNumErr M A B) / a0 + η
                            + 12·BMA·mtDetErr M A B / a0²

  — it degrades linearly in `1 / a0` as the determinant approaches zero,
  which is the correct behavior for a non-watertight kernel (MT is not
  watertight, so the bound buys no conservativity for `EXACT_NEAREST`-style
  pruning; `mtcheck` remains the empirical check).
-/
import LightRT.Robust.MTDot

namespace LightRT.Robust
open LightRT.FP LightRT.FP.Binary32 Geom

set_option maxHeartbeats 1600000

/-- **Möller–Trumbore `t` error, composed** (range-free). -/
theorem mt_t_fl_err_total_model (d0 d1 d2 e10 e11 e12 e20 e21 e22 tv0 tv1 tv2 : ℝ)
    (M A B : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd0 : |d0| ≤ M) (hd1 : |d1| ≤ M) (hd2 : |d2| ≤ M)
    (h10 : |e10| ≤ A) (h11 : |e11| ≤ A) (h12 : |e12| ≤ A)
    (h20 : |e20| ≤ B) (h21 : |e21| ≤ B) (h22 : |e22| ≤ B)
    (ht0 : |tv0| ≤ M) (ht1 : |tv1| ≤ M) (ht2 : |tv2| ≤ M)
    (a0 : ℝ) (a0pos : 0 < a0)
    (hA0 : a0 ≤ e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
      e12 * (d0 * e21 - d1 * e20))
    (hεD : mtDetErr M A B ≤ a0 / 2) :
    |model.fl (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
         model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
        model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) /
        model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
        model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
        model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) -
      (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) +
        e22 * (tv0 * e11 - tv1 * e10)) /
        (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20))| ≤
      (12 * model.u * B * M * A + (2 * model.u + 2) * mtNumErr M A B) / a0 + eta +
        12 * B * M * A * mtDetErr M A B / a0 ^ 2 := by
  have hu := model_u_lt1000
  have hu0 := model.u_pos
  have hMA : 0 ≤ M * A := mul_nonneg hM hA
  have hMB : 0 ≤ B * M := mul_nonneg hB hM
  have hM_pos : 0 ≤ 6 * B * M * A := by nlinarith [mul_nonneg hMB hA]
  have hεM_pos : 0 ≤ mtNumErr M A B := by
    unfold mtNumErr
    have h1 : 0 ≤ M * A := hMA
    have h2 : 0 ≤ M * A * (1 + model.u) + eta := by nlinarith [h1, model.u_lt_one.le, eta_pos, hu0]
    have h3 : 0 ≤ (M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta)) * (1 + model.u) + eta := by
      nlinarith [h2, eta_pos, model.u_lt_one.le, hu0]
    have h4 : 0 ≤ model.u * B * ((M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta)) * (1 + model.u) + eta) :=
      mul_nonneg (mul_nonneg hu0.le hB) h3
    have h5 : 0 ≤ model.u * (M * A + M * A) := mul_nonneg hu0.le (by nlinarith [h1])
    have h6 : 0 ≤ B * (7 * model.u * (M * A + M * A) + 12 * eta) :=
      mul_nonneg hB (by nlinarith [h5, eta_pos])
    nlinarith [h4, h6, eta_pos]
  have hεD_pos : 0 ≤ mtDetErr M A B := by
    unfold mtDetErr
    have h1 : 0 ≤ M * B := mul_nonneg hM hB
    have h2 : 0 ≤ M * B * (1 + model.u) + eta := by nlinarith [h1, model.u_lt_one.le, eta_pos, hu0]
    have h3 : 0 ≤ (M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta)) * (1 + model.u) + eta := by
      nlinarith [h2, eta_pos, model.u_lt_one.le, hu0]
    have h4 : 0 ≤ model.u * A * ((M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta)) * (1 + model.u) + eta) :=
      mul_nonneg (mul_nonneg hu0.le hA) h3
    have h5 : 0 ≤ model.u * (M * B + M * B) := mul_nonneg hu0.le (by nlinarith [h1])
    have h6 : 0 ≤ A * (7 * model.u * (M * B + M * B) + 12 * eta) :=
      mul_nonneg hA (by nlinarith [h5, eta_pos])
    nlinarith [h4, h6, eta_pos]
  -- stage bounds
  have hDet := mt_det_err_total d0 d1 d2 e10 e11 e12 e20 e21 e22 M A B hM hA hB
    hd0 hd1 hd2 h10 h11 h12 h20 h21 h22
  have hNum := mt_num_err_total e20 e21 e22 tv0 tv1 tv2 e10 e11 e12 M A B hM hA hB
    h20 h21 h22 ht0 ht1 ht2 h10 h11 h12
  -- exact-magnitude bound on the exact numerator
  have hEbound : |e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) +
        e22 * (tv0 * e11 - tv1 * e10)| ≤ 6 * B * M * A := by
    have h00 : |e20 * (tv1 * e12 - tv2 * e11)| ≤ B * (M * A + M * A) := by
      rw [abs_mul]
      have h1 : |tv1 * e12| ≤ M * A := by
        rw [abs_mul]; exact mul_le_mul ht1 h12 (abs_nonneg _) hM
      have h2 : |tv2 * e11| ≤ M * A := by
        rw [abs_mul]; exact mul_le_mul ht2 h11 (abs_nonneg _) hM
      have h3 : |tv1 * e12 - tv2 * e11| ≤ M * A + M * A := by
        have h := abs_sub_le'' (tv1 * e12) (tv2 * e11)
        nlinarith [h, h1, h2]
      exact mul_le_mul h20 h3 (abs_nonneg _) hB
    have h01 : |e21 * (tv2 * e10 - tv0 * e12)| ≤ B * (M * A + M * A) := by
      rw [abs_mul]
      have h1 : |tv2 * e10| ≤ M * A := by
        rw [abs_mul]; exact mul_le_mul ht2 h10 (abs_nonneg _) hM
      have h2 : |tv0 * e12| ≤ M * A := by
        rw [abs_mul]; exact mul_le_mul ht0 h12 (abs_nonneg _) hM
      have h3 : |tv2 * e10 - tv0 * e12| ≤ M * A + M * A := by
        have h := abs_sub_le'' (tv2 * e10) (tv0 * e12)
        nlinarith [h, h1, h2]
      exact mul_le_mul h21 h3 (abs_nonneg _) hB
    have h02 : |e22 * (tv0 * e11 - tv1 * e10)| ≤ B * (M * A + M * A) := by
      rw [abs_mul]
      have h1 : |tv0 * e11| ≤ M * A := by
        rw [abs_mul]; exact mul_le_mul ht0 h11 (abs_nonneg _) hM
      have h2 : |tv1 * e10| ≤ M * A := by
        rw [abs_mul]; exact mul_le_mul ht1 h10 (abs_nonneg _) hM
      have h3 : |tv0 * e11 - tv1 * e10| ≤ M * A + M * A := by
        have h := abs_sub_le'' (tv0 * e11) (tv1 * e10)
        nlinarith [h, h1, h2]
      exact mul_le_mul h22 h3 (abs_nonneg _) hB
    have h := abs_add_three (e20 * (tv1 * e12 - tv2 * e11))
      (e21 * (tv2 * e10 - tv0 * e12)) (e22 * (tv0 * e11 - tv1 * e10))
    nlinarith [h, h00, h01, h02]
  -- the F-model denominator is positive and within a factor of 2
  have hA0' : 0 < e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
      e12 * (d0 * e21 - d1 * e20) := lt_of_lt_of_le a0pos hA0
  have hDle : e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
        e12 * (d0 * e21 - d1 * e20) - mtDetErr M A B ≤
      model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
        model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
        model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) := by
    have h := (abs_le.mp hDet).1
    linarith
  have hDpos : 0 < model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
        model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
        model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) := by
    have h := hDle
    nlinarith [hA0, hεD, a0pos]
  have hD2 : a0 / 2 ≤ model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
        model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
        model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) := by
    have h := hDle
    nlinarith [hA0, hεD]
  -- bound |N / D|
  have hNbound : |model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
        model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
        model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10))))| ≤
      6 * B * M * A + mtNumErr M A B := by
    have h4 := abs_add_le
      (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
        model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
        model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) -
        (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)))
      (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10))
    have e : model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) =
        (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) -
          (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10))) +
        (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) := by
      ring
    rw [e]
    nlinarith [h4, hNum, hEbound]
  have hND : |model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
        model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
        model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) /
        model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
        model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
        model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))| ≤
      2 * (6 * B * M * A + mtNumErr M A B) / a0 := by
    rw [abs_div, abs_of_pos hDpos]
    have hden : 0 < model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) := hDpos
    have hq : 0 < a0 / 2 := by linarith
    have h1 : (6 * B * M * A + mtNumErr M A B) /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) ≤
        (6 * B * M * A + mtNumErr M A B) / (a0 / 2) := by
      have hMEp : 0 ≤ 6 * B * M * A + mtNumErr M A B := add_nonneg hM_pos hεM_pos
      exact div_le_div_of_nonneg_left hMEp hq hD2
    have h2 : (6 * B * M * A + mtNumErr M A B) / (a0 / 2) =
        2 * (6 * B * M * A + mtNumErr M A B) / a0 := by
      field_simp
    have h6 : |model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10))))| /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) ≤
        (6 * B * M * A + mtNumErr M A B) /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) := by
      rw [div_le_iff₀ hden]
      have h2 := div_mul_cancel₀ (6 * B * M * A + mtNumErr M A B) hden.ne'
      nlinarith [hNbound, h2]
    calc |model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10))))| /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))
        ≤ (6 * B * M * A + mtNumErr M A B) /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) := h6
      _ ≤ (6 * B * M * A + mtNumErr M A B) / (a0 / 2) := h1
      _ = 2 * (6 * B * M * A + mtNumErr M A B) / a0 := h2
  -- the division rounding
  have hq := model_abs_err_total
    (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
        model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
        model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) /
      model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
        model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
        model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))))
  rw [← eta_eq_def] at hq
  have hFl : |model.fl (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) -
      model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) / model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))| ≤
      2 * model.u * (6 * B * M * A + mtNumErr M A B) / a0 + eta := by
    have h2 := mul_le_mul_of_nonneg_left hND hu0.le
    have h3 : model.u * (2 * (6 * B * M * A + mtNumErr M A B) / a0) =
        2 * model.u * (6 * B * M * A + mtNumErr M A B) / a0 := by ring
    nlinarith [hq, h2, h3, eta_pos]
  -- the difference decomposition
  have habs := abs_add_le
    (model.fl (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) -
      model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) / model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))))
    (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) / model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) -
      (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) /
        (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)))
  -- |N*A - E*D| bound
  have hprod : |model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
        model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
        model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) *
        (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) -
      (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) *
        model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
        model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
        model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))| ≤
      mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
          e12 * (d0 * e21 - d1 * e20)) +
        6 * B * M * A * mtDetErr M A B := by
    have e : model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) *
          (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) -
        (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) *
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) =
        (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) -
          (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10))) *
          (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) +
        (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) *
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) -
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) := by ring
    rw [e]
    have h1 : |(model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) -
          (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10))) *
          (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20))| ≤
        mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
          e12 * (d0 * e21 - d1 * e20)) := by
      rw [abs_mul, abs_of_pos hA0']
      exact mul_le_mul (hNum) (le_refl _) hA0'.le hεM_pos
    have h2 : |(e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) *
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) -
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))))| ≤
        6 * B * M * A * mtDetErr M A B := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul hEbound (hDet) (abs_nonneg _) hM_pos
    have h := abs_add_le
      ((model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) -
          (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10))) *
          (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)))
      ((e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) *
        ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) -
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))))
    nlinarith [h, h1, h2]
  -- |N/D - E/A| bound
  have hND' : |model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
        model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
        model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) /
        model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
        model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
        model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) -
      (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) /
        (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20))| ≤
      2 * mtNumErr M A B / a0 + 12 * B * M * A * mtDetErr M A B / a0 ^ 2 := by
    have heq : model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) -
        (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) /
          (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) =
        (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) *
          (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) -
        (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) *
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) /
        ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) := by
      have h1 : (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) /
            (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) =
          ((e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) *
            model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
              model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
              model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) /
            ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
              model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
                model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
                model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) := by
        rw [div_eq_div_iff hA0'.ne' (mul_ne_zero hA0'.ne' hDpos.ne')]
        ring
      have h2 : model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
            model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
            model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
            model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
            model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) =
          (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
            model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
            model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) *
            (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20))) /
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
            model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
              model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
              model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) := by
        rw [div_eq_div_iff hDpos.ne' (mul_ne_zero hA0'.ne' hDpos.ne')]
        ring
      rw [h1, h2, ← sub_div]
    rw [heq, abs_div]
    have hden_pos : 0 < (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
        e12 * (d0 * e21 - d1 * e20)) *
        model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
        model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
        model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) :=
      mul_pos hA0' hDpos
    rw [abs_of_pos hden_pos]
    have hden_half : (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
          e12 * (d0 * e21 - d1 * e20)) * (a0 / 2) ≤
        (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) := by
      apply mul_le_mul_of_nonneg_left hD2 hA0'.le
    have hpos_num : 0 ≤ mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
        e12 * (d0 * e21 - d1 * e20)) + 6 * B * M * A * mtDetErr M A B := by
      have h1 : 0 ≤ mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
          e12 * (d0 * e21 - d1 * e20)) := mul_nonneg hεM_pos hA0'.le
      have h2 : 0 ≤ 6 * B * M * A * mtDetErr M A B := mul_nonneg hM_pos hεD_pos
      linarith
    have h1 : |model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) *
          (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) -
        (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) *
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))| /
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
            model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
            model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
            model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) ≤
        (mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20)) + 6 * B * M * A * mtDetErr M A B) /
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
            model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
            model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
            model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) := by
      rw [div_le_iff₀ hden_pos]
      have h2 := div_mul_cancel₀
        (mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
          e12 * (d0 * e21 - d1 * e20)) + 6 * B * M * A * mtDetErr M A B) hden_pos.ne'
      nlinarith [hprod, h2]
    have h2 : (mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20)) + 6 * B * M * A * mtDetErr M A B) /
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
            model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
            model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
            model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) ≤
        (mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20)) + 6 * B * M * A * mtDetErr M A B) /
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
            (a0 / 2)) := by
      have hQ : 0 < (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
          e12 * (d0 * e21 - d1 * e20)) * (a0 / 2) := by
        have hhalf : 0 < a0 / 2 := by linarith [a0pos]
        exact mul_pos hA0' hhalf
      have h3 := div_le_div_of_nonneg_left hpos_num hQ hden_half
      exact h3
    have h3 : (mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20)) + 6 * B * M * A * mtDetErr M A B) /
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
            (a0 / 2)) =
        2 * mtNumErr M A B / a0 + 12 * B * M * A * mtDetErr M A B /
          (a0 * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20))) := by
      have hhalf : (0:ℝ) < a0 / 2 := by linarith [a0pos]
      have hdet' : e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
          e12 * (d0 * e21 - d1 * e20) ≠ 0 := ne_of_gt hA0'
      have e1 : (2 * mtNumErr M A B / a0) * ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20)) * (a0 / 2)) =
          mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20)) := by
        rw [div_mul_eq_mul_div,
          show (2 : ℝ) * mtNumErr M A B * ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
              e12 * (d0 * e21 - d1 * e20)) * (a0 / 2)) =
            mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
              e12 * (d0 * e21 - d1 * e20)) * a0 from by ring,
          mul_comm (mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20))) a0, mul_div_cancel_left₀ _ a0pos.ne']
      have e2 : (12 * B * M * A * mtDetErr M A B / (a0 * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20)))) * ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20)) * (a0 / 2)) =
          6 * B * M * A * mtDetErr M A B := by
        rw [div_mul_eq_mul_div,
          show (12 : ℝ) * B * M * A * mtDetErr M A B * ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
              e12 * (d0 * e21 - d1 * e20)) * (a0 / 2)) =
            6 * B * M * A * mtDetErr M A B * (a0 * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
              e12 * (d0 * e21 - d1 * e20))) from by ring,
          mul_comm (6 * B * M * A * mtDetErr M A B) (a0 * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20))), mul_div_cancel_left₀ _ (mul_ne_zero a0pos.ne' hdet')]
      rw [div_eq_iff (mul_ne_zero hdet' hhalf.ne')]
      rw [add_mul, e1, e2]
    have h4 : 2 * mtNumErr M A B / a0 + 12 * B * M * A * mtDetErr M A B /
          (a0 * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20))) ≤
        2 * mtNumErr M A B / a0 + 12 * B * M * A * mtDetErr M A B / a0 ^ 2 := by
      have h6 : a0 * a0 ≤ a0 * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
          e12 * (d0 * e21 - d1 * e20)) := by
        apply mul_le_mul_of_nonneg_left hA0 a0pos.le
      have h7 : 12 * B * M * A * mtDetErr M A B / (a0 *
          (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20))) ≤
          12 * B * M * A * mtDetErr M A B / a0 ^ 2 := by
        rw [pow_two]
        apply div_le_div_of_nonneg_left _ (mul_pos a0pos a0pos) h6
        nlinarith [hM_pos, hεD_pos]
      linarith
    calc |model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) *
          (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) -
        (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) *
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))| /
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
            model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
            model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
            model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))))
        ≤ (mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20)) + 6 * B * M * A * mtDetErr M A B) /
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
            model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
            model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
            model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) := h1
      _ ≤ (mtNumErr M A B * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
            e12 * (d0 * e21 - d1 * e20)) + 6 * B * M * A * mtDetErr M A B) /
          ((e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) *
            (a0 / 2)) := h2
      _ = 2 * mtNumErr M A B / a0 + 12 * B * M * A * mtDetErr M A B /
          (a0 * (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20))) := h3
      _ ≤ 2 * mtNumErr M A B / a0 + 12 * B * M * A * mtDetErr M A B / a0 ^ 2 := h4
  -- final assembly
  have hgoal : model.fl (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) -
      (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) /
        (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20)) =
      (model.fl (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) /
          model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) -
        model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) / model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))))) +
      (model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
          model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
          model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) / model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
          model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
          model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) -
        (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) + e22 * (tv0 * e11 - tv1 * e10)) /
          (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) + e12 * (d0 * e21 - d1 * e20))) := by
    simp only [sub_eq_add_neg]
    abel

  have hsum : 2 * model.u * (6 * B * M * A + mtNumErr M A B) / a0 + 2 * mtNumErr M A B / a0 =
      (12 * model.u * B * M * A + (2 * model.u + 2) * mtNumErr M A B) / a0 := by
    field_simp [a0pos.ne']
    ring
  rw [hgoal]
  linarith [habs, hFl, hND', hsum]

end LightRT.Robust
