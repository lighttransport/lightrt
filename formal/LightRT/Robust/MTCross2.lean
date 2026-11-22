/-
  Cross-product component error bound (item 3b, stage bound):

    |fl(fl a·fl c − fl b·fl d) − (a·c − b·d)|

  proved as three small pieces with small contexts (the elaboration cost of
  this module in this toolchain is dominated by unification of the F-model's
  `model.fl` applications, so every `nlinarith` here sees ≤ 6 hypotheses):

  - `fl_pair_mul_bound`  the store-magnitude product:
                         `(A(1+u)+η)(C(1+u)+η) ≤ 4AC + 2η(A+C+1)`
  - `cross_mul_abs_err`  one product's operand rounding:
                         `|fl a·fl c − a·c| ≤ 3u·AC + 2η(A+C+1)`
  - `cross2_fl_err_total` the composed bound:
                         `|fl(fl a·fl c − fl b·fl d) − (a·c − b·d)|
                            ≤ 7u(AC+BD) + 4η(A+B+C+D+2)`

  All bounds are range-free: no `InRange` anywhere.
-/
import LightRT.Robust.MTTotal
import LightRT.Robust.MTLeaf

set_option maxHeartbeats 1200000

namespace LightRT.Robust
open LightRT.FP LightRT.FP.Binary32 Geom

/-- Store-magnitude product bound used for `|fl a * fl c|`. -/
theorem fl_pair_mul_bound (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    (A * (1 + model.u) + eta) * (C * (1 + model.u) + eta) ≤ 4 * A * C + 2 * eta * (A + C + 1) := by
  have hu := model_u_lt1000
  have hu0 := model.u_pos
  have hu1 : model.u ≤ 1 := by linarith
  have h1 : A * (1 + model.u) + eta ≤ 2 * A + eta := by nlinarith [hu, hu0, hA, eta_pos]
  have h2 : C * (1 + model.u) + eta ≤ 2 * C + eta := by nlinarith [hu, hu0, hC, eta_pos]
  have hA1 : 0 ≤ A * (1 + model.u) + eta := model_u_add_eta_nonneg' A hA
  have hC1 : 0 ≤ C * (1 + model.u) + eta := model_u_add_eta_nonneg' C hC
  have hA2 : 0 ≤ 2 * A + eta := by nlinarith [hA, eta_pos]
  have h5 : (A * (1 + model.u) + eta) * (C * (1 + model.u) + eta) ≤ (2 * A + eta) * (2 * C + eta) :=
    mul_le_mul h1 h2 hC1 hA2
  have hexpand : (2 * A + eta) * (2 * C + eta) =
      4 * A * C + 2 * eta * A + 2 * eta * C + eta ^ 2 := by ring
  have he : eta ^ 2 ≤ 2 * eta := by
    have h1e : eta ≤ 1 := by unfold eta; norm_num [zpow_neg]
    nlinarith [eta_pos, h1e]
  have h6 : (2 * A + eta) * (2 * C + eta) ≤ 4 * A * C + 2 * eta * (A + C + 1) := by
    nlinarith [hexpand, he, hA, hC, eta_pos]
  linarith [h5, h6]

/-- One product's operand-rounding error: `|fl a · fl c − a·c|`. -/
theorem cross_mul_abs_err (a c : ℝ) (A C : ℝ)
    (ha : |a| ≤ A) (hc : |c| ≤ C) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    |model.fl a * model.fl c - a * c| ≤ 3 * model.u * A * C + 2 * eta * (A + C + 1) := by
  have hu := model_u_lt1000
  have hu0 := model.u_pos
  have hu1 : model.u ≤ 1 := by linarith
  have h1 : |model.fl a - a| ≤ model.u * A + eta := by
    have h := model_abs_err_total a
    rw [← eta_eq_def] at h
    have huA : model.u * |a| ≤ model.u * A := mul_le_mul_of_nonneg_left ha hu0.le
    nlinarith [h, huA, eta_pos]
  have h2 : |model.fl c - c| ≤ model.u * C + eta := by
    have h := model_abs_err_total c
    rw [← eta_eq_def] at h
    have huC : model.u * |c| ≤ model.u * C := mul_le_mul_of_nonneg_left hc hu0.le
    nlinarith [h, huC, eta_pos]
  have hfc : |model.fl c| ≤ C * (1 + model.u) + eta := fl_abs_le hc
  have he1 : |(model.fl a - a) * model.fl c| ≤ (model.u * A + eta) * (C * (1 + model.u) + eta) := by
    rw [abs_mul]
    exact mul_le_mul h1 hfc (abs_nonneg _) (model_u_add_eta_nonneg A hA)
  have he2 : |a * (model.fl c - c)| ≤ A * (model.u * C + eta) := by
    rw [abs_mul]
    exact mul_le_mul ha h2 (abs_nonneg _) hA
  have hpair : (model.u * A + eta) * (C * (1 + model.u) + eta) ≤
      2 * model.u * A * C + eta * A + 2 * eta * C + eta := by
    have e : (model.u * A + eta) * (C * (1 + model.u) + eta) =
        model.u * A * C + model.u * model.u * A * C + model.u * eta * A +
          eta * C + model.u * eta * C + eta ^ 2 := by ring
    have hu2 : model.u * model.u * A * C ≤ model.u * A * C := by
      have hA2 : 0 ≤ A * C := mul_nonneg hA hC
      have hpow : model.u * model.u ≤ model.u := by nlinarith [hu1, hu0]
      nlinarith [hpow, hA2]
    have h2a : model.u * eta * A ≤ eta * A := by
      rw [show model.u * eta * A = eta * (model.u * A) from by ring]
      have h1 : model.u * A ≤ A := by nlinarith [hu, hA, hu0]
      exact mul_le_mul_of_nonneg_left h1 eta_pos.le
    have h2b : model.u * C * eta ≤ eta * C := by
      rw [show model.u * C * eta = eta * (model.u * C) from by ring]
      have h1 : model.u * C ≤ C := by nlinarith [hu, hC, hu0]
      exact mul_le_mul_of_nonneg_left h1 eta_pos.le
    have h3 : eta ^ 2 ≤ eta := by
      have h1e : eta ≤ 1 := by unfold eta; norm_num [zpow_neg]
      nlinarith [eta_pos, h1e]
    nlinarith [e, hu2, h2a, h2b, h3, hA, hC, eta_pos, hu0]
  have hsecond : A * (model.u * C + eta) ≤ model.u * A * C + eta * A := le_of_eq (by ring)
  have hsplit : model.fl a * model.fl c - a * c =
      (model.fl a - a) * model.fl c + a * (model.fl c - c) := by ring
  have h : |model.fl a * model.fl c - a * c| ≤
      |(model.fl a - a) * model.fl c| + |a * (model.fl c - c)| := by
    rw [hsplit]; exact abs_add_le _ _
  nlinarith [h, he1, he2, hpair, hsecond, hA, hC, eta_pos, hu, hu0]

/-- The cross-product component: `|fl(fl a·fl c − fl b·fl d) − (a·c − b·d)|`. -/
theorem cross2_fl_err_total (a b c d : ℝ) (A B C D : ℝ)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    |model.fl (model.fl a * model.fl c - model.fl b * model.fl d) - (a * c - b * d)| ≤
      7 * model.u * (A * C + B * D) + 4 * eta * (A + B + C + D + 2) := by
  have hu := model_u_lt1000
  have hu0 := model.u_pos
  have hAC : |model.fl a * model.fl c| ≤
      (A * (1 + model.u) + eta) * (C * (1 + model.u) + eta) := by
    rw [abs_mul]
    exact mul_le_mul (fl_abs_le ha) (fl_abs_le hc) (abs_nonneg _) (model_u_add_eta_nonneg' A hA)
  have hBD : |model.fl b * model.fl d| ≤
      (B * (1 + model.u) + eta) * (D * (1 + model.u) + eta) := by
    rw [abs_mul]
    exact mul_le_mul (fl_abs_le hb) (fl_abs_le hd) (abs_nonneg _) (model_u_add_eta_nonneg' B hB)
  have hA' : 0 ≤ (A * (1 + model.u) + eta) * (C * (1 + model.u) + eta) :=
    mul_nonneg (model_u_add_eta_nonneg' A hA) (model_u_add_eta_nonneg' C hC)
  have hB' : 0 ≤ (B * (1 + model.u) + eta) * (D * (1 + model.u) + eta) :=
    mul_nonneg (model_u_add_eta_nonneg' B hB) (model_u_add_eta_nonneg' D hD)
  have hP := sub2_fl_err_total (model.fl a * model.fl c) (model.fl b * model.fl d)
    ((A * (1 + model.u) + eta) * (C * (1 + model.u) + eta))
    ((B * (1 + model.u) + eta) * (D * (1 + model.u) + eta))
    hAC hBD hA' hB'
  have hpairAC := fl_pair_mul_bound A C hA hC
  have hpairBD := fl_pair_mul_bound B D hB hD
  have hpairsum : (A * (1 + model.u) + eta) * (C * (1 + model.u) + eta) +
        (B * (1 + model.u) + eta) * (D * (1 + model.u) + eta) ≤
        4 * (A * C + B * D) + 2 * eta * (A + B + C + D + 2) := by
    linarith [hpairAC, hpairBD]
  have hQP : |model.fl a * model.fl c - a * c| ≤
      3 * model.u * A * C + 2 * eta * (A + C + 1) :=
    cross_mul_abs_err a c A C ha hc hA hC
  have hQP' : |model.fl b * model.fl d - b * d| ≤
      3 * model.u * B * D + 2 * eta * (B + D + 1) :=
    cross_mul_abs_err b d B D hb hd hB hD
  have hsplit : |(model.fl a * model.fl c - model.fl b * model.fl d) - (a * c - b * d)| ≤
      |model.fl a * model.fl c - a * c| + |model.fl b * model.fl d - b * d| := by
    have e : model.fl a * model.fl c - model.fl b * model.fl d - (a * c - b * d) =
        (model.fl a * model.fl c - a * c) - (model.fl b * model.fl d - b * d) := by ring
    have h := abs_sub_le'' (model.fl a * model.fl c - a * c) (model.fl b * model.fl d - b * d)
    rw [e]
    linarith [h]
  have hUabs : |model.fl a * model.fl c - model.fl b * model.fl d| ≤
      (A * (1 + model.u) + eta) * (C * (1 + model.u) + eta) +
        (B * (1 + model.u) + eta) * (D * (1 + model.u) + eta) := by
    have e : model.fl a * model.fl c - model.fl b * model.fl d =
        model.fl a * model.fl c + (-(model.fl b * model.fl d)) := by ring
    rw [e]
    have h := abs_add_le (model.fl a * model.fl c) (-(model.fl b * model.fl d))
    rw [abs_neg] at h
    linarith [h, hAC, hBD]
  have hU := model_abs_err_total (model.fl a * model.fl c - model.fl b * model.fl d)
  rw [← eta_eq_def] at hU
  have hU' : model.u * |model.fl a * model.fl c - model.fl b * model.fl d| ≤
      4 * model.u * (A * C + B * D) + 2 * model.u * eta * (A + B + C + D + 2) := by
    have h1 := mul_le_mul_of_nonneg_left hUabs hu0.le
    have h3 := mul_le_mul_of_nonneg_left hpairsum hu0.le
    have h4 : model.u * (4 * (A * C + B * D) + 2 * eta * (A + B + C + D + 2)) =
        4 * model.u * (A * C + B * D) + 2 * model.u * eta * (A + B + C + D + 2) := by ring
    nlinarith [h1, h3, h4, hu0, hA, hB, hC, hD, eta_pos]
  have htotal1 : |model.fl (model.fl a * model.fl c - model.fl b * model.fl d) -
        (model.fl a * model.fl c - model.fl b * model.fl d)| ≤
      4 * model.u * (A * C + B * D) + 2 * model.u * eta * (A + B + C + D + 2) + eta := by
    nlinarith [hU, hU', eta_pos]
  have htotal2 : |(model.fl a * model.fl c - model.fl b * model.fl d) - (a * c - b * d)| ≤
      3 * model.u * (A * C + B * D) + 2 * eta * (A + B + C + D + 2) := by
    linarith [hQP, hQP', hsplit, hA, hB, hC, hD, eta_pos]
  have habs := abs_add_le
    (model.fl (model.fl a * model.fl c - model.fl b * model.fl d) -
      (model.fl a * model.fl c - model.fl b * model.fl d))
    ((model.fl a * model.fl c - model.fl b * model.fl d) - (a * c - b * d))
  have hgoal : model.fl (model.fl a * model.fl c - model.fl b * model.fl d) - (a * c - b * d) =
      (model.fl (model.fl a * model.fl c - model.fl b * model.fl d) -
        (model.fl a * model.fl c - model.fl b * model.fl d)) +
      ((model.fl a * model.fl c - model.fl b * model.fl d) - (a * c - b * d)) := by ring
  rw [hgoal]
  clear hUabs hP hAC hBD hpairsum hU' hpairAC hpairBD
  have heta : eta * (A + B + C + D + 2) ≥ eta := by nlinarith [hA, hB, hC, hD, eta_pos]
  have h2ueta : 2 * model.u * eta * (A + B + C + D + 2) ≤ 2 * eta * (A + B + C + D + 2) := by
    have h1 : model.u * eta * (A + B + C + D + 2) ≤ eta * (A + B + C + D + 2) := by
      have hn : 0 ≤ eta * (A + B + C + D + 2) := by nlinarith [hA, hB, hC, hD, eta_pos]
      have hu1 : model.u ≤ 1 := by linarith
      nlinarith [hu1, hu0, hn]
    nlinarith [h1]
  nlinarith [habs, htotal1, htotal2, heta, h2ueta, eta_pos]

end LightRT.Robust
