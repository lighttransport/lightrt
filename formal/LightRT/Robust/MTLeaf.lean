/-
  Small range-free rounding-errorlemmas reused by the-staged Möller–Trumbore
  bound. Kept small intentionally.
-/
import LightRT.Robust.MTTotal

namespace LightRT.Robust
open LightRT.FP LightRT.FP.Binary32 Geom

/-- Error of one fl sum of two already-rounded operands. -/
theorem add2_fl_err_total (a b : ℝ) (A B : ℝ)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |model.fl (model.fl a + model.fl b) - (a + b)| ≤
      3 * model.u * (A + B) + 4 * eta := by
  have hu : model.u ≤ 1 / 1000 := model_u_lt1000
  have u1 : model.u ≤ 1 := model.u_lt_one.le
  have h1 := fl_abs_le ha
  have h2 := fl_abs_le hb
  have h1' : |model.fl a - a| ≤ model.u * A + eta := by
    have h := model_abs_err_total a
    have h2a : model.u * |a| ≤ model.u * A := mul_le_mul_of_nonneg_left ha model.u_pos.le
    nlinarith [h, eta_pos, eta_eq_def]
  have h2' : |model.fl b - b| ≤ model.u * B + eta := by
    have h := model_abs_err_total b
    have h2b : model.u * |b| ≤ model.u * B := mul_le_mul_of_nonneg_left hb model.u_pos.le
    nlinarith [h, eta_pos, eta_eq_def]
  have h3 := model_abs_err_total (model.fl a + model.fl b)
  have habs : |model.fl a + model.fl b| ≤
      (A * (1 + model.u) + eta) + (B * (1 + model.u) + eta) := by
    have h := abs_add_le (model.fl a) (model.fl b)
    linarith
  have hstep : model.u * |model.fl a + model.fl b| ≤ 2 * model.u * (A + B) + eta := by
    have huAB : 0 ≤ A + B := by linarith
    have h1e : A * (1 + model.u) + eta + (B * (1 + model.u) + eta) ≤ 2 * (A + B + eta) := by
      nlinarith [u1, hA, hB, eta_pos]
    have h2e : model.u * (2 * (A + B + eta)) ≤ 2 * model.u * (A + B) + eta := by
      nlinarith [hu, u1, huAB, eta_pos, model.u_pos]
    nlinarith [habs, h1e, h2e, model.u_pos]
  have hsplit : model.fl (model.fl a + model.fl b) - (a + b) =
      (model.fl (model.fl a + model.fl b) - (model.fl a + model.fl b)) +
      ((model.fl a + model.fl b) - (a + b)) := by ring
  have h4 : |model.fl a + model.fl b - (a + b)| ≤ model.u * (A + B) + 2 * eta := by
    have e : model.fl a + model.fl b - (a + b) = (model.fl a - a) + (model.fl b - b) := by ring
    have h := abs_add_le (model.fl a - a) (model.fl b - b)
    rw [e]
    nlinarith [h, h1', h2']
  rw [hsplit]
  have h := abs_add_le (model.fl (model.fl a + model.fl b) - (model.fl a + model.fl b))
    (model.fl a + model.fl b - (a + b))
  nlinarith [h, h3, hstep, h4, eta_pos, model.u_pos, eta_eq_def]

/-- Error of one fl difference of two rounded operands. -/
theorem sub2_fl_err_total (a b : ℝ) (A B : ℝ)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |model.fl (model.fl a - model.fl b) - (a - b)| ≤
      3 * model.u * (A + B) + 4 * eta := by
  have hu : model.u ≤ 1 / 1000 := model_u_lt1000
  have u1 : model.u ≤ 1 := model.u_lt_one.le
  have h1 := fl_abs_le ha
  have h2 := fl_abs_le hb
  have h1' : |model.fl a - a| ≤ model.u * A + eta := by
    have h := model_abs_err_total a
    have h2a : model.u * |a| ≤ model.u * A := mul_le_mul_of_nonneg_left ha model.u_pos.le
    nlinarith [h, eta_pos, eta_eq_def]
  have h2' : |model.fl b - b| ≤ model.u * B + eta := by
    have h := model_abs_err_total b
    have h2b : model.u * |b| ≤ model.u * B := mul_le_mul_of_nonneg_left hb model.u_pos.le
    nlinarith [h, eta_pos, eta_eq_def]
  have h3 := model_abs_err_total (model.fl a - model.fl b)
  have habs : |model.fl a - model.fl b| ≤
      (A * (1 + model.u) + eta) + (B * (1 + model.u) + eta) := by
    have h := abs_sub_le'' (model.fl a) (model.fl b)
    linarith
  have hstep : model.u * |model.fl a - model.fl b| ≤ 2 * model.u * (A + B) + eta := by
    have huAB : 0 ≤ A + B := by linarith
    have h1e : A * (1 + model.u) + eta + (B * (1 + model.u) + eta) ≤ 2 * (A + B + eta) := by
      nlinarith [u1, hA, hB, eta_pos]
    have h2e : model.u * (2 * (A + B + eta)) ≤ 2 * model.u * (A + B) + eta := by
      nlinarith [hu, u1, huAB, eta_pos, model.u_pos]
    nlinarith [habs, h1e, h2e, model.u_pos]
  have hsplit : model.fl (model.fl a - model.fl b) - (a - b) =
      (model.fl (model.fl a - model.fl b) - (model.fl a - model.fl b)) +
      ((model.fl a - model.fl b) - (a - b)) := by ring
  have h4 : |model.fl a - model.fl b - (a - b)| ≤ model.u * (A + B) + 2 * eta := by
    have e : model.fl a - model.fl b - (a - b) = (model.fl a - a) - (model.fl b - b) := by ring
    have h := abs_sub_le'' (model.fl a - a) (model.fl b - b)
    rw [e]
    nlinarith [h, h1', h2']
  rw [hsplit]
  have h := abs_add_le (model.fl (model.fl a - model.fl b) - (model.fl a - model.fl b))
    (model.fl a - model.fl b - (a - b))
  nlinarith [h, h3, hstep, h4, eta_pos, model.u_pos, eta_eq_def]

end LightRT.Robust
