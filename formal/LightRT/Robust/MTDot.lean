/-
  Dot-product error analysis for Möller–Trumbore (item 3b, numerator stages).

  The C (`-ffp-contract=off`) rounds each product then each sum:

    fl(fl(fl(e0 * p0) + fl(e1 * p1)) + fl(e2 * p2))

  where the `pᵢ` are themselves rounded values (the cross products). This
  file proves the error of that whole expression relative to the exact
  `e0·q0 + e1·q1 + e2·q2` when `|pᵢ − qᵢ| ≤ Cp`:

  * `dot3_fl_err_total`: `≤ 12u·A·B + 12·A·Cp + 8η` (via `num_err_total` with a
    padded operand bound);
  * `cross_component_err`: one cross-product component as the C rounds it
    (two rounded products then a rounded subtract);
  * `mt_det_err_total` / `mt_num_err_total`: the two conclusions used by the
    `t`-error composition.

  All bounds are range-free.
-/
import LightRT.Robust.MTTotal
import LightRT.Robust.MTLeaf
import LightRT.Robust.MTCross2
import LightRT.Robust.Total

namespace LightRT.Robust
open LightRT.FP LightRT.FP.Binary32 Geom

/-- The determinant-stage error constant of the MT kernel (range-free):
    what `mt_det_err_total` bounds `|det_model − det_exact|` by. -/
noncomputable def mtDetErr (M A B : ℝ) : ℝ :=
  12 * model.u * A * ((M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta)) *
      (1 + model.u) + eta) +
    12 * A * (7 * model.u * (M * B + M * B) + 12 * eta) + 8 * eta

/-- The numerator-stage error constant of the MT kernel (range-free):
    what `mt_num_err_total` bounds `|num_model − num_exact|` by. -/
noncomputable def mtNumErr (M A B : ℝ) : ℝ :=
  12 * model.u * B * ((M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta)) *
      (1 + model.u) + eta) +
    12 * B * (7 * model.u * (M * A + M * A) + 12 * eta) + 8 * eta

set_option maxHeartbeats 1600000

/-- One cross-product component as the C rounds it (`FMUL`,`FMUL`,`FSUB` under
    `-ffp-contract=off`): raw real operands; products are rounded before the
    subtraction. -/
theorem cross_component_err (a b c d : ℝ) (A B C D : ℝ)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    |model.fl (model.fl (a * c) - model.fl (b * d)) - (a * c - b * d)| ≤
      7 * model.u * (A * C + B * D) + 12 * eta := by
  have hu := model_u_lt1000
  have hu0 := model.u_pos
  have hu1 : model.u ≤ 1 := by linarith
  have hbAC : |a * c| ≤ A * C := by rw [abs_mul]; exact mul_le_mul ha hc (abs_nonneg _) hA
  have hbBD : |b * d| ≤ B * D := by rw [abs_mul]; exact mul_le_mul hb hd (abs_nonneg _) hB
  have hP : |model.fl (a * c)| ≤ A * C * (1 + model.u) + eta := fl_abs_le hbAC
  have hQ : |model.fl (b * d)| ≤ B * D * (1 + model.u) + eta := fl_abs_le hbBD
  have hACBu : 0 ≤ A * C := mul_nonneg hA hC
  have hBDBu : 0 ≤ B * D := mul_nonneg hB hD
  have hPabs : |model.fl (a * c) - model.fl (b * d)| ≤
      A * C * (1 + model.u) + eta + (B * D * (1 + model.u) + eta) := by
    have e : model.fl (a * c) - model.fl (b * d) =
        model.fl (a * c) + (-(model.fl (b * d))) := by ring
    rw [e]
    have h := abs_add_le (model.fl (a * c)) (-(model.fl (b * d)))
    rw [abs_neg] at h
    linarith [h, hP, hQ]
  have hstep := model_abs_err_total (model.fl (a * c) - model.fl (b * d))
  rw [← eta_eq_def] at hstep
  have hmul : model.u * |model.fl (a * c) - model.fl (b * d)| ≤
      model.u * (A * C * (1 + model.u) + eta + (B * D * (1 + model.u) + eta)) :=
    mul_le_mul_of_nonneg_left hPabs hu0.le
  have hx' : |model.fl (a * c) - a * c| ≤ model.u * (A * C) + eta := by
    have h := model_abs_err_total (a * c)
    rw [← eta_eq_def] at h
    have hmul' := mul_le_mul_of_nonneg_left hbAC hu0.le
    nlinarith [h, hmul', eta_pos]
  have hy' : |model.fl (b * d) - b * d| ≤ model.u * (B * D) + eta := by
    have h := model_abs_err_total (b * d)
    rw [← eta_eq_def] at h
    have hmul' := mul_le_mul_of_nonneg_left hbBD hu0.le
    nlinarith [h, hmul', eta_pos]
  have hrel : |(model.fl (a * c) - model.fl (b * d)) - (a * c - b * d)| ≤
      model.u * (A * C + B * D) + 2 * eta := by
    have e : model.fl (a * c) - model.fl (b * d) - (a * c - b * d) =
        (model.fl (a * c) - a * c) - (model.fl (b * d) - b * d) := by ring
    have h := abs_sub_le'' (model.fl (a * c) - a * c) (model.fl (b * d) - b * d)
    rw [e]
    nlinarith [h, hx', hy']
  have hexp : A * C * (1 + model.u) + eta + (B * D * (1 + model.u) + eta) =
      A * C + B * D + (A * C * model.u + B * D * model.u) + 2 * eta := by ring
  have hACu' : A * C * model.u ≤ A * C := by nlinarith [hu1, hACBu, hu0]
  have hBDu' : B * D * model.u ≤ B * D := by nlinarith [hu1, hBDBu, hu0]
  have hstep' : model.u * (A * C * (1 + model.u) + eta + (B * D * (1 + model.u) + eta)) ≤
      2 * model.u * (A * C + B * D) + 2 * model.u * eta := by
    nlinarith [hexp, hACu', hBDu', hACBu, hBDBu, hu0, eta_pos]
  have hA1 : |model.fl (model.fl (a * c) - model.fl (b * d)) -
      (model.fl (a * c) - model.fl (b * d))| ≤
      2 * model.u * (A * C + B * D) + 2 * model.u * eta + eta := by
    nlinarith [hstep, hmul, hstep', eta_pos]
  have h2ueta : 2 * model.u * eta ≤ 2 * eta := by nlinarith [hu1, eta_pos]
  have habs := abs_add_le
    (model.fl (model.fl (a * c) - model.fl (b * d)) - (model.fl (a * c) - model.fl (b * d)))
    ((model.fl (a * c) - model.fl (b * d)) - (a * c - b * d))
  have hgoal : model.fl (model.fl (a * c) - model.fl (b * d)) - (a * c - b * d) =
      (model.fl (model.fl (a * c) - model.fl (b * d)) -
        (model.fl (a * c) - model.fl (b * d))) +
      ((model.fl (a * c) - model.fl (b * d)) - (a * c - b * d)) := by ring
  rw [hgoal]
  nlinarith [habs, hA1, hrel, h2ueta, hu0, eta_pos]

/-- The rounded 3-vector dot product, with possibly-rounded operands whose
    errors are bounded by `Cp`. Exact target: `e0·q0 + e1·q1 + e2·q2`. -/
theorem dot3_fl_err_total (hu : model.u ≤ 1 / 1000)
    (e0 e1 e2 p0 p1 p2 q0 q1 q2 : ℝ)
    (A B Cp : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hCp : 0 ≤ Cp)
    (he0 : |e0| ≤ A) (he1 : |e1| ≤ A) (he2 : |e2| ≤ A)
    (hp0 : |p0| ≤ B) (hp1 : |p1| ≤ B) (hp2 : |p2| ≤ B)
    (hq0 : |p0 - q0| ≤ Cp) (hq1 : |p1 - q1| ≤ Cp) (hq2 : |p2 - q2| ≤ Cp) :
    |model.fl (model.fl (model.fl (e0 * p0) + model.fl (e1 * p1)) + model.fl (e2 * p2)) -
      (e0 * q0 + e1 * q1 + e2 * q2)| ≤ 12 * model.u * A * B + 12 * A * Cp + 8 * eta := by
  have hu0 := model.u_pos
  have hb0 : 0 ≤ A * B + A * Cp / model.u := by
    have h1 : 0 ≤ A * B := mul_nonneg hA hB
    have h2 : 0 ≤ A * Cp / model.u := div_nonneg (mul_nonneg hA hCp) (le_of_lt hu0)
    linarith
  have hpad : A * Cp = model.u * (A * Cp / model.u) := by field_simp [hu0.ne']
  have q0h : |model.fl (e0 * p0) - e0 * q0| ≤ model.u * (A * B + A * Cp / model.u) + eta := by
    have h1 : |model.fl (e0 * p0) - e0 * p0| ≤ model.u * (A * B) + eta := by
      have h := model_abs_err_total (e0 * p0)
      rw [← eta_eq_def] at h
      have hb2 : |e0 * p0| ≤ A * B := by rw [abs_mul]; exact mul_le_mul he0 hp0 (abs_nonneg _) hA
      nlinarith [h, hb2]
    have h2 : |e0 * p0 - e0 * q0| ≤ A * Cp := by
      rw [show e0 * p0 - e0 * q0 = e0 * (p0 - q0) by ring, abs_mul]
      exact mul_le_mul he0 hq0 (abs_nonneg _) hA
    have e : model.fl (e0 * p0) - e0 * q0 =
        (model.fl (e0 * p0) - e0 * p0) + (e0 * p0 - e0 * q0) := by ring
    have hexp : model.u * (A * B + A * Cp / model.u) =
        model.u * (A * B) + model.u * (A * Cp / model.u) := by ring
    have h := abs_add_le (model.fl (e0 * p0) - e0 * p0) (e0 * p0 - e0 * q0)
    rw [e]
    nlinarith [h, h1, h2, hpad, hexp, hu0, hA, hB, hCp]
  have q1h : |model.fl (e1 * p1) - e1 * q1| ≤ model.u * (A * B + A * Cp / model.u) + eta := by
    have h1 : |model.fl (e1 * p1) - e1 * p1| ≤ model.u * (A * B) + eta := by
      have h := model_abs_err_total (e1 * p1)
      rw [← eta_eq_def] at h
      have hb2 : |e1 * p1| ≤ A * B := by rw [abs_mul]; exact mul_le_mul he1 hp1 (abs_nonneg _) hA
      nlinarith [h, hb2]
    have h2 : |e1 * p1 - e1 * q1| ≤ A * Cp := by
      rw [show e1 * p1 - e1 * q1 = e1 * (p1 - q1) by ring, abs_mul]
      exact mul_le_mul he1 hq1 (abs_nonneg _) hA
    have e : model.fl (e1 * p1) - e1 * q1 =
        (model.fl (e1 * p1) - e1 * p1) + (e1 * p1 - e1 * q1) := by ring
    have hexp : model.u * (A * B + A * Cp / model.u) =
        model.u * (A * B) + model.u * (A * Cp / model.u) := by ring
    have h := abs_add_le (model.fl (e1 * p1) - e1 * p1) (e1 * p1 - e1 * q1)
    rw [e]
    nlinarith [h, h1, h2, hpad, hexp, hu0, hA, hB, hCp]
  have q2h : |model.fl (e2 * p2) - e2 * q2| ≤ model.u * (A * B + A * Cp / model.u) + eta := by
    have h1 : |model.fl (e2 * p2) - e2 * p2| ≤ model.u * (A * B) + eta := by
      have h := model_abs_err_total (e2 * p2)
      rw [← eta_eq_def] at h
      have hb2 : |e2 * p2| ≤ A * B := by rw [abs_mul]; exact mul_le_mul he2 hp2 (abs_nonneg _) hA
      nlinarith [h, hb2]
    have h2 : |e2 * p2 - e2 * q2| ≤ A * Cp := by
      rw [show e2 * p2 - e2 * q2 = e2 * (p2 - q2) by ring, abs_mul]
      exact mul_le_mul he2 hq2 (abs_nonneg _) hA
    have e : model.fl (e2 * p2) - e2 * q2 =
        (model.fl (e2 * p2) - e2 * p2) + (e2 * p2 - e2 * q2) := by ring
    have hexp : model.u * (A * B + A * Cp / model.u) =
        model.u * (A * B) + model.u * (A * Cp / model.u) := by ring
    have h := abs_add_le (model.fl (e2 * p2) - e2 * p2) (e2 * p2 - e2 * q2)
    rw [e]
    nlinarith [h, h1, h2, hpad, hexp, hu0, hA, hB, hCp]
  have a0h : |model.fl (e0 * p0)| ≤ (1 + model.u) * (A * B + A * Cp / model.u) + eta := by
    have hb2 : |e0 * p0| ≤ A * B := by rw [abs_mul]; exact mul_le_mul he0 hp0 (abs_nonneg _) hA
    have h := fl_abs_le hb2
    have hexp : (1 + model.u) * (A * B + A * Cp / model.u) =
        (1 + model.u) * (A * B) + (1 + model.u) * (A * Cp / model.u) := by ring
    have hACp : 0 ≤ A * Cp / model.u := div_nonneg (mul_nonneg hA hCp) (le_of_lt hu0)
    nlinarith [h, hexp, hACp, hA, hB, hCp, hu0, model.u_lt_one.le, eta_pos]
  have a1h : |model.fl (e1 * p1)| ≤ (1 + model.u) * (A * B + A * Cp / model.u) + eta := by
    have hb2 : |e1 * p1| ≤ A * B := by rw [abs_mul]; exact mul_le_mul he1 hp1 (abs_nonneg _) hA
    have h := fl_abs_le hb2
    have hexp : (1 + model.u) * (A * B + A * Cp / model.u) =
        (1 + model.u) * (A * B) + (1 + model.u) * (A * Cp / model.u) := by ring
    have hACp : 0 ≤ A * Cp / model.u := div_nonneg (mul_nonneg hA hCp) (le_of_lt hu0)
    nlinarith [h, hexp, hACp, hA, hB, hCp, hu0, model.u_lt_one.le, eta_pos]
  have a2h : |model.fl (e2 * p2)| ≤ (1 + model.u) * (A * B + A * Cp / model.u) + eta := by
    have hb2 : |e2 * p2| ≤ A * B := by rw [abs_mul]; exact mul_le_mul he2 hp2 (abs_nonneg _) hA
    have h := fl_abs_le hb2
    have hexp : (1 + model.u) * (A * B + A * Cp / model.u) =
        (1 + model.u) * (A * B) + (1 + model.u) * (A * Cp / model.u) := by ring
    have hACp : 0 ≤ A * Cp / model.u := div_nonneg (mul_nonneg hA hCp) (le_of_lt hu0)
    nlinarith [h, hexp, hACp, hA, hB, hCp, hu0, model.u_lt_one.le, eta_pos]
  have e1_ : |model.fl (model.fl (e0 * p0) + model.fl (e1 * p1)) -
        (model.fl (e0 * p0) + model.fl (e1 * p1))| ≤
      model.u * |model.fl (e0 * p0) + model.fl (e1 * p1)| + eta := by
    have h := model_abs_err_total (model.fl (e0 * p0) + model.fl (e1 * p1))
    rw [← eta_eq_def] at h
    exact h
  have eN : |model.fl (model.fl (model.fl (e0 * p0) + model.fl (e1 * p1)) + model.fl (e2 * p2)) -
        (model.fl (model.fl (e0 * p0) + model.fl (e1 * p1)) + model.fl (e2 * p2))| ≤
      model.u * |model.fl (model.fl (e0 * p0) + model.fl (e1 * p1)) + model.fl (e2 * p2)| + eta := by
    have h := model_abs_err_total
      (model.fl (model.fl (e0 * p0) + model.fl (e1 * p1)) + model.fl (e2 * p2))
    rw [← eta_eq_def] at h
    exact h
  have hnum := num_err_total model hu
    (model.fl (e0 * p0)) (model.fl (e1 * p1)) (model.fl (e2 * p2))
    (e0 * q0) (e1 * q1) (e2 * q2)
    (A * B + A * Cp / model.u) (A * B + A * Cp / model.u) (A * B + A * Cp / model.u)
    hb0 hb0 hb0 q0h q1h q2h a0h a1h a2h e1_ eN
  have he : 4 * model.u *
        ((A * B + A * Cp / model.u) + (A * B + A * Cp / model.u) + (A * B + A * Cp / model.u)) +
        8 * eta = 12 * model.u * A * B + 12 * A * Cp + 8 * eta := by
    field_simp [hu0.ne']
    ring
  rwa [he] at hnum

/-- **Determinant error for the MT kernel** (range-free): the C's op order,

    fl(fl(fl(e10 * px) + fl(e11 * py)) + fl(e12 * pz)),    px = fl(fl(d1*e22) - fl(d2*e21)) …,

    relative to the exact determinant `e1 · (d × e2)`.

    `|dᵢ| ≤ M`, `|e1ᵢ| ≤ A`, `|e2ᵢ| ≤ B`. -/
theorem mt_det_err_total (d0 d1 d2 e10 e11 e12 e20 e21 e22 : ℝ)
    (M A B : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd0 : |d0| ≤ M) (hd1 : |d1| ≤ M) (hd2 : |d2| ≤ M)
    (h10 : |e10| ≤ A) (h11 : |e11| ≤ A) (h12 : |e12| ≤ A)
    (h20 : |e20| ≤ B) (h21 : |e21| ≤ B) (h22 : |e22| ≤ B) :
    |model.fl (model.fl (model.fl (e10 * model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))) +
        model.fl (e11 * model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))) +
        model.fl (e12 * model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))) -
      (e10 * (d1 * e22 - d2 * e21) + e11 * (d2 * e20 - d0 * e22) +
        e12 * (d0 * e21 - d1 * e20))| ≤
      mtDetErr M A B := by
  have hu := model_u_lt1000
  have hu0 := model.u_pos
  have hCc : 0 ≤ 7 * model.u * (M * B + M * B) + 12 * eta := by
    have h1 : 0 ≤ M * B := mul_nonneg hM hB
    nlinarith [hu0, h1, eta_pos]
  have hPc : 0 ≤ (M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta)) * (1 + model.u) + eta := by
    have h1 : 0 ≤ M * B := mul_nonneg hM hB
    nlinarith [h1, eta_pos, hu0, model.u_lt_one.le]
  -- magnitudes of the three rounded cross components
  have hp1 : |model.fl (model.fl (d1 * e22) - model.fl (d2 * e21))| ≤
      (M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta)) * (1 + model.u) + eta := by
    have h1 : |d1 * e22| ≤ M * B := by rw [abs_mul]; exact mul_le_mul hd1 h22 (abs_nonneg _) hM
    have h2 : |d2 * e21| ≤ M * B := by rw [abs_mul]; exact mul_le_mul hd2 h21 (abs_nonneg _) hM
    have hP := fl_abs_le h1
    have hQ := fl_abs_le h2
    have hPQ : |model.fl (d1 * e22) - model.fl (d2 * e21)| ≤
        M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta) := by
      have h := abs_sub_le'' (model.fl (d1 * e22)) (model.fl (d2 * e21))
      nlinarith [h, hP, hQ]
    exact fl_abs_le hPQ
  have hp2 : |model.fl (model.fl (d2 * e20) - model.fl (d0 * e22))| ≤
      (M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta)) * (1 + model.u) + eta := by
    have h1 : |d2 * e20| ≤ M * B := by rw [abs_mul]; exact mul_le_mul hd2 h20 (abs_nonneg _) hM
    have h2 : |d0 * e22| ≤ M * B := by rw [abs_mul]; exact mul_le_mul hd0 h22 (abs_nonneg _) hM
    have hP := fl_abs_le h1
    have hQ := fl_abs_le h2
    have hPQ : |model.fl (d2 * e20) - model.fl (d0 * e22)| ≤
        M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta) := by
      have h := abs_sub_le'' (model.fl (d2 * e20)) (model.fl (d0 * e22))
      nlinarith [h, hP, hQ]
    exact fl_abs_le hPQ
  have hp3 : |model.fl (model.fl (d0 * e21) - model.fl (d1 * e20))| ≤
      (M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta)) * (1 + model.u) + eta := by
    have h1 : |d0 * e21| ≤ M * B := by rw [abs_mul]; exact mul_le_mul hd0 h21 (abs_nonneg _) hM
    have h2 : |d1 * e20| ≤ M * B := by rw [abs_mul]; exact mul_le_mul hd1 h20 (abs_nonneg _) hM
    have hP := fl_abs_le h1
    have hQ := fl_abs_le h2
    have hPQ : |model.fl (d0 * e21) - model.fl (d1 * e20)| ≤
        M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta) := by
      have h := abs_sub_le'' (model.fl (d0 * e21)) (model.fl (d1 * e20))
      nlinarith [h, hP, hQ]
    exact fl_abs_le hPQ
  -- operand errors of the cross components
  have hq1 := cross_component_err d1 d2 e22 e21 M M B B hd1 hd2 h22 h21 hM hM hB hB
  have hq2 := cross_component_err d2 d0 e20 e22 M M B B hd2 hd0 h20 h22 hM hM hB hB
  have hq3 := cross_component_err d0 d1 e21 e20 M M B B hd0 hd1 h21 h20 hM hM hB hB
  exact dot3_fl_err_total hu e10 e11 e12
    (model.fl (model.fl (d1 * e22) - model.fl (d2 * e21)))
    (model.fl (model.fl (d2 * e20) - model.fl (d0 * e22)))
    (model.fl (model.fl (d0 * e21) - model.fl (d1 * e20)))
    (d1 * e22 - d2 * e21) (d2 * e20 - d0 * e22) (d0 * e21 - d1 * e20)
    A ((M * B * (1 + model.u) + eta + (M * B * (1 + model.u) + eta)) * (1 + model.u) + eta)
    (7 * model.u * (M * B + M * B) + 12 * eta)
    hA hPc hCc h10 h11 h12 hp1 hp2 hp3 hq1 hq2 hq3

/-- **Numerator error for the MT kernel's `t`** (range-free): the C's op order,

    fl(fl(fl(e20 * qx) + fl(e21 * qy)) + fl(e22 * qz)),    qx = fl(fl(tv1*e12) - fl(tv2*e11)) …,

    relative to the exact `e2 · (tv × e1)`.

    `|tvᵢ| ≤ M`, `|e1ᵢ| ≤ A`, `|e2ᵢ| ≤ B`. -/
theorem mt_num_err_total (e20 e21 e22 tv0 tv1 tv2 e10 e11 e12 : ℝ)
    (M A B : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he20 : |e20| ≤ B) (he21 : |e21| ≤ B) (he22 : |e22| ≤ B)
    (htv0 : |tv0| ≤ M) (htv1 : |tv1| ≤ M) (htv2 : |tv2| ≤ M)
    (h10 : |e10| ≤ A) (h11 : |e11| ≤ A) (h12 : |e12| ≤ A) :
    |model.fl (model.fl (model.fl (e20 * model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))) +
        model.fl (e21 * model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))) +
        model.fl (e22 * model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))) -
      (e20 * (tv1 * e12 - tv2 * e11) + e21 * (tv2 * e10 - tv0 * e12) +
        e22 * (tv0 * e11 - tv1 * e10))| ≤
      mtNumErr M A B := by
  have hu := model_u_lt1000
  have hu0 := model.u_pos
  have hCc : 0 ≤ 7 * model.u * (M * A + M * A) + 12 * eta := by
    have h1 : 0 ≤ M * A := mul_nonneg hM hA
    nlinarith [hu0, h1, eta_pos]
  have hPc : 0 ≤ (M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta)) * (1 + model.u) + eta := by
    have h1 : 0 ≤ M * A := mul_nonneg hM hA
    nlinarith [h1, eta_pos, hu0, model.u_lt_one.le]
  have hp1 : |model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11))| ≤
      (M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta)) * (1 + model.u) + eta := by
    have h1 : |tv1 * e12| ≤ M * A := by rw [abs_mul]; exact mul_le_mul htv1 h12 (abs_nonneg _) hM
    have h2 : |tv2 * e11| ≤ M * A := by rw [abs_mul]; exact mul_le_mul htv2 h11 (abs_nonneg _) hM
    have hP := fl_abs_le h1
    have hQ := fl_abs_le h2
    have hPQ : |model.fl (tv1 * e12) - model.fl (tv2 * e11)| ≤
        M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta) := by
      have h := abs_sub_le'' (model.fl (tv1 * e12)) (model.fl (tv2 * e11))
      nlinarith [h, hP, hQ]
    exact fl_abs_le hPQ
  have hp2 : |model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12))| ≤
      (M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta)) * (1 + model.u) + eta := by
    have h1 : |tv2 * e10| ≤ M * A := by rw [abs_mul]; exact mul_le_mul htv2 h10 (abs_nonneg _) hM
    have h2 : |tv0 * e12| ≤ M * A := by rw [abs_mul]; exact mul_le_mul htv0 h12 (abs_nonneg _) hM
    have hP := fl_abs_le h1
    have hQ := fl_abs_le h2
    have hPQ : |model.fl (tv2 * e10) - model.fl (tv0 * e12)| ≤
        M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta) := by
      have h := abs_sub_le'' (model.fl (tv2 * e10)) (model.fl (tv0 * e12))
      nlinarith [h, hP, hQ]
    exact fl_abs_le hPQ
  have hp3 : |model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10))| ≤
      (M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta)) * (1 + model.u) + eta := by
    have h1 : |tv0 * e11| ≤ M * A := by rw [abs_mul]; exact mul_le_mul htv0 h11 (abs_nonneg _) hM
    have h2 : |tv1 * e10| ≤ M * A := by rw [abs_mul]; exact mul_le_mul htv1 h10 (abs_nonneg _) hM
    have hP := fl_abs_le h1
    have hQ := fl_abs_le h2
    have hPQ : |model.fl (tv0 * e11) - model.fl (tv1 * e10)| ≤
        M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta) := by
      have h := abs_sub_le'' (model.fl (tv0 * e11)) (model.fl (tv1 * e10))
      nlinarith [h, hP, hQ]
    exact fl_abs_le hPQ
  have hq1 := cross_component_err tv1 tv2 e12 e11 M M A A htv1 htv2 h12 h11 hM hM hA hA
  have hq2 := cross_component_err tv2 tv0 e10 e12 M M A A htv2 htv0 h10 h12 hM hM hA hA
  have hq3 := cross_component_err tv0 tv1 e11 e10 M M A A htv0 htv1 h11 h10 hM hM hA hA
  exact dot3_fl_err_total hu e20 e21 e22
    (model.fl (model.fl (tv1 * e12) - model.fl (tv2 * e11)))
    (model.fl (model.fl (tv2 * e10) - model.fl (tv0 * e12)))
    (model.fl (model.fl (tv0 * e11) - model.fl (tv1 * e10)))
    (tv1 * e12 - tv2 * e11) (tv2 * e10 - tv0 * e12) (tv0 * e11 - tv1 * e10)
    B ((M * A * (1 + model.u) + eta + (M * A * (1 + model.u) + eta)) * (1 + model.u) + eta)
    (7 * model.u * (M * A + M * A) + 12 * eta)
    hB hPc hCc he20 he21 he22 hp1 hp2 hp3 hq1 hq2 hq3

end LightRT.Robust
