/-
  Range-free rounding error for Möller–Trumbore (item 3b).

  Range-free means: no `InRange` hypothesis anywhere. Each rounding is bounded
  by `model_abs_err_total` (`|fl(x) - x| ≤ u|x| + eta`), so constants grow
  with the input bound `M` and pick up `eta` (half the subnormal quantum,
  `2^-150`) terms. The Woop `t` had convex-combination structure giving
  `u·|t| + eta/a0`; MT's `t = (e2·q)/det` is a plain quotient whose error
  degrades like `eta/det`, which is the correct behaviour for a non-watertight
  kernel.

  Building blocks:
    `fl_sub_err_total`  |fl(a - b) - (a - b)| ≤ u|a - b| + eta
    `fl_add_err_total`  |fl(a + b) - (a + b)| ≤ u|a + b| + eta
    `fl_mul_err_total`  |fl(fl a · fl b) - a·b| ≤ 6u·A·B + 20eta·(A+B+1)
-/
import LightRT.FP.TotalErr
import LightRT.Robust.Total

namespace LightRT.Robust
open LightRT.FP LightRT.FP.Binary32 Geom

/-- `u := 2^-24 ≤ 1/1000`. -/
theorem model_u_lt1000 : model.u ≤ 1 / 1000 := by unfold model; norm_num [zpow_neg]

/-- Triangle inequality for subtraction (local copy). -/
theorem abs_sub_le'' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa using abs_sub_le a 0 b

theorem eta_eq_def : eta = 2 ^ (-150 : ℤ) := rfl

/-- `0 ≤ u·x + η` for `0 ≤ x` (used for non-negativity of store-magnitude terms). -/
theorem model_u_add_eta_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ model.u * x + eta :=
  add_nonneg (mul_nonneg model.u_pos.le hx) eta_pos.le

/-- `0 ≤ x·(1 + u) + η` for `0 ≤ x`. -/
theorem model_u_add_eta_nonneg' (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x * (1 + model.u) + eta := by
  nlinarith [mul_nonneg hx model.u_pos.le, hx, eta_pos]

/-- |fl x| ≤ A·(1 + u) + η for |x| ≤ A: the honest fl-magnitude bound. -/
theorem fl_abs_le {x : ℝ} {A : ℝ} (hx : |x| ≤ A) : |model.fl x| ≤ A * (1 + model.u) + eta := by
  have h := abs_add_le x (model.fl x - x)
  rw [show x + (model.fl x - x) = model.fl x by ring] at h
  have e := model_abs_err_total x
  have hu : 0 ≤ model.u := model.u_pos.le
  have h2 : model.u * |x| ≤ model.u * A := mul_le_mul_of_nonneg_left hx hu
  nlinarith [e, h2, eta_eq_def, eta_pos]


theorem fl_sub_err_total (a b : ℝ) :
    |model.fl (a - b) - (a - b)| ≤ model.u * |a - b| + eta := by
  have h := model_abs_err_total (a - b)
  simpa [eta] using h

theorem fl_add_err_total (a b : ℝ) :
    |model.fl (a + b) - (a + b)| ≤ model.u * |a + b| + eta := by
  have h := model_abs_err_total (a + b)
  simpa [eta] using h

set_option maxHeartbeats 1600000 in
/-- Range-free error of one `fl a · fl b`: `7u·A·B + 9η·(A+B+1)` for
    `|a| ≤ A`, `|b| ≤ B`. The store-magnitude bound `A·(1+u) + η` drives
    both rounding steps. -/
theorem fl_mul_err_total (a b : ℝ) (A B : ℝ)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |model.fl (model.fl a * model.fl b) - a * b| ≤
      7 * model.u * A * B + 9 * eta * (A + B + 1) := by
  have hu : model.u ≤ 1 / 1000 := model_u_lt1000
  have u0 := model.u_pos
  have u1 : model.u ≤ 1 := model.u_lt_one.le
  have heta1 : eta ≤ 1 := by unfold eta; norm_num [zpow_neg]
  have en := eta_pos
  have hA2 : A * (1 + model.u) + eta ≤ 2 * A + 2 * eta := by nlinarith [u1, hA, en]
  have hB2 : B * (1 + model.u) + eta ≤ 2 * B + 2 * eta := by nlinarith [u1, hB, en]
  have hPA : 0 ≤ A * (1 + model.u) + eta := by nlinarith [hA, u0, en]
  have hPB : 0 ≤ B * (1 + model.u) + eta := by nlinarith [hB, u0, en]
  have hPA2z : 0 ≤ 2 * A + 2 * eta := by nlinarith [hA, en]
  have hPB2z : 0 ≤ 2 * B + 2 * eta := by nlinarith [hB, en]
  have hP2 : (A * (1 + model.u) + eta) * (B * (1 + model.u) + eta) ≤ (2 * A + 2 * eta) * (2 * B + 2 * eta) :=
    mul_le_mul hA2 hB2 hPB hPA2z
  -- first lane: the inner rounding
  have h1c : |model.fl (model.fl a * model.fl b) - model.fl a * model.fl b| ≤
      model.u * ((A * (1 + model.u) + eta) * (B * (1 + model.u) + eta)) + eta := by
    have h8 := model_abs_err_total (model.fl a * model.fl b)
    have h1pe := fl_abs_le ha
    have h1qe := fl_abs_le hb
    have h9 : |model.fl a * model.fl b| ≤
        (A * (1 + model.u) + eta) * (B * (1 + model.u) + eta) := by
      rw [abs_mul]
      exact mul_le_mul h1pe h1qe (abs_nonneg _) hPA
    have hu2 : model.u * |model.fl a * model.fl b| ≤
        model.u * ((A * (1 + model.u) + eta) * (B * (1 + model.u) + eta)) :=
      mul_le_mul_of_nonneg_left h9 u0.le
    nlinarith [h8, hu2, en, eta_eq_def]
  have h1c' : |model.fl (model.fl a * model.fl b) - model.fl a * model.fl b| ≤
      4 * model.u * A * B + 5 * eta * (A + B + 1) := by
    have hu2 : model.u * ((A * (1 + model.u) + eta) * (B * (1 + model.u) + eta)) ≤
        model.u * ((2 * A + 2 * eta) * (2 * B + 2 * eta)) :=
      mul_le_mul_of_nonneg_left hP2 u0.le
    have hex : model.u * ((2 * A + 2 * eta) * (2 * B + 2 * eta)) =
        4 * model.u * A * B + 4 * model.u * eta * (A + B) + 4 * model.u * eta ^ 2 := by ring
    have he2 : eta ^ 2 ≤ eta := by nlinarith [heta1, en]
    have h6 : 4 * model.u * eta ^ 2 ≤ eta := by nlinarith [hu, he2, en]
    have h7 : 4 * model.u * eta * (A + B) ≤ 2 * eta * (A + B) := by
      have hAB : 0 ≤ A + B := by linarith [hA, hB]
      have hX : 0 ≤ eta * (A + B) := mul_nonneg en.le hAB
      have h1 : 4 * model.u ≤ 2 := by linarith [hu]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right h1 hX
    have hsum2 : 2 * eta * (A + B) + eta ≤ 3 * eta * (A + B + 1) := by
      nlinarith [hA, hB, en]
    have htot : model.u * ((2 * A + 2 * eta) * (2 * B + 2 * eta)) ≤ 4 * model.u * A * B + 3 * eta * (A + B + 1) := by
      linarith [hex, h6, h7, hsum2]
    have htot2 : model.u * ((A * (1 + model.u) + eta) * (B * (1 + model.u) + eta)) ≤
        4 * model.u * A * B + 3 * eta * (A + B + 1) := by
      linarith [hu2, htot]
    have hsum3 : 4 * model.u * A * B + 3 * eta * (A + B + 1) + eta ≤
        4 * model.u * A * B + 5 * eta * (A + B + 1) := by
      have h11 : eta ≤ eta * (A + B + 1) := by
        have h12 : 1 ≤ A + B + 1 := by linarith [hA, hB]
        have h13 := mul_le_mul_of_nonneg_left h12 en.le
        simpa using h13
      linarith
    linarith [h1c, htot2, hsum3]
  -- second lane: the one-level split
  have h1' : |model.fl a - a| ≤ model.u * A + eta := by
    have h := model_abs_err_total a
    have huA : model.u * |a| ≤ model.u * A := mul_le_mul_of_nonneg_left ha u0.le
    nlinarith [h, en, eta_eq_def]
  have h2' : |model.fl b - b| ≤ model.u * B + eta := by
    have h := model_abs_err_total b
    have huB : model.u * |b| ≤ model.u * B := mul_le_mul_of_nonneg_left hb u0.le
    nlinarith [h, en, eta_eq_def]
  have split2 : model.fl a * model.fl b - a * b =
      (model.fl a - a) * b + a * (model.fl b - b) + (model.fl a - a) * (model.fl b - b) := by ring
  have pa : |(model.fl a - a) * b| ≤ (model.u * A + eta) * B := by
    rw [abs_mul]
    exact mul_le_mul h1' hb (abs_nonneg _) (model_u_add_eta_nonneg A hA)
  have pb : |a * (model.fl b - b)| ≤ A * (model.u * B + eta) := by
    rw [abs_mul]
    exact mul_le_mul ha h2' (abs_nonneg _) hA
  have pc : |(model.fl a - a) * (model.fl b - b)| ≤ (model.u * A + eta) * (model.u * B + eta) := by
    rw [abs_mul]
    have h := mul_le_mul h1' h2' (abs_nonneg _) (by nlinarith [u0, hA, en])
    exact h
  have hpc : |model.fl a * model.fl b - a * b| ≤
      (model.u * A + eta) * B + A * (model.u * B + eta) +
        (model.u * A + eta) * (model.u * B + eta) := by
    have h := abs_add_three ((model.fl a - a) * b) (a * (model.fl b - b))
      ((model.fl a - a) * (model.fl b - b))
    rw [← split2] at h
    linarith [pa, pb, pc, h]
  -- assemble
  have hfinal : |model.fl (model.fl a * model.fl b) - a * b| ≤
      (4 * model.u * A * B + 5 * eta * (A + B + 1)) +
      ((model.u * A + eta) * B + A * (model.u * B + eta) +
        (model.u * A + eta) * (model.u * B + eta)) := by
    rw [show model.fl (model.fl a * model.fl b) - a * b =
        (model.fl (model.fl a * model.fl b) - model.fl a * model.fl b) +
        (model.fl a * model.fl b - a * b) by ring]
    have h := abs_add_le (model.fl (model.fl a * model.fl b) - model.fl a * model.fl b)
      (model.fl a * model.fl b - a * b)
    linarith [h, h1c', hpc]
  have hetaS : eta ≤ A + B + 1 := by nlinarith [hA, hB, en]
  have heta2h : eta * eta ≤ eta * (A + B + 1) := by nlinarith [en, hetaS, heta1]
  have hs3 : (model.u * A + eta) * (model.u * B + eta) ≤
      model.u * A * B + 3 * eta * (A + B + 1) := by
    have expand : (model.u * A + eta) * (model.u * B + eta) =
        model.u * model.u * A * B + model.u * A * eta + eta * (model.u * B) + eta ^ 2 := by ring
    have h1p : model.u * model.u * A * B ≤ model.u * A * B := by
      have hAB : 0 ≤ A * B := mul_nonneg hA hB
      have hu2 : model.u * model.u ≤ model.u := by nlinarith [u1, u0]
      have huA : model.u * model.u * A ≤ model.u * A := mul_le_mul_of_nonneg_right hu2 hA
      exact mul_le_mul_of_nonneg_right huA hB
    have h2p : model.u * A * eta ≤ eta * (A + B + 1) := by
      nlinarith [u1, hA, hB, en]
    have h3p : model.u * B * eta ≤ eta * (A + B + 1) := by
      nlinarith [u1, hA, hB, en]
    nlinarith [expand, h1p, h2p, h3p, heta2h]
  have hs1 : (model.u * A + eta) * B ≤ model.u * A * B + eta * (A + B + 1) := by
    nlinarith [en, hA, hB, u0, hetaS]
  have hs2 : A * (model.u * B + eta) ≤ model.u * A * B + eta * (A + B + 1) := by
    nlinarith [en, hA, hB, u0, hetaS]
  have hpc' : (model.u * A + eta) * B + A * (model.u * B + eta) + (model.u * A + eta) * (model.u * B + eta) ≤
      3 * model.u * A * B + 5 * eta * (A + B + 1) := by
    linarith [hs1, hs2, hs3]
  have hsum : (4 * model.u * A * B + 5 * eta * (A + B + 1)) +
      ((model.u * A + eta) * B + A * (model.u * B + eta) + (model.u * A + eta) * (model.u * B + eta)) ≤
      7 * model.u * A * B + 9 * eta * (A + B + 1) := by
    linarith [hpc']
  linarith [hfinal, hsum]

theorem fl_mul_ops_err_total (a b af bf : ℝ) (A B ea eb : ℝ)
    (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hf_ea : |af - a| ≤ ea) (hf_eb : |bf - b| ≤ eb)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hea : 0 ≤ ea) (heb : 0 ≤ eb) :
    |model.fl (af * bf) - a * b| ≤
      model.u * ((A + ea) * (B + eb)) + eta + ea * (B + eb) + A * eb := by
  have u0 := model.u_pos
  have u1 : model.u ≤ 1 := model.u_lt_one.le
  have en := eta_pos
  have hfaf : |af| ≤ A + ea := by
    have h := abs_add_le a (af - a)
    rw [show a + (af - a) = af by ring] at h
    linarith
  have hbfb : |bf| ≤ B + eb := by
    have h := abs_add_le b (bf - b)
    rw [show b + (bf - b) = bf by ring] at h
    linarith
  have hmul : |af * bf| ≤ (A + ea) * (B + eb) := by
    rw [abs_mul]
    exact mul_le_mul hfaf hbfb (abs_nonneg _) (by nlinarith [hA, hB, en, hea, heb])
  have h1 := model_abs_err_total (af * bf)
  have habs : |model.fl (af * bf) - af * bf| ≤ model.u * ((A + ea) * (B + eb)) + eta := by
    have hu2 : model.u * |af * bf| ≤ model.u * ((A + ea) * (B + eb)) :=
      mul_le_mul_of_nonneg_left hmul u0.le
    nlinarith [h1, eta_pos, eta_eq_def]
  have he : af * bf - a * b = af * (bf - b) + (af - a) * b := by ring
  have hpmf : |af * (bf - b)| ≤ (A + ea) * eb := by
    rw [abs_mul]
    exact mul_le_mul hfaf hf_eb (abs_nonneg _) (by nlinarith [hA, en, hea])
  have hpm : |(af - a) * b| ≤ ea * B := by
    rw [abs_mul]
    exact mul_le_mul hf_ea hb (abs_nonneg _) hea
  have hsplit : |af * bf - a * b| ≤ (A + ea) * eb + ea * B := by
    have h := abs_add_le (af * (bf - b)) ((af - a) * b)
    rw [he]
    nlinarith [h, hpmf, hpm]
  have hadd := abs_add_le (model.fl (af * bf) - af * bf) (af * bf - a * b)
  have e : model.fl (af * bf) - af * bf + (af * bf - a * b) = model.fl (af * bf) - a * b := by ring
  rw [e] at hadd
  have hsub : ea * (B + eb) + A * eb = (A + ea) * eb + ea * B := by ring
  nlinarith [hadd, habs, hsplit, hsub, hea, heb, hA, hB, en, u0, u1, eta_eq_def]

end LightRT.Robust
