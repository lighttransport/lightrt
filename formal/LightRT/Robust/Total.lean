/-
  Range-free (subnormal-safe) numerator bound for the Woop `t`.

  `num_err` in `BVH/ExactPrune.lean` bounds the rounded numerator through
  `RoundingModel.abs_err`, which needs `InRange`. Here each rounding is
  instead bounded by `u |x| + eta` (`TotalErr.model_abs_err_total`,
  `eta = 2^-150`):

  * `num_err_total`: numerator within `4u(b0+b1+b2) + 8eta`;
  * `den_bounds_total`: denominator within `4eta` of the relative bounds;
  * `quot_bounds_total`: `|fl(N/D) - E/A| <= 40uM + 100eta(1+M)/a0 + 4eta`
    given a positive lower bound `a0` on the exact denominator (and
    `4eta <= a0/2`);
  * `woop_t_err_total` / `woop_t_err_total_model`: the full Woop `t` error
    with **no** `InRange` hypothesis. The price is the `eta/a0` term: when
    the projected area (`a0 <= sum e`) is tiny the bound degrades, which is
    exactly the subnormal/degenerate case.
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


set_option maxHeartbeats 1600000 in
theorem quot_bounds_total (hu : R.u ≤ 1 / 1000) (N D E A B M a0 : ℝ)
    (a0pos : 0 < a0) (hAa0 : a0 ≤ A)
    (hηa : 4 * eta ≤ a0 / 2)
    (Dpos : 0 < D)
    (Dlo : (1 - R.u) * ((1 - R.u) * A) - 4 * eta ≤ D)
    (Dhi : D ≤ (1 + R.u) * ((1 + R.u) * A) + 4 * eta)
    (NB : |N - E| ≤ 4 * R.u * B + 8 * eta) (hE : |E| ≤ B) (BA : B ≤ A * M)
    (hM : 0 ≤ M) (hB0 : 0 ≤ B)
    (rq : |R.fl (N / D) - N / D| ≤ R.u * |N / D| + eta) :
    |R.fl (N / D) - E / A| ≤ 40 * R.u * M + 100 * eta * (1 + M) / a0 + 4 * eta := by
  have u0 := R.u_pos
  have un : R.u ≤ 1 := R.u_lt_one.le
  have en := eta_pos
  have hA : 0 < A := lt_of_lt_of_le a0pos hAa0
  have hAn : 0 ≤ A := hA.le
  have hu2 : R.u * R.u ≤ R.u := by nlinarith [u0.le, un]
  have hAD : 0 < A * D := mul_pos hA Dpos
  have h4e : 4 * eta * A ≤ A * A / 2 := by nlinarith [hηa, hAa0, hAn]
  have hsq : (1:ℝ) / 4 ≤ (1 - R.u) * (1 - R.u) := by nlinarith [u0.le, un, hu2]
  have hADge : A * A / 4 ≤ A * D := by
    have h1 : (1 - R.u) * ((1 - R.u) * A) = (1 - R.u) * (1 - R.u) * A := by ring
    have h2 : A * ((1 - R.u) * (1 - R.u) * A) = (1 - R.u) * (1 - R.u) * (A * A) := by ring
    have := mul_le_mul_of_nonneg_left Dlo hAn
    nlinarith [this, h1, h2, h4e, hsq, hAn, mul_nonneg hAn hAn]
  have hADabs : |A - D| ≤ 3 * R.u * A + 4 * eta := by
    rw [abs_le]
    constructor
    · nlinarith [Dhi, hAn, hu2, u0.le, un]
    · nlinarith [Dlo, hAn, hu2, u0.le, un]
  have hnum : |N * A - E * D| ≤ 7 * R.u * (A * B) + 8 * eta * A + 4 * eta * B := by
    have heq : N * A - E * D = (N - E) * A + E * (A - D) := by ring
    have h1 : |N * A - E * D| ≤ |N - E| * A + |E| * |A - D| := by
      rw [heq]
      calc |(N - E) * A + E * (A - D)|
          ≤ |(N - E) * A| + |E * (A - D)| := abs_add_le _ _
        _ = |N - E| * A + |E| * |A - D| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hAn]
    have hne1 : |N - E| * A ≤ (4 * R.u * B + 8 * eta) * A :=
      mul_le_mul_of_nonneg_right NB hAn
    have h2 : |E| * |A - D| ≤ B * (3 * R.u * A + 4 * eta) :=
      mul_le_mul hE hADabs (abs_nonneg _) hB0
    nlinarith [h1, hne1, h2, hAn, hB0, hM]
  have hratio : |N / D - E / A| ≤ 28 * R.u * M + 48 * eta * (1 + M) / a0 := by
    have heq : N / D - E / A = (N * A - E * D) / (A * D) := by field_simp
    rw [heq, abs_div, abs_of_pos hAD, div_le_iff₀ hAD]
    have hAdiv : A ≤ A * (A / a0) := by
      have h1 : 1 ≤ A / a0 := (le_div_iff₀ a0pos).2 (by linarith)
      simpa using mul_le_mul_of_nonneg_left h1 hAn
    have hlow : 7 * R.u * (A * B) + 8 * eta * A + 4 * eta * B ≤
        7 * R.u * (A * (A * M)) + 12 * eta * (1 + M) * A := by
      nlinarith [BA, hB0, hM, hAn, mul_le_mul_of_nonneg_left BA hAn]
    have hcoef : 0 ≤ 28 * R.u * M + 48 * eta * (1 + M) / a0 := by positivity
    have hrhs : 7 * R.u * (A * (A * M)) + 12 * eta * (1 + M) * A ≤
        (28 * R.u * M + 48 * eta * (1 + M) / a0) * (A * D) := by
      have h1 := mul_le_mul_of_nonneg_left hADge hcoef
      have e1 : (28 * R.u * M + 48 * eta * (1 + M) / a0) * (A * A / 4) =
          7 * R.u * (A * (A * M)) + 12 * eta * (1 + M) * (A * A / a0) := by ring
      have h2 : 7 * R.u * (A * (A * M)) + 12 * eta * (1 + M) * (A * A / a0) ≥
          7 * R.u * (A * (A * M)) + 12 * eta * (1 + M) * A := by
        have h3 : A * A / a0 = A * (A / a0) := by ring
        have h4 : 1 ≤ A / a0 := (le_div_iff₀ a0pos).2 (by linarith)
        have h5 : 0 ≤ 12 * eta * (1 + M) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h4 hAn, h5]
      linarith
    linarith
  have hEA : |E / A| ≤ M := by
    rw [abs_div, abs_of_pos hA, div_le_iff₀ hA]
    exact hE.trans (by rwa [mul_comm] at BA)
  have hNabs : |N / D| ≤ M + (28 * R.u * M + 48 * eta * (1 + M) / a0) := by
    have := abs_sub_abs_le_abs_sub (N / D) (E / A)
    linarith [hratio]
  have htri : |R.fl (N / D) - E / A| ≤
      |R.fl (N / D) - N / D| + |N / D - E / A| := by
    have := abs_add_le (R.fl (N / D) - N / D) (N / D - E / A)
    rwa [show R.fl (N / D) - N / D + (N / D - E / A) = R.fl (N / D) - E / A by ring] at this
  have hfl : |R.fl (N / D) - N / D| ≤
      R.u * (M + (28 * R.u * M + 48 * eta * (1 + M) / a0)) + eta := by
    have := mul_le_mul_of_nonneg_left hNabs u0.le
    linarith
  have h1M : 0 ≤ 1 + M := by linarith
  have hY : 0 ≤ eta * (1 + M) / a0 := div_nonneg (mul_nonneg en.le h1M) a0pos.le
  have huY : R.u * (eta * (1 + M) / a0) ≤ eta * (1 + M) / a0 := by
    have := mul_le_mul_of_nonneg_right un hY
    simpa using this
  have hfl' : |R.fl (N / D) - N / D| ≤
      R.u * M + 28 * R.u * R.u * M + 48 * (R.u * (eta * (1 + M) / a0)) + eta := by
    have := hfl
    have e : R.u * (M + (28 * R.u * M + 48 * eta * (1 + M) / a0)) + eta =
        R.u * M + 28 * R.u * R.u * M + 48 * (R.u * (eta * (1 + M) / a0)) + eta := by ring
    rwa [e] at this
  have hratio' : |N / D - E / A| ≤ 28 * R.u * M + 48 * (eta * (1 + M) / a0) := by
    have := hratio
    have e : 28 * R.u * M + 48 * eta * (1 + M) / a0 =
        28 * R.u * M + 48 * (eta * (1 + M) / a0) := by ring
    rwa [e] at this
  have hcorr : |R.fl (N / D) - E / A| ≤
      (R.u * M + 28 * R.u * R.u * M + 48 * (R.u * (eta * (1 + M) / a0)) + eta) +
      (28 * R.u * M + 48 * (eta * (1 + M) / a0)) := by
    linarith [htri, hfl', hratio']
  have hbound : (R.u * M + 28 * R.u * R.u * M + 48 * (R.u * (eta * (1 + M) / a0)) + eta) +
      (28 * R.u * M + 48 * (eta * (1 + M) / a0)) ≤
      40 * R.u * M + 100 * (eta * (1 + M) / a0) + 4 * eta := by
    have h28 : 28 * (R.u * R.u) * M ≤ 28 * R.u * M := by nlinarith [hu2, hM]
    have h48 : 48 * (R.u * (eta * (1 + M) / a0)) ≤ 48 * (eta * (1 + M) / a0) := by
      have := mul_le_mul_of_nonneg_right huY (by norm_num : (0:ℝ) ≤ 48)
      nlinarith [this]
    nlinarith [h28, h48, hM, hY, en, hu2, hcorr]
  have e : 40 * R.u * M + 100 * eta * (1 + M) / a0 + 4 * eta =
      40 * R.u * M + 100 * (eta * (1 + M) / a0) + 4 * eta := by ring
  rw [e]
  linarith [hcorr, hbound]

set_option maxHeartbeats 1600000 in
theorem woop_t_err_total (hu : R.u ≤ 1 / 1000)
    (e0 e1 e2 z0 z1 z2 M a0 : ℝ) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M) (hM : 0 ≤ M)
    (a0pos : 0 < a0) (hA0 : a0 ≤ e0 + e1 + e2) (hηa : 4 * eta ≤ a0 / 2)
    (r0 : |R.fl (e0 * z0) - e0 * z0| ≤ R.u * (e0 * |z0|) + eta)
    (r1 : |R.fl (e1 * z1) - e1 * z1| ≤ R.u * (e1 * |z1|) + eta)
    (r2 : |R.fl (e2 * z2) - e2 * z2| ≤ R.u * (e2 * |z2|) + eta)
    (rs : |R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) -
      (R.fl (e0 * z0) + R.fl (e1 * z1))| ≤
      R.u * |R.fl (e0 * z0) + R.fl (e1 * z1)| + eta)
    (rN : |R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) -
      (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2))| ≤
      R.u * |R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)| + eta)
    (rd : |R.fl (e0 + e1) - (e0 + e1)| ≤ R.u * (e0 + e1) + eta)
    (rD : |R.fl (R.fl (e0 + e1) + e2) - (R.fl (e0 + e1) + e2)| ≤
      R.u * |R.fl (e0 + e1) + e2| + eta)
    (hD : R.fl (R.fl (e0 + e1) + e2) ≠ 0)
    (rq : |R.fl (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
      R.fl (R.fl (e0 + e1) + e2)) -
      R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
      R.fl (R.fl (e0 + e1) + e2)| ≤
      R.u * |R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
        R.fl (R.fl (e0 + e1) + e2)| + eta) :
    |R.fl (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
        R.fl (R.fl (e0 + e1) + e2)) -
      (e0 * z0 + e1 * z1 + e2 * z2) / (e0 + e1 + e2)| ≤
      40 * R.u * M + 100 * eta * (1 + M) / a0 + 4 * eta := by
  set b0 := e0 * |z0|
  set b1 := e1 * |z1|
  set b2 := e2 * |z2|
  set A := e0 + e1 + e2
  set B := b0 + b1 + b2
  set N := R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2))
  set D := R.fl (R.fl (e0 + e1) + e2)
  set E := e0 * z0 + e1 * z1 + e2 * z2
  have hb0 : 0 ≤ b0 := by rw [show b0 = e0 * |z0| from rfl]; positivity
  have hb1 : 0 ≤ b1 := by rw [show b1 = e1 * |z1| from rfl]; positivity
  have hb2 : 0 ≤ b2 := by rw [show b2 = e2 * |z2| from rfl]; positivity
  have hB0 : 0 ≤ B := by rw [show B = b0 + b1 + b2 from rfl]; linarith
  have hE : |E| ≤ B := by
    have := abs_add_three (e0 * z0) (e1 * z1) (e2 * z2)
    simp only [abs_mul, abs_of_nonneg he0, abs_of_nonneg he1, abs_of_nonneg he2] at this
    dsimp only [E, B, b0, b1, b2]; linarith
  have hBA : B ≤ A * M := by
    have h1 := mul_le_mul_of_nonneg_left hM0 he0
    have h2 := mul_le_mul_of_nonneg_left hM1 he1
    have h3 := mul_le_mul_of_nonneg_left hM2 he2
    dsimp only [A, B, b0, b1, b2]
    nlinarith
  have hNE := num_err_total R hu (R.fl (e0 * z0)) (R.fl (e1 * z1)) (R.fl (e2 * z2))
    (e0 * z0) (e1 * z1) (e2 * z2) b0 b1 b2 hb0 hb1 hb2
    (by dsimp only [b0]; exact r0) (by dsimp only [b1]; exact r1) (by dsimp only [b2]; exact r2)
    (by
      have hb : |e0 * z0| = b0 := by rw [show b0 = e0 * |z0| from rfl, abs_mul,
        abs_of_nonneg he0]
      have := abs_sub_abs_le_abs_sub (R.fl (e0 * z0)) (e0 * z0)
      nlinarith [r0, hb])
    (by
      have hb : |e1 * z1| = b1 := by rw [show b1 = e1 * |z1| from rfl, abs_mul,
        abs_of_nonneg he1]
      have := abs_sub_abs_le_abs_sub (R.fl (e1 * z1)) (e1 * z1)
      nlinarith [r1, hb])
    (by
      have hb : |e2 * z2| = b2 := by rw [show b2 = e2 * |z2| from rfl, abs_mul,
        abs_of_nonneg he2]
      have := abs_sub_abs_le_abs_sub (R.fl (e2 * z2)) (e2 * z2)
      nlinarith [r2, hb])
    rs rN
  obtain ⟨Dn, Dlo, Dhi⟩ := den_bounds_total R e0 e1 e2 he0 he1 he2 rd rD
  have Dpos : 0 < D := lt_of_le_of_ne Dn (Ne.symm hD)
  have hquot := quot_bounds_total R hu N D E A B M a0 a0pos hA0 hηa Dpos Dlo Dhi hNE hE hBA hM hB0 rq
  simpa only [N, D, E, A, B, b0, b1, b2] using hquot


set_option maxHeartbeats 1600000 in
/-- **Range-free Woop `t` error for the binary32 model.** No `InRange`
    hypothesis: each rounding uses `model_abs_err_total`. `a0` is a positive
    lower bound on the exact denominator (twice the projected area). -/
theorem woop_t_err_total_model
    (e0 e1 e2 z0 z1 z2 M a0 : ℝ) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M) (hM : 0 ≤ M)
    (a0pos : 0 < a0) (hA0 : a0 ≤ e0 + e1 + e2) (hηa : 4 * eta ≤ a0 / 2)
    (hD : model.fl (model.fl (e0 + e1) + e2) ≠ 0) :
    |model.fl (model.fl (model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) +
        model.fl (e2 * z2)) / model.fl (model.fl (e0 + e1) + e2)) -
      (e0 * z0 + e1 * z1 + e2 * z2) / (e0 + e1 + e2)| ≤
      40 * model.u * M + 100 * eta * (1 + M) / a0 + 4 * eta := by
  have hu : model.u ≤ 1 / 1000 := by
    unfold model; norm_num [zpow_neg]
  have h0 : |model.fl (e0 * z0) - e0 * z0| ≤ model.u * (e0 * |z0|) + eta := by
    simpa [eta, abs_mul, abs_of_nonneg he0] using model_abs_err_total (e0 * z0)
  have h1 : |model.fl (e1 * z1) - e1 * z1| ≤ model.u * (e1 * |z1|) + eta := by
    simpa [eta, abs_mul, abs_of_nonneg he1] using model_abs_err_total (e1 * z1)
  have h2 : |model.fl (e2 * z2) - e2 * z2| ≤ model.u * (e2 * |z2|) + eta := by
    simpa [eta, abs_mul, abs_of_nonneg he2] using model_abs_err_total (e2 * z2)
  have hs : |model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) -
      (model.fl (e0 * z0) + model.fl (e1 * z1))| ≤
      model.u * |model.fl (e0 * z0) + model.fl (e1 * z1)| + eta := by
    simpa [eta] using model_abs_err_total _
  have hN : |model.fl (model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) +
        model.fl (e2 * z2)) -
      (model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) + model.fl (e2 * z2))| ≤
      model.u * |model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) + model.fl (e2 * z2)| + eta := by
    simpa [eta] using model_abs_err_total _
  have hd : |model.fl (e0 + e1) - (e0 + e1)| ≤ model.u * (e0 + e1) + eta := by
    simpa [eta, abs_of_nonneg (by linarith : (0:ℝ) ≤ e0 + e1)] using model_abs_err_total (e0 + e1)
  have hDd : |model.fl (model.fl (e0 + e1) + e2) - (model.fl (e0 + e1) + e2)| ≤
      model.u * |model.fl (e0 + e1) + e2| + eta := by
    simpa [eta] using model_abs_err_total _
  exact woop_t_err_total model hu e0 e1 e2 z0 z1 z2 M a0 he0 he1 he2 hM0 hM1 hM2 hM
    a0pos hA0 hηa h0 h1 h2 hs hN hd hDd hD (by simpa [eta] using model_abs_err_total _)

set_option maxHeartbeats 1600000 in
theorem quot_bounds_total_tight (hu : R.u ≤ 1 / 1000) (N D E A B M a0 : ℝ)
    (a0pos : 0 < a0) (hAa0 : a0 ≤ A)
    (hηa : 4 * eta ≤ a0 / 2)
    (Dpos : 0 < D)
    (Dlo : (1 - R.u) * ((1 - R.u) * A) - 4 * eta ≤ D)
    (Dhi : D ≤ (1 + R.u) * ((1 + R.u) * A) + 4 * eta)
    (NB : |N - E| ≤ 4 * R.u * B + 8 * eta) (hE : |E| ≤ B) (BA : B ≤ A * M)
    (hM : 0 ≤ M) (hB0 : 0 ≤ B)
    (rq : |R.fl (N / D) - N / D| ≤ R.u * |N / D| + eta) :
    |R.fl (N / D) - E / A| ≤ 29.1 * R.u * M + 49 * eta * (1 + M) / a0 + eta := by
  have u0 := R.u_pos
  have un : R.u ≤ 1 := R.u_lt_one.le
  have en := eta_pos
  have hA : 0 < A := lt_of_lt_of_le a0pos hAa0
  have hAn : 0 ≤ A := hA.le
  have hu2 : R.u * R.u ≤ R.u := by nlinarith [u0.le, un]
  have hAD : 0 < A * D := mul_pos hA Dpos
  have h4e : 4 * eta * A ≤ A * A / 2 := by nlinarith [hηa, hAa0, hAn]
  have hsq : (1:ℝ) / 4 ≤ (1 - R.u) * (1 - R.u) := by nlinarith [u0.le, un, hu2]
  have hADge : A * A / 4 ≤ A * D := by
    have h1 : (1 - R.u) * ((1 - R.u) * A) = (1 - R.u) * (1 - R.u) * A := by ring
    have h2 : A * ((1 - R.u) * (1 - R.u) * A) = (1 - R.u) * (1 - R.u) * (A * A) := by ring
    have := mul_le_mul_of_nonneg_left Dlo hAn
    nlinarith [this, h1, h2, h4e, hsq, hAn, mul_nonneg hAn hAn]
  have hADabs : |A - D| ≤ 3 * R.u * A + 4 * eta := by
    rw [abs_le]
    constructor
    · nlinarith [Dhi, hAn, hu2, u0.le, un]
    · nlinarith [Dlo, hAn, hu2, u0.le, un]
  have hnum : |N * A - E * D| ≤ 7 * R.u * (A * B) + 8 * eta * A + 4 * eta * B := by
    have heq : N * A - E * D = (N - E) * A + E * (A - D) := by ring
    have h1 : |N * A - E * D| ≤ |N - E| * A + |E| * |A - D| := by
      rw [heq]
      calc |(N - E) * A + E * (A - D)|
          ≤ |(N - E) * A| + |E * (A - D)| := abs_add_le _ _
        _ = |N - E| * A + |E| * |A - D| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hAn]
    have hne1 : |N - E| * A ≤ (4 * R.u * B + 8 * eta) * A :=
      mul_le_mul_of_nonneg_right NB hAn
    have h2 : |E| * |A - D| ≤ B * (3 * R.u * A + 4 * eta) :=
      mul_le_mul hE hADabs (abs_nonneg _) hB0
    nlinarith [h1, hne1, h2, hAn, hB0, hM]
  have hratio : |N / D - E / A| ≤ 28 * R.u * M + 48 * eta * (1 + M) / a0 := by
    have heq : N / D - E / A = (N * A - E * D) / (A * D) := by field_simp
    rw [heq, abs_div, abs_of_pos hAD, div_le_iff₀ hAD]
    have hAdiv : A ≤ A * (A / a0) := by
      have h1 : 1 ≤ A / a0 := (le_div_iff₀ a0pos).2 (by linarith)
      simpa using mul_le_mul_of_nonneg_left h1 hAn
    have hlow : 7 * R.u * (A * B) + 8 * eta * A + 4 * eta * B ≤
        7 * R.u * (A * (A * M)) + 12 * eta * (1 + M) * A := by
      nlinarith [BA, hB0, hM, hAn, mul_le_mul_of_nonneg_left BA hAn]
    have hcoef : 0 ≤ 28 * R.u * M + 48 * eta * (1 + M) / a0 := by positivity
    have hrhs : 7 * R.u * (A * (A * M)) + 12 * eta * (1 + M) * A ≤
        (28 * R.u * M + 48 * eta * (1 + M) / a0) * (A * D) := by
      have h1 := mul_le_mul_of_nonneg_left hADge hcoef
      have e1 : (28 * R.u * M + 48 * eta * (1 + M) / a0) * (A * A / 4) =
          7 * R.u * (A * (A * M)) + 12 * eta * (1 + M) * (A * A / a0) := by ring
      have h2 : 7 * R.u * (A * (A * M)) + 12 * eta * (1 + M) * (A * A / a0) ≥
          7 * R.u * (A * (A * M)) + 12 * eta * (1 + M) * A := by
        have h3 : A * A / a0 = A * (A / a0) := by ring
        have h4 : 1 ≤ A / a0 := (le_div_iff₀ a0pos).2 (by linarith)
        have h5 : 0 ≤ 12 * eta * (1 + M) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h4 hAn, h5]
      linarith
    linarith
  have hEA : |E / A| ≤ M := by
    rw [abs_div, abs_of_pos hA, div_le_iff₀ hA]
    exact hE.trans (by rwa [mul_comm] at BA)
  have hNabs : |N / D| ≤ M + (28 * R.u * M + 48 * eta * (1 + M) / a0) := by
    have := abs_sub_abs_le_abs_sub (N / D) (E / A)
    linarith [hratio]
  have htri : |R.fl (N / D) - E / A| ≤
      |R.fl (N / D) - N / D| + |N / D - E / A| := by
    have := abs_add_le (R.fl (N / D) - N / D) (N / D - E / A)
    rwa [show R.fl (N / D) - N / D + (N / D - E / A) = R.fl (N / D) - E / A by ring] at this
  have hfl : |R.fl (N / D) - N / D| ≤
      R.u * (M + (28 * R.u * M + 48 * eta * (1 + M) / a0)) + eta := by
    have := mul_le_mul_of_nonneg_left hNabs u0.le
    linarith
  have h1M : 0 ≤ 1 + M := by linarith
  have hY : 0 ≤ eta * (1 + M) / a0 := div_nonneg (mul_nonneg en.le h1M) a0pos.le
  have huY : R.u * (eta * (1 + M) / a0) ≤ eta * (1 + M) / a0 := by
    have := mul_le_mul_of_nonneg_right un hY
    simpa using this
  have hfl' : |R.fl (N / D) - N / D| ≤
      R.u * M + 28 * R.u * R.u * M + 48 * (R.u * (eta * (1 + M) / a0)) + eta := by
    have := hfl
    have e : R.u * (M + (28 * R.u * M + 48 * eta * (1 + M) / a0)) + eta =
        R.u * M + 28 * R.u * R.u * M + 48 * (R.u * (eta * (1 + M) / a0)) + eta := by ring
    rwa [e] at this
  have hratio' : |N / D - E / A| ≤ 28 * R.u * M + 48 * (eta * (1 + M) / a0) := by
    have := hratio
    have e : 28 * R.u * M + 48 * eta * (1 + M) / a0 =
        28 * R.u * M + 48 * (eta * (1 + M) / a0) := by ring
    rwa [e] at this
  have hcorr : |R.fl (N / D) - E / A| ≤
      (R.u * M + 28 * R.u * R.u * M + 48 * (R.u * (eta * (1 + M) / a0)) + eta) +
      (28 * R.u * M + 48 * (eta * (1 + M) / a0)) := by
    linarith [htri, hfl', hratio']
  have hbound : (R.u * M + 28 * R.u * R.u * M + 48 * (R.u * (eta * (1 + M) / a0)) + eta) +
      (28 * R.u * M + 48 * (eta * (1 + M) / a0)) ≤
      29.1 * R.u * M + 49 * (eta * (1 + M) / a0) + eta := by
    have hu3 : R.u * R.u ≤ R.u / 1000 := by nlinarith [un, u0.le]
    have h28 : 28 * (R.u * R.u) * M ≤ 0.1 * R.u * M := by nlinarith [hu3, hM, u0.le]
    have h48u : 48 * R.u ≤ 1 := by nlinarith [un]
    have h48 : 48 * (R.u * (eta * (1 + M) / a0)) ≤ eta * (1 + M) / a0 := by
      have := mul_le_mul_of_nonneg_right h48u hY
      nlinarith [this]
    nlinarith [h28, h48, hM, hY, en, hu2]
  have e : 29.1 * R.u * M + 49 * eta * (1 + M) / a0 + eta =
      29.1 * R.u * M + 49 * (eta * (1 + M) / a0) + eta := by ring
  rw [e]
  linarith [hcorr, hbound]



set_option maxHeartbeats 1600000 in
theorem woop_t_err_total_tight (hu : R.u ≤ 1 / 1000)
    (e0 e1 e2 z0 z1 z2 M a0 : ℝ) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M) (hM : 0 ≤ M)
    (a0pos : 0 < a0) (hA0 : a0 ≤ e0 + e1 + e2) (hηa : 4 * eta ≤ a0 / 2)
    (r0 : |R.fl (e0 * z0) - e0 * z0| ≤ R.u * (e0 * |z0|) + eta)
    (r1 : |R.fl (e1 * z1) - e1 * z1| ≤ R.u * (e1 * |z1|) + eta)
    (r2 : |R.fl (e2 * z2) - e2 * z2| ≤ R.u * (e2 * |z2|) + eta)
    (rs : |R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) -
      (R.fl (e0 * z0) + R.fl (e1 * z1))| ≤
      R.u * |R.fl (e0 * z0) + R.fl (e1 * z1)| + eta)
    (rN : |R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) -
      (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2))| ≤
      R.u * |R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)| + eta)
    (rd : |R.fl (e0 + e1) - (e0 + e1)| ≤ R.u * (e0 + e1) + eta)
    (rD : |R.fl (R.fl (e0 + e1) + e2) - (R.fl (e0 + e1) + e2)| ≤
      R.u * |R.fl (e0 + e1) + e2| + eta)
    (hD : R.fl (R.fl (e0 + e1) + e2) ≠ 0)
    (rq : |R.fl (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
      R.fl (R.fl (e0 + e1) + e2)) -
      R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
      R.fl (R.fl (e0 + e1) + e2)| ≤
      R.u * |R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
        R.fl (R.fl (e0 + e1) + e2)| + eta) :
    |R.fl (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
        R.fl (R.fl (e0 + e1) + e2)) -
      (e0 * z0 + e1 * z1 + e2 * z2) / (e0 + e1 + e2)| ≤
      29.1 * R.u * M + 49 * eta * (1 + M) / a0 + eta := by
  set b0 := e0 * |z0|
  set b1 := e1 * |z1|
  set b2 := e2 * |z2|
  set A := e0 + e1 + e2
  set B := b0 + b1 + b2
  set N := R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2))
  set D := R.fl (R.fl (e0 + e1) + e2)
  set E := e0 * z0 + e1 * z1 + e2 * z2
  have hb0 : 0 ≤ b0 := by rw [show b0 = e0 * |z0| from rfl]; positivity
  have hb1 : 0 ≤ b1 := by rw [show b1 = e1 * |z1| from rfl]; positivity
  have hb2 : 0 ≤ b2 := by rw [show b2 = e2 * |z2| from rfl]; positivity
  have hB0 : 0 ≤ B := by rw [show B = b0 + b1 + b2 from rfl]; linarith
  have hE : |E| ≤ B := by
    have := abs_add_three (e0 * z0) (e1 * z1) (e2 * z2)
    simp only [abs_mul, abs_of_nonneg he0, abs_of_nonneg he1, abs_of_nonneg he2] at this
    dsimp only [E, B, b0, b1, b2]; linarith
  have hBA : B ≤ A * M := by
    have h1 := mul_le_mul_of_nonneg_left hM0 he0
    have h2 := mul_le_mul_of_nonneg_left hM1 he1
    have h3 := mul_le_mul_of_nonneg_left hM2 he2
    dsimp only [A, B, b0, b1, b2]
    nlinarith
  have hNE := num_err_total R hu (R.fl (e0 * z0)) (R.fl (e1 * z1)) (R.fl (e2 * z2))
    (e0 * z0) (e1 * z1) (e2 * z2) b0 b1 b2 hb0 hb1 hb2
    (by dsimp only [b0]; exact r0) (by dsimp only [b1]; exact r1) (by dsimp only [b2]; exact r2)
    (by
      have hb : |e0 * z0| = b0 := by rw [show b0 = e0 * |z0| from rfl, abs_mul,
        abs_of_nonneg he0]
      have := abs_sub_abs_le_abs_sub (R.fl (e0 * z0)) (e0 * z0)
      nlinarith [r0, hb])
    (by
      have hb : |e1 * z1| = b1 := by rw [show b1 = e1 * |z1| from rfl, abs_mul,
        abs_of_nonneg he1]
      have := abs_sub_abs_le_abs_sub (R.fl (e1 * z1)) (e1 * z1)
      nlinarith [r1, hb])
    (by
      have hb : |e2 * z2| = b2 := by rw [show b2 = e2 * |z2| from rfl, abs_mul,
        abs_of_nonneg he2]
      have := abs_sub_abs_le_abs_sub (R.fl (e2 * z2)) (e2 * z2)
      nlinarith [r2, hb])
    rs rN
  obtain ⟨Dn, Dlo, Dhi⟩ := den_bounds_total R e0 e1 e2 he0 he1 he2 rd rD
  have Dpos : 0 < D := lt_of_le_of_ne Dn (Ne.symm hD)
  have hquot := quot_bounds_total_tight R hu N D E A B M a0 a0pos hA0 hηa Dpos Dlo Dhi hNE hE hBA hM hB0 rq
  simpa only [N, D, E, A, B, b0, b1, b2] using hquot



set_option maxHeartbeats 1600000 in
/-- **Range-free Woop `t` error for the binary32 model.** No `InRange`
    hypothesis: each rounding uses `model_abs_err_total`. `a0` is a positive
    lower bound on the exact denominator (twice the projected area). -/
theorem woop_t_err_total_model_tight
    (e0 e1 e2 z0 z1 z2 M a0 : ℝ) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M) (hM : 0 ≤ M)
    (a0pos : 0 < a0) (hA0 : a0 ≤ e0 + e1 + e2) (hηa : 4 * eta ≤ a0 / 2)
    (hD : model.fl (model.fl (e0 + e1) + e2) ≠ 0) :
    |model.fl (model.fl (model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) +
        model.fl (e2 * z2)) / model.fl (model.fl (e0 + e1) + e2)) -
      (e0 * z0 + e1 * z1 + e2 * z2) / (e0 + e1 + e2)| ≤
      29.1 * model.u * M + 49 * eta * (1 + M) / a0 + eta := by
  have hu : model.u ≤ 1 / 1000 := by
    unfold model; norm_num [zpow_neg]
  have h0 : |model.fl (e0 * z0) - e0 * z0| ≤ model.u * (e0 * |z0|) + eta := by
    simpa [eta, abs_mul, abs_of_nonneg he0] using model_abs_err_total (e0 * z0)
  have h1 : |model.fl (e1 * z1) - e1 * z1| ≤ model.u * (e1 * |z1|) + eta := by
    simpa [eta, abs_mul, abs_of_nonneg he1] using model_abs_err_total (e1 * z1)
  have h2 : |model.fl (e2 * z2) - e2 * z2| ≤ model.u * (e2 * |z2|) + eta := by
    simpa [eta, abs_mul, abs_of_nonneg he2] using model_abs_err_total (e2 * z2)
  have hs : |model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) -
      (model.fl (e0 * z0) + model.fl (e1 * z1))| ≤
      model.u * |model.fl (e0 * z0) + model.fl (e1 * z1)| + eta := by
    simpa [eta] using model_abs_err_total _
  have hN : |model.fl (model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) +
        model.fl (e2 * z2)) -
      (model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) + model.fl (e2 * z2))| ≤
      model.u * |model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) + model.fl (e2 * z2)| + eta := by
    simpa [eta] using model_abs_err_total _
  have hd : |model.fl (e0 + e1) - (e0 + e1)| ≤ model.u * (e0 + e1) + eta := by
    simpa [eta, abs_of_nonneg (by linarith : (0:ℝ) ≤ e0 + e1)] using model_abs_err_total (e0 + e1)
  have hDd : |model.fl (model.fl (e0 + e1) + e2) - (model.fl (e0 + e1) + e2)| ≤
      model.u * |model.fl (e0 + e1) + e2| + eta := by
    simpa [eta] using model_abs_err_total _
  exact woop_t_err_total_tight model hu e0 e1 e2 z0 z1 z2 M a0 he0 he1 he2 hM0 hM1 hM2 hM
    a0pos hA0 hηa h0 h1 h2 hs hN hd hDd hD (by simpa [eta] using model_abs_err_total _)

set_option maxHeartbeats 1600000 in
/-- **Range-free Woop `t` error, nonpositive edge-sign class.** Both the
    numerator and the denominator flip sign, so the error bound is unchanged;
    `a0` bounds the absolute exact denominator. -/
theorem woop_t_err_total_model_tight_neg
    (e0 e1 e2 z0 z1 z2 M a0 : ℝ) (he0 : e0 ≤ 0) (he1 : e1 ≤ 0) (he2 : e2 ≤ 0)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M) (hM : 0 ≤ M)
    (a0pos : 0 < a0) (hA0 : a0 ≤ -(e0 + e1 + e2)) (hηa : 4 * eta ≤ a0 / 2)
    (hD : model.fl (model.fl (e0 + e1) + e2) ≠ 0) :
    |model.fl (model.fl (model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) +
        model.fl (e2 * z2)) / model.fl (model.fl (e0 + e1) + e2)) -
      (e0 * z0 + e1 * z1 + e2 * z2) / (e0 + e1 + e2)| ≤
      29.1 * model.u * M + 49 * eta * (1 + M) / a0 + eta := by
  have flip : ∀ a b : ℝ, model.fl (a + b) = -model.fl (-a + -b) := by
    intro a b
    have h := model.neg (a + b)
    rw [show -(a + b) = -a + -b by ring] at h
    linarith [h]
  have flipm : ∀ e z : ℝ, model.fl (e * z) = -model.fl (-e * z) := by
    intro e z
    have h := model.neg (e * z)
    rw [show -(e * z) = -e * z by ring] at h
    linarith [h]
  have hD' : model.fl (model.fl (-e0 + -e1) + -e2) ≠ 0 := by
    intro h
    apply hD
    rw [flip (model.fl (e0 + e1)) e2, flip e0 e1, neg_neg, h, neg_zero]
  have key := woop_t_err_total_model_tight (-e0) (-e1) (-e2) z0 z1 z2 M a0
    (by linarith) (by linarith) (by linarith) hM0 hM1 hM2 hM a0pos
    (by linarith) hηa hD'
  have eqN : model.fl (model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) + model.fl (e2 * z2)) =
      -model.fl (model.fl (model.fl (-e0 * z0) + model.fl (-e1 * z1)) + model.fl (-e2 * z2)) := by
    rw [flip (model.fl (model.fl (e0 * z0) + model.fl (e1 * z1))) (model.fl (e2 * z2)),
        flip (model.fl (e0 * z0)) (model.fl (e1 * z1)),
        flipm e0 z0, flipm e1 z1, flipm e2 z2]
    simp only [neg_neg]
  have eqD : model.fl (model.fl (e0 + e1) + e2) =
      -model.fl (model.fl (-e0 + -e1) + -e2) := by
    rw [flip (model.fl (e0 + e1)) e2, flip e0 e1, neg_neg]
  have hdiv : model.fl (model.fl (model.fl (model.fl (e0 * z0) + model.fl (e1 * z1)) +
        model.fl (e2 * z2)) / model.fl (model.fl (e0 + e1) + e2)) =
      model.fl (model.fl (model.fl (model.fl (-e0 * z0) + model.fl (-e1 * z1)) +
        model.fl (-e2 * z2)) / model.fl (model.fl (-e0 + -e1) + -e2)) := by
    rw [eqN, eqD, neg_div_neg_eq]
  have hEA : (e0 * z0 + e1 * z1 + e2 * z2) / (e0 + e1 + e2) =
      ((-e0) * z0 + (-e1) * z1 + (-e2) * z2) / ((-e0) + (-e1) + (-e2)) := by
    rw [show (-e0) * z0 + (-e1) * z1 + (-e2) * z2 = -(e0 * z0 + e1 * z1 + e2 * z2) by ring,
        show (-e0) + (-e1) + (-e2) = -(e0 + e1 + e2) by ring,
        neg_div_neg_eq]
  rw [hdiv, hEA]
  exact key

end LightRT.Robust
