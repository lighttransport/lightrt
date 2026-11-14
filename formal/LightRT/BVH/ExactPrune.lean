/-
  Exact nearest hit WITH pruning, for the watertight (Woop) leaf.

  `Flat.run_root` needs C2: a pushed node key `tn` is at most the computed `t`
  of every primitive below it that beats `best`. The slab entry does not satisfy
  it (rounded `tnear` can exceed a grazing triangle's rounded `t`), so plain
  `EXACT_NEAREST` pushed `tmin` and lost pruning (`run_exact`).

  The Woop leaf's `t` is a weighted mean of the vertex depths along the ray's
  dominant axis: `t = fl(N / D)` with `N = fl(fl(fl(e0 z0) + fl(e1 z1)) + fl(e2 z2))`,
  `D = fl(fl(e0 + e1) + e2)`, where after the sign test all edge values `e_i`
  share a sign and `z_i = fl(sz * fl(v_i[kz] - o[kz]))`.

  1. `woop_t_lower` / `woop_t_lower_neg`: `t ≥ m - 10 u M` when `m ≤ z_i` and
     `|z_i| ≤ M` (both edge-sign cases).
  2. `depth_bounds`: for a vertex coordinate in `[lo, hi]`, the rounded depth
     lies between the rounded depths of the two faces (rounding is monotone),
     so `m := min(zlo, zhi)`, `M := max(|zlo|, |zhi|)` work for every vertex in
     the box.
  3. `key_le`: the float key `fl(m - fl(c * M))` with `c ≥ 32 u` is at most
     `m - 16 u M`.

  Hence a node key `max(key, tmin)` satisfies C2 for every triangle whose exact
  vertices lie in the node box (`LEAF_BOX_EXACT` on vertex-format leaves), and
  `run_root` gives exactly the brute-force nearest `t` while pruning by `best`.
  All under the relative rounding model's `InRange` hypotheses (no underflow).
-/
import LightRT.FP.Model

namespace LightRT.BVH.ExactPrune
open LightRT.FP

variable (R : RoundingModel)

theorem fl_abs_le' {x : ℝ} (hr : R.InRange x) : |R.fl x| ≤ (1 + R.u) * |x| := by
  have h := R.abs_err hr
  have := abs_sub_abs_le_abs_sub (R.fl x) x
  nlinarith [abs_nonneg x]

theorem fl_ge {x : ℝ} (hr : R.InRange x) : x - R.u * |x| ≤ R.fl x := by
  have h := R.abs_err hr
  have := (abs_le.1 h).1
  linarith

theorem fl_le {x : ℝ} (hr : R.InRange x) : R.fl x ≤ x + R.u * |x| := by
  have h := R.abs_err hr
  have := (abs_le.1 h).2
  linarith

/-- Numerator: `fl(fl(p0 + p1) + p2)` vs the exact `E0 + E1 + E2`, where each
    rounded product `p_i` is within `u b_i` of `E_i` and `|p_i| ≤ (1+u) b_i`. -/
theorem num_err (hu : R.u ≤ 1 / 1000) (p0 p1 p2 E0 E1 E2 b0 b1 b2 : ℝ)
    (b0n : 0 ≤ b0) (b1n : 0 ≤ b1) (b2n : 0 ≤ b2)
    (q0 : |p0 - E0| ≤ R.u * b0) (q1 : |p1 - E1| ≤ R.u * b1) (q2 : |p2 - E2| ≤ R.u * b2)
    (a0 : |p0| ≤ (1 + R.u) * b0) (a1 : |p1| ≤ (1 + R.u) * b1) (a2 : |p2| ≤ (1 + R.u) * b2)
    (rs1 : R.InRange (p0 + p1)) (rN : R.InRange (R.fl (p0 + p1) + p2)) :
    |R.fl (R.fl (p0 + p1) + p2) - (E0 + E1 + E2)| ≤ 4 * R.u * (b0 + b1 + b2) := by
  have u0 := R.u_pos
  have ub0 : R.u * b0 ≤ 0.001 * b0 := mul_le_mul_of_nonneg_right hu b0n |>.trans (by linarith)
  have ub1 : R.u * b1 ≤ 0.001 * b1 := mul_le_mul_of_nonneg_right hu b1n |>.trans (by linarith)
  have ub2 : R.u * b2 ≤ 0.001 * b2 := mul_le_mul_of_nonneg_right hu b2n |>.trans (by linarith)
  have as1 : |p0 + p1| ≤ 1.001 * (b0 + b1) := by
    have := abs_add_le p0 p1
    have e0 : (1 + R.u) * b0 = b0 + R.u * b0 := by ring
    have e1 : (1 + R.u) * b1 = b1 + R.u * b1 := by ring
    linarith
  have es1 : |R.fl (p0 + p1) - (p0 + p1)| ≤ R.u * (1.001 * (b0 + b1)) := by
    have := R.abs_err rs1
    have := mul_le_mul_of_nonneg_left as1 u0.le
    linarith
  have small : R.u * (1.001 * (b0 + b1)) ≤ 0.002 * (b0 + b1) := by nlinarith
  have as2 : |R.fl (p0 + p1) + p2| ≤ 1.003 * (b0 + b1) + 1.001 * b2 := by
    have := abs_add_le (R.fl (p0 + p1)) p2
    have := abs_sub_abs_le_abs_sub (R.fl (p0 + p1)) (p0 + p1)
    have e2 : (1 + R.u) * b2 = b2 + R.u * b2 := by ring
    linarith
  have eN : |R.fl (R.fl (p0 + p1) + p2) - (R.fl (p0 + p1) + p2)| ≤
      R.u * (1.003 * (b0 + b1) + 1.001 * b2) := by
    have := R.abs_err rN
    have := mul_le_mul_of_nonneg_left as2 u0.le
    linarith
  have eP : |(p0 - E0) + (p1 - E1) + (p2 - E2)| ≤ R.u * b0 + R.u * b1 + R.u * b2 := by
    have := abs_add_three (p0 - E0) (p1 - E1) (p2 - E2)
    linarith
  calc |R.fl (R.fl (p0 + p1) + p2) - (E0 + E1 + E2)|
      = |(R.fl (R.fl (p0 + p1) + p2) - (R.fl (p0 + p1) + p2)) + (R.fl (p0 + p1) - (p0 + p1)) +
          ((p0 - E0) + (p1 - E1) + (p2 - E2))| := by ring_nf
    _ ≤ |R.fl (R.fl (p0 + p1) + p2) - (R.fl (p0 + p1) + p2)| + |R.fl (p0 + p1) - (p0 + p1)| +
          |(p0 - E0) + (p1 - E1) + (p2 - E2)| := abs_add_three _ _ _
    _ ≤ 4 * R.u * (b0 + b1 + b2) := by nlinarith

/-- Denominator `fl(fl(e0 + e1) + e2)` for nonnegative `e_i`. -/
theorem den_bounds (e0 e1 e2 : ℝ) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (rd1 : R.InRange (e0 + e1)) (rD : R.InRange (R.fl (e0 + e1) + e2)) :
    0 ≤ R.fl (R.fl (e0 + e1) + e2) ∧
      (1 - R.u) * ((1 - R.u) * (e0 + e1 + e2)) ≤ R.fl (R.fl (e0 + e1) + e2) ∧
      R.fl (R.fl (e0 + e1) + e2) ≤ (1 + R.u) * ((1 + R.u) * (e0 + e1 + e2)) := by
  have u0 := R.u_pos
  have u1 := R.u_lt_one
  set d1 := R.fl (e0 + e1)
  have d1n : 0 ≤ d1 := R.fl_nonneg (by linarith)
  have ed1 := R.abs_err rd1
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ e0 + e1)] at ed1
  have eD := R.abs_err rD
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ d1 + e2)] at eD
  have l1 := (abs_le.1 ed1).1
  have h1 := (abs_le.1 ed1).2
  have l2 := (abs_le.1 eD).1
  have h2 := (abs_le.1 eD).2
  refine ⟨R.fl_nonneg (by linarith), ?_, ?_⟩
  · have : (1 - R.u) * (e0 + e1) ≤ d1 := by linarith
    have : (1 - R.u) * ((1 - R.u) * (e0 + e1) + e2) ≤ (1 - R.u) * (d1 + e2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    have : (1 - R.u) * ((1 - R.u) * (e0 + e1 + e2)) ≤ (1 - R.u) * ((1 - R.u) * (e0 + e1) + e2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); nlinarith
    linarith
  · have : d1 ≤ (1 + R.u) * (e0 + e1) := by linarith
    have : (1 + R.u) * (d1 + e2) ≤ (1 + R.u) * ((1 + R.u) * (e0 + e1) + e2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    have : (1 + R.u) * ((1 + R.u) * (e0 + e1) + e2) ≤ (1 + R.u) * ((1 + R.u) * (e0 + e1 + e2)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); nlinarith
    linarith

/-- Quotient: from the numerator and denominator bounds, `N / D ≥ m - 8 u M`
    and `|N / D| ≤ 2 M`. -/
theorem quot_bounds (hu : R.u ≤ 1 / 1000) (N D A m M : ℝ) (Apos : 0 < A) (Dpos : 0 < D)
    (Dlo : (1 - R.u) * ((1 - R.u) * A) ≤ D) (Dhi : D ≤ (1 + R.u) * ((1 + R.u) * A))
    (Nlo : A * (m - 4 * R.u * M) ≤ N) (Nabs : |N| ≤ (1 + 4 * R.u) * (A * M))
    (hM : 0 ≤ M) (mM : m ≤ M) (mM' : -M ≤ m) :
    m - 8 * R.u * M ≤ N / D ∧ |N / D| ≤ 2 * M := by
  have u0 := R.u_pos
  have uM : 0 ≤ R.u * M := mul_nonneg u0.le hM
  constructor
  · rw [le_div_iff₀ Dpos]
    set Y := m - 8 * R.u * M
    rcases le_total 0 Y with hy | hy
    · have h1 : Y * D ≤ Y * ((1 + R.u) * ((1 + R.u) * A)) := mul_le_mul_of_nonneg_left Dhi hy
      have e : Y * ((1 + R.u) * ((1 + R.u) * A)) = A * (Y + Y * (2 * R.u + R.u * R.u)) := by ring
      have hYM : Y ≤ M := by simp only [Y]; linarith
      have g : Y * (2 * R.u + R.u * R.u) ≤ M * (2 * R.u + R.u * R.u) :=
        mul_le_mul_of_nonneg_right hYM (by positivity)
      have g2 : M * (2 * R.u + R.u * R.u) ≤ 4 * R.u * M := by nlinarith
      have : Y + Y * (2 * R.u + R.u * R.u) ≤ m - 4 * R.u * M := by simp only [Y] at g ⊢; linarith
      have := mul_le_mul_of_nonneg_left this Apos.le
      linarith
    · have h1 : Y * D ≤ Y * ((1 - R.u) * ((1 - R.u) * A)) := mul_le_mul_of_nonpos_left Dlo hy
      have e : Y * ((1 - R.u) * ((1 - R.u) * A)) = A * (Y + (-Y) * (2 * R.u - R.u * R.u)) := by ring
      have hYM : -Y ≤ M + 8 * R.u * M := by simp only [Y]; linarith
      have hpos : 0 ≤ 2 * R.u - R.u * R.u := by nlinarith
      have g : (-Y) * (2 * R.u - R.u * R.u) ≤ (M + 8 * R.u * M) * (2 * R.u - R.u * R.u) :=
        mul_le_mul_of_nonneg_right hYM hpos
      have g2 : (M + 8 * R.u * M) * (2 * R.u - R.u * R.u) ≤ 4 * R.u * M := by nlinarith
      have : Y + (-Y) * (2 * R.u - R.u * R.u) ≤ m - 4 * R.u * M := by simp only [Y] at g ⊢; linarith
      have := mul_le_mul_of_nonneg_left this Apos.le
      linarith
  · rw [abs_div, abs_of_pos Dpos, div_le_iff₀ Dpos]
    have k : (1 + 4 * R.u) ≤ 2 * ((1 - R.u) * (1 - R.u)) := by nlinarith
    have := mul_le_mul_of_nonneg_right k (mul_nonneg Apos.le hM)
    have := mul_le_mul_of_nonneg_left Dlo (by linarith : (0:ℝ) ≤ 2 * M)
    nlinarith

/-- **Woop `t` lower bound, nonnegative edge values.** -/
theorem woop_t_lower (hu : R.u ≤ 1 / 1000)
    (e0 e1 e2 z0 z1 z2 m M : ℝ) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hm0 : m ≤ z0) (hm1 : m ≤ z1) (hm2 : m ≤ z2)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M) (mM' : -M ≤ m)
    (r0 : R.InRange (e0 * z0)) (r1 : R.InRange (e1 * z1)) (r2 : R.InRange (e2 * z2))
    (rs1 : R.InRange (R.fl (e0 * z0) + R.fl (e1 * z1)))
    (rN : R.InRange (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)))
    (rd1 : R.InRange (e0 + e1)) (rD : R.InRange (R.fl (e0 + e1) + e2))
    (hD : R.fl (R.fl (e0 + e1) + e2) ≠ 0)
    (rq : R.InRange (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
      R.fl (R.fl (e0 + e1) + e2))) :
    m - 16 * R.u * M ≤ R.fl (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
      R.fl (R.fl (e0 + e1) + e2)) := by
  have u0 := R.u_pos
  have hM : 0 ≤ M := (abs_nonneg z0).trans hM0
  have ep : ∀ e z : ℝ, 0 ≤ e → R.InRange (e * z) →
      |R.fl (e * z) - e * z| ≤ R.u * (e * |z|) ∧ |R.fl (e * z)| ≤ (1 + R.u) * (e * |z|) := by
    intro e z he hr
    have h1 := R.abs_err hr
    have h2 := fl_abs_le' R hr
    rw [abs_mul, abs_of_nonneg he] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨q0, a0⟩ := ep e0 z0 he0 r0
  obtain ⟨q1, a1⟩ := ep e1 z1 he1 r1
  obtain ⟨q2, a2⟩ := ep e2 z2 he2 r2
  have hNE := num_err R hu _ _ _ _ _ _ _ _ _ (mul_nonneg he0 (abs_nonneg z0))
    (mul_nonneg he1 (abs_nonneg z1)) (mul_nonneg he2 (abs_nonneg z2)) q0 q1 q2 a0 a1 a2 rs1 rN
  obtain ⟨Dn, Dlo, Dhi⟩ := den_bounds R e0 e1 e2 he0 he1 he2 rd1 rD
  set N := R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2))
  set D := R.fl (R.fl (e0 + e1) + e2)
  set A := e0 + e1 + e2
  set B := e0 * |z0| + e1 * |z1| + e2 * |z2|
  have Dpos : 0 < D := lt_of_le_of_ne Dn (Ne.symm hD)
  have Apos : 0 < A := by
    by_contra h
    push Not at h
    have : (1 + R.u) * ((1 + R.u) * A) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (mul_nonpos_of_nonneg_of_nonpos (by linarith) h)
    linarith
  have hBA : B ≤ A * M := by
    have := mul_le_mul_of_nonneg_left hM0 he0
    have := mul_le_mul_of_nonneg_left hM1 he1
    have := mul_le_mul_of_nonneg_left hM2 he2
    have e : A * M = e0 * M + e1 * M + e2 * M := by simp only [A]; ring
    linarith
  have hE : m * A ≤ e0 * z0 + e1 * z1 + e2 * z2 := by
    have := mul_le_mul_of_nonneg_left hm0 he0
    have := mul_le_mul_of_nonneg_left hm1 he1
    have := mul_le_mul_of_nonneg_left hm2 he2
    have e : m * A = e0 * m + e1 * m + e2 * m := by simp only [A]; ring
    linarith
  have aE : |e0 * z0 + e1 * z1 + e2 * z2| ≤ B := by
    have := abs_add_three (e0 * z0) (e1 * z1) (e2 * z2)
    simp only [abs_mul, abs_of_nonneg he0, abs_of_nonneg he1, abs_of_nonneg he2] at this
    exact this
  have k4 : 4 * R.u * B ≤ 4 * R.u * (A * M) := mul_le_mul_of_nonneg_left hBA (by linarith)
  have Nlo : A * (m - 4 * R.u * M) ≤ N := by
    have := (abs_le.1 hNE).1
    have e : A * (m - 4 * R.u * M) = m * A - 4 * R.u * (A * M) := by ring
    linarith
  have Nabs : |N| ≤ (1 + 4 * R.u) * (A * M) := by
    have := abs_sub_abs_le_abs_sub N (e0 * z0 + e1 * z1 + e2 * z2)
    have e : (1 + 4 * R.u) * (A * M) = A * M + 4 * R.u * (A * M) := by ring
    linarith
  have mM : m ≤ M := hm0.trans ((le_abs_self z0).trans hM0)
  obtain ⟨hq, hqa⟩ := quot_bounds R hu N D A m M Apos Dpos Dlo Dhi Nlo Nabs hM mM mM'
  have ht := fl_ge R rq
  have := mul_le_mul_of_nonneg_left hqa u0.le
  have uM : 0 ≤ R.u * M := mul_nonneg u0.le hM
  linarith

/-- **Same bound for nonpositive edge values** (the other sign class the Woop
    test accepts): rounding is odd, so numerator and denominator both flip. -/
theorem woop_t_lower_neg (hu : R.u ≤ 1 / 1000)
    (e0 e1 e2 z0 z1 z2 m M : ℝ) (he0 : e0 ≤ 0) (he1 : e1 ≤ 0) (he2 : e2 ≤ 0)
    (hm0 : m ≤ z0) (hm1 : m ≤ z1) (hm2 : m ≤ z2)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M) (mM' : -M ≤ m)
    (r0 : R.InRange (-e0 * z0)) (r1 : R.InRange (-e1 * z1)) (r2 : R.InRange (-e2 * z2))
    (rs1 : R.InRange (R.fl (-e0 * z0) + R.fl (-e1 * z1)))
    (rN : R.InRange (R.fl (R.fl (-e0 * z0) + R.fl (-e1 * z1)) + R.fl (-e2 * z2)))
    (rd1 : R.InRange (-e0 + -e1)) (rD : R.InRange (R.fl (-e0 + -e1) + -e2))
    (hD : R.fl (R.fl (e0 + e1) + e2) ≠ 0)
    (rq : R.InRange (R.fl (R.fl (R.fl (-e0 * z0) + R.fl (-e1 * z1)) + R.fl (-e2 * z2)) /
      R.fl (R.fl (-e0 + -e1) + -e2))) :
    m - 16 * R.u * M ≤ R.fl (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
      R.fl (R.fl (e0 + e1) + e2)) := by
  have flip : ∀ a b : ℝ, R.fl (a + b) = -R.fl (-a + -b) := by
    intro a b; rw [← R.neg]; congr 1; ring
  have flipm : ∀ e z : ℝ, R.fl (e * z) = -R.fl (-e * z) := by
    intro e z; rw [← R.neg]; congr 1; ring
  have hD' : R.fl (R.fl (-e0 + -e1) + -e2) ≠ 0 := by
    intro h; apply hD
    rw [flip (R.fl (e0 + e1)) e2, flip e0 e1, neg_neg, h, neg_zero]
  have key := woop_t_lower R hu (-e0) (-e1) (-e2) z0 z1 z2 m M (by linarith) (by linarith)
    (by linarith) hm0 hm1 hm2 hM0 hM1 hM2 mM' r0 r1 r2 rs1 rN rd1 rD hD' rq
  have eqN : R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) =
      -R.fl (R.fl (R.fl (-e0 * z0) + R.fl (-e1 * z1)) + R.fl (-e2 * z2)) := by
    rw [flip (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1))) (R.fl (e2 * z2)), flip (R.fl (e0 * z0)),
      flipm e0, flipm e1, flipm e2]
    simp only [neg_neg]
  have eqD : R.fl (R.fl (e0 + e1) + e2) = -R.fl (R.fl (-e0 + -e1) + -e2) := by
    rw [flip (R.fl (e0 + e1)) e2, flip e0 e1, neg_neg]
  rw [eqN, eqD, neg_div_neg_eq]
  exact key

/-- **Quotient error, generic form**: `fl(N/D)` is within `16 u M` of the exact
    ratio `E/A`, from relative denominator bounds and absolute numerator
    bounds (`|N - E| ≤ 4uB`, `|E| ≤ B ≤ A M`). -/
theorem quot_err (hu : R.u ≤ 1 / 1000) (N D E A B M : ℝ) (Apos : 0 < A) (Dpos : 0 < D)
    (Dlo : (1 - R.u) * ((1 - R.u) * A) ≤ D) (Dhi : D ≤ (1 + R.u) * ((1 + R.u) * A))
    (NB : |N - E| ≤ 4 * R.u * B) (hE : |E| ≤ B) (BA : B ≤ A * M)
    (hB0 : 0 ≤ B) (hM : 0 ≤ M) (rq : R.InRange (N / D)) :
    |R.fl (N / D) - E / A| ≤ 16 * R.u * M := by
  have u0 := R.u_pos
  have hu1 : R.u ≤ 1 := by linarith
  have hA := Apos.le
  have hAA : 0 < A * A := mul_pos Apos Apos
  have hAD : |A - D| ≤ 3 * R.u * A := by
    rw [abs_le]
    constructor
    · nlinarith [Dhi, u0, hA, hAA, hu1]
    · nlinarith [Dlo, u0, hA, hAA, hu1]
  have hnum : |N * A - E * D| ≤ 7 * R.u * (A * B) := by
    have heq : N * A - E * D = (N - E) * A + E * (A - D) := by ring
    rw [heq]
    have h1 : |(N - E) * A + E * (A - D)| ≤ |N - E| * A + |E| * |A - D| := by
      have h := abs_add_le ((N - E) * A) (E * (A - D))
      rwa [abs_mul, abs_mul, abs_of_nonneg hA] at h
    have h2 : |N - E| * A ≤ 4 * R.u * B * A := by
      have := mul_le_mul_of_nonneg_right NB hA
      linarith
    have h3 : 3 * R.u * A = 3 * (R.u * A) := by ring
    have h4 : |E| * |A - D| ≤ B * (3 * R.u * A) := by
      apply mul_le_mul hE hAD (abs_nonneg _) hB0
    nlinarith [h1, h2, h4]
  have hratio : |N / D - E / A| ≤ 8 * R.u * M := by
    have hADpos : 0 < A * D := mul_pos Apos Dpos
    have hsplit : N / D - E / A = (N * A - E * D) / (A * D) := by
      field_simp
    rw [hsplit, abs_div, abs_of_pos hADpos, div_le_iff₀ hADpos]
    have hd : (1 - R.u) * ((1 - R.u) * A) * A ≤ A * D := by
      have := mul_le_mul_of_nonneg_right Dlo hA
      linarith
    have hB : A * B ≤ A * (A * M) := mul_le_mul_of_nonneg_left BA hA
    have h7 : |N * A - E * D| ≤ 7 * R.u * (A * B) := hnum
    have h7' : 7 * R.u * (A * B) ≤ 7 * R.u * (A * (A * M)) := by
      have := mul_le_mul_of_nonneg_left hB (by positivity : (0:ℝ) ≤ 7 * R.u)
      linarith
    have hu2 : R.u * R.u ≤ R.u := by nlinarith [hu1, u0]
    have h8 : 7 * R.u * (A * (A * M)) ≤ 8 * R.u * M * (A * D) := by
      have h2 : 8 * R.u * M * ((1 - R.u) * ((1 - R.u) * A) * A) ≤ 8 * R.u * M * (A * D) := by
        apply mul_le_mul_of_nonneg_left hd
        positivity
      have h3 : 7 * R.u * (A * (A * M)) ≤
          8 * R.u * M * ((1 - R.u) * ((1 - R.u) * A) * A) := by
        have key : 7 * R.u ≤ 8 * R.u * (1 - R.u) * (1 - R.u) := by
          nlinarith [hu, hu2, u0]
        have hpos : (0:ℝ) ≤ A * (A * M) := by positivity
        have := mul_le_mul_of_nonneg_right key hpos
        nlinarith [this]
      linarith
    linarith
  have hEA : |E / A| ≤ M := by
    rw [abs_div, abs_of_pos Apos, div_le_iff₀ Apos]
    exact hE.trans (by rwa [mul_comm] at BA)
  have hNabs : |N / D| ≤ (1 + 8 * R.u) * M := by
    have := abs_sub_abs_le_abs_sub (N / D) (E / A)
    linarith [hratio]
  have hq := R.abs_err rq
  have htri : |R.fl (N / D) - E / A| ≤ |R.fl (N / D) - N / D| + |N / D - E / A| := by
    have h := abs_add_le (R.fl (N / D) - N / D) (N / D - E / A)
    rwa [show R.fl (N / D) - N / D + (N / D - E / A) = R.fl (N / D) - E / A by ring] at h
  have h1 : |R.fl (N / D) - N / D| ≤ R.u * ((1 + 8 * R.u) * M) := by
    have := mul_le_mul_of_nonneg_left hNabs u0.le
    linarith
  have hu8 : 8 * R.u ≤ 7 := by nlinarith [hu]
  have hsq : 8 * R.u * R.u * M ≤ 7 * R.u * M := by
    have h7 : 0 ≤ 7 - 8 * R.u := by linarith
    have := mul_nonneg (mul_nonneg h7 u0.le) hM
    nlinarith [this]
  nlinarith [htri, h1, hratio]

/-- **Woop `t` error, nonnegative edge values**: the computed `t` is within
    `16 u M` of the exact weighted mean `(Σ eᵢ zᵢ)/(Σ eᵢ)` of the depths. -/
theorem woop_t_err (hu : R.u ≤ 1 / 1000)
    (e0 e1 e2 z0 z1 z2 M : ℝ) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M)
    (r0 : R.InRange (e0 * z0)) (r1 : R.InRange (e1 * z1)) (r2 : R.InRange (e2 * z2))
    (rs1 : R.InRange (R.fl (e0 * z0) + R.fl (e1 * z1)))
    (rN : R.InRange (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)))
    (rd1 : R.InRange (e0 + e1)) (rD : R.InRange (R.fl (e0 + e1) + e2))
    (hD : R.fl (R.fl (e0 + e1) + e2) ≠ 0)
    (rq : R.InRange (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
      R.fl (R.fl (e0 + e1) + e2))) :
    |R.fl (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
        R.fl (R.fl (e0 + e1) + e2)) -
      (e0 * z0 + e1 * z1 + e2 * z2) / (e0 + e1 + e2)| ≤ 16 * R.u * M := by
  have u0 := R.u_pos
  have hM : 0 ≤ M := (abs_nonneg z0).trans hM0
  have ep : ∀ e z : ℝ, 0 ≤ e → R.InRange (e * z) →
      |R.fl (e * z) - e * z| ≤ R.u * (e * |z|) ∧ |R.fl (e * z)| ≤ (1 + R.u) * (e * |z|) := by
    intro e z he hr
    have h1 := R.abs_err hr
    have h2 := fl_abs_le' R hr
    rw [abs_mul, abs_of_nonneg he] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨q0, a0⟩ := ep e0 z0 he0 r0
  obtain ⟨q1, a1⟩ := ep e1 z1 he1 r1
  obtain ⟨q2, a2⟩ := ep e2 z2 he2 r2
  have hNE := num_err R hu _ _ _ _ _ _ _ _ _ (mul_nonneg he0 (abs_nonneg z0))
    (mul_nonneg he1 (abs_nonneg z1)) (mul_nonneg he2 (abs_nonneg z2)) q0 q1 q2 a0 a1 a2 rs1 rN
  obtain ⟨Dn, Dlo, Dhi⟩ := den_bounds R e0 e1 e2 he0 he1 he2 rd1 rD
  set N := R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2))
  set D := R.fl (R.fl (e0 + e1) + e2)
  set A := e0 + e1 + e2
  set E := e0 * z0 + e1 * z1 + e2 * z2
  set B := e0 * |z0| + e1 * |z1| + e2 * |z2|
  have Dpos : 0 < D := lt_of_le_of_ne Dn (Ne.symm hD)
  have Apos : 0 < A := by
    by_contra h
    push Not at h
    have : (1 + R.u) * ((1 + R.u) * A) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (mul_nonpos_of_nonneg_of_nonpos (by linarith) h)
    linarith
  have hBA : B ≤ A * M := by
    have := mul_le_mul_of_nonneg_left hM0 he0
    have := mul_le_mul_of_nonneg_left hM1 he1
    have := mul_le_mul_of_nonneg_left hM2 he2
    have e : A * M = e0 * M + e1 * M + e2 * M := by simp only [A]; ring
    linarith
  have hE : |E| ≤ B := by
    have := abs_add_three (e0 * z0) (e1 * z1) (e2 * z2)
    simp only [abs_mul, abs_of_nonneg he0, abs_of_nonneg he1, abs_of_nonneg he2] at this
    exact this
  have hB0 : 0 ≤ B := by
    have := mul_nonneg he0 (abs_nonneg z0)
    have := mul_nonneg he1 (abs_nonneg z1)
    have := mul_nonneg he2 (abs_nonneg z2)
    simp only [B]; linarith
  exact quot_err R hu N D E A B M Apos Dpos Dlo Dhi hNE hE hBA hB0 hM rq

/-- **Same error bound for nonpositive edge values** (rounded numerator and
    denominator both flip sign). -/
theorem woop_t_err_neg (hu : R.u ≤ 1 / 1000)
    (e0 e1 e2 z0 z1 z2 M : ℝ) (he0 : e0 ≤ 0) (he1 : e1 ≤ 0) (he2 : e2 ≤ 0)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M)
    (r0 : R.InRange (-e0 * z0)) (r1 : R.InRange (-e1 * z1)) (r2 : R.InRange (-e2 * z2))
    (rs1 : R.InRange (R.fl (-e0 * z0) + R.fl (-e1 * z1)))
    (rN : R.InRange (R.fl (R.fl (-e0 * z0) + R.fl (-e1 * z1)) + R.fl (-e2 * z2)))
    (rd1 : R.InRange (-e0 + -e1)) (rD : R.InRange (R.fl (-e0 + -e1) + -e2))
    (hD : R.fl (R.fl (e0 + e1) + e2) ≠ 0)
    (rq : R.InRange (R.fl (R.fl (R.fl (-e0 * z0) + R.fl (-e1 * z1)) + R.fl (-e2 * z2)) /
      R.fl (R.fl (-e0 + -e1) + -e2))) :
    |R.fl (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
        R.fl (R.fl (e0 + e1) + e2)) -
      (e0 * z0 + e1 * z1 + e2 * z2) / (e0 + e1 + e2)| ≤ 16 * R.u * M := by
  have flip : ∀ a b : ℝ, R.fl (a + b) = -R.fl (-a + -b) := by
    intro a b; rw [← R.neg]; congr 1; ring
  have flipm : ∀ e z : ℝ, R.fl (e * z) = -R.fl (-e * z) := by
    intro e z; rw [← R.neg]; congr 1; ring
  have hD' : R.fl (R.fl (-e0 + -e1) + -e2) ≠ 0 := by
    intro h; apply hD
    rw [flip (R.fl (e0 + e1)) e2, flip e0 e1, neg_neg, h, neg_zero]
  have key := woop_t_err R hu (-e0) (-e1) (-e2) z0 z1 z2 M (by linarith) (by linarith)
    (by linarith) hM0 hM1 hM2 r0 r1 r2 rs1 rN rd1 rD hD' rq
  have eqN : R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) =
      -R.fl (R.fl (R.fl (-e0 * z0) + R.fl (-e1 * z1)) + R.fl (-e2 * z2)) := by
    rw [flip (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1))) (R.fl (e2 * z2)), flip (R.fl (e0 * z0)),
      flipm e0, flipm e1, flipm e2]
    simp only [neg_neg]
  have eqD : R.fl (R.fl (e0 + e1) + e2) = -R.fl (R.fl (-e0 + -e1) + -e2) := by
    rw [flip (R.fl (e0 + e1)) e2, flip e0 e1, neg_neg]
  have eqE : e0 * z0 + e1 * z1 + e2 * z2 = -(-e0 * z0 + -e1 * z1 + -e2 * z2) := by ring
  have eqA : e0 + e1 + e2 = -(-e0 + -e1 + -e2) := by ring
  rw [eqN, eqD, eqE, eqA, neg_div_neg_eq, neg_div_neg_eq]
  exact key

/-- **Woop `t` upper bound**: when all vertex depths are at most `Z`, the
    computed `t` is at most `Z + 16 u M`. -/
theorem woop_t_upper (hu : R.u ≤ 1 / 1000)
    (e0 e1 e2 z0 z1 z2 Z M : ℝ) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hZ0 : z0 ≤ Z) (hZ1 : z1 ≤ Z) (hZ2 : z2 ≤ Z)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M)
    (r0 : R.InRange (e0 * z0)) (r1 : R.InRange (e1 * z1)) (r2 : R.InRange (e2 * z2))
    (rs1 : R.InRange (R.fl (e0 * z0) + R.fl (e1 * z1)))
    (rN : R.InRange (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)))
    (rd1 : R.InRange (e0 + e1)) (rD : R.InRange (R.fl (e0 + e1) + e2))
    (hD : R.fl (R.fl (e0 + e1) + e2) ≠ 0)
    (rq : R.InRange (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
      R.fl (R.fl (e0 + e1) + e2))) :
    R.fl (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
        R.fl (R.fl (e0 + e1) + e2)) ≤ Z + 16 * R.u * M := by
  have h := woop_t_err R hu e0 e1 e2 z0 z1 z2 M he0 he1 he2 hM0 hM1 hM2 r0 r1 r2 rs1 rN
    rd1 rD hD rq
  have u0 := R.u_pos
  have hM : 0 ≤ M := (abs_nonneg z0).trans hM0
  have hA : 0 < e0 + e1 + e2 := by
    rcases lt_or_eq_of_le (show (0:ℝ) ≤ e0 + e1 + e2 by linarith) with h | h
    · exact h
    · exfalso
      apply hD
      have he0' : e0 = 0 := le_antisymm (by linarith) he0
      have he1' : e1 = 0 := le_antisymm (by linarith) he1
      have he2' : e2 = 0 := le_antisymm (by linarith) he2
      rw [he0', he1', he2']; simp [R.fl_zero]
  have ht : (e0 * z0 + e1 * z1 + e2 * z2) / (e0 + e1 + e2) ≤ Z := by
    rw [div_le_iff₀ hA]
    have h1 := mul_le_mul_of_nonneg_left hZ0 he0
    have h2 := mul_le_mul_of_nonneg_left hZ1 he1
    have h3 := mul_le_mul_of_nonneg_left hZ2 he2
    have e : Z * (e0 + e1 + e2) = e0 * Z + e1 * Z + e2 * Z := by ring
    linarith
  nlinarith [(abs_le.1 h).2]

/-- **Woop `t` upper bound for nonpositive edge values.** -/
theorem woop_t_upper_neg (hu : R.u ≤ 1 / 1000)
    (e0 e1 e2 z0 z1 z2 Z M : ℝ) (he0 : e0 ≤ 0) (he1 : e1 ≤ 0) (he2 : e2 ≤ 0)
    (hZ0 : z0 ≤ Z) (hZ1 : z1 ≤ Z) (hZ2 : z2 ≤ Z)
    (hM0 : |z0| ≤ M) (hM1 : |z1| ≤ M) (hM2 : |z2| ≤ M)
    (r0 : R.InRange (-e0 * z0)) (r1 : R.InRange (-e1 * z1)) (r2 : R.InRange (-e2 * z2))
    (rs1 : R.InRange (R.fl (-e0 * z0) + R.fl (-e1 * z1)))
    (rN : R.InRange (R.fl (R.fl (-e0 * z0) + R.fl (-e1 * z1)) + R.fl (-e2 * z2)))
    (rd1 : R.InRange (-e0 + -e1)) (rD : R.InRange (R.fl (-e0 + -e1) + -e2))
    (hD : R.fl (R.fl (e0 + e1) + e2) ≠ 0)
    (rq : R.InRange (R.fl (R.fl (R.fl (-e0 * z0) + R.fl (-e1 * z1)) + R.fl (-e2 * z2)) /
      R.fl (R.fl (-e0 + -e1) + -e2))) :
    R.fl (R.fl (R.fl (R.fl (e0 * z0) + R.fl (e1 * z1)) + R.fl (e2 * z2)) /
        R.fl (R.fl (e0 + e1) + e2)) ≤ Z + 16 * R.u * M := by
  have h := woop_t_err_neg R hu e0 e1 e2 z0 z1 z2 M he0 he1 he2 hM0 hM1 hM2 r0 r1 r2 rs1 rN
    rd1 rD hD rq
  have u0 := R.u_pos
  have hM : 0 ≤ M := (abs_nonneg z0).trans hM0
  have hA : e0 + e1 + e2 < 0 := by
    rcases lt_or_eq_of_le (show e0 + e1 + e2 ≤ 0 by linarith) with h | h
    · exact h
    · exfalso
      apply hD
      have he0' : e0 = 0 := le_antisymm he0 (by linarith)
      have he1' : e1 = 0 := le_antisymm he1 (by linarith)
      have he2' : e2 = 0 := le_antisymm he2 (by linarith)
      rw [he0', he1', he2']; simp [R.fl_zero]
  have ht : (e0 * z0 + e1 * z1 + e2 * z2) / (e0 + e1 + e2) ≤ Z := by
    rw [div_le_iff_of_neg hA]
    have h1 := mul_le_mul_of_nonneg_left hZ0 (by linarith : (0:ℝ) ≤ -e0)
    have h2 := mul_le_mul_of_nonneg_left hZ1 (by linarith : (0:ℝ) ≤ -e1)
    have h3 := mul_le_mul_of_nonneg_left hZ2 (by linarith : (0:ℝ) ≤ -e2)
    nlinarith
  nlinarith [(abs_le.1 h).2]

/-- **Depth of a vertex in the box lies between the two faces' depths**
    (`z = fl(sz * fl(v - o))`, rounding monotone). -/
theorem depth_bounds (sz o lo hi v : ℝ) (hlo : lo ≤ v) (hhi : v ≤ hi) :
    min (R.fl (sz * R.fl (lo - o))) (R.fl (sz * R.fl (hi - o))) ≤ R.fl (sz * R.fl (v - o)) ∧
      |R.fl (sz * R.fl (v - o))| ≤
        max |R.fl (sz * R.fl (lo - o))| |R.fl (sz * R.fl (hi - o))| := by
  have a1 : R.fl (lo - o) ≤ R.fl (v - o) := R.mono (by linarith)
  have a2 : R.fl (v - o) ≤ R.fl (hi - o) := R.mono (by linarith)
  rcases le_total 0 sz with hs | hs
  · have b1 : R.fl (sz * R.fl (lo - o)) ≤ R.fl (sz * R.fl (v - o)) :=
      R.mono (mul_le_mul_of_nonneg_left a1 hs)
    have b2 : R.fl (sz * R.fl (v - o)) ≤ R.fl (sz * R.fl (hi - o)) :=
      R.mono (mul_le_mul_of_nonneg_left a2 hs)
    refine ⟨min_le_of_left_le b1, ?_⟩
    rw [abs_le]
    constructor
    · have := neg_abs_le (R.fl (sz * R.fl (lo - o)))
      have := le_max_left |R.fl (sz * R.fl (lo - o))| |R.fl (sz * R.fl (hi - o))|
      linarith
    · have := le_abs_self (R.fl (sz * R.fl (hi - o)))
      have := le_max_right |R.fl (sz * R.fl (lo - o))| |R.fl (sz * R.fl (hi - o))|
      linarith
  · have b1 : R.fl (sz * R.fl (v - o)) ≤ R.fl (sz * R.fl (lo - o)) :=
      R.mono (mul_le_mul_of_nonpos_left a1 hs)
    have b2 : R.fl (sz * R.fl (hi - o)) ≤ R.fl (sz * R.fl (v - o)) :=
      R.mono (mul_le_mul_of_nonpos_left a2 hs)
    refine ⟨min_le_of_right_le b2, ?_⟩
    rw [abs_le]
    constructor
    · have := neg_abs_le (R.fl (sz * R.fl (hi - o)))
      have := le_max_right |R.fl (sz * R.fl (lo - o))| |R.fl (sz * R.fl (hi - o))|
      linarith
    · have := le_abs_self (R.fl (sz * R.fl (lo - o)))
      have := le_max_left |R.fl (sz * R.fl (lo - o))| |R.fl (sz * R.fl (hi - o))|
      linarith

/-- **The float node key is below the proved bound**: `fl(m - fl(c * M))` with
    `32 u ≤ c ≤ 1` and `|m| ≤ M`. -/
theorem key_le (hu : R.u ≤ 1 / 1000) (m M c : ℝ) (hmM : |m| ≤ M) (hc : 32 * R.u ≤ c)
    (hc1 : c ≤ 1) (r1 : R.InRange (c * M)) (r2 : R.InRange (m - R.fl (c * M))) :
    R.fl (m - R.fl (c * M)) ≤ m - 16 * R.u * M := by
  have u0 := R.u_pos
  have hM : 0 ≤ M := (abs_nonneg m).trans hmM
  have hc0 : 0 ≤ c := by linarith
  have h1 := fl_ge R r1
  rw [abs_of_nonneg (mul_nonneg hc0 hM)] at h1
  have h1' := fl_le R r1
  rw [abs_of_nonneg (mul_nonneg hc0 hM)] at h1'
  have h2 := fl_le R r2
  have hx : |m - R.fl (c * M)| ≤ M + (1 + R.u) * (c * M) := by
    have := abs_sub m (R.fl (c * M))
    have : |R.fl (c * M)| ≤ (1 + R.u) * (c * M) := by
      have := fl_abs_le' R r1
      rwa [abs_of_nonneg (mul_nonneg hc0 hM)] at this
    linarith
  have := mul_le_mul_of_nonneg_left hx u0.le
  have : R.u * ((1 + R.u) * (c * M)) ≤ R.u * (2 * M) := by
    apply mul_le_mul_of_nonneg_left _ u0.le
    nlinarith
  have : 31 * R.u * M ≤ (1 - R.u) * (c * M) := by
    have := mul_le_mul_of_nonneg_right hc hM
    nlinarith [mul_nonneg u0.le hM]
  nlinarith [mul_nonneg u0.le hM]

/-- **C2 for the watertight leaf**: a triangle accepted by the Woop test (edge
    values of one sign) whose exact vertices lie in the node's `kz`-slab
    `[lo, hi]` has computed `t` at least the node key. With `tn := max(key,
    tmin)` (also `≤ t`, since accepted hits satisfy `t ≥ tmin`), this is the
    hypothesis C2 of `Flat.run_root`; C1 is the box test against the fixed
    `tmax` (as for `run_exact`). -/
theorem woop_key_le_t (hu : R.u ≤ 1 / 1000) (sz o lo hi c : ℝ) (hc : 32 * R.u ≤ c) (hc1 : c ≤ 1)
    (v0 v1 v2 e0 e1 e2 : ℝ) (hv0 : lo ≤ v0 ∧ v0 ≤ hi) (hv1 : lo ≤ v1 ∧ v1 ≤ hi)
    (hv2 : lo ≤ v2 ∧ v2 ≤ hi)
    (hsign : (0 ≤ e0 ∧ 0 ≤ e1 ∧ 0 ≤ e2) ∨ (e0 ≤ 0 ∧ e1 ≤ 0 ∧ e2 ≤ 0))
    (hD : R.fl (R.fl (e0 + e1) + e2) ≠ 0)
    (hrange : ∀ x : ℝ, R.InRange x) :
    let z := fun v => R.fl (sz * R.fl (v - o))
    let m := min (z lo) (z hi)
    let M := max |z lo| |z hi|
    R.fl (m - R.fl (c * M)) ≤
      R.fl (R.fl (R.fl (R.fl (e0 * z v0) + R.fl (e1 * z v1)) + R.fl (e2 * z v2)) /
        R.fl (R.fl (e0 + e1) + e2)) := by
  intro z m M
  obtain ⟨m0, M0⟩ := depth_bounds R sz o lo hi v0 hv0.1 hv0.2
  obtain ⟨m1, M1⟩ := depth_bounds R sz o lo hi v1 hv1.1 hv1.2
  obtain ⟨m2, M2⟩ := depth_bounds R sz o lo hi v2 hv2.1 hv2.2
  have hmM : |m| ≤ M := by
    simp only [m, M]
    rcases min_choice (z lo) (z hi) with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hk := key_le R hu m M c hmM hc hc1 (hrange _) (hrange _)
  have mM' : -M ≤ m := by have := neg_abs_le m; linarith
  rcases hsign with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · have := woop_t_lower R hu e0 e1 e2 (z v0) (z v1) (z v2) m M a b d m0 m1 m2 M0 M1 M2 mM'
      (hrange _) (hrange _) (hrange _) (hrange _) (hrange _) (hrange _) (hrange _) hD (hrange _)
    linarith
  · have := woop_t_lower_neg R hu e0 e1 e2 (z v0) (z v1) (z v2) m M a b d m0 m1 m2 M0 M1 M2 mM'
      (hrange _) (hrange _) (hrange _) (hrange _) (hrange _) (hrange _) (hrange _) hD (hrange _)
    linarith

end LightRT.BVH.ExactPrune
