/-
  Explicit control-point bounds for the `ofCubic` Bézier system (M14 data supply).
-/
import Mathlib
import LightRT.Geom.BezNewton
import LightRT.Geom.Hull

namespace LightRT.Geom
open Hull

/-- Bernstein convex-combination bound: on `[0,1]`, a cubic Bézier value lies
    within the max absolute control-point magnitude. -/
theorem abs_bez3_le_max (P : Fin 4 → ℝ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |bez3 P t| ≤ Finset.univ.sup' Finset.univ_nonempty (fun k => |P k|) := by
  rw [bez3]
  have hn : ∀ k, 0 ≤ bern3 t k := bern3_nonneg h0 h1
  have hs : ∑ k, bern3 t k = 1 := bern3_sum t
  have hsup : ∀ k, |P k| ≤ Finset.univ.sup' Finset.univ_nonempty (fun k => |P k|) := by
    intro k; exact Finset.le_sup' (f := fun k => |P k|) (Finset.mem_univ k)
  have h1' : |∑ k, bern3 t k * P k| ≤ ∑ k, bern3 t k * |P k| := by
    calc |∑ k, bern3 t k * P k| ≤ ∑ k, |bern3 t k * P k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, bern3 t k * |P k| := by
        apply Finset.sum_congr rfl; intro k hk
        rw [abs_mul, abs_of_nonneg (hn k)]
  have h2 : ∑ k, bern3 t k * |P k| ≤ ∑ k, bern3 t k *
      (Finset.univ.sup' Finset.univ_nonempty (fun k => |P k|)) := by
    apply Finset.sum_le_sum; intro k hk
    exact mul_le_mul_of_nonneg_left (hsup k) (hn k)
  have h3 : ∑ k, bern3 t k *
      (Finset.univ.sup' Finset.univ_nonempty (fun k => |P k|)) =
      Finset.univ.sup' Finset.univ_nonempty (fun k => |P k|) := by
    rw [← Finset.sum_mul, hs, one_mul]
  linarith

/-- `bezP` in Bernstein form. -/
theorem bezP_eq_bez3 (b0 b1 b2 b3 t : ℝ) :
    bezP b0 b1 b2 b3 t = bez3 ![b0, b1, b2, b3] t := by
  simp [bezP, bez3, bern3, Fin.sum_univ_four]
  ring

/-- Component bound for `bezP` on `[0,1]`. -/
theorem abs_bezP_le_max (b0 b1 b2 b3 t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |bezP b0 b1 b2 b3 t| ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun k : Fin 4 => |![b0, b1, b2, b3] k|) := by
  rw [bezP_eq_bez3]
  exact abs_bez3_le_max ![b0, b1, b2, b3] h0 h1


/-- Quadratic Bernstein weights sum to one and are nonnegative on `[0,1]`. -/
theorem bern2_sum (t : ℝ) : (1 - t)^2 + 2*(1-t)*t + t^2 = 1 := by ring

theorem abs_dBezP_le (b0 b1 b2 b3 t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |dBezP b0 b1 b2 b3 t| ≤ 3 * max (max |b1-b0| |b2-b1|) |b3-b2| := by
  have hu : 0 ≤ 1 - t := by linarith
  have w0 : 0 ≤ (1-t)^2 := sq_nonneg _
  have w1 : 0 ≤ 2*(1-t)*t := by positivity
  have w2 : 0 ≤ t^2 := sq_nonneg _
  have hs := bern2_sum t
  set a0 := b1 - b0; set a1 := b2 - b1; set a2 := b3 - b2
  set M := max (max |a0| |a1|) |a2|
  have ha0 : |a0| ≤ M := by dsimp [M]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have ha1 : |a1| ≤ M := by dsimp [M]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have ha2 : |a2| ≤ M := by dsimp [M]; exact le_max_right _ _
  have htri0 : |(1-t)^2*a0 + 2*(1-t)*t*a1 + t^2*a2| ≤
      |(1-t)^2*a0| + |2*(1-t)*t*a1| + |t^2*a2| := by
    have h1 := abs_add_le ((1-t)^2*a0 + 2*(1-t)*t*a1) (t^2*a2)
    have h2 := abs_add_le ((1-t)^2*a0) (2*(1-t)*t*a1)
    linarith [h1, h2]
  have htri : |(1-t)^2*a0 + 2*(1-t)*t*a1 + t^2*a2| ≤
      (1-t)^2*|a0| + 2*(1-t)*t*|a1| + t^2*|a2| := by
    rw [abs_mul, abs_of_nonneg w0, abs_mul, abs_of_nonneg w1, abs_mul, abs_of_nonneg w2] at htri0
    exact htri0
  have hle : (1-t)^2*|a0| + 2*(1-t)*t*|a1| + t^2*|a2| ≤ M := by
    calc (1-t)^2*|a0| + 2*(1-t)*t*|a1| + t^2*|a2| ≤
        (1-t)^2*M + 2*(1-t)*t*M + t^2*M := by gcongr
      _ = M := by rw [← add_mul, ← add_mul, hs, one_mul]
  have hd : |3 * ((1-t)^2*a0 + 2*(1-t)*t*a1 + t^2*a2)| ≤ 3 * M := by
    rw [abs_mul]
    norm_num
    nlinarith [htri, hle]
  dsimp [dBezP, a0, a1, a2, M] at hd ⊢
  exact hd

/-- Linear Bernstein bound for the second derivative. -/
theorem abs_ddBezP_le (b0 b1 b2 b3 t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |ddBezP b0 b1 b2 b3 t| ≤ 6 * max |b2 - 2*b1 + b0| |b3 - 2*b2 + b1| := by
  have hu : 0 ≤ 1 - t := by linarith
  set a0 := b2 - 2*b1 + b0; set a1 := b3 - 2*b2 + b1
  set M := max |a0| |a1|
  have ha0 : |a0| ≤ M := le_max_left _ _
  have ha1 : |a1| ≤ M := le_max_right _ _
  have htri : |(1-t)*a0 + t*a1| ≤ (1-t)*|a0| + t*|a1| := by
    have h1 := abs_add_le ((1-t)*a0) (t*a1)
    rw [abs_mul, abs_of_nonneg hu, abs_mul, abs_of_nonneg h0] at h1
    exact h1
  have hle : (1-t)*|a0| + t*|a1| ≤ M := by
    calc (1-t)*|a0| + t*|a1| ≤ (1-t)*M + t*M := by gcongr
      _ = M := by ring
  have hd : |6 * ((1-t)*a0 + t*a1)| ≤ 6 * M := by
    rw [abs_mul]
    norm_num
    nlinarith [htri, hle]
  dsimp [ddBezP, a0, a1, M] at hd ⊢
  exact hd

end LightRT.Geom
