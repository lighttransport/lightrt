/-
  Bounding boxes of curves, patches and points (the containment hypothesis
  `inside p b` of the BVH theorems for the non-triangle primitives).

  One lemma does the work, `hull_of_balls`: a convex combination of points
  `y k`, each within `r k` of a control point `P k` (per axis), lies in every
  box that contains all the `P k ± r k`. Instances:
  * `bezier_tube_in_box`  round cubic Bézier curve (CPs with radii);
  * `linear_tube_in_box`  round-linear and flat (ribbon) curves: the convex
    hull of the two end balls;
  * `bilinear_in_box`, `bicubic_in_box`  patches (control-point hull);
  * `rational_in_box`     rational (NURBS-extracted) patch with positive
    weights, against the box of the projected control points `x / w`;
  * `ball_in_box`         sphere / disc points.
  `decasteljau_left` / `decasteljau_right`: the split control points describe
  exactly the two halves of the cubic, so the box of a pre-subdivided
  sub-arc's control points bounds that sub-arc.
  The C side (`tools/primboxcheck.c`) checks exactly that every C box contains
  all `P k ± r k` (resp. `x/w`) of the STORED leaf data.
-/
import Mathlib

namespace LightRT.Geom.Hull
open Finset

/-- **Convex hull of balls.** Per axis: if `λ` are convex weights and each
    `y k` is within `r k` of `P k`, the combination lies in any `[lo, hi]`
    containing every `[P k - r k, P k + r k]`. -/
theorem hull_of_balls {n : ℕ} (lam P r y : Fin n → ℝ) (lo hi : ℝ)
    (h0 : ∀ k, 0 ≤ lam k) (h1 : ∑ k, lam k = 1)
    (hy : ∀ k, |y k - P k| ≤ r k)
    (hlo : ∀ k, lo ≤ P k - r k) (hhi : ∀ k, P k + r k ≤ hi) :
    lo ≤ ∑ k, lam k * y k ∧ ∑ k, lam k * y k ≤ hi := by
  constructor
  · calc lo = ∑ k, lam k * lo := by rw [← sum_mul, h1, one_mul]
      _ ≤ ∑ k, lam k * y k := by
        apply sum_le_sum; intro k _
        apply mul_le_mul_of_nonneg_left _ (h0 k)
        have := (abs_le.1 (hy k)).1; linarith [hlo k]
  · have hs : ∑ k, lam k * y k ≤ ∑ k, lam k * hi := by
      apply sum_le_sum; intro k _
      apply mul_le_mul_of_nonneg_left _ (h0 k)
      have := (abs_le.1 (hy k)).2; linarith [hhi k]
    rwa [← sum_mul, h1, one_mul] at hs

/-- Points (`r = 0`): a convex combination of control points is in their box. -/
theorem hull_of_points {n : ℕ} (lam P : Fin n → ℝ) (lo hi : ℝ)
    (h0 : ∀ k, 0 ≤ lam k) (h1 : ∑ k, lam k = 1)
    (hlo : ∀ k, lo ≤ P k) (hhi : ∀ k, P k ≤ hi) :
    lo ≤ ∑ k, lam k * P k ∧ ∑ k, lam k * P k ≤ hi :=
  hull_of_balls lam P 0 P lo hi h0 h1 (by simp) (by simpa using hlo) (by simpa using hhi)

/-! ### Bernstein weights -/

/-- Cubic Bernstein basis. -/
def bern3 (t : ℝ) : Fin 4 → ℝ := ![(1 - t) ^ 3, 3 * t * (1 - t) ^ 2, 3 * t ^ 2 * (1 - t), t ^ 3]

theorem bern3_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (k : Fin 4) : 0 ≤ bern3 t k := by
  have : 0 ≤ 1 - t := by linarith
  fin_cases k <;> simp [bern3] <;> positivity

theorem bern3_sum (t : ℝ) : ∑ k, bern3 t k = 1 := by
  simp [bern3, Fin.sum_univ_four]; ring

/-- Cubic Bézier evaluation of one coordinate. -/
def bez3 (P : Fin 4 → ℝ) (t : ℝ) : ℝ := ∑ k, bern3 t k * P k

/-- **Round cubic Bézier curve.** A tube point is `C(t) + R(t)·n` with the
    centre `C` and radius `R` both Bézier in the control data and `|n_a| ≤ 1`
    (any unit direction); it is the convex combination of the points
    `P k + r k · n`, each inside its control ball. -/
theorem bezier_tube_in_box (P r : Fin 4 → ℝ) (t nA lo hi : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hr : ∀ k, 0 ≤ r k) (hn : |nA| ≤ 1)
    (hlo : ∀ k, lo ≤ P k - r k) (hhi : ∀ k, P k + r k ≤ hi) :
    lo ≤ bez3 P t + bez3 r t * nA ∧ bez3 P t + bez3 r t * nA ≤ hi := by
  have e : bez3 P t + bez3 r t * nA = ∑ k, bern3 t k * (P k + r k * nA) := by
    simp only [bez3, sum_mul, ← sum_add_distrib]; congr 1; ext k; ring
  rw [e]
  refine hull_of_balls (bern3 t) P r (fun k => P k + r k * nA) lo hi (bern3_nonneg h0 h1)
    (bern3_sum t) (fun k => ?_) hlo hhi
  simp only [add_sub_cancel_left, abs_mul, abs_of_nonneg (hr k)]
  exact mul_le_of_le_one_right (hr k) hn

/-- **Round-linear / flat curve.** The swept shape (tapered cone + end spheres;
    the ray-facing ribbon of half-width `r(s)`) is inside the convex hull of the
    two end balls: a point `(1-s)·y0 + s·y1` with `y i` in ball `i`. -/
theorem linear_tube_in_box (p0 p1 r0 r1 y0 y1 s lo hi : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (hy0 : |y0 - p0| ≤ r0) (hy1 : |y1 - p1| ≤ r1)
    (hlo0 : lo ≤ p0 - r0) (hlo1 : lo ≤ p1 - r1) (hhi0 : p0 + r0 ≤ hi) (hhi1 : p1 + r1 ≤ hi) :
    lo ≤ (1 - s) * y0 + s * y1 ∧ (1 - s) * y0 + s * y1 ≤ hi := by
  have := hull_of_balls ![1 - s, s] ![p0, p1] ![r0, r1] ![y0, y1] lo hi
    (fun k => by fin_cases k <;> simp <;> linarith) (by simp [Fin.sum_univ_two])
    (fun k => by fin_cases k <;> simpa) (fun k => by fin_cases k <;> simpa)
    (fun k => by fin_cases k <;> simpa)
  simpa [Fin.sum_univ_two] using this

/-- **Bilinear patch** `(1-u)(1-v)P0 + u(1-v)P1 + (1-u)v P2 + uv P3`, any corner order. -/
theorem bilinear_in_box (P : Fin 4 → ℝ) (u v lo hi : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hlo : ∀ k, lo ≤ P k) (hhi : ∀ k, P k ≤ hi) :
    let w : Fin 4 → ℝ := ![(1 - u) * (1 - v), u * (1 - v), (1 - u) * v, u * v]
    lo ≤ ∑ k, w k * P k ∧ ∑ k, w k * P k ≤ hi := by
  intro w
  have a : 0 ≤ 1 - u := by linarith
  have b : 0 ≤ 1 - v := by linarith
  exact hull_of_points w P lo hi (fun k => by fin_cases k <;> simp [w] <;> positivity)
    (by simp [w, Fin.sum_univ_four]; ring) hlo hhi

/-- Tensor-product bicubic weights `B_i(u) B_j(v)`, flattened `k = 4 j + i`. -/
def bern33 (u v : ℝ) (k : Fin 16) : ℝ := bern3 u ⟨k.val % 4, by omega⟩ * bern3 v ⟨k.val / 4, by omega⟩

theorem bern33_nonneg {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (k : Fin 16) : 0 ≤ bern33 u v k :=
  mul_nonneg (bern3_nonneg hu0 hu1 _) (bern3_nonneg hv0 hv1 _)

theorem bern33_sum (u v : ℝ) : ∑ k, bern33 u v k = 1 := by
  have hu := bern3_sum u
  have hv := bern3_sum v
  simp only [Fin.sum_univ_four] at hu hv
  simp only [bern33, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Fin.val_zero, Fin.val_succ]
  norm_num
  linear_combination (bern3 v 0 + bern3 v 1 + bern3 v 2 + bern3 v 3) * hu + hv

/-- **Bicubic Bézier patch**: inside the box of its 16 control points. -/
theorem bicubic_in_box (P : Fin 16 → ℝ) (u v lo hi : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hlo : ∀ k, lo ≤ P k) (hhi : ∀ k, P k ≤ hi) :
    lo ≤ ∑ k, bern33 u v k * P k ∧ ∑ k, bern33 u v k * P k ≤ hi :=
  hull_of_points _ P lo hi (bern33_nonneg hu0 hu1 hv0 hv1) (bern33_sum u v) hlo hhi

/-- **Rational patch** (NURBS → rational Bézier, homogeneous CPs `(x, w)` with
    `w > 0`): `S = Σ β_k x_k / Σ β_k w_k` lies in any box containing every
    projected control point `x_k / w_k`. The C build requires `w > 0`. -/
theorem rational_in_box {n : ℕ} (beta x w : Fin n → ℝ) (lo hi : ℝ)
    (hb0 : ∀ k, 0 ≤ beta k) (hb1 : ∑ k, beta k = 1) (hw : ∀ k, 0 < w k)
    (hlo : ∀ k, lo ≤ x k / w k) (hhi : ∀ k, x k / w k ≤ hi) :
    lo ≤ (∑ k, beta k * x k) / (∑ k, beta k * w k) ∧
      (∑ k, beta k * x k) / (∑ k, beta k * w k) ≤ hi := by
  have hD : 0 < ∑ k, beta k * w k := by
    obtain ⟨k, -, hk⟩ : ∃ k ∈ (univ : Finset (Fin n)), 0 < beta k := by
      by_contra hc
      push_neg at hc
      have : ∑ k, beta k ≤ 0 := sum_nonpos fun k hk => hc k hk
      linarith
    exact lt_of_lt_of_le (mul_pos hk (hw k))
      (single_le_sum (f := fun k => beta k * w k)
        (fun j _ => mul_nonneg (hb0 j) (hw j).le) (mem_univ k))
  set D := ∑ k, beta k * w k
  have e : (∑ k, beta k * x k) / D = ∑ k, (beta k * w k / D) * (x k / w k) := by
    rw [sum_div]; congr 1; ext k; field_simp [(hw k).ne']
  rw [e]
  exact hull_of_points (fun k => beta k * w k / D) (fun k => x k / w k) lo hi
    (fun k => div_nonneg (mul_nonneg (hb0 k) (hw k).le) hD.le)
    (by rw [← sum_div, div_self hD.ne']) hlo hhi

/-- **Points**: a sphere point, or any disc of radius `r` centred at `c`. -/
theorem ball_in_box (c r y lo hi : ℝ) (hy : |y - c| ≤ r) (hlo : lo ≤ c - r) (hhi : c + r ≤ hi) :
    lo ≤ y ∧ y ≤ hi := by
  have := abs_le.1 hy; constructor <;> linarith

/-! ### de Casteljau pre-subdivision is exact -/

/-- Left half of the de Casteljau split at `t` (`tri_bez_split`'s `L`). -/
def splitL (P : Fin 4 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  let ab := P 0 + (P 1 - P 0) * t
  let bc := P 1 + (P 2 - P 1) * t
  let cd := P 2 + (P 3 - P 2) * t
  let abc := ab + (bc - ab) * t
  let bcd := bc + (cd - bc) * t
  ![P 0, ab, abc, abc + (bcd - abc) * t]

/-- Right half (`tri_bez_split`'s `R`). -/
def splitR (P : Fin 4 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  let ab := P 0 + (P 1 - P 0) * t
  let bc := P 1 + (P 2 - P 1) * t
  let cd := P 2 + (P 3 - P 2) * t
  let abc := ab + (bc - ab) * t
  let bcd := bc + (cd - bc) * t
  ![abc + (bcd - abc) * t, bcd, cd, P 3]

theorem decasteljau_left (P : Fin 4 → ℝ) (t s : ℝ) : bez3 (splitL P t) s = bez3 P (t * s) := by
  simp [bez3, bern3, splitL, Fin.sum_univ_four]; ring

theorem decasteljau_right (P : Fin 4 → ℝ) (t s : ℝ) :
    bez3 (splitR P t) s = bez3 P (t + (1 - t) * s) := by
  simp [bez3, bern3, splitR, Fin.sum_univ_four]; ring

end LightRT.Geom.Hull
