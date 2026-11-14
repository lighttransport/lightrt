/-
  The one-dimensional core of the sphere-trace first-contact argument.

  The Bézier leaf (`lightrt_c_tri.c`, `tri_bezcurve_*`) traces a ray against
  the union of balls around a curve: at parameter `t` it takes a step of the
  (unsigned) distance `f t` to the curve. `f` is 1-Lipschitz (a distance
  function is), so a step can never pass a point where `f ≤ 0`:

      f root ≤ 0,  y ≤ root  →  y + f y ≤ root.

  Hence every iterate starting left of a surface point stays left of it
  (`trace_le_root`), and the trace is monotone where `f > 0`. This is the
  "no overshoot / no false miss" half of the first-contact argument; the full
  model (the actual signed distance of the Bézier curve, and the Newton
  refinement) is the remaining part of PLAN M14.
-/
import Mathlib

namespace LightRT.Geom

/-- A 1-Lipschitz real function: the distance to the curve along the ray. -/
def Lipschitz1 (f : ℝ → ℝ) : Prop := ∀ x y, |f x - f y| ≤ |x - y|

/-- One sphere-trace step. -/
def stStep (f : ℝ → ℝ) (t : ℝ) : ℝ := t + f t

/-- `n` sphere-trace steps from `t`. -/
def stTrace (f : ℝ → ℝ) (t : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => stStep f (stTrace f t n)

theorem stStep_le_root {f : ℝ → ℝ} (hf : Lipschitz1 f) {root y : ℝ}
    (hroot : f root ≤ 0) (hy : y ≤ root) : stStep f y ≤ root := by
  have h1 := hf y root
  have h2 : |y - root| = root - y := by rw [abs_of_nonpos (by linarith)]; ring
  have h3 : f y - f root ≤ root - y := by
    have := (abs_le.1 h1).2
    linarith [h2]
  unfold stStep
  linarith

/-- Every iterate stays left of a surface point. -/
theorem stTrace_le_root {f : ℝ → ℝ} (hf : Lipschitz1 f) {root : ℝ}
    (hroot : f root ≤ 0) :
    ∀ {t : ℝ}, t ≤ root → ∀ n, stTrace f t n ≤ root
  | t, ht, 0 => ht
  | t, ht, n + 1 => stStep_le_root hf hroot (stTrace_le_root hf hroot ht n)

/-- A positive step advances. -/
theorem stStep_gt {f : ℝ → ℝ} {t : ℝ} (h : 0 < f t) : t < stStep f t := by
  unfold stStep; linarith

/-- A nonnegative step does not go backwards. -/
theorem stStep_ge {f : ℝ → ℝ} {t : ℝ} (h : 0 ≤ f t) : t ≤ stStep f t := by
  unfold stStep; linarith

/-- The trace is monotone while the distance is nonnegative. -/
theorem stTrace_mono {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) (t : ℝ) :
    ∀ n, stTrace f t n ≤ stTrace f t (n + 1) :=
  fun n => stStep_ge (hf _)

/-- **Distance to a point is 1-Lipschitz** (reverse triangle inequality). This
    is the atom of the Bézier tube-distance function: each sampled point's
    distance is 1-Lipschitz in `x`, and a minimum over samples inherits it. -/
theorem dist_point_lipschitz (p x y : ℝ) : abs (abs (x - p) - abs (y - p)) ≤ abs (x - y) := by
  have h1 : |x - p| ≤ |x - y| + |y - p| := by
    have : x - p = (x - y) + (y - p) := by ring
    rw [this]
    exact abs_add_le (x - y) (y - p)
  have h2 : |y - p| ≤ |x - y| + |x - p| := by
    have : y - p = (y - x) + (x - p) := by ring
    rw [this]
    have := abs_add_le (y - x) (x - p)
    rw [abs_sub_comm y x] at this
    exact this
  rw [abs_le]
  constructor
  · linarith [h1]
  · linarith [h2]

/-- **Newton step for solving `f x = 0`.** -/
noncomputable def newtonStep (f : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / deriv f x

/-- **One Newton step squares the error.** If `f r = 0`, `f` is differentiable
    on the interval between `r` and `x`, `deriv f` is `K`-Lipschitz there, and
    `|deriv f x| ≥ c > 0`, then
    `|newtonStep f x - r| ≤ K |x - r|² / c`.

    This is the convergence core of the Bézier Newton refinement
    (`tri_bez_newton`): near a simple root each step is quadratically
    contracting, provided the derivative stays bounded away from zero and varies
    no faster than `K`. -/
theorem newton_step_quadratic {f : ℝ → ℝ} {r x K c : ℝ}
    (hr : f r = 0)
    (hK : 0 ≤ K)
    (hdiff : DifferentiableOn ℝ f (Set.Icc (min r x) (max r x)))
    (hlip : ∀ a b, a ∈ Set.Icc (min r x) (max r x) →
        b ∈ Set.Icc (min r x) (max r x) →
        |deriv f a - deriv f b| ≤ K * |a - b|)
    (hden : c ≤ |deriv f x|) (hc : 0 < c) :
    |newtonStep f x - r| ≤ K * |x - r| ^ 2 / c := by
  by_cases hxr : x = r
  · subst hxr
    simp [newtonStep, hr]
  · have hab : min r x < max r x := by
      rcases le_total r x with h | h
      · simp [min_eq_left h, max_eq_right h]
        exact lt_of_le_of_ne h (Ne.symm hxr)
      · simp [min_eq_right h, max_eq_left h]
        exact lt_of_le_of_ne h hxr
    have hcont : ContinuousOn f (Set.Icc (min r x) (max r x)) :=
      hdiff.continuousOn
    have hsub : Set.Ioo (min r x) (max r x) ⊆ Set.Icc (min r x) (max r x) := by
      intro y hy
      exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hdiff_oo : DifferentiableOn ℝ f (Set.Ioo (min r x) (max r x)) :=
      DifferentiableOn.mono hdiff hsub
    obtain ⟨ξ, hξ, hMVT⟩ := exists_deriv_eq_slope f hab hcont hdiff_oo
    have hξcc : ξ ∈ Set.Icc (min r x) (max r x) :=
      ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
    have hxcc : x ∈ Set.Icc (min r x) (max r x) :=
      ⟨min_le_right r x, le_max_right r x⟩
    have hxrn : x - r ≠ 0 := sub_ne_zero.mpr hxr
    have hdx : deriv f x ≠ 0 := by
      intro h
      rw [h, abs_zero] at hden
      linarith [hc, hden]
    have hfx : f x = deriv f ξ * (x - r) := by
      have := hMVT
      rcases le_total r x with hrx | hrx
      · simp [min_eq_left hrx, max_eq_right hrx] at this
        rw [hr] at this
        have : deriv f ξ * (x - r) = f x := by
          rw [this]; field_simp [hxrn]; ring
        exact this.symm
      · simp [min_eq_right hrx, max_eq_left hrx] at this
        have hthis : deriv f ξ = (f r - f x) / (r - x) := by simpa using this
        rw [hr] at hthis
        have : deriv f ξ * (x - r) = f x := by
          rw [hthis]; field_simp [hxrn]; ring
        exact this.symm
    have hstep : newtonStep f x - r = (x - r) * (deriv f x - deriv f ξ) / deriv f x := by
      unfold newtonStep
      rw [hfx]
      field_simp [hdx]
      ring
    have hlipξ : |deriv f x - deriv f ξ| ≤ K * |x - ξ| :=
      hlip x ξ hxcc hξcc
    have hxξ : |x - ξ| ≤ |x - r| := by
      -- ξ lies between r and x
      rcases le_total r x with hrx | hrx
      · -- r ≤ x: ξ ∈ [r, x]
        simp [min_eq_left hrx, max_eq_right hrx] at hξ
        have h1 : r ≤ ξ := le_of_lt hξ.1
        have h2 : ξ ≤ x := le_of_lt hξ.2
        have : |x - ξ| = x - ξ := abs_of_nonneg (sub_nonneg.mpr h2)
        have : |x - r| = x - r := abs_of_nonneg (sub_nonneg.mpr hrx)
        linarith [h1]
      · -- x ≤ r: ξ ∈ [x, r]
        simp [min_eq_right hrx, max_eq_left hrx] at hξ
        have h1 : x ≤ ξ := le_of_lt hξ.1
        have h2 : ξ ≤ r := le_of_lt hξ.2
        have : |x - ξ| = -(x - ξ) := abs_of_nonpos (sub_nonpos.mpr h1)
        have : |x - r| = -(x - r) := abs_of_nonpos (sub_nonpos.mpr hrx)
        linarith [h2]
    -- final calc
    have habs : |newtonStep f x - r| = |x - r| * |deriv f x - deriv f ξ| / |deriv f x| := by
      rw [hstep]
      rw [abs_div]
      rw [abs_mul]
    calc |newtonStep f x - r|
        = |x - r| * |deriv f x - deriv f ξ| / |deriv f x| := habs
        _ ≤ |x - r| * (K * |x - ξ|) / c := by
            gcongr
        _ ≤ |x - r| * (K * |x - r|) / c := by
            gcongr
        _ = K * |x - r| ^ 2 / c := by ring

end LightRT.Geom
