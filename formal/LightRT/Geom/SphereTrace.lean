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

end LightRT.Geom
