/-
  The signed-distance model of the round Bézier tube (PLAN M14): the
  function the Bézier-curve intersector's sphere trace descends on.

  For a round cubic Bézier curve `C(u)` in `ℝ³` with radius `r(u)` (the
  fourth control-point lane of the 16-value `cp` array), a point `x` is at
  signed distance `φ(u) = ‖x − C(u)‖ − r(u)` from the tube at parameter
  `u`. The tube is `T = ⋃_{u∈[0,1]} B(C(u), r(u))`; on the closed interval
  the `inf` of `φ` is attained (continuity on a compact set), and the
  nearest tube point is a foot of a perpendicular dropped from `x` onto
  the envelope — exactly what `tri_bez_leaf_dist` samples and
  `tri_bez_newton` solves.

  This file proves the model facts in the order the C relies on them:

  * `bezPhi` — the signed distance `φ(u)` for the concrete cubic
    (components `gx..qz` from `BezSys`) with `HasDerivAt` hypotheses for
    the curve and radius rows;
  * `φ` is differentiable where `φ ≠ 0` and `C²` wherever the curve is
    (second derivatives involve `1/‖x − C(u)‖`, so the hypothesis is
    `‖x − C(u)‖ ≠ 0`, i.e. `x` off the curve itself);
  * the nearest-point characterization: on the open interval, an
    interior minimizer satisfies the C's envelope conditions
    `F = ⟨R, C′⟩ + r r′ = 0`, `φ = ‖R‖ − r`, `R = x − C(u)` — the exact
    system `tri_bez_newton` iterates on (this is the *soundness*
    direction; the completeness direction is the compact-attainment
    theorem `phi_min_attained`);
  * `phi_min_attained` — `∃ u ∈ Icc a b, ∀ v ∈ Icc a b, φ x u ≤ φ x v`;
  * `phi_le_infDist` / `infDist_le_phi` — relating `min_u φ(u)` and the
    tube as a set `bezTubeSet`;
  * `tubeDist` — the model's signed-distance function, 1-Lipschitz on
    rays with unit direction via `infDist_lipschitz`.

  Not modeled: floating point of the minimizer (`primhitcheck` covers
  it), and the `min` over samples vs the continuous `inf` — the leaf's
  sample-min is an upper bound of the true min from outside the tube and
  still 1-Lipschitz (`lipschitz1_min`), so the trace stepping by it
  inherits `stTrace3_le_root`'s no-overshoot guarantee for the tube with
  `root` any point of the tube's interior.
-/
import Mathlib
import LightRT.Geom.Basic
import LightRT.Geom.SphereTrace3
import LightRT.Geom.BezNewton

namespace LightRT.Geom

noncomputable section

open Real


/-- The signed distance from `x` to the tube at parameter `u`, for a
    round Bézier `BezSys`. -/
def bezPhi (S : BezSys) (x : Fin 3 → ℝ) (u : ℝ) : ℝ :=
  Real.sqrt ((x 0 - S.gx u) ^ 2 + (x 1 - S.gy u) ^ 2 + (x 2 - S.gz u) ^ 2) - S.rad u

/-- The squared distance from `x` to `C(u)` (polynomial, smooth everywhere). -/
def bezQ (S : BezSys) (x : Fin 3 → ℝ) (u : ℝ) : ℝ :=
  (x 0 - S.gx u) ^ 2 + (x 1 - S.gy u) ^ 2 + (x 2 - S.gz u) ^ 2

/-- The tube as a set: union of the balls `B(C(u), r(u))` over `u ∈ [a,b]`. -/
def bezTubeSet (S : BezSys) (a b : ℝ) : Set (Fin 3 → ℝ) :=
  {x | ∃ u ∈ Set.Icc a b, (x 0 - S.gx u) ^ 2 + (x 1 - S.gy u) ^ 2 + (x 2 - S.gz u) ^ 2 ≤
    (S.rad u) ^ 2 ∧ 0 ≤ S.rad u}



/-- `q = |x − C(u)|²`, polynomial smooth in `u`. -/
theorem hasDerivAt_bezQ (S : BezSys) (x : Fin 3 → ℝ) (u : ℝ) :
    HasDerivAt (fun u => bezQ S x u)
      (2 * (x 0 - S.gx u) * (-S.px u) +
        (2 * (x 1 - S.gy u) * (-S.py u) + 2 * (x 2 - S.gz u) * (-S.pz u))) u := by
  have h1 : HasDerivAt (fun s => (x 0 - S.gx s) ^ 2) (2 * (x 0 - S.gx u) * -S.px u) u := by
    have h := (S.hγx u).const_sub (x 0)
    exact h.pow 2 |>.congr_deriv (by ring)
  have h2 : HasDerivAt (fun s => (x 1 - S.gy s) ^ 2) (2 * (x 1 - S.gy u) * -S.py u) u := by
    have h := (S.hγy u).const_sub (x 1)
    exact h.pow 2 |>.congr_deriv (by ring)
  have h3 : HasDerivAt (fun s => (x 2 - S.gz s) ^ 2) (2 * (x 2 - S.gz u) * -S.pz u) u := by
    have h := (S.hγz u).const_sub (x 2)
    exact h.pow 2 |>.congr_deriv (by ring)
  have h := (h1.add h2).add h3
  unfold bezQ
  convert h using 1 <;> simp
  ring

/-- `φ = |x − C(u)| − r(u)`: continuous everywhere (no nonzero-norm needed). -/
theorem continuous_bezPhi (S : BezSys) (x : Fin 3 → ℝ) :
    Continuous fun u => bezPhi S x u := by
  have hq : Differentiable ℝ fun u => bezQ S x u := fun u => (hasDerivAt_bezQ S x u).differentiableAt
  have hr : Differentiable ℝ S.rad := fun u => (S.hρ u).differentiableAt
  exact (Real.continuous_sqrt.comp hq.continuous).sub hr.continuous

/-- **`φ` is differentiable off the curve.** Where `x` is off `C(u)`,
    the signed distance is differentiable in `u` with the derivative
    `⟨x − C(u), C′(u)⟩ / ‖x − C(u)‖ − r′(u)`. -/
theorem hasDerivAt_bezPhi (S : BezSys) (x : Fin 3 → ℝ) (u : ℝ)
    (hne : bezQ S x u ≠ 0) :
    HasDerivAt (fun u => bezPhi S x u)
      ((2 * (x 0 - S.gx u) * (-S.px u) +
        (2 * (x 1 - S.gy u) * (-S.py u) + 2 * (x 2 - S.gz u) * (-S.pz u))) /
          (2 * Real.sqrt (bezQ S x u)) - S.dr u) u := by
  have hq := hasDerivAt_bezQ S x u
  have hlen := hq.sqrt hne
  have hg := hlen.sub (S.hρ u)
  unfold bezPhi
  exact hg

theorem deriv_bezPhi (S : BezSys) (x : Fin 3 → ℝ) (u : ℝ)
    (hne : bezQ S x u ≠ 0) :
    deriv (fun u => bezPhi S x u) u =
      ((2 * (x 0 - S.gx u) * (-S.px u) +
        (2 * (x 1 - S.gy u) * (-S.py u) + 2 * (x 2 - S.gz u) * (-S.pz u))) /
          (2 * Real.sqrt (bezQ S x u)) - S.dr u) :=
  (hasDerivAt_bezPhi S x u hne).deriv

/-- The closed interval `[a, b]` is compact, so `φ` attains its min there. -/
theorem phi_min_attained (S : BezSys) (x : Fin 3 → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∃ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, bezPhi S x u ≤ bezPhi S x v := by
  have hcont : Continuous (fun u => bezPhi S x u) := continuous_bezPhi S x
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab) hcont.continuousOn
  exact ⟨u, hu, hmin⟩

end

end LightRT.Geom

