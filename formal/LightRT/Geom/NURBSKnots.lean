/-
  Cox–de Boor B-spline basis and the Bezier knot vector, over R. Establishes
  that for the cubic Bezier knot vector (0,0,0,0,1,1,1,1) the B-spline basis
  is exactly the cubic Bernstein basis, hence a degree-3 B-spline curve over
  that knot vector equals the Bezier curve. Foundation for the knot-insertion
  / Bezier-extraction path used by the NURBS surface intersector.
  Tier 1 item 1 of the roadmap.
-/
import Mathlib
import LightRT.Geom.BezPatchReal

namespace LightRT.Geom
noncomputable section

/-- Cox–de Boor B-spline basis function `N_{i,p}` over a knot vector `U`.
    The degree-0 basis uses the half-open convention `[U_i, U_{i+1})`, so all
    identities below hold on `[0,1)` (right endpoint handled separately). -/
def bsplineBasis (U : ℕ → ℝ) (i p : ℕ) (u : ℝ) : ℝ :=
  match p with
  | 0 => if U i ≤ u ∧ u < U (i + 1) then 1 else 0
  | p + 1 =>
      let a := (u - U i) / (U (i + p + 1) - U i)
      let b := (U (i + p + 2) - u) / (U (i + p + 2) - U (i + 1))
      a * bsplineBasis U i p u + b * bsplineBasis U (i + 1) p u

/-- The Bezier knot vector of degree 3: 0 repeated 4 times, then 1. -/
def bezKnot (p : ℕ) : ℕ → ℝ := fun j => if j ≤ p then 0 else 1

theorem bezKnot_basis0 (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineBasis (bezKnot 3) 0 3 u = (1-u)^3 := by
  simp [bsplineBasis, bezKnot, hu0, hu1]; ring

theorem bezKnot_basis1 (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineBasis (bezKnot 3) 1 3 u = 3*u*(1-u)^2 := by
  simp [bsplineBasis, bezKnot, hu0, hu1]; ring

theorem bezKnot_basis2 (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineBasis (bezKnot 3) 2 3 u = 3*u^2*(1-u) := by
  simp [bsplineBasis, bezKnot, hu0, hu1]; ring

theorem bezKnot_basis3 (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineBasis (bezKnot 3) 3 3 u = u^3 := by
  simp [bsplineBasis, bezKnot, hu0, hu1]; ring

/-- Basis functions outside the Bezier knot vector's nonzero range vanish. -/
theorem bezKnot_basis_ge4 (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) {i : ℕ} (hi : 4 ≤ i) :
    bsplineBasis (bezKnot 3) i 3 u = 0 := by
  have hi' : ¬ i ≤ 3 := by omega
  have hi1 : ¬ i < 3 := by omega
  have hi2 : ¬ i + 1 < 3 := by omega
  have hi3 : ¬ i + 2 < 3 := by omega
  have hi4 : ¬ i + 3 < 3 := by omega
  simp [bsplineBasis, bezKnot, hu0, hu1, hi', hi1, hi2, hi3, hi4]

/-- Partition of unity for the cubic Bezier knot vector on `[0,1)`. -/
theorem bezKnot_sum (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineBasis (bezKnot 3) 0 3 u + bsplineBasis (bezKnot 3) 1 3 u +
    bsplineBasis (bezKnot 3) 2 3 u + bsplineBasis (bezKnot 3) 3 3 u = 1 := by
  rw [bezKnot_basis0 u hu0 hu1, bezKnot_basis1 u hu0 hu1,
    bezKnot_basis2 u hu0 hu1, bezKnot_basis3 u hu0 hu1]
  ring

/-- A B-spline curve of degree `p` over `U`. -/
def bsplineCurve (U : ℕ → ℝ) (P : ℕ → Vec3) (p n : ℕ) (u : ℝ) : Vec3 :=
  ∑ i ∈ Finset.range (n + 1), bsplineBasis U i p u • P i

/-- For the cubic Bezier knot vector, the B-spline curve equals the Bezier
    curve `bez3Vec` (the tensor-Bernstein u-row) on `[0,1)`. -/
theorem bezKnot_curve (P : Fin 4 → Vec3) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineCurve (bezKnot 3) (fun i => if h : i < 4 then P ⟨i, h⟩ else 0) 3 3 u =
      bez3Vec P u := by
  unfold bsplineCurve
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  rw [bezKnot_basis0 u hu0 hu1, bezKnot_basis1 u hu0 hu1,
    bezKnot_basis2 u hu0 hu1, bezKnot_basis3 u hu0 hu1]
  simp [bez3Vec, Hull.bern3, Fin.sum_univ_four]

end
end LightRT.Geom
