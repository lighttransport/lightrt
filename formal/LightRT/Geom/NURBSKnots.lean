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
import LightRT.Geom.NURBSReal

namespace LightRT.Geom
open LightRT.Geom.Hull
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


/-- Insert a new knot `u` into knot vector `U` after index `k`, producing
    `Ū = [U₀..U_k, u, U_{k+1}..]`. -/
def insertKnot (U : ℕ → ℝ) (k : ℕ) (u : ℝ) : ℕ → ℝ :=
  fun j => if j ≤ k then U j else if j = k + 1 then u else U (j - 1)

@[simp] theorem insertKnot_le {U : ℕ → ℝ} (u : ℝ) {k j : ℕ} (h : j ≤ k) :
    insertKnot U k u j = U j := by simp [insertKnot, h]

@[simp] theorem insertKnot_mid {U : ℕ → ℝ} (u : ℝ) {k : ℕ} :
    insertKnot U k u (k+1) = u := by simp [insertKnot]

@[simp] theorem insertKnot_gt {U : ℕ → ℝ} (u : ℝ) {k j : ℕ} (h : k + 1 < j) :
    insertKnot U k u j = U (j-1) := by
  have hnot : ¬ j ≤ k := by omega
  have hne : ¬ j = k + 1 := by omega
  simp [insertKnot, hnot, hne]

/-- **Degree-0 B-spline refinement.** Inserting a knot `u` in `[U_k, U_{k+1})`
    splits the support of `N_{k,0}` into two and leaves all other degree-0
    basis functions (shifted) unchanged. -/
theorem bsplineBasis_zero_refinement (U : ℕ → ℝ) (k : ℕ) (u x : ℝ)
    (hlo : U k ≤ u) (hhi : u < U (k+1)) :
    (∀ i < k, bsplineBasis (insertKnot U k u) i 0 x = bsplineBasis U i 0 x) ∧
    bsplineBasis U k 0 x =
      bsplineBasis (insertKnot U k u) k 0 x + bsplineBasis (insertKnot U k u) (k+1) 0 x ∧
    (∀ i, k < i → bsplineBasis U i 0 x = bsplineBasis (insertKnot U k u) (i+1) 0 x) := by
  constructor
  · intro i hi
    simp [bsplineBasis]
    have hik : i ≤ k := by omega
    have hi1 : i + 1 ≤ k := by omega
    simp [insertKnot, hik, hi1]
  constructor
  · simp [bsplineBasis]
    have h1 : k ≤ k := le_rfl
    have h2 : ¬ k + 1 ≤ k := by omega
    have h3 : k + 1 = k + 1 := rfl
    have h4 : ¬ k + 2 ≤ k := by omega
    have h5 : ¬ k + 2 = k + 1 := by omega
    have h6 : k + 2 - 1 = k + 1 := by omega
    by_cases hxU : U k ≤ x ∧ x < U (k+1)
    · have hsplit : (U k ≤ x ∧ x < u) ∨ (u ≤ x ∧ x < U (k+1)) := by
        by_cases hxu : x < u
        · exact Or.inl ⟨hxU.1, hxu⟩
        · exact Or.inr ⟨le_of_not_gt hxu, hxU.2⟩
      rcases hsplit with h | h <;> simp [hxU, h]
    · have hn1 : ¬ (U k ≤ x ∧ x < u) := by
        intro h; exact hxU ⟨h.1, lt_trans h.2 hhi⟩
      have hn2 : ¬ (u ≤ x ∧ x < U (k+1)) := by
        intro h; exact hxU ⟨le_trans hlo h.1, h.2⟩
      simp [hxU, hn1, hn2]
    -- unused old branch
  · intro i hi
    simp [bsplineBasis]
    have hik' : i ≠ k := by omega
    have h1 : ¬ i + 1 ≤ k := by omega
    have h2 : ¬ i + 1 = k + 1 := by omega
    have h4 : ¬ i + 1 = k := by omega
    have h5 : ¬ i + 1 < k := by omega
    have h3 : i + 1 - 1 = i := by omega
    simp [insertKnot, hik', h1, h2, h4, h5, h3]


/-- Partition of unity for the degree-1 refined Bezier knot vector. -/
theorem bezKnot1_refined_sum (t u : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineBasis (insertKnot (bezKnot 1) 1 t) 0 1 u +
    bsplineBasis (insertKnot (bezKnot 1) 1 t) 1 1 u +
    bsplineBasis (insertKnot (bezKnot 1) 1 t) 2 1 u = 1 := by
  simp [bsplineBasis, insertKnot, bezKnot]
  by_cases hut : u < t
  · have htu : ¬ t ≤ u := by linarith
    simp [hut, htu, hu0, hu1]
    field_simp [ne_of_gt ht0]
    ring
  · have htu : t ≤ u := le_of_not_gt hut
    simp [hut, htu, hu0, hu1]
    field_simp [ne_of_gt (sub_pos.mpr ht1)]
    ring

/-- Boehm control points for inserting knot `t` into the degree-1 Bezier
    knot vector over control points `P₀, P₁`. -/
def boehm1 (P : Fin 2 → Vec3) (t : ℝ) : Fin 3 → Vec3 :=
  ![P 0, (1-t) • P 0 + t • P 1, P 1]

theorem boehm1_preserves (P : Fin 2 → Vec3) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineCurve (insertKnot (bezKnot 1) 1 t)
      (fun i => if h : i < 3 then boehm1 P t ⟨i, h⟩ else 0) 1 2 u =
      bsplineCurve (bezKnot 1) (fun i => if h : i < 2 then P ⟨i, h⟩ else 0) 1 1 u := by
  -- unfold both curves
  unfold bsplineCurve
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [bsplineBasis, insertKnot, bezKnot]
  -- case split u < t
  by_cases hut : u < t
  · have htu : ¬ t ≤ u := by linarith
    simp [hut, htu, ht0.le, ht1.le, hu0, hu1, boehm1]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt ht0]
    ring
  · have htu : t ≤ u := le_of_not_gt hut
    simp [hut, htu, ht0.le, ht1.le, hu0, hu1, boehm1]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt (sub_pos.mpr ht1)]
    ring

/-- Tensor-product rational B-spline evaluation over the cubic Bezier knot
    vector equals the rational bicubic evaluation `ratEval` of NURBSReal.
    This is the surface form of Bezier extraction: for a NURBS patch whose
    knot vectors are Bezier knot vectors, no knot insertion is needed. -/
theorem bezKnot_ratEval (w : Fin 16 → ℝ) (P : Fin 16 → Vec3) (u v : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    (fun i => (∑ k : Fin 16,
        (bsplineBasis (bezKnot 3) (k.val % 4) 3 u *
         bsplineBasis (bezKnot 3) (k.val / 4) 3 v * w k) • P k i) /
      (∑ k : Fin 16, bern33 u v k * w k)) = ratEval w P u v := by
  have hbasisU (j : ℕ) (hj : j < 4) :
      bsplineBasis (bezKnot 3) j 3 u = bern3 u ⟨j, hj⟩ := by
    interval_cases j <;> simp [Hull.bern3,
      bezKnot_basis0 u hu0 hu1, bezKnot_basis1 u hu0 hu1,
      bezKnot_basis2 u hu0 hu1, bezKnot_basis3 u hu0 hu1]
  have hbasisV (j : ℕ) (hj : j < 4) :
      bsplineBasis (bezKnot 3) j 3 v = bern3 v ⟨j, hj⟩ := by
    interval_cases j <;> simp [Hull.bern3,
      bezKnot_basis0 v hv0 hv1, bezKnot_basis1 v hv0 hv1,
      bezKnot_basis2 v hv0 hv1, bezKnot_basis3 v hv0 hv1]
  ext i
  unfold ratEval ratWeight
  apply congrArg (fun z => z / (∑ k : Fin 16, bern33 u v k * w k))
  apply Finset.sum_congr rfl
  intro k hk
  rw [hbasisU (k.val % 4) (by omega), hbasisV (k.val / 4) (by omega)]
  simp [bern33, Pi.smul_apply, smul_eq_mul, mul_assoc]

end
end LightRT.Geom
