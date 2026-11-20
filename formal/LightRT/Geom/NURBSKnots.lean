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

/-- Bezier extraction for surfaces, stated entirely in B-spline terms: rational
    tensor-product B-spline evaluation over the cubic Bezier knot vector equals
    `ratEval` of NURBSReal. Both the numerator and denominator use `bsplineBasis`,
    so the identity is not circular. -/
theorem bezKnot_ratEval (w : Fin 16 → ℝ) (P : Fin 16 → Vec3) (u v : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    (fun i => (∑ k : Fin 16,
        (bsplineBasis (bezKnot 3) (k.val % 4) 3 u *
         bsplineBasis (bezKnot 3) (k.val / 4) 3 v * w k) • P k i) /
      (∑ k : Fin 16,
        bsplineBasis (bezKnot 3) (k.val % 4) 3 u *
        bsplineBasis (bezKnot 3) (k.val / 4) 3 v * w k)) = ratEval w P u v := by
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
  have hterm (k : Fin 16) :
      bsplineBasis (bezKnot 3) (k.val % 4) 3 u *
        bsplineBasis (bezKnot 3) (k.val / 4) 3 v * w k =
      bern33 u v k * w k := by
    rw [hbasisU (k.val % 4) (by omega), hbasisV (k.val / 4) (by omega)]
    simp [bern33, mul_assoc]
  have hden : (∑ k : Fin 16,
        bsplineBasis (bezKnot 3) (k.val % 4) 3 u *
        bsplineBasis (bezKnot 3) (k.val / 4) 3 v * w k) =
      (∑ k : Fin 16, bern33 u v k * w k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k
  ext i
  rw [hden]
  unfold ratEval ratWeight
  apply congrArg (fun z => z / (∑ k : Fin 16, bern33 u v k * w k))
  apply Finset.sum_congr rfl
  intro k hk
  rw [hterm k]
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem bezKnot_basis0_deg2 (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineBasis (bezKnot 2) 0 2 u = (1-u)^2 := by
  simp [bsplineBasis, bezKnot, hu0, hu1]
  ring

theorem bezKnot_basis1_deg2 (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineBasis (bezKnot 2) 1 2 u = 2*u*(1-u) := by
  simp [bsplineBasis, bezKnot, hu0, hu1]
  ring

theorem bezKnot_basis2_deg2 (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineBasis (bezKnot 2) 2 2 u = u^2 := by
  simp [bsplineBasis, bezKnot, hu0, hu1]
  ring

def boehm2 (P : Fin 3 → Vec3) (t : ℝ) : Fin 4 → Vec3 :=
  ![P 0, (1-t) • P 0 + t • P 1, (1-t) • P 1 + t • P 2, P 2]

/-- Degree-2 Boehm knot insertion preserves the Bezier curve. -/
theorem boehm2_preserves (P : Fin 3 → Vec3) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineCurve (insertKnot (bezKnot 2) 2 t) (fun i => if h : i < 4 then boehm2 P t ⟨i,h⟩ else 0) 2 3 u =
      bsplineCurve (bezKnot 2) (fun i => if h : i < 3 then P ⟨i,h⟩ else 0) 2 2 u := by
  ext coord
  unfold bsplineCurve
  -- expand the sums over Fin 3 / Fin 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  -- evaluate old basis
  rw [bezKnot_basis0_deg2 u hu0 hu1, bezKnot_basis1_deg2 u hu0 hu1, bezKnot_basis2_deg2 u hu0 hu1]
  -- evaluate new basis by case split on u < t
  by_cases htu : u < t
  · have ht_le : ¬ t ≤ u := by linarith
    simp [bsplineBasis, insertKnot, bezKnot, htu, hu0, hu1, ht0.le, ht1.le,
          ht_le, boehm2] at *
    field_simp [ne_of_gt ht0]
    ring
  · have ht_le : t ≤ u := le_of_not_gt htu
    simp [bsplineBasis, insertKnot, bezKnot, htu, hu0, hu1, ht0.le, ht1.le,
          ht_le, boehm2] at *
    field_simp [ne_of_gt ht0]
    ring

def insertAlpha (U : ℕ → ℝ) (k : ℕ) (u : ℝ) (i p : ℕ) : ℝ :=
  if p ≤ k ∧ i ≤ k - p then 0
  else if i ≤ k then (U (i + p) - u) / (U (i + p) - U i)
  else 1

structure KnotData (U : ℕ → ℝ) (k : ℕ) (u : ℝ) where
  hbelow : ∀ j, j ≤ k → U j < u
  habove : ∀ j, k + 1 ≤ j → u < U j
  hden : ∀ i p, 0 < p → U (i + p) ≠ U i

lemma coeff1 (U : ℕ → ℝ) (k : ℕ) (u x : ℝ) (D : KnotData U k u) (p i : ℕ) :
    ((x - U i) / (U (i + p + 1) - U i)) * (1 - insertAlpha U k u i p) =
      (1 - insertAlpha U k u i (p+1)) *
        ((x - insertKnot U k u i) / (insertKnot U k u (i + p + 1) - insertKnot U k u i)) := by
  have hdpos : ∀ (j q : ℕ), 0 < q → U (j + q) - U j ≠ 0 := by
    intro j q hq h; apply D.hden j q hq; linarith
  have hupos : ∀ j, u - U j ≠ 0 := by
    intro j h
    by_cases hj : j ≤ k
    · have := D.hbelow j hj; linarith
    · have hj' : k + 1 ≤ j := by omega
      have := D.habove j hj'; linarith
  unfold insertAlpha
  simp (disch := omega) [insertKnot]
  split_ifs <;> try omega
  all_goals
    have h1 : U (i + p + 1) - U i ≠ 0 := by
      have hh := hdpos i (p+1) (by omega)
      have heq : i + (p+1) = i+p+1 := by omega
      simpa [heq] using hh
    have hu' : -U i + u ≠ 0 := by intro h; apply hupos i; linarith
    have hu_neg : ∀ j, -U j + u ≠ 0 := by intro j h; apply hupos j; linarith
    have hUu : ∀ j, U j - u ≠ 0 := by intro j h; apply hupos j; linarith
    have hUn : ∀ j q, 0 < q → -U j + U (j+q) ≠ 0 := by
      intro j q hq h; apply hdpos j q hq; linarith
    have ha : U (2+i+p) - U (1+i) ≠ 0 := by
      have heq : (1+i) + (p+1) = 2+i+p := by omega
      rw [← heq]
      exact hdpos (1+i) (p+1) (by omega)
    have hc : -U (1+i) + U (2+i+p) ≠ 0 := by intro h; apply ha; linarith
    field_simp [h1, hu', ha, hc, hdpos, hupos, hu_neg, hUu, hUn, Nat.add_assoc] <;> ring_nf <;> try
      (have hp_pos : 0 < p := by omega
       have h0 : U (i+p) - U i ≠ 0 := hdpos i p hp_pos
       have h0' : -U i + U (i+p) ≠ 0 := by intro h; apply h0; linarith
       have hd : U (1+i+p) - U (1+i) ≠ 0 := by
         have heq : (1+i) + p = 1+i+p := by omega
         rw [← heq]
         exact hdpos (1+i) p hp_pos
       have hd' : -U (1+i) + U (1+i+p) ≠ 0 := by intro h; apply hd; linarith
       have hu1 : U (1+i+p) - u ≠ 0 := by
         by_cases hh : 1+i+p ≤ k
         · have := D.hbelow (1+i+p) hh; linarith
         · have hh' : k+1 ≤ 1+i+p := by omega
           have := D.habove (1+i+p) hh'; linarith
       field_simp [h0, h0', hd, hd', hu1, ha, hc] <;> ring)
    all_goals field_simp [ha, hc] <;> ring


/-- Coefficient identity (2). -/
lemma coeff2 (U : ℕ → ℝ) (k : ℕ) (u x : ℝ) (D : KnotData U k u) (p i : ℕ) :
    ((x - U i) / (U (i+p+1) - U i)) * insertAlpha U k u (i+1) p +
      ((U (i+p+2) - x) / (U (i+p+2) - U (i+1))) * (1 - insertAlpha U k u (i+1) p) =
    (1 - insertAlpha U k u i (p+1)) *
      ((insertKnot U k u (i+p+2) - x) / (insertKnot U k u (i+p+2) - insertKnot U k u (i+1))) +
      insertAlpha U k u (i+1) (p+1) *
      ((x - insertKnot U k u (i+1)) / (insertKnot U k u (i+p+2) - insertKnot U k u (i+1))) := by
  have hdpos : ∀ (j q : ℕ), 0 < q → U (j + q) - U j ≠ 0 := by
    intro j q hq h; apply D.hden j q hq; linarith
  have hupos : ∀ j, u - U j ≠ 0 := by
    intro j h
    by_cases hj : j ≤ k
    · have := D.hbelow j hj; linarith
    · have hj' : k + 1 ≤ j := by omega
      have := D.habove j hj'; linarith
  unfold insertAlpha
  simp (disch := omega) [insertKnot]
  split_ifs <;> try omega
  all_goals
    have h1 : U (i + p + 1) - U i ≠ 0 := by
      have hh := hdpos i (p+1) (by omega)
      have heq : i + (p+1) = i+p+1 := by omega
      simpa [heq] using hh
    have hu' : -U i + u ≠ 0 := by intro h; apply hupos i; linarith
    have hu_neg : ∀ j, -U j + u ≠ 0 := by intro j h; apply hupos j; linarith
    have hUu : ∀ j, U j - u ≠ 0 := by intro j h; apply hupos j; linarith
    have hUn : ∀ j q, 0 < q → -U j + U (j+q) ≠ 0 := by
      intro j q hq h; apply hdpos j q hq; linarith
    have ha : U (2+i+p) - U (1+i) ≠ 0 := by
      have heq : (1+i) + (p+1) = 2+i+p := by omega
      rw [← heq]
      exact hdpos (1+i) (p+1) (by omega)
    have hc : -U (1+i) + U (2+i+p) ≠ 0 := by intro h; apply ha; linarith
    field_simp [h1, hu', ha, hc, hdpos, hupos, hu_neg, hUu, hUn, Nat.add_assoc] <;> ring_nf <;> try
      (have hp_pos : 0 < p := by omega
       have h0 : U (i+p) - U i ≠ 0 := hdpos i p hp_pos
       have h0' : -U i + U (i+p) ≠ 0 := by intro h; apply h0; linarith
       have hd : U (1+i+p) - U (1+i) ≠ 0 := by
         have heq : (1+i) + p = 1+i+p := by omega
         rw [← heq]
         exact hdpos (1+i) p hp_pos
       have hd' : -U (1+i) + U (1+i+p) ≠ 0 := by intro h; apply hd; linarith
       have hu1 : U (1+i+p) - u ≠ 0 := by
         by_cases hh : 1+i+p ≤ k
         · have := D.hbelow (1+i+p) hh; linarith
         · have hh' : k+1 ≤ 1+i+p := by omega
           have := D.habove (1+i+p) hh'; linarith
       field_simp [h0, h0', hd, hd', hu1, ha, hc] <;> ring)
    all_goals field_simp [ha, hc] <;> ring


/-- Coefficient identity (3). -/
lemma coeff3 (U : ℕ → ℝ) (k : ℕ) (u x : ℝ) (D : KnotData U k u) (p i : ℕ) :
    ((U (i+p+2) - x) / (U (i+p+2) - U (i+1))) * insertAlpha U k u (i+2) p =
      insertAlpha U k u (i+1) (p+1) *
      ((insertKnot U k u (i+p+3) - x) / (insertKnot U k u (i+p+3) - insertKnot U k u (i+2))) := by
  have hdpos : ∀ (j q : ℕ), 0 < q → U (j + q) - U j ≠ 0 := by
    intro j q hq h; apply D.hden j q hq; linarith
  have hupos : ∀ j, u - U j ≠ 0 := by
    intro j h
    by_cases hj : j ≤ k
    · have := D.hbelow j hj; linarith
    · have hj' : k + 1 ≤ j := by omega
      have := D.habove j hj'; linarith
  unfold insertAlpha
  simp (disch := omega) [insertKnot]
  split_ifs <;> try omega
  all_goals
    have h1 : U (i + p + 1) - U i ≠ 0 := by
      have hh := hdpos i (p+1) (by omega)
      have heq : i + (p+1) = i+p+1 := by omega
      simpa [heq] using hh
    have hu' : -U i + u ≠ 0 := by intro h; apply hupos i; linarith
    have hu_neg : ∀ j, -U j + u ≠ 0 := by intro j h; apply hupos j; linarith
    have hUu : ∀ j, U j - u ≠ 0 := by intro j h; apply hupos j; linarith
    have hUn : ∀ j q, 0 < q → -U j + U (j+q) ≠ 0 := by
      intro j q hq h; apply hdpos j q hq; linarith
    have ha : U (2+i+p) - U (1+i) ≠ 0 := by
      have heq : (1+i) + (p+1) = 2+i+p := by omega
      rw [← heq]
      exact hdpos (1+i) (p+1) (by omega)
    have hc : -U (1+i) + U (2+i+p) ≠ 0 := by intro h; apply ha; linarith
    field_simp [h1, hu', ha, hc, hdpos, hupos, hu_neg, hUu, hUn, Nat.add_assoc] <;> ring_nf <;> try
      (have hp_pos : 0 < p := by omega
       have h0 : U (i+p) - U i ≠ 0 := hdpos i p hp_pos
       have h0' : -U i + U (i+p) ≠ 0 := by intro h; apply h0; linarith
       have hd : U (1+i+p) - U (1+i) ≠ 0 := by
         have heq : (1+i) + p = 1+i+p := by omega
         rw [← heq]
         exact hdpos (1+i) p hp_pos
       have hd' : -U (1+i) + U (1+i+p) ≠ 0 := by intro h; apply hd; linarith
       have hu1 : U (1+i+p) - u ≠ 0 := by
         by_cases hh : 1+i+p ≤ k
         · have := D.hbelow (1+i+p) hh; linarith
         · have hh' : k+1 ≤ 1+i+p := by omega
           have := D.habove (1+i+p) hh'; linarith
       field_simp [h0, h0', hd, hd', hu1, ha, hc] <;> ring)
    all_goals field_simp [ha, hc] <;> ring

/-- **General Cox–de Boor refinement.** Inserting a knot `u` strictly inside
    span `k` refines every degree-p basis function:
    N_i^p = (1-α_i^p) N'^p_i + α_{i+1}^p N'^p_{i+1}. -/
theorem bsplineBasis_refine (U : ℕ → ℝ) (k : ℕ) (u x : ℝ)
    (D : KnotData U k u) (p : ℕ) :
    ∀ i, bsplineBasis U i p x =
      (1 - insertAlpha U k u i p) * bsplineBasis (insertKnot U k u) i p x +
      insertAlpha U k u (i+1) p * bsplineBasis (insertKnot U k u) (i+1) p x := by
  induction p with
  | zero =>
      intro i
      have hr := bsplineBasis_zero_refinement U k u x (le_of_lt (D.hbelow k le_rfl)) (D.habove (k+1) le_rfl)
      unfold insertAlpha
      by_cases hik : i ≤ k
      · by_cases hlt : i < k
        · have hi1 : i + 1 ≤ k := by omega
          simp [hik, hi1]
          exact (hr.1 i hlt).symm
        · have hik_eq : i = k := by omega
          subst i
          have hk1 : ¬ k + 1 ≤ k := by omega
          simp [hk1]
          exact hr.2.1
      · have hi1 : ¬ i + 1 ≤ k := by omega
        simp [hik, hi1]
        exact hr.2.2 i (by omega : k < i)
  | succ p ih =>
      intro i
      simp only [bsplineBasis]
      rw [ih i, ih (i+1)]
      have h1 := coeff1 U k u x D p i
      have h2 := coeff2 U k u x D p i
      have h3 := coeff3 U k u x D p i
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h1 h2 h3 ⊢
      -- let the three new-basis terms be atoms and use the coefficient identities
      linear_combination h1 * bsplineBasis (insertKnot U k u) i p x +
        h2 * bsplineBasis (insertKnot U k u) (i+1) p x +
        h3 * bsplineBasis (insertKnot U k u) (i+2) p x


/-- Boehm control points for inserting knot `u` at span `k`, degree `p`. -/
def boehmControl (U : ℕ → ℝ) (k : ℕ) (u : ℝ) (p : ℕ) (P : ℕ → Vec3) (j : ℕ) : Vec3 :=
  (1 - insertAlpha U k u j p) • P j + insertAlpha U k u j p • P (j - 1)

/-- **General Boehm knot insertion preserves the curve.** -/
theorem boehm_preserves (U : ℕ → ℝ) (k : ℕ) (u : ℝ) (D : KnotData U k u)
    (p n : ℕ) (hpk : p ≤ k) (hn : k ≤ n) (P : ℕ → Vec3) :
    bsplineCurve (insertKnot U k u) (boehmControl U k u p P) p (n+1) u =
      bsplineCurve U P p n u := by
  unfold bsplineCurve boehmControl
  simp_rw [bsplineBasis_refine U k u u D p]
  -- RHS is now sum of ((1-α_i)N'_i + α_{i+1}N'_{i+1}) • P_i
  -- rewrite smul_add and sum_add_distrib
  simp_rw [add_smul, Finset.sum_add_distrib]
  -- first sum: Σ (1-α_i) • N'_i • P_i ; second: Σ α_{i+1} • N'_{i+1} • P_i
  -- LHS is Σ_{j=0}^{n+1} N'_j • ((1-α_j)•P_j + α_j•P_{j-1})
  rw [Finset.sum_range_succ]
  simp only [smul_add, Finset.sum_add_distrib]
  have h0 : insertAlpha U k u 0 p = 0 := by
    unfold insertAlpha
    have hkp : 0 ≤ k - p := by omega
    simp [hpk, hkp]
  have hlast : insertAlpha U k u (n+1) p = 1 := by
    unfold insertAlpha
    have hklt : ¬ n + 1 ≤ k := by omega
    have hpk' : ¬ (p ≤ k ∧ n + 1 ≤ k - p) := by
      intro h; omega
    have hknp : k ≤ n + p := by omega
    simp [hpk', hklt, hknp]
  have hshift :
      (∑ x ∈ Finset.range (n+1), bsplineBasis (insertKnot U k u) x p u •
          insertAlpha U k u x p • P (x-1)) =
        ∑ x ∈ Finset.range n, bsplineBasis (insertKnot U k u) (x+1) p u •
          insertAlpha U k u (x+1) p • P x := by
    rw [Finset.sum_range_succ']
    simp [h0]
  rw [hshift]
  simp [h0, hlast]
  simp only [Finset.sum_range_succ]
  simp [hlast, smul_smul, mul_comm]
  module


end
end LightRT.Geom
