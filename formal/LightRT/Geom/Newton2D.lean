/-
  The two-dimensional Newton step with a quadratic contraction bound.

  `tri_bez_newton` solves the coupled `(u, t)` system

    F(u, t) = ( f(u, t), g(u, t) ) = ( ⟨R, C′⟩ + r·r′,  |R| − r ) = 0,

  where `R = o + t·d − C(u)`. Near a simple root (nonzero Jacobian determinant)
  one Newton step squares the error, and this file proves that core for a
  general smooth `F : ℝ² → ℝ²`, by expanding along one axis with the 1D mean
  value theorem twice and the other axis once:

    F(x) − F(x*) = J(x*)·e + R(e),      |R_i| ≤ 3K‖e‖₁²
    J(x)  = J(x*) + Δ,                  |Δ_ij| ≤ K‖e‖₁

  `x′ = x − J(x)⁻¹ F(x)` then satisfies `‖x′ − x*‖∞ ≤ C ‖e‖₁²` with
  `C = (12 B K̄ + 8 K̄²‖e‖₁)/δ` (`e` the error before the step,
  `δ ≤ |det J(x)|`, `B` a bound on `J`'s entries at `x`, `K` the
  second-derivative bound, `K̄ = max K_f K_g`).

  Smoothness is phrased constructively: `pd*` are plain `deriv` partial
  derivatives and `C2Seg` bundles the single-variable differentiability
  hypotheses and the second-derivative bound on the closed segments containing
  the iterate and the root. The hypotheses hold trivially for the polynomial
  Bézier evaluates, and the determinant side condition is exactly the C's own
  acceptance guard.
-/
import Mathlib
import LightRT.Geom.Basic

namespace LightRT.Geom

/-- First partial derivative `∂f/∂u`. -/
noncomputable def pd1 (f : ℝ → ℝ → ℝ) (u t : ℝ) : ℝ := deriv (fun s => f s t) u
/-- First partial derivative `∂f/∂t`. -/
noncomputable def pd2 (f : ℝ → ℝ → ℝ) (u t : ℝ) : ℝ := deriv (fun s => f u s) t
/-- Second partials. -/
noncomputable def pdd11 (f : ℝ → ℝ → ℝ) (u t : ℝ) : ℝ := deriv (fun s => pd1 f s t) u
noncomputable def pdd12 (f : ℝ → ℝ → ℝ) (u t : ℝ) : ℝ := deriv (fun s => pd1 f u s) t
noncomputable def pdd21 (f : ℝ → ℝ → ℝ) (u t : ℝ) : ℝ := deriv (fun s => pd2 f s t) u
noncomputable def pdd22 (f : ℝ → ℝ → ℝ) (u t : ℝ) : ℝ := deriv (fun s => pd2 f u s) t

/-- The Jacobian determinant of `(f, g)` at `(u, t)`. -/
noncomputable def jacDet (f g : ℝ → ℝ → ℝ) (u t : ℝ) : ℝ :=
  pd1 f u t * pd2 g u t - pd2 f u t * pd1 g u t

/-- Second smoothness bundle on a closed segment: everything the
    one-dimensional mean value theorem needs, plus uniform second-derivative
    bounds. -/
structure C2Seg (f : ℝ → ℝ → ℝ) (a b c d K : ℝ) : Prop where
  row  : ∀ t ∈ Set.Icc c d, DifferentiableOn ℝ (fun s => f s t) (Set.Icc a b)
  col  : ∀ u ∈ Set.Icc a b, DifferentiableOn ℝ (fun s => f u s) (Set.Icc c d)
  row₁ : ∀ t ∈ Set.Icc c d, DifferentiableOn ℝ (fun s => pd1 f s t) (Set.Icc a b)
  col₁ : ∀ u ∈ Set.Icc a b, DifferentiableOn ℝ (fun s => pd1 f u s) (Set.Icc c d)
  row₂ : ∀ t ∈ Set.Icc c d, DifferentiableOn ℝ (fun s => pd2 f s t) (Set.Icc a b)
  col₂ : ∀ u ∈ Set.Icc a b, DifferentiableOn ℝ (fun s => pd2 f u s) (Set.Icc c d)
  b₁₁  : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd11 f u t| ≤ K
  b₁₂  : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd12 f u t| ≤ K
  b₂₁  : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd21 f u t| ≤ K
  b₂₂  : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd22 f u t| ≤ K

/-- 1D mean value theorem on the closed segment between two points. -/
theorem mvt {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hf : DifferentiableOn ℝ φ (Set.Icc (min a b) (max a b))) :
    ∃ ξ ∈ Set.Ioo (min a b) (max a b),
      deriv φ ξ = (φ b - φ a) / (b - a) := by
  have hab' : min a b < max a b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
      rcases lt_or_eq_of_le h with hlt | rfl
      · exact hlt
      · exact absurd rfl hab
    · rw [min_eq_right h, max_eq_left h]
      rcases lt_or_eq_of_le h with hlt | rfl
      · exact hlt
      · exact absurd rfl (Ne.symm hab)
  obtain ⟨ξ, hξ, hMVT⟩ := exists_deriv_eq_slope φ hab' hf.continuousOn
    (hf.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h] at hMVT
    exact ⟨ξ, hξ, hMVT⟩
  · rw [min_eq_right h, max_eq_left h] at hMVT
    refine ⟨ξ, hξ, ?_⟩
    rw [hMVT]
    field_simp
    ring

/-- Membership transfer: a point of the open interval `(a, b)` lies in the
    closed interval, given both endpoints do. -/
theorem ioo_mem_seg {a b c d x : ℝ} (ha : a ∈ Set.Icc c d) (hb : b ∈ Set.Icc c d)
    (hx : x ∈ Set.Ioo (min a b) (max a b)) : x ∈ Set.Icc c d := by
  rcases le_total a b with h | h
  · simp [min_eq_left h, max_eq_right h] at hx
    exact ⟨ha.1.trans (le_of_lt hx.1), (le_of_lt hx.2).trans hb.2⟩
  · simp [min_eq_right h, max_eq_left h] at hx
    exact ⟨hb.1.trans (le_of_lt hx.1), (le_of_lt hx.2).trans ha.2⟩

/-- A point of the open `(u₀, u)` differs from either endpoint by at most
    `|u - u₀|`. -/
theorem ioo_u_dist_le {u₀ u x : ℝ} (hx : x ∈ Set.Ioo (min u u₀) (max u u₀)) :
    |x - u₀| ≤ |u - u₀| ∧ |x - u| ≤ |u - u₀| := by
  rcases le_total u u₀ with h | h
  · simp [min_eq_left h, max_eq_right h] at hx
    have h1 : |x - u₀| = -(x - u₀) := abs_of_nonpos (by linarith [hx.2])
    have h2 : |u - u₀| = -(u - u₀) := abs_of_nonpos (by linarith)
    have h3 : |x - u| = x - u := abs_of_nonneg (by linarith [hx.1])
    constructor <;> linarith
  · simp [min_eq_right h, max_eq_left h] at hx
    have h1 : |x - u₀| = x - u₀ := abs_of_nonneg (by linarith [hx.1])
    have h2 : |u - u₀| = u - u₀ := abs_of_nonneg (by linarith)
    have h3 : |x - u| = -(x - u) := abs_of_nonpos (by linarith [hx.2])
    constructor <;> linarith

/-- Same for the `t` axis. -/
theorem ioo_t_dist_le {t₀ t x : ℝ} (hx : x ∈ Set.Ioo (min t t₀) (max t t₀)) :
    |x - t₀| ≤ |t - t₀| ∧ |x - t| ≤ |t - t₀| := by
  rcases le_total t t₀ with h | h
  · simp [min_eq_left h, max_eq_right h] at hx
    have h1 : |x - t₀| = -(x - t₀) := abs_of_nonpos (by linarith [hx.2])
    have h2 : |t - t₀| = -(t - t₀) := abs_of_nonpos (by linarith)
    have h3 : |x - t| = x - t := abs_of_nonneg (by linarith [hx.1])
    constructor <;> linarith
  · simp [min_eq_right h, max_eq_left h] at hx
    have h1 : |x - t₀| = x - t₀ := abs_of_nonneg (by linarith [hx.1])
    have h2 : |t - t₀| = t - t₀ := abs_of_nonneg (by linarith)
    have h3 : |x - t| = -(x - t) := abs_of_nonpos (by linarith [hx.2])
    constructor <;> linarith

/-- The residual of the first-order expansion of one component. -/
noncomputable def residual (f : ℝ → ℝ → ℝ) (u₀ t₀ : ℝ) (u t : ℝ) : ℝ :=
  f u t - f u₀ t₀ - pd1 f u₀ t₀ * (u - u₀) - pd2 f u₀ t₀ * (t - t₀)

theorem ne_sub_self {a b : ℝ} (h : a ≠ b) : a - b ≠ 0 := by
  intro e
  apply h
  linarith [e]

theorem abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa using abs_sub_le a 0 b

theorem residual_decomp (f : ℝ → ℝ → ℝ) (u₀ t₀ u t : ℝ) :
    residual f u₀ t₀ u t =
      (f u t - f u₀ t) + (f u₀ t - f u₀ t₀) -
        pd1 f u₀ t₀ * (u - u₀) - pd2 f u₀ t₀ * (t - t₀) := by
  unfold residual; ring

/-- The column (`t`) difference of `f` expands as a derivative times `dt`. -/
theorem col_diff (f : ℝ → ℝ → ℝ) {u₀ t₀ t : ℝ} (hf : DifferentiableOn ℝ (fun s => f u₀ s)
    (Set.Icc (min t t₀) (max t t₀))) (ht0 : t ≠ t₀) :
    ∃ ζ₁ ∈ Set.Ioo (min t t₀) (max t t₀),
      pd2 f u₀ ζ₁ = (f u₀ t - f u₀ t₀) / (t - t₀) := by
  obtain ⟨ζ₁, hζ₁, h⟩ := mvt (φ := fun s => f u₀ s) (a := t) (b := t₀) ht0 hf
  exact ⟨ζ₁, hζ₁, by
    rw [show pd2 f u₀ ζ₁ = deriv (fun s => f u₀ s) ζ₁ from rfl, h,
        show f u₀ t₀ - f u₀ t = -(f u₀ t - f u₀ t₀) by ring,
        show t₀ - t = -(t - t₀) by ring, neg_div_neg_eq]⟩

/-- The derivative column difference expands as a second derivative times `dt`. -/
theorem col_diff₂ (f : ℝ → ℝ → ℝ) {u₀ t₀ t : ℝ} (hf : DifferentiableOn ℝ (fun s => pd2 f u₀ s)
    (Set.Icc (min t t₀) (max t t₀))) (ht0 : t ≠ t₀) :
    ∃ η₂ ∈ Set.Ioo (min t t₀) (max t t₀),
      pdd22 f u₀ η₂ = (pd2 f u₀ t - pd2 f u₀ t₀) / (t - t₀) := by
  obtain ⟨η₂, hη₂, h⟩ := mvt (φ := fun s => pd2 f u₀ s) (a := t) (b := t₀) ht0 hf
  exact ⟨η₂, hη₂, by
    rw [show pdd22 f u₀ η₂ = deriv (fun s => pd2 f u₀ s) η₂ from rfl, h,
        show pd2 f u₀ t₀ - pd2 f u₀ t = -(pd2 f u₀ t - pd2 f u₀ t₀) by ring,
        show t₀ - t = -(t - t₀) by ring, neg_div_neg_eq]⟩

theorem row_diff (f : ℝ → ℝ → ℝ) {u₀ t u : ℝ} (hf : DifferentiableOn ℝ (fun s => f s t)
    (Set.Icc (min u u₀) (max u u₀))) (hu0 : u ≠ u₀) :
    ∃ ξ₁ ∈ Set.Ioo (min u u₀) (max u u₀),
      pd1 f ξ₁ t = (f u t - f u₀ t) / (u - u₀) := by
  obtain ⟨ξ₁, hξ₁, h⟩ := mvt (φ := fun s => f s t) (a := u) (b := u₀) hu0 hf
  exact ⟨ξ₁, hξ₁, by
    rw [show pd1 f ξ₁ t = deriv (fun s => f s t) ξ₁ from rfl, h,
        show f u₀ t - f u t = -(f u t - f u₀ t) by ring,
        show u₀ - u = -(u - u₀) by ring, neg_div_neg_eq]⟩

theorem row_diff₁ (f : ℝ → ℝ → ℝ) {u₀ t₀ u : ℝ} (hf : DifferentiableOn ℝ (fun s => pd1 f s t₀)
    (Set.Icc (min u u₀) (max u u₀))) (hu0 : u ≠ u₀) :
    ∃ ξ₂ ∈ Set.Ioo (min u u₀) (max u u₀),
      pdd11 f ξ₂ t₀ = (pd1 f u t₀ - pd1 f u₀ t₀) / (u - u₀) := by
  obtain ⟨ξ₂, hξ₂, h⟩ := mvt (φ := fun s => pd1 f s t₀) (a := u) (b := u₀) hu0 hf
  exact ⟨ξ₂, hξ₂, by
    rw [show pdd11 f ξ₂ t₀ = deriv (fun s => pd1 f s t₀) ξ₂ from rfl, h,
        show pd1 f u₀ t₀ - pd1 f u t₀ = -(pd1 f u t₀ - pd1 f u₀ t₀) by ring,
        show u₀ - u = -(u - u₀) by ring, neg_div_neg_eq]⟩

theorem col_diff₁ (f : ℝ → ℝ → ℝ) {u₀ t₀ t : ℝ} (hf : DifferentiableOn ℝ (fun s => pd1 f u₀ s)
    (Set.Icc (min t t₀) (max t t₀))) (ht0 : t ≠ t₀) :
    ∃ η₁ ∈ Set.Ioo (min t t₀) (max t t₀),
      pdd12 f u₀ η₁ = (pd1 f u₀ t - pd1 f u₀ t₀) / (t - t₀) := by
  obtain ⟨η₁, hη₁, h⟩ := mvt (φ := fun s => pd1 f u₀ s) (a := t) (b := t₀) ht0 hf
  exact ⟨η₁, hη₁, by
    rw [show pdd12 f u₀ η₁ = deriv (fun s => pd1 f u₀ s) η₁ from rfl, h,
        show pd1 f u₀ t₀ - pd1 f u₀ t = -(pd1 f u₀ t - pd1 f u₀ t₀) by ring,
        show t₀ - t = -(t - t₀) by ring, neg_div_neg_eq]⟩

theorem row_diff₂ (f : ℝ → ℝ → ℝ) {u₀ t u : ℝ} (hf : DifferentiableOn ℝ (fun s => pd2 f s t)
    (Set.Icc (min u u₀) (max u u₀))) (hu0 : u ≠ u₀) :
    ∃ ξ₃ ∈ Set.Ioo (min u u₀) (max u u₀),
      pdd21 f ξ₃ t = (pd2 f u t - pd2 f u₀ t) / (u - u₀) := by
  obtain ⟨ξ₃, hξ₃, h⟩ := mvt (φ := fun s => pd2 f s t) (a := u) (b := u₀) hu0 hf
  exact ⟨ξ₃, hξ₃, by
    rw [show pdd21 f ξ₃ t = deriv (fun s => pd2 f s t) ξ₃ from rfl, h,
        show pd2 f u₀ t - pd2 f u t = -(pd2 f u t - pd2 f u₀ t) by ring,
        show u₀ - u = -(u - u₀) by ring, neg_div_neg_eq]⟩


/-- Sub-rectangle membership: the open `(u₀, u)` is inside `Set.Icc a b` when
    both endpoints are. -/
theorem Ioo_subset (a b u u₀ : ℝ) (hu : u ∈ Set.Icc a b) (hu₀ : u₀ ∈ Set.Icc a b) :
    Set.Icc (min u u₀) (max u u₀) ⊆ Set.Icc a b := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  have h3 : min u u₀ ≥ a := by
    rcases le_total u u₀ with h | h
    · rw [min_eq_left h]; exact hu.1
    · rw [min_eq_right h]; exact hu₀.1
  have h4 : max u u₀ ≤ b := by
    rcases le_total u u₀ with h | h
    · rw [max_eq_right h]; exact hu₀.2
    · rw [max_eq_left h]; exact hu.2
  exact ⟨le_trans h3 h1, le_trans h2 h4⟩

theorem Ioo_subset_t (c d t t₀ : ℝ) (ht : t ∈ Set.Icc c d) (ht₀ : t₀ ∈ Set.Icc c d) :
    Set.Icc (min t t₀) (max t t₀) ⊆ Set.Icc c d := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  have h3 : min t t₀ ≥ c := by
    rcases le_total t t₀ with h | h
    · rw [min_eq_left h]; exact ht.1
    · rw [min_eq_right h]; exact ht₀.1
  have h4 : max t t₀ ≤ d := by
    rcases le_total t t₀ with h | h
    · rw [max_eq_right h]; exact ht₀.2
    · rw [max_eq_left h]; exact ht.2
  exact ⟨le_trans h3 h1, le_trans h2 h4⟩

/-- Sub-rectangle membership: the closed `(u₀, u)` segment is inside the big
    segment because both endpoints are. -/
theorem SetIoo_subset {a b u u₀ : ℝ} (hu : u ∈ Set.Icc a b) (hu₀ : u₀ ∈ Set.Icc a b) :
    Set.Icc (min u u₀) (max u u₀) ⊆ Set.Icc a b := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  have h3 : min u u₀ ≥ a := by
    rcases le_total u u₀ with h | h
    · rw [min_eq_left h]; exact hu.1
    · rw [min_eq_right h]; exact hu₀.1
  have h4 : max u u₀ ≤ b := by
    rcases le_total u u₀ with h | h
    · rw [max_eq_right h]; exact hu₀.2
    · rw [max_eq_left h]; exact hu.2
  exact ⟨le_trans h3 h1, le_trans h2 h4⟩

/-- The same for the `t` axis. -/
theorem SetIoo_subset_t {c d t t₀ : ℝ} (ht : t ∈ Set.Icc c d) (ht₀ : t₀ ∈ Set.Icc c d) :
    Set.Icc (min t t₀) (max t t₀) ⊆ Set.Icc c d := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  have h3 : min t t₀ ≥ c := by
    rcases le_total t t₀ with h | h
    · rw [min_eq_left h]; exact ht.1
    · rw [min_eq_right h]; exact ht₀.1
  have h4 : max t t₀ ≤ d := by
    rcases le_total t t₀ with h | h
    · rw [max_eq_right h]; exact ht₀.2
    · rw [max_eq_left h]; exact ht.2
  exact ⟨le_trans h3 h1, le_trans h2 h4⟩

set_option maxHeartbeats 1600000 in
/-- **Second-order expansion of one component.** On a segment containing both
    points, `|R| ≤ 3K‖e‖₁²` with `e‖₁ = |du| + |dt|`. -/
theorem residual_bound {f : ℝ → ℝ → ℝ} {a b c d K : ℝ}
    (hf : C2Seg f a b c d K) (hK : 0 ≤ K) {u₀ t₀ u t : ℝ}
    (hu : u ∈ Set.Icc a b) (hu₀ : u₀ ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc c d) (ht₀ : t₀ ∈ Set.Icc c d) :
    |residual f u₀ t₀ u t| ≤ 3 * K * ((|u - u₀| + |t - t₀|) ^ 2) := by
  set du := u - u₀ with hdu
  set dt := t - t₀ with hdt
  set E := |du| + |dt| with hE
  have hE0 : 0 ≤ E := by
    have h := hE
    rw [h]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hle : |du| ≤ E ∧ |dt| ≤ E := by
    have h := hE
    rw [h]
    constructor <;> linarith [abs_nonneg du, abs_nonneg dt]
  by_cases hu0 : u = u₀
  · have hdu0 : du = 0 := by rw [hdu, hu0, sub_self]
    by_cases ht0 : t = t₀
    · have hdt0 : dt = 0 := by rw [hdt, ht0, sub_self]
      have hE' : E = 0 := by
        rw [hE, hdu0, hdt0, abs_zero, add_zero]
      have hres : residual f u₀ t₀ u t = 0 := by
        unfold residual
        rw [hu0, ht0]
        ring
      rw [hres]
      simp
      positivity
    · -- u = u₀: residual is a single pd2 term
      have hsub : Set.Icc (min t t₀) (max t t₀) ⊆ Set.Icc c d :=
        SetIoo_subset_t ht ht₀
      have hfcol : DifferentiableOn ℝ (fun s => f u₀ s) (Set.Icc (min t t₀) (max t t₀)) :=
        (hf.col u₀ hu₀).mono hsub
      obtain ⟨ζ₁, hζ₁, h⟩ := col_diff f hfcol ht0
      have hζ₁' : ζ₁ ∈ Set.Icc c d := ioo_mem_seg ht ht₀ hζ₁
      have hc : f u₀ t - f u₀ t₀ = pd2 f u₀ ζ₁ * (t - t₀) := by
        rw [h]
        exact (div_mul_cancel₀ (f u₀ t - f u₀ t₀) (ne_sub_self ht0)).symm
      have hsub2 : Set.Icc (min ζ₁ t₀) (max ζ₁ t₀) ⊆ Set.Icc c d :=
        SetIoo_subset_t hζ₁' ht₀
      have hfcol₂ : DifferentiableOn ℝ (fun s => pd2 f u₀ s)
          (Set.Icc (min ζ₁ t₀) (max ζ₁ t₀)) := (hf.col₂ u₀ hu₀).mono hsub2
      have hζ₀ : ζ₁ ≠ t₀ := by
        intro h; rw [h] at hζ₁
        rcases le_total t t₀ with h | h
        · simp [min_eq_left h, max_eq_right h] at hζ₁
        · simp [min_eq_right h, max_eq_left h] at hζ₁
      obtain ⟨η₂, hη₂, h₂⟩ := col_diff₂ f hfcol₂ hζ₀
      have hc2 : pd2 f u₀ ζ₁ - pd2 f u₀ t₀ = pdd22 f u₀ η₂ * (ζ₁ - t₀) := by
        rw [h₂]
        exact (div_mul_cancel₀ (pd2 f u₀ ζ₁ - pd2 f u₀ t₀) (ne_sub_self hζ₀)).symm
      have hres : residual f u₀ t₀ u t = (pd2 f u₀ ζ₁ - pd2 f u₀ t₀) * (t - t₀) := by
        unfold residual
        rw [hu0]
        rw [show f u₀ t - f u₀ t₀ = pd2 f u₀ ζ₁ * (t - t₀) from hc]
        ring
      calc |residual f u₀ t₀ u t|
          = |(pd2 f u₀ ζ₁ - pd2 f u₀ t₀) * (t - t₀)| := by rw [hres]
        _ = |pd2 f u₀ ζ₁ - pd2 f u₀ t₀| * |t - t₀| := abs_mul _ _
        _ = |pdd22 f u₀ η₂| * |ζ₁ - t₀| * |t - t₀| := by rw [hc2, abs_mul]
        _ ≤ K * |t - t₀| * |t - t₀| := by
            have hζ : |ζ₁ - t₀| ≤ |t - t₀| := (ioo_t_dist_le hζ₁).1
            have hη₂' : η₂ ∈ Set.Icc c d := ioo_mem_seg hζ₁' ht₀ hη₂
            have hK' := hf.b₂₂ u₀ hu₀ η₂ hη₂'
            have h2 := mul_le_mul hK' hζ (abs_nonneg _) hK
            nlinarith [h2, abs_nonneg (t - t₀)]
        _ = K * |t - t₀| ^ 2 := by ring
        _ ≤ 3 * K * E ^ 2 := by
            have hE' : E = |t - t₀| := by
              calc E = |du| + |dt| := hE
                _ = |dt| := by rw [hdu0]; simp
                _ = |t - t₀| := by rw [hdt]
            rw [hE']
            nlinarith [hK, abs_nonneg (t - t₀)]
  · by_cases ht0 : t = t₀
    · have hdt0 : dt = 0 := by rw [hdt, ht0, sub_self]
      have hsub : Set.Icc (min u u₀) (max u u₀) ⊆ Set.Icc a b :=
        SetIoo_subset hu hu₀
      have hfrow : DifferentiableOn ℝ (fun s => f s t₀) (Set.Icc (min u u₀) (max u u₀)) :=
        (hf.row t₀ ht₀).mono hsub
      obtain ⟨ξ₁, hξ₁, h⟩ := row_diff f hfrow hu0
      have hξ₁' : ξ₁ ∈ Set.Icc a b := ioo_mem_seg hu hu₀ hξ₁
      have hc : f u t₀ - f u₀ t₀ = pd1 f ξ₁ t₀ * du := by
        rw [h]
        exact (div_mul_cancel₀ (f u t₀ - f u₀ t₀) (ne_sub_self hu0)).symm
      have hsub2 : Set.Icc (min ξ₁ u₀) (max ξ₁ u₀) ⊆ Set.Icc a b := by
        intro x hx; exact SetIoo_subset hξ₁' hu₀ hx
      have hfrow₁ : DifferentiableOn ℝ (fun s => pd1 f s t₀)
          (Set.Icc (min ξ₁ u₀) (max ξ₁ u₀)) := (hf.row₁ t₀ ht₀).mono hsub2
      have h₁₀ : ξ₁ ≠ u₀ := by
        intro h; rw [h] at hξ₁
        rcases le_total u u₀ with h | h
        · simp [min_eq_left h, max_eq_right h] at hξ₁

        · simp [min_eq_right h, max_eq_left h] at hξ₁

      obtain ⟨ξ₂, hξ₂, h₂⟩ := row_diff₁ f hfrow₁ h₁₀
      have hc2 : pd1 f ξ₁ t₀ - pd1 f u₀ t₀ = pdd11 f ξ₂ t₀ * (ξ₁ - u₀) := by
        rw [h₂]
        exact (div_mul_cancel₀ (pd1 f ξ₁ t₀ - pd1 f u₀ t₀) (ne_sub_self h₁₀)).symm
      have hdt0 : dt = 0 := by
        rw [hdt, ht0]
        ring
      have hres : residual f u₀ t₀ u t = (pd1 f ξ₁ t₀ - pd1 f u₀ t₀) * du := by
        unfold residual
        rw [ht0]
        rw [show f u t₀ - f u₀ t₀ = pd1 f ξ₁ t₀ * du from hc]
        ring
      calc |residual f u₀ t₀ u t|
          = |(pd1 f ξ₁ t₀ - pd1 f u₀ t₀) * du| := by rw [hres]
        _ = |pd1 f ξ₁ t₀ - pd1 f u₀ t₀| * |du| := abs_mul _ _
        _ = |pdd11 f ξ₂ t₀| * |ξ₁ - u₀| * |du| := by rw [hc2, abs_mul]
        _ ≤ K * |du| * |du| := by
            have hξ := (ioo_u_dist_le hξ₁).1
            have hK' := hf.b₁₁ ξ₂ (ioo_mem_seg hξ₁' hu₀ hξ₂) t₀ ht₀
            have h2 := mul_le_mul hK' hξ (abs_nonneg _) hK
            nlinarith [h2, abs_nonneg (u - u₀), hE0, hK]
        _ = K * |du| ^ 2 := by ring
        _ ≤ 3 * K * E ^ 2 := by
            have hE' : E = |du| := by
              calc E = |du| + |dt| := hE
                _ = |du| := by rw [hdt0]; simp
            rw [hE']
            nlinarith [hK, abs_nonneg (u - u₀)]
    · -- both du, dt potentially nonzero
      have hsub : Set.Icc (min u u₀) (max u u₀) ⊆ Set.Icc a b := SetIoo_subset hu hu₀
      have hfrow : DifferentiableOn ℝ (fun s => f s t) (Set.Icc (min u u₀) (max u u₀)) :=
        (hf.row t ht).mono hsub
      obtain ⟨ξ₁, hξ₁, h₁⟩ := row_diff f hfrow hu0
      have hξ₁' : ξ₁ ∈ Set.Icc a b := ioo_mem_seg hu hu₀ hξ₁
      have hsub' : Set.Icc (min t t₀) (max t t₀) ⊆ Set.Icc c d := SetIoo_subset_t ht ht₀
      have hfrow' : DifferentiableOn ℝ (fun s => f u₀ s) (Set.Icc (min t t₀) (max t t₀)) :=
        (hf.col u₀ hu₀).mono hsub'
      obtain ⟨ζ₁, hζ₁, h₂⟩ := col_diff f hfrow' ht0
      have hζ₁' : ζ₁ ∈ Set.Icc c d := ioo_mem_seg ht ht₀ hζ₁
      have hc₁ : f u t - f u₀ t = pd1 f ξ₁ t * du := by
        rw [h₁]
        exact (div_mul_cancel₀ (f u t - f u₀ t) (ne_sub_self hu0)).symm
      have hc₂ : f u₀ t - f u₀ t₀ = pd2 f u₀ ζ₁ * dt := by
        rw [h₂]
        exact (div_mul_cancel₀ (f u₀ t - f u₀ t₀) (ne_sub_self ht0)).symm
      have hfcol₁ : DifferentiableOn ℝ (fun s => pd1 f ξ₁ s) (Set.Icc (min t t₀) (max t t₀)) :=
        (hf.col₁ ξ₁ hξ₁').mono hsub'
      obtain ⟨η₁, hη₁, h₃⟩ := col_diff₁ f hfcol₁ ht0
      have hc₃ : pd1 f ξ₁ t = pd1 f ξ₁ t₀ + pdd12 f ξ₁ η₁ * dt := by
        rw [h₃]
        field_simp
        ring
      have hsub2 : Set.Icc (min ζ₁ t₀) (max ζ₁ t₀) ⊆ Set.Icc c d := by
        intro x hx; exact SetIoo_subset_t hζ₁' ht₀ hx
      have hfcol₂ : DifferentiableOn ℝ (fun s => pd2 f u₀ s)
          (Set.Icc (min ζ₁ t₀) (max ζ₁ t₀)) := (hf.col₂ u₀ hu₀).mono hsub2
      have hζ₀ : ζ₁ ≠ t₀ := by
        intro h; rw [h] at hζ₁
        rcases le_total t t₀ with h | h
        · simp [min_eq_left h, max_eq_right h] at hζ₁

        · simp [min_eq_right h, max_eq_left h] at hζ₁

      obtain ⟨η₂, hη₂, h₄⟩ := col_diff₂ f hfcol₂ hζ₀
      have hc₄ : pd2 f u₀ ζ₁ = pd2 f u₀ t₀ + pdd22 f u₀ η₂ * (ζ₁ - t₀) := by
        rw [h₄]
        field_simp
        ring
      have hsub3 : Set.Icc (min ξ₁ u₀) (max ξ₁ u₀) ⊆ Set.Icc a b := by
        intro x hx; exact SetIoo_subset hξ₁' hu₀ hx
      have hfrow₁ : DifferentiableOn ℝ (fun s => pd1 f s t₀)
          (Set.Icc (min ξ₁ u₀) (max ξ₁ u₀)) := (hf.row₁ t₀ ht₀).mono hsub3
      have h₁₀ : ξ₁ ≠ u₀ := by
        intro h; rw [h] at hξ₁
        rcases le_total u u₀ with h | h
        · simp [min_eq_left h, max_eq_right h] at hξ₁

        · simp [min_eq_right h, max_eq_left h] at hξ₁

      obtain ⟨ξ₂, hξ₂, h₅⟩ := row_diff₁ f hfrow₁ h₁₀
      have hc₅ : pd1 f ξ₁ t₀ = pd1 f u₀ t₀ + pdd11 f ξ₂ t₀ * (ξ₁ - u₀) := by
        rw [h₅]
        field_simp
        ring
      have hres : residual f u₀ t₀ u t =
          pdd12 f ξ₁ η₁ * dt * du + pdd11 f ξ₂ t₀ * (ξ₁ - u₀) * du +
            pdd22 f u₀ η₂ * (ζ₁ - t₀) * dt := by
        rw [residual_decomp, hc₁, hc₂]
        rw [hc₃, hc₅, hc₄]
        ring
      have hξ : |ξ₁ - u₀| ≤ |du| := by
        have h := (ioo_u_dist_le hξ₁).1
        rw [← hdu] at h
        exact h
      have hζ : |ζ₁ - t₀| ≤ |dt| := by
        have h := (ioo_t_dist_le hζ₁).1
        rw [← hdt] at h
        exact h
      have hdu0 : 0 ≤ |du| := abs_nonneg _
      have hdt0 : 0 ≤ |dt| := abs_nonneg _
      have hb1 : |pdd12 f ξ₁ η₁| ≤ K := hf.b₁₂ ξ₁ hξ₁' η₁ (ioo_mem_seg ht ht₀ hη₁)
      have hb2 : |pdd11 f ξ₂ t₀| ≤ K := hf.b₁₁ ξ₂ (ioo_mem_seg hξ₁' hu₀ hξ₂) t₀ ht₀
      have hb3 : |pdd22 f u₀ η₂| ≤ K := hf.b₂₂ u₀ hu₀ η₂ (ioo_mem_seg hζ₁' ht₀ hη₂)
      have h1 : |pdd12 f ξ₁ η₁ * dt * du| ≤ K * E ^ 2 := by
        have e : |pdd12 f ξ₁ η₁ * dt * du| = |pdd12 f ξ₁ η₁| * (|dt| * |du|) := by
          rw [abs_mul, abs_mul, mul_assoc]
        rw [e]
        have h1' : |dt| * |du| ≤ E * E := by
          have h2 : |dt| ≤ E := hle.2
          have h3 : |du| ≤ E := hle.1
          nlinarith [hdt0, hdu0, hE0]
        have h4 : |pdd12 f ξ₁ η₁| * (|dt| * |du|) ≤ K * (E * E) :=
          mul_le_mul hb1 h1' (mul_nonneg (abs_nonneg dt) (abs_nonneg du)) hK
        nlinarith [h4, hE0]
      have h2 : |pdd11 f ξ₂ t₀ * (ξ₁ - u₀) * du| ≤ K * E ^ 2 := by
        have e : |pdd11 f ξ₂ t₀ * (ξ₁ - u₀) * du| = |pdd11 f ξ₂ t₀| * (|ξ₁ - u₀| * |du|) := by
          rw [abs_mul, abs_mul, mul_assoc]
        rw [e]
        have h2' : |ξ₁ - u₀| * |du| ≤ E * E := by
          have h3 : |ξ₁ - u₀| ≤ E := by linarith [hξ, hle.2, hle.1]
          have h4 : |du| ≤ E := hle.1
          nlinarith [hdu0, hE0]
        have h4 : |pdd11 f ξ₂ t₀| * (|ξ₁ - u₀| * |du|) ≤ K * (E * E) :=
          mul_le_mul hb2 h2' (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hK
        nlinarith [h4, hE0]
      have h3 : |pdd22 f u₀ η₂ * (ζ₁ - t₀) * dt| ≤ K * E ^ 2 := by
        have e : |pdd22 f u₀ η₂ * (ζ₁ - t₀) * dt| = |pdd22 f u₀ η₂| * (|ζ₁ - t₀| * |dt|) := by
          rw [abs_mul, abs_mul, mul_assoc]
        rw [e]
        have h3' : |ζ₁ - t₀| * |dt| ≤ E * E := by
          have h4 : |ζ₁ - t₀| ≤ E := by linarith [hζ, hle.1, hle.2]
          have h5 : |dt| ≤ E := hle.2
          nlinarith [hdt0, hE0]
        have h4 : |pdd22 f u₀ η₂| * (|ζ₁ - t₀| * |dt|) ≤ K * (E * E) :=
          mul_le_mul hb3 h3' (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hK
        nlinarith [h4, hE0]
      calc |residual f u₀ t₀ u t|
          = |pdd12 f ξ₁ η₁ * dt * du + pdd11 f ξ₂ t₀ * (ξ₁ - u₀) * du +
              pdd22 f u₀ η₂ * (ζ₁ - t₀) * dt| := by rw [hres]
        _ ≤ |pdd12 f ξ₁ η₁ * dt * du| + |pdd11 f ξ₂ t₀ * (ξ₁ - u₀) * du| +
            |pdd22 f u₀ η₂ * (ζ₁ - t₀) * dt| := by
              have := abs_add_le (pdd12 f ξ₁ η₁ * dt * du + pdd11 f ξ₂ t₀ * (ξ₁ - u₀) * du)
                (pdd22 f u₀ η₂ * (ζ₁ - t₀) * dt)
              have := abs_add_le (pdd12 f ξ₁ η₁ * dt * du)
                (pdd11 f ξ₂ t₀ * (ξ₁ - u₀) * du)
              linarith
        _ ≤ 3 * K * E ^ 2 := by linarith [h1, h2, h3]

theorem inc_bound {φ : ℝ → ℝ} {a b K : ℝ} (hab : a ≠ b)
    (hφ : DifferentiableOn ℝ φ (Set.Icc (min a b) (max a b)))
    (bound : ∀ ξ ∈ Set.Icc (min a b) (max a b), |deriv φ ξ| ≤ K) :
    |φ b - φ a| ≤ K * |b - a| := by
  obtain ⟨ξ, hξ, h⟩ := mvt hab hφ
  have hξ' : ξ ∈ Set.Icc (min a b) (max a b) :=
    ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  have hb0 : |b - a| ≠ 0 := by
    rw [ne_eq, abs_eq_zero]
    exact ne_sub_self (Ne.symm hab)
  have hkey : |φ b - φ a| = |deriv φ ξ| * |b - a| := by
    rw [h, abs_div]
    exact (div_mul_cancel₀ _ hb0).symm
  calc |φ b - φ a|
      = |deriv φ ξ| * |b - a| := hkey
    _ ≤ K * |b - a| := mul_le_mul_of_nonneg_right (bound ξ hξ') (abs_nonneg _)

/-- First partials of `f` differ by at most `K‖e‖₁` between any two points of the
    rectangle. -/
theorem pd1_diff_bound {f : ℝ → ℝ → ℝ} {a b c d K : ℝ}
    (hf : C2Seg f a b c d K) (hK : 0 ≤ K) {u₀ t₀ u t : ℝ}
    (hu : u ∈ Set.Icc a b) (hu₀ : u₀ ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc c d) (ht₀ : t₀ ∈ Set.Icc c d) :
    |pd1 f u t - pd1 f u₀ t₀| ≤ K * (|u - u₀| + |t - t₀|) := by
  have hu_sub : Set.Icc (min u u₀) (max u u₀) ⊆ Set.Icc a b := SetIoo_subset hu hu₀
  have ht_sub : Set.Icc (min t t₀) (max t t₀) ⊆ Set.Icc c d := SetIoo_subset_t ht ht₀
  -- t-direction
  have htpart : |pd1 f u t - pd1 f u t₀| ≤ K * |t - t₀| := by
    by_cases ht0 : t = t₀
    · rw [ht0]
      simp
    · have h1 := inc_bound (a := t) (b := t₀) ht0 ((hf.col₁ u hu).mono ht_sub)
        (fun ξ hξ => hf.b₁₂ u hu ξ (SetIoo_subset_t ht ht₀ hξ))
      rwa [abs_sub_comm (pd1 f u t₀) (pd1 f u t), abs_sub_comm t₀ t] at h1
  have hupart : |pd1 f u t₀ - pd1 f u₀ t₀| ≤ K * |u - u₀| := by
    by_cases hu0 : u = u₀
    · rw [hu0]
      simp
    · have h1 := inc_bound (a := u) (b := u₀) hu0 ((hf.row₁ t₀ ht₀).mono hu_sub)
        (fun ξ hξ => hf.b₁₁ ξ (SetIoo_subset hu hu₀ hξ) t₀ ht₀)
      rwa [abs_sub_comm (pd1 f u₀ t₀) (pd1 f u t₀), abs_sub_comm u₀ u] at h1
  have hsplit : pd1 f u t - pd1 f u₀ t₀ = (pd1 f u t - pd1 f u t₀) + (pd1 f u t₀ - pd1 f u₀ t₀) := by
    ring
  rw [hsplit]
  calc |pd1 f u t - pd1 f u t₀ + (pd1 f u t₀ - pd1 f u₀ t₀)|
      ≤ |pd1 f u t - pd1 f u t₀| + |pd1 f u t₀ - pd1 f u₀ t₀| := abs_add_le _ _
    _ ≤ K * |t - t₀| + K * |u - u₀| := by nlinarith [htpart, hupart]
    _ = K * (|u - u₀| + |t - t₀|) := by ring

/-- Second partials differ by at most `K‖e‖₁` too (via `col₁`/`row₁`/`col₂`). -/
theorem pd2_diff_bound {f : ℝ → ℝ → ℝ} {a b c d K : ℝ}
    (hf : C2Seg f a b c d K) (hK : 0 ≤ K) {u₀ t₀ u t : ℝ}
    (hu : u ∈ Set.Icc a b) (hu₀ : u₀ ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc c d) (ht₀ : t₀ ∈ Set.Icc c d) :
    |pd2 f u t - pd2 f u₀ t₀| ≤ K * (|u - u₀| + |t - t₀|) := by
  have hu_sub : Set.Icc (min u u₀) (max u u₀) ⊆ Set.Icc a b := SetIoo_subset hu hu₀
  have ht_sub : Set.Icc (min t t₀) (max t t₀) ⊆ Set.Icc c d := SetIoo_subset_t ht ht₀
  have htpart : |pd2 f u t - pd2 f u t₀| ≤ K * |t - t₀| := by
    by_cases ht0 : t = t₀
    · rw [ht0]
      simp
    · have h1 := inc_bound (a := t) (b := t₀) ht0 ((hf.col₂ u hu).mono ht_sub)
        (fun ξ hξ => hf.b₂₂ u hu ξ (SetIoo_subset_t ht ht₀ hξ))
      rwa [abs_sub_comm (pd2 f u t₀) (pd2 f u t), abs_sub_comm t₀ t] at h1
  have hupart : |pd2 f u t₀ - pd2 f u₀ t₀| ≤ K * |u - u₀| := by
    by_cases hu0 : u = u₀
    · rw [hu0]
      simp
    · have h1 := inc_bound (a := u) (b := u₀) hu0 ((hf.row₂ t₀ ht₀).mono hu_sub)
        (fun ξ hξ => hf.b₂₁ ξ (SetIoo_subset hu hu₀ hξ) t₀ ht₀)
      rwa [abs_sub_comm (pd2 f u₀ t₀) (pd2 f u t₀), abs_sub_comm u₀ u] at h1
  have hsplit : pd2 f u t - pd2 f u₀ t₀ = (pd2 f u t - pd2 f u t₀) + (pd2 f u t₀ - pd2 f u₀ t₀) := by
    ring
  rw [hsplit]
  calc |pd2 f u t - pd2 f u t₀ + (pd2 f u t₀ - pd2 f u₀ t₀)|
      ≤ |pd2 f u t - pd2 f u t₀| + |pd2 f u t₀ - pd2 f u₀ t₀| := abs_add_le _ _
    _ ≤ K * |t - t₀| + K * |u - u₀| := by nlinarith [htpart, hupart]
    _ = K * (|u - u₀| + |t - t₀|) := by ring

/-- One two-dimensional Newton step for `F = (f, g)`: the Cramer update. -/
noncomputable def newton2Step (f g : ℝ → ℝ → ℝ) (u t : ℝ) : ℝ × ℝ :=
  (u - (f u t * pd2 g u t - pd2 f u t * g u t) / jacDet f g u t,
   t - (pd1 f u t * g u t - pd1 g u t * f u t) / jacDet f g u t)

set_option maxHeartbeats 3200000 in
/-- **Two-dimensional Newton step contracts quadratically near a simple root.**
The Bez triangle/tube Newton solves `F = (⟨R, C′⟩ + r r′, |R| − r) = 0`; near a
front-facing, simple contact each step squares the error. Hypotheses: `(f, g)`
are `C2` with `0 < K` bounding the second derivatives, all eight partials
(at both points) bounded by `B ≥ 0`, `|det J(x)| ≥ δ > 0` (the C's own
acceptance guard at the iterate), `K‖x − x*‖₁ ≤ B`, and the iterate within
`E = ‖x − x*‖₁` of the root. Then

  `|(x′ − x*)₁| ≤ (10 B K / δ) E²`, `|(x′ − x*)₂| ≤ (8 B K E² + 2 B² E)/δ`,

where `x′ = x − J(x)⁻¹ F(x)`. The `B²E` term is the contribution of the two
cross-derivative products; if `E ≥ B/K` additionally holds this is `≤ (10 B K/δ) E²`
as well (the honest bound used for convergence is the `E²` one since `E` is
small in the ball the C iterates in). -/
theorem newton2_step_quadratic {f g : ℝ → ℝ → ℝ} {a b c d K B δ : ℝ}
    (hf : C2Seg f a b c d K) (hg : C2Seg g a b c d K) (hK : 0 < K) (hB : 0 ≤ B)
    {u₀ t₀ u t : ℝ} (hu : u ∈ Set.Icc a b) (hu₀ : u₀ ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc c d) (ht₀ : t₀ ∈ Set.Icc c d)
    (hroot : f u₀ t₀ = 0 ∧ g u₀ t₀ = 0)
    (hUb : |pd1 f u t| ≤ B) (hVb : |pd2 f u t| ≤ B)
    (hWb : |pd1 g u t| ≤ B) (hZb : |pd2 g u t| ≤ B)
    (hAb : |pd1 f u₀ t₀| ≤ B) (hBb : |pd2 f u₀ t₀| ≤ B)
    (hCb : |pd1 g u₀ t₀| ≤ B) (hDb : |pd2 g u₀ t₀| ≤ B)
    (hden : δ ≤ |jacDet f g u t|) (hδ : 0 < δ)
    (hE : |u - u₀| + |t - t₀| ≤ B / K) :
    |(newton2Step f g u t).1 - u₀| ≤ (10 * B * K / δ) * (|u - u₀| + |t - t₀|) ^ 2 ∧
    |(newton2Step f g u t).2 - t₀| ≤ (8 * B * K * (|u - u₀| + |t - t₀|) ^ 2 + 2 * B ^ 2 *
      (|u - u₀| + |t - t₀|)) / δ := by
  set du := u - u₀ with hdu
  set dt := t - t₀ with hdt
  set E := |du| + |dt| with hE_def
  have hE0 : 0 ≤ E := by
    rw [hE_def]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hKB : K * E ≤ B := by
    have h1 : E ≤ B / K := hE
    rw [le_div_iff₀' hK] at h1
    nlinarith [h1]
  have hle : |du| ≤ E ∧ |dt| ≤ E := by
    have h := hE_def
    rw [h]
    constructor <;> linarith [abs_nonneg du, abs_nonneg dt]
  set U := pd1 f u t with hU
  set V := pd2 f u t with hV
  set W := pd1 g u t with hW
  set Z := pd2 g u t with hZ
  set A := pd1 f u₀ t₀ with hA
  set B0 := pd2 f u₀ t₀ with hB0
  set C := pd1 g u₀ t₀ with hC
  set D := pd2 g u₀ t₀ with hD
  set Rf := residual f u₀ t₀ u t with hRf_def
  set Rg := residual g u₀ t₀ u t with hRg_def
  have hRfb : |Rf| ≤ 3 * K * E ^ 2 := residual_bound hf hK.le hu hu₀ ht ht₀
  have hRgb : |Rg| ≤ 3 * K * E ^ 2 := residual_bound hg hK.le hu hu₀ ht ht₀
  have hX : f u t = A * du + B0 * dt + Rf := by
    unfold Rf
    unfold residual
    rw [hroot.1]
    ring
  have hY : g u t = C * du + D * dt + Rg := by
    unfold Rg
    unfold residual
    rw [hroot.2]
    ring
  have hDU : |U - A| ≤ K * E := pd1_diff_bound hf hK.le hu hu₀ ht ht₀
  have hDV : |V - B0| ≤ K * E := pd2_diff_bound hf hK.le hu hu₀ ht ht₀
  have hDW : |W - C| ≤ K * E := pd1_diff_bound hg hK.le hu hu₀ ht ht₀
  have hDZ : |Z - D| ≤ K * E := pd2_diff_bound hg hK.le hu hu₀ ht ht₀
  have hdet : 0 < |jacDet f g u t| := by linarith [hδ, hden]
  have hdet' : jacDet f g u t = U * Z - V * W := rfl
  have he1 : (newton2Step f g u t).1 - u₀ =
      (du * jacDet f g u t - (f u t * Z - V * g u t)) / jacDet f g u t := by
    unfold newton2Step
    simp only [Prod.fst]
    rw [← hZ, ← hV, hdu]
    field_simp [abs_pos.mp hdet]
    ring
  have he2 : (newton2Step f g u t).2 - t₀ =
      (dt * jacDet f g u t - (U * g u t - W * f u t)) / jacDet f g u t := by
    unfold newton2Step
    simp only [Prod.snd]
    rw [← hW, ← hU, hdt]
    field_simp [abs_pos.mp hdet]
    ring
  have key1 : f u t * Z - V * g u t =
      (A * Z - C * V) * du + (B0 * Z - D * V) * dt + (Rf * Z - Rg * V) := by
    rw [hX, hY]; ring
  have key2 : U * g u t - W * f u t =
      (U * C - W * A) * du + (U * D - W * B0) * dt + (U * Rg - W * Rf) := by
    rw [hX, hY]; ring
  have hnum1 : du * jacDet f g u t - (f u t * Z - V * g u t) =
      du * (Z * (U - A) + V * (C - W)) - dt * (B0 * Z - D * V) - (Rf * Z - Rg * V) := by
    rw [hdet', key1]; ring
  have hnum2 : dt * jacDet f g u t - (U * g u t - W * f u t) =
      dt * (U * (Z - D) - W * (V - B0)) - du * (U * C - W * A) - (U * Rg - W * Rf) := by
    rw [hdet', key2]; ring
  have hA1 : |du * (Z * (U - A) + V * (C - W))| ≤ 2 * B * K * E ^ 2 := by
    have h1 : |Z * (U - A)| ≤ B * (K * E) := by
      rw [abs_mul]
      exact mul_le_mul hZb hDU (abs_nonneg _) hB
    have h2 : |V * (C - W)| ≤ B * (K * E) := by
      rw [abs_mul]
      have hCW : |C - W| ≤ K * E := by rwa [abs_sub_comm]
      exact mul_le_mul hVb hCW (abs_nonneg _) hB
    have h3 : |Z * (U - A) + V * (C - W)| ≤ 2 * B * (K * E) := by
      have := abs_add_le (Z * (U - A)) (V * (C - W))
      linarith [h1, h2, this]
    calc |du * (Z * (U - A) + V * (C - W))|
        = |du| * |Z * (U - A) + V * (C - W)| := by rw [abs_mul]
      _ ≤ E * (2 * B * (K * E)) := by
          apply mul_le_mul hle.1 h3 (abs_nonneg _) hE0
      _ = 2 * B * K * E ^ 2 := by ring
  have hA2 : |dt * (B0 * Z - D * V)| ≤ 2 * B * K * E ^ 2 := by
    have e : B0 * Z - D * V = B0 * (Z - D) - D * (V - B0) := by ring
    have h1 : |B0 * (Z - D)| ≤ B * (K * E) := by
      rw [abs_mul]
      exact mul_le_mul hBb hDZ (abs_nonneg _) hB
    have h2 : |D * (V - B0)| ≤ B * (K * E) := by
      rw [abs_mul]
      exact mul_le_mul hDb hDV (abs_nonneg _) hB
    have h3 : |B0 * (Z - D) - D * (V - B0)| ≤ 2 * B * (K * E) := by
      have := abs_sub_le' (B0 * (Z - D)) (D * (V - B0))
      linarith [h1, h2, this]
    calc |dt * (B0 * Z - D * V)|
        = |dt| * |B0 * Z - D * V| := by rw [abs_mul]
      _ ≤ E * (2 * B * (K * E)) := by
          rw [e]
          apply mul_le_mul hle.2 h3 (abs_nonneg _) hE0
      _ = 2 * B * K * E ^ 2 := by ring
  have hA3 : |Rf * Z - Rg * V| ≤ 6 * B * K * E ^ 2 := by
    have h1 : |Rf * Z| ≤ 3 * K * E ^ 2 * B := by
      rw [abs_mul]
      apply mul_le_mul hRfb hZb (abs_nonneg _) (by positivity)
    have h2 : |Rg * V| ≤ 3 * K * E ^ 2 * B := by
      rw [abs_mul]
      apply mul_le_mul hRgb hVb (abs_nonneg _) (by positivity)
    have h3 : |Rf * Z - Rg * V| ≤ |Rf * Z| + |Rg * V| := abs_sub_le' _ _
    linarith [h1, h2, h3]
  have hnum1_bound : |du * jacDet f g u t - (f u t * Z - V * g u t)| ≤ 10 * B * K * E ^ 2 := by
    have hadd := abs_add_three (du * (Z * (U - A) + V * (C - W)))
      (-(dt * (B0 * Z - D * V))) (-(Rf * Z - Rg * V))
    rw [abs_neg, abs_neg] at hadd
    have e : du * jacDet f g u t - (f u t * Z - V * g u t) =
        du * (Z * (U - A) + V * (C - W)) + (-(dt * (B0 * Z - D * V))) + (-(Rf * Z - Rg * V)) := by
      rw [hnum1]; ring
    rw [e]
    linarith [hadd, hA1, hA2, hA3]
  have hA4 : |dt * (U * (Z - D) - W * (V - B0))| ≤ 2 * B * K * E ^ 2 := by
    have h1 : |U * (Z - D)| ≤ B * (K * E) := by
      rw [abs_mul]
      exact mul_le_mul hUb hDZ (abs_nonneg _) hB
    have h2 : |W * (V - B0)| ≤ B * (K * E) := by
      rw [abs_mul]
      exact mul_le_mul hWb hDV (abs_nonneg _) hB
    have h3 : |U * (Z - D) - W * (V - B0)| ≤ 2 * B * (K * E) := by
      have := abs_sub_le' (U * (Z - D)) (W * (V - B0))
      nlinarith [h1, h2]
    calc |dt * (U * (Z - D) - W * (V - B0))|
        = |dt| * |U * (Z - D) - W * (V - B0)| := by rw [abs_mul]
      _ ≤ E * (2 * B * (K * E)) := by
          apply mul_le_mul hle.2 h3 (abs_nonneg _) hE0
      _ = 2 * B * K * E ^ 2 := by ring
  have hA5 : |du * (U * C - W * A)| ≤ 2 * B ^ 2 * E := by
    have h1 : |U * C - W * A| ≤ 2 * B * B := by
      have h1a : |U * C| ≤ B * B := by
        rw [abs_mul]
        exact mul_le_mul hUb hCb (abs_nonneg _) hB
      have h1b : |W * A| ≤ B * B := by
        rw [abs_mul]
        exact mul_le_mul hWb hAb (abs_nonneg _) hB
      have := abs_sub_le' (U * C) (W * A)
      linarith [h1a, h1b, this]
    have h2 : |du| * |U * C - W * A| ≤ E * (2 * B * B) := by
      apply mul_le_mul hle.1 h1 (abs_nonneg _) hE0
    have h3 : |du * (U * C - W * A)| = |du| * |U * C - W * A| := by rw [abs_mul]
    linarith [h2, h3]
  have hA6 : |U * Rg - W * Rf| ≤ 6 * B * K * E ^ 2 := by
    have h1 : |U * Rg| ≤ B * (3 * K * E ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul hUb hRgb (by positivity) hB
    have h2 : |W * Rf| ≤ B * (3 * K * E ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul hWb hRfb (by positivity) hB
    have h3 : |U * Rg - W * Rf| ≤ |U * Rg| + |W * Rf| := abs_sub_le' _ _
    linarith [h1, h2, h3]
  have hnum2_bound : |dt * jacDet f g u t - (U * g u t - W * f u t)| ≤
      8 * B * K * E ^ 2 + 2 * B ^ 2 * E := by
    have hadd := abs_add_three (dt * (U * (Z - D) - W * (V - B0)))
      (-(du * (U * C - W * A))) (-(U * Rg - W * Rf))
    rw [abs_neg, abs_neg] at hadd
    have e : dt * jacDet f g u t - (U * g u t - W * f u t) =
        dt * (U * (Z - D) - W * (V - B0)) + (-(du * (U * C - W * A))) + (-(U * Rg - W * Rf)) := by
      rw [hnum2]; ring
    rw [e]
    linarith [hadd, hA4, hA5, hA6]
  have hd' : δ ≤ |jacDet f g u t| := hden
  have hd'' : 0 < |jacDet f g u t| := hdet
  have e1' : |(newton2Step f g u t).1 - u₀| ≤ (10 * B * K / δ) * E ^ 2 := by
    rw [he1, abs_div]
    have h2 : |du * jacDet f g u t - (f u t * Z - V * g u t)| / |jacDet f g u t| ≤
        10 * B * K * E ^ 2 / δ := by
      rw [div_le_iff₀ hd'']
      have h4 : 10 * B * K * E ^ 2 / δ * |jacDet f g u t| ≥ 10 * B * K * E ^ 2 / δ * δ :=
        mul_le_mul_of_nonneg_left hd' (by positivity)
      have h4' : 10 * B * K * E ^ 2 / δ * δ = 10 * B * K * E ^ 2 :=
        div_mul_cancel₀ _ (ne_of_gt hδ)
      linarith [h4, h4', hnum1_bound]
    calc |du * jacDet f g u t - (f u t * Z - V * g u t)| / |jacDet f g u t|
        ≤ 10 * B * K * E ^ 2 / δ := h2
      _ = (10 * B * K / δ) * E ^ 2 := by ring
  have e2' : |(newton2Step f g u t).2 - t₀| ≤
      (8 * B * K * E ^ 2 + 2 * B ^ 2 * E) / δ := by
    rw [he2, abs_div]
    have h2 : |dt * jacDet f g u t - (U * g u t - W * f u t)| / |jacDet f g u t| ≤
        (8 * B * K * E ^ 2 + 2 * B ^ 2 * E) / δ := by
      rw [div_le_iff₀ hd'']
      have h4 : (8 * B * K * E ^ 2 + 2 * B ^ 2 * E) / δ * |jacDet f g u t| ≥
          (8 * B * K * E ^ 2 + 2 * B ^ 2 * E) / δ * δ :=
        mul_le_mul_of_nonneg_left hd' (by positivity)
      have h4' : (8 * B * K * E ^ 2 + 2 * B ^ 2 * E) / δ * δ = 8 * B * K * E ^ 2 + 2 * B ^ 2 * E :=
        div_mul_cancel₀ _ (ne_of_gt hδ)
      linarith [h4, h4', hnum2_bound]
    calc |dt * jacDet f g u t - (U * g u t - W * f u t)| / |jacDet f g u t|
        ≤ (8 * B * K * E ^ 2 + 2 * B ^ 2 * E) / δ := h2
      _ = (8 * B * K * E ^ 2 + 2 * B ^ 2 * E) / δ := rfl
  exact ⟨e1', e2'⟩

end LightRT.Geom
