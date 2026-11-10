/-
  Stage 2: Higham's γₙ = n·u / (1 - n·u) and composition lemmas.
-/
import LightRT.FP.Model

namespace LightRT.FP

/-- `γ n u = n u / (1 - n u)`; meaningful when `n u < 1`. -/
noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ := n * u / (1 - n * u)

theorem gamma_nonneg {u : ℝ} {n : ℕ} (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1) :
    0 ≤ gamma u n := by
  unfold gamma; apply div_nonneg <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem gamma_mono {u : ℝ} {m n : ℕ} (hu : 0 ≤ u) (hmn : m ≤ n)
    (hn : (n : ℝ) * u < 1) : gamma u m ≤ gamma u n := by
  sorry

/-- Higham Lemma 3.1: a product of `n` factors `(1+δᵢ)^{±1}` is `1 + θ`, `|θ| ≤ γₙ`.
    Each `δᵢ` is independent (`δ : Fin n → ℝ`). -/
theorem prod_one_add_le {u : ℝ} {n : ℕ} (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (δ : Fin n → ℝ) (hδ : ∀ i, |δ i| ≤ u) :
    |(∏ i, (1 + δ i)) - 1| ≤ gamma u n := by
  sorry

/-- Same, allowing each factor to be inverted (needed for `1/d`). -/
theorem prod_one_add_zpow_le {u : ℝ} {n : ℕ} (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (δ : Fin n → ℝ) (hδ : ∀ i, |δ i| ≤ u) (s : Fin n → Bool) :
    |(∏ i, (if s i then (1 + δ i) else (1 + δ i)⁻¹)) - 1| ≤ gamma u n := by
  sorry

/-- Composition: `(1+θₘ)(1+θₙ) = 1+θ_{m+n}`. -/
theorem gamma_compose {u : ℝ} {m n : ℕ} (hu : 0 ≤ u) (h : ((m + n : ℕ) : ℝ) * u < 1)
    {a b : ℝ} (ha : |a| ≤ gamma u m) (hb : |b| ≤ gamma u n) :
    |(1 + a) * (1 + b) - 1| ≤ gamma u (m + n) := by
  sorry

end LightRT.FP
