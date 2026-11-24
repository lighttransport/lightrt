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
  unfold gamma
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hmu : (m : ℝ) * u ≤ n * u := mul_le_mul_of_nonneg_right hmn' hu
  have h1 : 0 < 1 - (n : ℝ) * u := by linarith
  have h2 : 0 < 1 - (m : ℝ) * u := by linarith
  rw [div_le_div_iff₀ h2 h1]; nlinarith

/-- Composition: `(1+θₘ)(1+θₙ) = 1+θ_{m+n}`. -/
theorem gamma_compose {u : ℝ} {m n : ℕ} (hu : 0 ≤ u) (h : ((m + n : ℕ) : ℝ) * u < 1)
    {a b : ℝ} (ha : |a| ≤ gamma u m) (hb : |b| ≤ gamma u n) :
    |(1 + a) * (1 + b) - 1| ≤ gamma u (m + n) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast at h
  have hp : (m : ℝ) * u < 1 := by nlinarith
  have hq : (n : ℝ) * u < 1 := by nlinarith
  have ga0 := gamma_nonneg (n := m) hu hp
  have gb0 := gamma_nonneg (n := n) hu hq
  -- (1+γm)(1+γn) ≤ 1+γ(m+n)
  have key : gamma u m + gamma u n + gamma u m * gamma u n ≤ gamma u (m + n) := by
    unfold gamma; push_cast
    have h1 : 0 < 1 - (m : ℝ) * u := by linarith
    have h2 : 0 < 1 - (n : ℝ) * u := by linarith
    have h3 : 0 < 1 - ((m : ℝ) + n) * u := by linarith
    rw [div_add_div _ _ h1.ne' h2.ne', div_mul_div_comm, div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) h3]
    have hmu : 0 ≤ (m : ℝ) * u := by positivity
    have hnu : 0 ≤ (n : ℝ) * u := by positivity
    nlinarith [mul_nonneg hmu hnu, mul_nonneg (mul_nonneg hmu hnu) h1.le,
      mul_nonneg (mul_nonneg hmu hnu) h2.le, mul_nonneg (mul_nonneg hmu hnu) (mul_nonneg h1.le h2.le)]
  have hab : |a * b| ≤ gamma u m * gamma u n := by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ga0
  calc |(1 + a) * (1 + b) - 1| = |a + b + a * b| := by ring_nf
    _ ≤ |a| + |b| + |a * b| := abs_add_three _ _ _
    _ ≤ _ := by linarith

/-- Same, allowing each factor to be inverted (needed for `1/d`). -/
theorem prod_one_add_zpow_le {u : ℝ} {n : ℕ} (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (δ : Fin n → ℝ) (hδ : ∀ i, |δ i| ≤ u) (s : Fin n → Bool) :
    |(∏ i, (if s i then (1 + δ i) else (1 + δ i)⁻¹)) - 1| ≤ gamma u n := by
  induction n with
  | zero => simp [gamma]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have hn' : (n : ℝ) * u < 1 := by push_cast at hn; nlinarith
    have hu1 : u < 1 := by push_cast at hn; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hr := ih hn' (fun i => δ i.succ) (fun i => hδ i.succ) (fun i => s i.succ)
    have h0 : |(if s 0 then (1 + δ 0) else (1 + δ 0)⁻¹) - 1| ≤ gamma u 1 := by
      have hd := abs_le.1 (hδ 0)
      unfold gamma; norm_num
      split_ifs
      · rw [le_div_iff₀ (by linarith)]; simp only [add_sub_cancel_left]
        nlinarith [hδ 0, abs_nonneg (δ 0)]
      · have hp : 0 < 1 + δ 0 := by linarith
        rw [show (1 + δ 0)⁻¹ - 1 = -δ 0 / (1 + δ 0) by field_simp; ring, abs_div, abs_neg,
          abs_of_pos hp, div_le_div_iff₀ hp (by linarith)]
        nlinarith [hδ 0, abs_nonneg (δ 0)]
    have := gamma_compose (m := 1) (n := n) hu (by rw [add_comm]; exact hn) h0 hr
    rw [add_comm 1 n] at this
    simpa using this

/-- Higham Lemma 3.1: a product of `n` factors `(1+δᵢ)^{±1}` is `1 + θ`, `|θ| ≤ γₙ`.
    Each `δᵢ` is independent (`δ : Fin n → ℝ`). -/
theorem prod_one_add_le {u : ℝ} {n : ℕ} (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (δ : Fin n → ℝ) (hδ : ∀ i, |δ i| ≤ u) :
    |(∏ i, (1 + δ i)) - 1| ≤ gamma u n := by
  simpa using prod_one_add_zpow_le hu hn δ hδ (fun _ => true)

end LightRT.FP
