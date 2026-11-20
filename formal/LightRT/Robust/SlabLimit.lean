/-
  The tangency boundary of the conservative slab test, closed as a **proved
  limitation** rather than left as an open gap.

  `Robust/Slab.lean` proves `slab_no_false_miss` under `SlabInRange`, and
  `Robust/SlabTotal.lean` proves the range-free `slab_no_false_miss_total_of_floor`
  under a non-degeneracy floor `κ ≤ |(x - o)/d|` on the slab endpoints. Both
  routes need a relative error bound `θ < 1` for the scalar slab parameter
  `fpT = fl(fl(x - o) * fl(1/d))`; the floor is what converts the absolute
  error (which contains a subnormal `η` term) into such a relative bound.

  This module proves that the relative bound cannot hold uniformly: at the
  smallest binary32 subnormal quantum, `fl(2⁻¹⁵⁰) = 0` (round-to-nearest-even),
  so the error of `fpT` equals `|t|` itself and no `θ < 1` can dominate it.
  Consequently no single error-dominating inflation factor `K` can be derived
  without the floor, and a concrete, genuinely-hit box has no valid `θ < 1`
  on its endpoints. This is why the boundary exists; it is not missing effort.
-/
import LightRT.Robust.SlabTotal

namespace LightRT.Robust
open LightRT.FP LightRT.FP.Binary32 LightRT.Geom
noncomputable section

/-! ### Concrete binary32 facts at the subnormal quantum -/

/-- For `0 < x < 2⁻¹²⁶` the quantum exponent clamps at the subnormal floor. -/
lemma qexp_eq_neg149_of_small {x : ℝ} (hpos : 0 < x) (hx : x < (2 : ℝ)^(-126 : ℤ)) :
    qexp x = (-149 : ℤ) := by
  rw [qexp_eq]
  have hlog : Int.log 2 x ≤ -126 := by
    by_contra hlt
    push Not at hlt
    have h1 := two_zpow_log_le hpos
    have h2 : (2 : ℝ)^(-126 : ℤ) < (2 : ℝ)^(Int.log 2 x) := by
      apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
      omega
    linarith
  rw [abs_of_pos hpos, max_eq_right hlog]
  norm_num

lemma roundEven_half_zero : roundEven ((1 : ℝ) / 2) = 0 := by
  unfold roundEven; norm_num

lemma half_quantum_small : (1/2 : ℝ) * (2 : ℝ)^(-149 : ℤ) < (2 : ℝ)^(-126 : ℤ) := by
  norm_num [zpow_neg]

/-- Round-to-nearest-even sends half the smallest subnormal quantum to zero. -/
lemma rneR_half_quantum : rneR ((2 : ℝ)^(-150 : ℤ)) = 0 := by
  have hc : ((2 : ℝ)^(-150 : ℤ)) = (1/2 : ℝ) * (2 : ℝ)^(-149 : ℤ) := by
    rw [show (-150 : ℤ) = -149 - 1 by norm_num, zpow_sub₀ (by norm_num)]
    field_simp
  rw [hc, rneR, rne]
  simp only [↓reduceIte]
  have hxpos : 0 < (1/2 : ℝ) * (2 : ℝ)^(-149 : ℤ) := by positivity
  rw [abs_of_pos hxpos]
  rw [qexp_eq_neg149_of_small hxpos half_quantum_small]
  norm_num
  rw [roundEven_half_zero]

/-- For the unit-direction ray from the origin, `fpT` at `2⁻¹⁵⁰` is exactly zero. -/
lemma fpT_at_subnormal :
    let r : Ray := { o := fun _ => 0, d := fun _ => 1, tmin := 0, tmax := 1 }
    fpT model r ((2 : ℝ)^(-150 : ℤ)) 0 = 0 := by
  dsimp only
  unfold fpT fpInvd
  change rneR (rneR (((2 : ℝ)^(-150 : ℤ)) - 0) * rneR (1 / (1 : ℝ))) = 0
  rw [sub_zero, rneR_half_quantum]
  simp [rneR, rne]

/-! ### The impossibility results -/

/-- **No uniform relative bound for the slab parameter.** There is no `θ < 1`
    such that `|fpT - t| ≤ θ |t|` for every ray, endpoint and axis. At the
    subnormal quantum the error equals `|t|` itself, so `θ ≥ 1` would be
    required. This is the exact obstruction at a tangent ray: the range-free
    error is not relatively bounded, hence the floor in
    `slab_no_false_miss_total_of_floor` is necessary for this proof route. -/
theorem fpT_no_uniform_relative :
    ¬ ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ (r : Ray) (x : ℝ) (i : Fin 3), r.d i ≠ 0 →
        |fpT model r x i - (x - r.o i) / r.d i| ≤ θ * |(x - r.o i) / r.d i| := by
  rintro ⟨θ, hθ0, hθ1, hbound⟩
  let r : Ray := { o := fun _ => 0, d := fun _ => 1, tmin := 0, tmax := 1 }
  let x : ℝ := (2 : ℝ)^(-150 : ℤ)
  have hd : r.d (0 : Fin 3) ≠ 0 := by simp [r]
  have h := hbound r x 0 hd
  have hfp : fpT model r x 0 = 0 := by simpa [r, x] using fpT_at_subnormal
  have ht : (x - r.o 0) / r.d 0 = x := by simp [r, x]
  rw [hfp, ht] at h
  have hxpos : 0 < x := by dsimp [x]; positivity
  rw [zero_sub, abs_neg, abs_of_pos hxpos] at h
  nlinarith

/-- **No uniform inflation factor via the relative-error route.** The
    range-free no-false-miss theorem needs a relative bound `θ < 1` (so that
    `(1 - θ)(1 - u) K` is positive and can dominate `1 + θ + η/κT`). Since no
    such uniform `θ` exists, no single error-dominating `K` can be established
    without the floor `κ ≤ |(x - o)/d|`. -/
theorem slab_no_uniform_inflation :
    ¬ ∃ (K θ : ℝ), 0 ≤ θ ∧ θ < 1 ∧ 1 ≤ K ∧
      (∀ (r : Ray) (x : ℝ) (i : Fin 3), r.d i ≠ 0 →
        |fpT model r x i - (x - r.o i) / r.d i| ≤ θ * |(x - r.o i) / r.d i|) := by
  rintro ⟨K, θ, hθ0, hθ1, hK, hrel⟩
  exact fpT_no_uniform_relative ⟨θ, hθ0, hθ1, hrel⟩

/-- **A concrete hit box with no admissible endpoint bound.** The box
    `[2⁻¹⁵⁰, 1]³` is genuinely hit by the unit ray from the origin, yet no
    `θ < 1` bounds the relative error of `fpT` on its endpoints (the lower
    endpoint `2⁻¹⁵⁰` needs `θ ≥ 1`). Hence the `hθbound` hypothesis of
    `slab_no_false_miss_total_of_floor` is not satisfiable for this box without
    a floor that excludes subnormal endpoint parameters. -/
theorem slab_hit_box_no_endpoint_theta :
    let r : Ray := { o := fun _ => 0, d := fun _ => 1, tmin := 0, tmax := 1 }
    let b : Box := { lo := fun _ => (2 : ℝ)^(-150 : ℤ), hi := fun _ => 1 }
    HitsBox r b ∧
    ¬ ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ i, ∀ x ∈ ({b.lo i, b.hi i} : Set ℝ),
        |fpT model r x i - (x - r.o i) / r.d i| ≤ θ * |(x - r.o i) / r.d i| := by
  dsimp only
  constructor
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    intro i
    constructor <;> norm_num [Ray.at]
  · rintro ⟨θ, hθ0, hθ1, hbound⟩
    have hmem : ((2 : ℝ)^(-150 : ℤ)) ∈ ({(2 : ℝ)^(-150 : ℤ), 1} : Set ℝ) := by simp
    have h := hbound 0 ((2 : ℝ)^(-150 : ℤ)) hmem
    have hfp : fpT model
        ({ o := fun _ => 0, d := fun _ => 1, tmin := 0, tmax := 1 } : Ray)
        ((2 : ℝ)^(-150 : ℤ)) 0 = 0 := fpT_at_subnormal
    have ht : (((2 : ℝ)^(-150 : ℤ)) - (0 : ℝ)) / (1 : ℝ) = (2 : ℝ)^(-150 : ℤ) := by ring
    rw [hfp, ht] at h
    have hxpos : 0 < (2 : ℝ)^(-150 : ℤ) := by positivity
    rw [zero_sub, abs_neg, abs_of_pos hxpos] at h
    nlinarith

end
end LightRT.Robust
