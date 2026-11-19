/-
  Rational (NURBS) bicubic surface over R: the rational evaluation of a
  post-Bezier-extraction NURBS patch (weights + Cartesian control net), with
  positive-weight denominator, convex-combination identity, control-hull
  containment, hit soundness/culling, and continuity. Tier 1 item 1
  (parametric surfaces), building on `Geom/BezPatchReal.lean` / `Geom/Hull.lean`.
-/
import Mathlib
import LightRT.Geom.BezPatchReal
set_option maxHeartbeats 2000000
namespace LightRT.Geom
noncomputable section
open Matrix
open LightRT.Geom.Hull

/-- Denominator (weight sum) of a rational bicubic patch. -/
def ratWeight (w : Fin 16 → ℝ) (u v : ℝ) : ℝ := ∑ k : Fin 16, bern33 u v k * w k

/-- Cartesian rational (NURBS) bicubic evaluation: weighted sum of Cartesian
    control points divided by the Bernstein-weighted weight sum. -/
def ratEval (w : Fin 16 → ℝ) (P : Fin 16 → Vec3) (u v : ℝ) : Vec3 :=
  fun i => (∑ k : Fin 16, bern33 u v k * w k * P k i) / ratWeight w u v

/-- The denominator is positive on [0,1]^2 when all weights are positive. -/
theorem ratWeight_pos (w : Fin 16 → ℝ) (hw : ∀ k, 0 < w k)
    {u v : ℝ} (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) :
    0 < ratWeight w u v := by
  unfold ratWeight
  have hex : ∃ k : Fin 16, 0 < bern33 u v k := by
    by_contra h
    push Not at h
    have hz : ∑ k : Fin 16, bern33 u v k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact le_antisymm (h k) (bern33_nonneg hu0 hu1 hv0 hv1 k)
    have hs := bern33_sum u v
    linarith
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (bern33_nonneg hu0 hu1 hv0 hv1 k) (le_of_lt (hw k))
  · rcases hex with ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, mul_pos hk (hw k)⟩

/-- The normalized rational weights sum to one. -/
theorem ratLambda_sum (w : Fin 16 → ℝ) (u v : ℝ) (hD : ratWeight w u v ≠ 0) :
    ∑ k : Fin 16, (bern33 u v k * w k) / ratWeight w u v = 1 := by
  rw [← Finset.sum_div]
  unfold ratWeight at hD ⊢
  exact div_self hD

/-- Cartesian rational evaluation as a convex combination of Cartesian controls. -/
theorem ratEval_eq_lambda (w : Fin 16 → ℝ) (P : Fin 16 → Vec3) (u v : ℝ)
    (hD : ratWeight w u v ≠ 0) (i : Fin 3) :
    ratEval w P u v i = ∑ k : Fin 16, (bern33 u v k * w k / ratWeight w u v) * P k i := by
  unfold ratEval
  rw [div_eq_iff hD]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  field_simp

/-- The rational patch point lies in the Cartesian control-point box. -/
theorem ratEval_in_box (w : Fin 16 → ℝ) (P : Fin 16 → Vec3) (lo hi : Vec3)
    (hw : ∀ k, 0 < w k)
    (hlo : ∀ k i, lo i ≤ P k i) (hhi : ∀ k i, P k i ≤ hi i)
    {u v : ℝ} (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) :
    Box.Mem ⟨lo, hi⟩ (ratEval w P u v) := by
  have hDpos := ratWeight_pos w hw hu0 hu1 hv0 hv1
  have hDne : ratWeight w u v ≠ 0 := ne_of_gt hDpos
  intro i
  rw [ratEval_eq_lambda w P u v hDne i]
  apply hull_of_points
  · intro k
    exact div_nonneg (mul_nonneg (bern33_nonneg hu0 hu1 hv0 hv1 k) (le_of_lt (hw k)))
      (le_of_lt hDpos)
  · exact ratLambda_sum w u v hDne
  · intro k; exact hlo k i
  · intro k; exact hhi k i


/-- A ray/patch hit for a rational (NURBS) patch. -/
def HitsRatPatchRay (o d : Vec3) (w : Fin 16 → ℝ) (P : Fin 16 → Vec3) (tmin tbest : ℝ) : Prop :=
  ∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1, ∃ t,
    tmin ≤ t ∧ t < tbest ∧ o + t • d = ratEval w P u v

/-- Soundness of accepting a rational-patch sample. -/
theorem hitsRatPatchRay_of_accept (o d : Vec3) (w : Fin 16 → ℝ) (P : Fin 16 → Vec3)
    {tmin tbest u v t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hpt : o + t • d = ratEval w P u v) :
    HitsRatPatchRay o d w P tmin tbest :=
  ⟨u, ⟨hu0, hu1⟩, v, ⟨hv0, hv1⟩, t, htmin, htbest, hpt⟩

/-- Culling soundness for the rational patch (positive weights). -/
theorem ratpatch_cull_sound (o d : Vec3) (w : Fin 16 → ℝ) (P : Fin 16 → Vec3)
    (lo hi : Vec3) (hw : ∀ k, 0 < w k)
    (hlo : ∀ k i, lo i ≤ P k i) (hhi : ∀ k i, P k i ≤ hi i) {tmin tbest : ℝ}
    (hmiss : ∀ t, tmin ≤ t → t < tbest → ¬ Box.Mem ⟨lo, hi⟩ (o + t • d)) :
    ¬ HitsRatPatchRay o d w P tmin tbest := by
  rintro ⟨u, hu, v, hv, t, htmin, htbest, hpt⟩
  apply hmiss t htmin htbest
  rw [hpt]
  exact ratEval_in_box w P lo hi hw hlo hhi hu.1 hu.2 hv.1 hv.2

/-- The rational evaluation is continuous wherever the denominator is nonzero;
    with positive weights it is continuous on the whole unit square. -/
theorem continuous_ratEval (w : Fin 16 → ℝ) (P : Fin 16 → Vec3) (hw : ∀ k, 0 < w k) :
    ContinuousOn (fun p : ℝ × ℝ => ratEval w P p.1 p.2) (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) := by
  unfold ratEval ratWeight
  apply continuousOn_pi.2
  intro i
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    unfold bern33 bern3
    fun_prop
  · apply Continuous.continuousOn
    unfold bern33 bern3
    fun_prop
  · intro p hp
    exact ne_of_gt (ratWeight_pos w hw hp.1.1 hp.1.2 hp.2.1 hp.2.2)

/-- With uniform weights the rational patch reduces to the Bézier patch. -/
theorem ratEval_const_weight (c : ℝ) (hc : c ≠ 0) (P : Fin 16 → Vec3) (u v : ℝ) :
    ratEval (fun _ => c) P u v = bicubicEval P u v := by
  ext i
  unfold ratEval ratWeight bicubicEval
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hnum : (∑ x : Fin 16, bern33 u v x * c * P x i) =
      (∑ x : Fin 16, bern33 u v x * P x i) * c := by
    calc
      (∑ x : Fin 16, bern33 u v x * c * P x i) =
          ∑ x : Fin 16, (bern33 u v x * P x i) * c := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = (∑ x : Fin 16, bern33 u v x * P x i) * c := by
        rw [Finset.sum_mul]
  have hden : (∑ x : Fin 16, bern33 u v x * c) = c := by
    rw [← Finset.sum_mul, bern33_sum, one_mul]
  rw [hnum, hden]
  exact mul_div_cancel_right₀ _ hc

end
end LightRT.Geom
