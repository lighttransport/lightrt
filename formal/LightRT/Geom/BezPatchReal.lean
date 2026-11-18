/-
  Bicubic Bezier patch over R (`tri_bezpatch_eval` / `tri_bezpatch_isect_one`):
  tensor Bernstein evaluation, control-hull containment, continuity and u
  partial derivative, ray/patch hit soundness, and culling soundness (a ray
  missing the control hull cannot hit the patch). Tier 1 item 1 (parametric
  surfaces), building on `Geom/Hull.lean`.
-/
import Mathlib
import LightRT.Geom.Hull
import LightRT.Geom.Basic

namespace LightRT.Geom
noncomputable section
open Matrix
open LightRT.Geom.Hull

/-- Tensor-product bicubic Bézier patch evaluation: `Σ_k B(u,v,k) · cp k`. -/
def bicubicEval (cp : Fin 16 → Vec3) (u v : ℝ) : Vec3 :=
  ∑ k : Fin 16, bern33 u v k • cp k

/-- Every coordinate of a patch point lies in the box of the control points. -/
theorem bicubicEval_in_box (cp : Fin 16 → Vec3) (lo hi : Vec3)
    (hlo : ∀ k i, lo i ≤ cp k i) (hhi : ∀ k i, cp k i ≤ hi i)
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Box.Mem ⟨lo, hi⟩ (bicubicEval cp u v) := by
  intro i
  have h := bicubic_in_box (fun k => cp k i) u v (lo i) (hi i) hu0 hu1 hv0 hv1
    (fun k => hlo k i) (fun k => hhi k i)
  constructor
  · simpa [bicubicEval, dotProduct] using h.1
  · simpa [bicubicEval, dotProduct] using h.2

/-- A ray/patch hit: some `(u,v)` in the unit square and `t` in range with the
    ray point on the patch. -/
def HitsBezPatchRay (o d : Vec3) (cp : Fin 16 → Vec3) (tmin tbest : ℝ) : Prop :=
  ∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1, ∃ t,
    tmin ≤ t ∧ t < tbest ∧ o + t • d = bicubicEval cp u v

/-- Soundness of accepting a Newton-refined sample: the reported parameter
    gives a genuine patch hit. -/
theorem hitsBezPatchRay_of_accept (o d : Vec3) (cp : Fin 16 → Vec3) {tmin tbest u v t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hpt : o + t • d = bicubicEval cp u v) :
    HitsBezPatchRay o d cp tmin tbest :=
  ⟨u, ⟨hu0, hu1⟩, v, ⟨hv0, hv1⟩, t, htmin, htbest, hpt⟩

/-- Culling soundness: if every ray point in range misses the control-point
    hull, the ray misses the patch (no false cull). -/
theorem bezpatch_cull_sound (o d : Vec3) (cp : Fin 16 → Vec3) (lo hi : Vec3)
    (hlo : ∀ k i, lo i ≤ cp k i) (hhi : ∀ k i, cp k i ≤ hi i) {tmin tbest : ℝ}
    (hmiss : ∀ t, tmin ≤ t → t < tbest → ¬ Box.Mem ⟨lo, hi⟩ (o + t • d)) :
    ¬ HitsBezPatchRay o d cp tmin tbest := by
  rintro ⟨u, hu, v, hv, t, htmin, htbest, hpt⟩
  apply hmiss t htmin htbest
  rw [hpt]
  exact bicubicEval_in_box cp lo hi hlo hhi hu.1 hu.2 hv.1 hv.2


/-- The bicubic patch evaluation is continuous in (u,v). -/
theorem continuous_bicubicEval (cp : Fin 16 → Vec3) :
    Continuous (fun p : ℝ × ℝ => bicubicEval cp p.1 p.2) := by
  unfold bicubicEval bern33 bern3
  fun_prop

/-- Derivative of a cubic Bernstein weight. -/
def bern3' (t : ℝ) (k : Fin 4) : ℝ :=
  match k with
  | ⟨0, _⟩ => -3 * (1 - t) ^ 2
  | ⟨1, _⟩ => 3 * (1 - t) ^ 2 - 6 * (1 - t) * t
  | ⟨2, _⟩ => 6 * (1 - t) * t - 3 * t ^ 2
  | ⟨_, _⟩ => 3 * t ^ 2

theorem hasDerivAt_bern3 (t : ℝ) (k : Fin 4) :
    HasDerivAt (fun t => bern3 t k) (bern3' t k) t := by
  fin_cases k
  · convert (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 3) using 1
    · ext x <;> simp [bern3, Pi.sub_apply, Pi.pow_apply, id_eq] <;> ring_nf
    · change (-3 * (1 - t)^2) = _
      simp [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring_nf
  · convert ((hasDerivAt_id t).mul (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2)).const_mul 3 using 1
    · ext x <;> simp [bern3, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring_nf
    · change (3 * (1 - t)^2 - 6 * (1 - t) * t) = _
      simp [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring_nf
  · convert (((hasDerivAt_id t).pow 2).mul (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)))).const_mul 3 using 1
    · ext x <;> simp [bern3, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring_nf
    · change (6 * (1 - t) * t - 3 * t^2) = _
      simp [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring_nf
  · convert ((hasDerivAt_id t).pow 3) using 1
    · ext x <;> simp [bern3, id_eq] <;> ring_nf
    · simp [bern3', id_eq] <;> ring_nf

/-- Partial derivative of the patch with respect to u. -/
def bicubicEval_du (cp : Fin 16 → Vec3) (u v : ℝ) : Vec3 :=
  ∑ k : Fin 16, (bern3' u ⟨k.val % 4, by omega⟩ * bern3 v ⟨k.val / 4, by omega⟩) • cp k

theorem bicubicEval_hasDerivAt_u (cp : Fin 16 → Vec3) (u v : ℝ) :
    HasDerivAt (fun u => bicubicEval cp u v) (bicubicEval_du cp u v) u := by
  unfold bicubicEval bicubicEval_du bern33
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 u ⟨k.val % 4, by omega⟩).mul_const
      (bern3 v ⟨k.val / 4, by omega⟩)).smul_const (cp k))) using 1
  · ext y; simp [bern33] <;> ring_nf

theorem bezpatch_cull_complete (o d : Vec3) (cp : Fin 16 → Vec3) (lo hi : Vec3)
    (hlo : ∀ k i, lo i ≤ cp k i) (hhi : ∀ k i, cp k i ≤ hi i)
    {tmin tbest : ℝ} (hhit : HitsBezPatchRay o d cp tmin tbest) :
    ∃ t, tmin ≤ t ∧ t < tbest ∧ Box.Mem ⟨lo, hi⟩ (o + t • d) := by
  rcases hhit with ⟨u, hu, v, hv, t, htmin, htbest, hpt⟩
  refine ⟨t, htmin, htbest, ?_⟩
  rw [hpt]
  exact bicubicEval_in_box cp lo hi hlo hhi hu.1 hu.2 hv.1 hv.2

end
end LightRT.Geom
