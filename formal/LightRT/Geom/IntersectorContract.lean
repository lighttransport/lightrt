/-
  Abstract intersector contracts (M15/M16) over R: sampled acceptance is
  sound, and tracing / adaptive search never misses the nearest hit.
  Composes the existing M14 first-contact chain (curves) and the patch
  subdivision-plus-Newton results (surfaces). Tier 1 item 3 of the roadmap.
-/
import Mathlib
import LightRT.Geom.BezFirstContact
import LightRT.Geom.BezCurveReal
import LightRT.Geom.BezPatchConvergence
import LightRT.Geom.BezPatchSubdivision
import LightRT.Geom.BilinearSurface
import LightRT.Geom.NURBSReal
import LightRT.Geom.Trim

namespace LightRT.Geom
noncomputable section
open Filter Topology

/-! ### Curves (M15) -/

/-- **Curve intersector contract, soundness.** A sampled-accepted contact on
    a cubic-Bezier curve is a genuine tube hit. -/
theorem curve_contract_sound (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u) (sites : List ℝ)
    (hsites : ∀ u ∈ sites, u ∈ Set.Icc a b) (hne : sites ≠ [])
    {x₀ v : EuclideanSpace ℝ (Fin 3)} {tmin tbest t : ℝ}
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hsam : samDist S sites (x₀ + t • v) ≤ 0) :
    HitsBezCurveRay S a b tmin tbest x₀ v t :=
  bezCurve_hit_of_sampled_accept S hab hrad sites hsites hne htmin htbest hsam

/-- **Curve intersector contract, no missed nearest.** The exact-distance
    trace from a start before the root never steps past it. -/
theorem curve_contract_no_missed (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u)
    {x₀ v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ ≤ 1)
    {t₀ root : ℝ} (hstart : t₀ ≤ root)
    (hroot : bezPhiMin S (x₀ + root • v) a b ≤ 0) (n : ℕ) :
    stTrace (fun s => Metric.infDist (x₀ + s • v) (bezTubeSet S a b)) t₀ n ≤ root :=
  bez_first_contact_no_missed_exact S hab hrad hv hstart hroot n

/-- **Curve intersector contract, completeness.** If the ray starts outside
    the tube and enters later, a boundary contact exists in between. -/
theorem curve_contract_complete (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u)
    {x₀ v : EuclideanSpace ℝ (Fin 3)} {t₀ root : ℝ} (ht : t₀ < root)
    (hout : 0 < Metric.infDist (x₀ + t₀ • v) (bezTubeSet S a b))
    (hin : Metric.infDist (x₀ + root • v) (bezTubeSet S a b) ≤ 0) :
    ∃ s ∈ Set.Icc t₀ root, x₀ + s • v ∈ bezTubeSet S a b :=
  bezCurve_complete S hab hrad ht hout hin

/-! ### Surfaces (M16) -/

/-- **Surface intersector contract, soundness.** A contact-zero sample on a
    bicubic-Bezier patch is a genuine patch hit. -/
theorem surface_contract_sound (o d : Vec3) (cp : Fin 16 → Vec3)
    {tmin tbest u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (htmin : tmin ≤ t) (htbest : t < tbest)
    (hres : bezPatchContact o d cp t u v = 0) :
    HitsBezPatchRay o d cp tmin tbest :=
  newton_patch_hit_of_contact_zero o d cp hu0 hu1 hv0 hv1 htmin htbest hres

/-- **Surface intersector contract, no missed nearest.** A converged patch
    contact is no nearer than the nearest patch hit. -/
theorem surface_contract_no_missed (o d : Vec3) (cp : Fin 16 → Vec3)
    {tmin tbest u v t : ℝ} (hab : tmin ≤ tbest)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hres : bezPatchContact o d cp t u v = 0) :
    ∃ tstar, tstar ∈ Set.Icc tmin tbest ∧
      (∃ u' ∈ Set.Icc (0:ℝ) 1, ∃ v' ∈ Set.Icc (0:ℝ) 1,
        o + tstar • d = bicubicEval cp u' v') ∧
      (∀ s, s ∈ Set.Icc tmin tbest →
        (∃ u' ∈ Set.Icc (0:ℝ) 1, ∃ v' ∈ Set.Icc (0:ℝ) 1,
          o + s • d = bicubicEval cp u' v') → tstar ≤ s) ∧
      tstar ≤ t :=
  newton_patch_contact_ge_nearest o d cp hab hu0 hu1 hv0 hv1 htmin htbest hres

/-- **Surface intersector contract, nearest-existence.** A hit on a patch
    implies a minimal hit parameter exists. -/
theorem surface_contract_nearest_exists (o d : Vec3) (cp : Fin 16 → Vec3)
    {tmin tbest : ℝ} (hab : tmin ≤ tbest)
    (hhit : HitsBezPatchRay o d cp tmin tbest) :
    ∃ tstar, (∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1,
              o + tstar • d = bicubicEval cp u v) ∧
      tmin ≤ tstar ∧ tstar ≤ tbest ∧
      (∀ t, tmin ≤ t → t ≤ tbest →
        (∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1,
          o + t • d = bicubicEval cp u v) → tstar ≤ t) :=
  bezpatch_exists_nearest_hit o d cp hab hhit


/-! ### Bilinear / NURBS / trimmed surfaces -/

/-- **Bilinear-patch contract, soundness.** -/
theorem bilinear_contract_sound {o d q00 q10 q11 q01 : Vec3} {tmin tbest t u v : ℝ}
    (h : bilinReal o d q00 q10 q11 q01 tmin tbest = some (t, u, v)) :
    HitsBilinearAt o d q00 q10 q11 q01 tmin tbest t :=
  bilinReal_sound h

/-- **Bilinear-patch contract, completeness.** A genuine hit in generic
    position is found. -/
theorem bilinear_contract_complete {o d q00 q10 q11 q01 : Vec3} {tmin tbest t u v : ℝ}
    (hA : (q10 - q00) ⬝ᵥ crossProduct d (q11 - q10 - q01 + q00) ≠ 0)
    (hden : 0 < (crossProduct d (q01 - q00 + u • (q11 - q10 - q01 + q00))) ⬝ᵥ
      (crossProduct d (q01 - q00 + u • (q11 - q10 - q01 + q00))))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hpt : o + t • d = bilinEval q00 q10 q11 q01 u v) :
    ∃ t' u' v', bilinReal o d q00 q10 q11 q01 tmin tbest = some (t', u', v') :=
  bilinReal_complete hA hden hu0 hu1 hv0 hv1 htmin htbest hpt

/-- **Rational (NURBS) patch contract, soundness.** -/
theorem ratpatch_contract_sound (o d : Vec3) (w : Fin 16 → ℝ) (P : Fin 16 → Vec3)
    {tmin tbest : ℝ} (h : HitsRatPatchRay o d w P tmin tbest) :
    ∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1, ∃ t,
      tmin ≤ t ∧ t < tbest ∧ o + t • d = ratEval w P u v := h

/-- **Rational (NURBS) patch contract, nearest-hit existence.** -/
theorem ratpatch_contract_nearest (o d : Vec3) (w : Fin 16 → ℝ) (P : Fin 16 → Vec3)
    (hw : ∀ k, 0 < w k) {tmin tbest : ℝ} (hab : tmin ≤ tbest)
    (hhit : HitsRatPatchRay o d w P tmin tbest) :
    ∃ tstar, (∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1,
              o + tstar • d = ratEval w P u v) ∧
      tmin ≤ tstar ∧ tstar ≤ tbest ∧
      (∀ t, tmin ≤ t → t ≤ tbest →
        (∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1,
          o + t • d = ratEval w P u v) → tstar ≤ t) :=
  ratpatch_exists_nearest_hit o d w P hw hab hhit

/-- **Trimmed-NURBS contract.** If a finite scan of rational-patch hits with
    (u,v) trim visibility returns `t`, then `t` is a genuine visible trimmed
    hit and is minimal among visible hits in the list. -/
theorem trimmed_contract_spec (o d : Vec3) (w : Fin 16 → ℝ) (P : Fin 16 → Vec3)
    (R : TrimRegion) {tmin tbest : ℝ}
    (hits : List (ℝ × ℝ × ℝ))
    (hparam : ∀ u v t, (u, v, t) ∈ hits → tmin ≤ t ∧ t < tbest ∧
      o + t • d = ratEval w P u v)
    {t : ℝ} (hscan : nearestVisibleT R hits = some t) :
    (∃ u v, (u, v, t) ∈ hits ∧ trimVisible R u v) ∧
    (∀ t', (∃ u v, (u, v, t') ∈ hits ∧ trimVisible R u v) → t ≤ t') ∧
    (∃ u v, o + t • d = ratEval w P u v) := by
  have hs := nearestVisibleT_spec R hits hscan
  rcases hs.1 with ⟨u, v, hmem, hvis⟩
  have hp := hparam u v t hmem
  exact ⟨⟨u, v, hmem, hvis⟩, hs.2, ⟨u, v, hp.2.2⟩⟩

end
end LightRT.Geom
