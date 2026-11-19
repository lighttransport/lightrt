/-
  Cubic-Bezier curve ray-hit API over R: soundness, completeness and nearest
  hit, composing the existing M14 BezTube / SphereTrace / BezFirstContact
  chain. Tier 1 item 1 of the roadmap.
-/
import Mathlib
import LightRT.Geom.BezFirstContact

namespace LightRT.Geom
noncomputable section
open Filter Topology

/-- A ray hit on a cubic-Bezier tube within the parameter window. -/
def HitsBezCurveRay (S : BezSys) (a b tmin tbest : ℝ)
    (x₀ v : EuclideanSpace ℝ (Fin 3)) (t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ x₀ + t • v ∈ bezTubeSet S a b

/-- **Soundness**: a sampled-accepted contact is a genuine Bezier-tube hit. -/
theorem bezCurve_hit_of_sampled_accept (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u) (sites : List ℝ)
    (hsites : ∀ u ∈ sites, u ∈ Set.Icc a b) (hne : sites ≠ [])
    {x₀ v : EuclideanSpace ℝ (Fin 3)} {tmin tbest t : ℝ}
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hsam : samDist S sites (x₀ + t • v) ≤ 0) :
    HitsBezCurveRay S a b tmin tbest x₀ v t := by
  refine ⟨htmin, htbest, ?_⟩
  exact samDist_nonpos_mem_tube S (x₀ + t • v) hab hrad sites hsites hne hsam

/-- **Completeness**: if the ray is outside the tube at `t₀` and inside at a
    later `root`, some parameter in between touches the tube boundary. -/
theorem bezCurve_complete (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u)
    {x₀ v : EuclideanSpace ℝ (Fin 3)} {t₀ root : ℝ} (ht : t₀ < root)
    (hout : 0 < Metric.infDist (x₀ + t₀ • v) (bezTubeSet S a b))
    (hin : Metric.infDist (x₀ + root • v) (bezTubeSet S a b) ≤ 0) :
    ∃ s ∈ Set.Icc t₀ root, x₀ + s • v ∈ bezTubeSet S a b :=
  bez_first_contact_boundary S hab hrad ht hout hin

/-- **Nearest hit exists**: if the hit-parameter set is closed (the tube is
    closed and the ray map continuous) and a hit exists, a minimal hit
    parameter exists. The closedness is a hypothesis, as for patches. -/
theorem bezCurve_exists_nearest_hit (S : BezSys) (a b tmin tbest : ℝ)
    (x₀ v : EuclideanSpace ℝ (Fin 3))
    (hclosed : IsClosed {t : ℝ | HitsBezCurveRay S a b tmin tbest x₀ v t})
    (hhit : ∃ t, HitsBezCurveRay S a b tmin tbest x₀ v t) :
    ∃ tstar, HitsBezCurveRay S a b tmin tbest x₀ v tstar ∧
      ∀ t, HitsBezCurveRay S a b tmin tbest x₀ v t → tstar ≤ t := by
  let H : Set ℝ := {t | HitsBezCurveRay S a b tmin tbest x₀ v t}
  have hsub : H ⊆ Set.Icc tmin tbest := by intro t ht; exact ⟨ht.1, le_of_lt ht.2.1⟩
  have hcomp : IsCompact H := (isCompact_Icc : IsCompact (Set.Icc tmin tbest)).of_isClosed_subset hclosed hsub
  have hcont : ContinuousOn (fun t : ℝ => t) H := continuous_id.continuousOn
  obtain ⟨tstar, htstarH, hmin⟩ := hcomp.exists_isMinOn hhit hcont
  exact ⟨tstar, htstarH, fun t ht => hmin ht⟩

end
end LightRT.Geom
