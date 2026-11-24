/-
  First-contact contract for cubic-Bézier tube intersections over ℝ: composes
  the existing `Geom/BezTube.lean` chain (sampled acceptance soundness, exact
  and sampled sphere-trace no-overshoot, boundary existence) into a single
  soundness/no-missed-nearest API for the round-Bézier curve intersector.
  Tier 1 item 1 of the formalization roadmap.
-/
import Mathlib
import LightRT.Geom.BezTube

namespace LightRT.Geom
noncomputable section

/-- A cubic-Bézier tube first-contact event along a ray segment: some
    parameter in `[tmin, tbest)` lands inside the tube. -/
def HitsBezTubeRay (S : BezSys) (a b tmin tbest : ℝ)
    (x₀ v : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ t, tmin ≤ t ∧ t < tbest ∧ x₀ + t • v ∈ bezTubeSet S a b

/-- **Sampled acceptance is sound** (first-contact contract, soundness half):
    if the sampled distance fold at a parameter in the range is nonpositive
    (the C's acceptance test) and the sample sites lie in `[a,b]`, then the
    ray point is a genuine tube point. -/
theorem hitsBezTubeRay_of_sampled_accept (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u) (sites : List ℝ)
    (hsites : ∀ u ∈ sites, u ∈ Set.Icc a b) (hne : sites ≠ [])
    {x₀ v : EuclideanSpace ℝ (Fin 3)} {t tmin tbest : ℝ}
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hsam : samDist S sites (x₀ + t • v) ≤ 0) :
    HitsBezTubeRay S a b tmin tbest x₀ v := by
  refine ⟨t, htmin, htbest, ?_⟩
  exact samDist_nonpos_mem_tube S (x₀ + t • v) hab hrad sites hsites hne hsam

/-- **No missed nearest, exact distance** (first-contact contract, completeness
    half): if the ray is inside the tube at a parameter `root` ahead of the
    trace start and the direction has norm ≤ 1, then tracing the exact signed
    distance from the start never steps past `root`. -/
theorem bez_first_contact_no_missed_exact (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u)
    {x₀ v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ ≤ 1)
    {t₀ root : ℝ} (hstart : t₀ ≤ root)
    (hroot : bezPhiMin S (x₀ + root • v) a b ≤ 0) (n : ℕ) :
    stTrace (fun s => Metric.infDist (x₀ + s • v) (bezTubeSet S a b)) t₀ n ≤ root :=
  stTrace3_bezTube_le_root S hab hrad hv hroot hstart n

/-- **No missed nearest, sampled distance**: the same guard for the C's
    sampled fold, provided the sampled distance at the contact is nonpositive
    (samples dense enough at the contact). -/
theorem bez_first_contact_no_missed_sampled (S : BezSys) (sites : List ℝ)
    {x₀ v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ ≤ 1)
    {t₀ root : ℝ} (hstart : t₀ ≤ root)
    (hroot : samDist S sites (x₀ + root • v) ≤ 0) (n : ℕ) :
    stTrace (fun s => samDist S sites (x₀ + s • v)) t₀ n ≤ root :=
  stTrace3_samDist_le_root S sites hv hroot hstart n

/-- **First-contact boundary existence**: if the trace starts strictly outside
    the tube and a later parameter touches/enters it, some parameter in between
    is exactly on the tube boundary. -/
theorem bez_first_contact_boundary (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u)
    {x₀ v : EuclideanSpace ℝ (Fin 3)} {t₀ root : ℝ} (ht : t₀ < root)
    (hout : 0 < Metric.infDist (x₀ + t₀ • v) (bezTubeSet S a b))
    (hin : Metric.infDist (x₀ + root • v) (bezTubeSet S a b) ≤ 0) :
    ∃ s ∈ Set.Icc t₀ root, x₀ + s • v ∈ bezTubeSet S a b := by
  obtain ⟨s, hs, hszero⟩ := exists_bezTube_boundary_point S ht hout hin
  refine ⟨s, hs, ?_⟩
  rw [infDist_bezTubeSet S (x₀ + s • v) hab hrad] at hszero
  have hphi : bezPhiMin S (x₀ + s • v) a b ≤ 0 :=
    (le_max_right (0:ℝ) (bezPhiMin S (x₀ + s • v) a b)).trans (le_of_eq hszero)
  obtain ⟨u, hu, hφm⟩ := bezPhiMin_eq S (x₀ + s • v) hab
  exact mem_bezTubeSet_of_bezPhi_le S (x₀ + s • v) hrad hu (hφm ▸ hphi)

end
end LightRT.Geom
