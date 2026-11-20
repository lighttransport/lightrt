/-
  SDF primitive intersector over R: sphere-trace soundness (the limit is a
  surface point), no-overshoot (the trace never steps past a contact) and
  boundary existence, composing SphereTrace / SphereTrace3 /
  SphereTraceConvergence. Tier 1 item 1 of the roadmap.
-/
import Mathlib
import LightRT.Geom.SphereTraceConvergence
import LightRT.Geom.SphereTrace3
import LightRT.Geom.Basic
import LightRT.Geom.CapsuleReal

namespace LightRT.Geom
noncomputable section
open Filter Topology

/-- **SDF trace soundness**: the sphere-trace limit is a surface point. -/
theorem sdf_trace_sound {f : ℝ → ℝ} (hf : Lipschitz1 f)
    {root : ℝ} (hroot : f root ≤ 0) {t : ℝ} (ht : t ≤ root)
    (hnonneg : ∀ s, t ≤ s → s ≤ root → 0 ≤ f s) :
    ∃ L ≤ root, Tendsto (fun n => stTrace f t n) atTop (𝓝 L) ∧ f L = 0 :=
  stTrace_tendsto_contact hf hroot ht hnonneg

/-- **SDF no-overshoot**: for an SDF-like field along a ray with ‖v‖ ≤ 1,
    tracing never steps past a contact at `root`. -/
theorem sdf_ray_no_overshoot {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {x₀ v : X} (hv : ‖v‖ ≤ 1)
    {t₀ root : ℝ} (hstart : t₀ ≤ root)
    (hroot : x₀ + root • v ∈ S) (n : ℕ) :
    stTrace (fun s => Metric.infDist (x₀ + s • v) S) t₀ n ≤ root :=
  stTrace3_le_root S hv (le_of_eq (Metric.infDist_zero_of_mem hroot)) hstart n

/-- **SDF boundary existence**: if the ray starts outside the surface set and
    a later parameter lies in it, some intermediate parameter is on the
    boundary (infDist = 0). -/
theorem sdf_boundary_exists {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {x₀ v : X} (hv : ‖v‖ ≤ 1) {t₀ root : ℝ} (ht : t₀ < root)
    (hout : 0 < Metric.infDist (x₀ + t₀ • v) S)
    (hin : x₀ + root • v ∈ S) :
    ∃ s ∈ Set.Icc t₀ root, Metric.infDist (x₀ + s • v) S = 0 := by
  let g : ℝ → ℝ := fun s => Metric.infDist (x₀ + s • v) S
  have hcont : ContinuousOn g (Set.Icc t₀ root) :=
    (continuous_of_Lipschitz1 (lipschitz1_infDist_line S hv)).continuousOn
  have hzero : g root = 0 := Metric.infDist_zero_of_mem hin
  have hy : (0 : ℝ) ∈ Set.Icc (g root) (g t₀) := by
    constructor
    · rw [hzero]
    · simpa [g] using le_of_lt hout
  have himg := intermediate_value_Icc' (le_of_lt ht) hcont hy
  rcases himg with ⟨s, hs, hsg⟩
  exact ⟨s, hs, by simpa [g] using hsg⟩

/-- The sphere SDF `p ↦ dist p c - r` is 1-Lipschitz. -/
theorem sdfSphere_AbsLipschitz (c : Vec3) (r : ℝ) :
    AbsLipschitz (fun p : Vec3 => dist p c - r) := by
  intro x y
  have h := absLipschitz_infDist ({c} : Set Vec3) x y
  simpa [Metric.infDist_singleton] using h

/-- The sphere SDF along a ray with `‖v‖ ≤ 1` is 1-Lipschitz in the parameter. -/
theorem sdfSphere_line_lipschitz (c : Vec3) (r : ℝ) {x₀ v : Vec3} (hv : ‖v‖ ≤ 1) (t u : ℝ) :
    |(dist (x₀ + t • v) c - r) - (dist (x₀ + u • v) c - r)| ≤ |t - u| := by
  simpa [Metric.infDist_singleton] using
    (infDist_line_lipschitz ({c} : Set Vec3) hv t u)

/-- The curve-capsule intersector over ℝ is exactly the capsule model:
    a constant-radius hair segment is a capsule. Its sound/complete/nearest
    facts are `capsuleReal_sound` / `capsuleReal_complete` and the nearest-hit
    existence from compactness of the capsule section. -/
theorem crvReal_sound {o dir p0 p1 : Vec3} {r tmin tbest t : ℝ}
    (h : capsuleReal o dir p0 p1 r tmin tbest = some t) :
    HitsCapsuleAt o dir p0 p1 r tmin tbest t :=
  capsuleReal_sound h

theorem crvReal_complete {o dir p0 p1 : Vec3} {r tmin tbest t : ℝ}
    (hp0p1 : p0 ≠ p1) (hdir : perpTo dir (p1 - p0) ≠ 0)
    (hhit : HitsCapsuleAt o dir p0 p1 r tmin tbest t) :
    ∃ t', capsuleReal o dir p0 p1 r tmin tbest = some t' ∧ t' ≤ t :=
  capsuleReal_complete hp0p1 hdir hhit

end
end LightRT.Geom
