/-
  SDF primitive intersector over R: sphere-trace soundness (the limit is a
  surface point), no-overshoot (the trace never steps past a contact) and
  boundary existence, composing SphereTrace / SphereTrace3 /
  SphereTraceConvergence. Tier 1 item 1 of the roadmap.
-/
import Mathlib
import LightRT.Geom.SphereTraceConvergence
import LightRT.Geom.SphereTrace3

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

end
end LightRT.Geom
