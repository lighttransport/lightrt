/-
  Convergence of sphere tracing to the nearest contact for an SDF-like
  1-Lipschitz function. Complements `Geom/SphereTrace.lean`'s no-overshoot
  result (`stTrace_le_root`) with the limit/fixed-point half used by the
  SDF sphere-trace intersector. Tier 1 item 1 of the formalization roadmap.
-/
import Mathlib
import LightRT.Geom.SphereTrace

namespace LightRT.Geom
open Filter Topology

/-- A 1-Lipschitz real function is continuous. -/
theorem continuous_of_Lipschitz1 {f : ℝ → ℝ} (hf : Lipschitz1 f) : Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  exact lt_of_le_of_lt (by simpa [Real.dist_eq] using hf y x) hy

/-- **Sphere-trace convergence to a contact.** If `f` is 1-Lipschitz,
    nonnegative on `[t, root]`, and nonpositive at `root`, the trace started
    at `t <= root` converges to a point `L <= root` with `f L = 0`: the trace
    reaches the nearest contact without overshooting. This is the convergence
    half of the SDF sphere-trace first-contact argument (`stTrace_le_root` is
    the no-overshoot half). -/
theorem stTrace_tendsto_contact {f : ℝ → ℝ} (hf : Lipschitz1 f)
    {root : ℝ} (hroot : f root ≤ 0) {t : ℝ} (ht : t ≤ root)
    (hnonneg : ∀ s, t ≤ s → s ≤ root → 0 ≤ f s) :
    ∃ L ≤ root, Tendsto (fun n => stTrace f t n) atTop (𝓝 L) ∧ f L = 0 := by
  have hstep_le : ∀ y, y ≤ root → stStep f y ≤ root := fun y hy => stStep_le_root hf hroot hy
  have hinvar : ∀ n, t ≤ stTrace f t n ∧ stTrace f t n ≤ root := by
    intro n
    induction n with
    | zero => exact ⟨le_rfl, ht⟩
    | succ n ih =>
        have hfn : 0 ≤ f (stTrace f t n) := hnonneg _ ih.1 ih.2
        exact ⟨le_trans ih.1 (stStep_ge hfn), hstep_le _ ih.2⟩
  have hsucc : ∀ n, stTrace f t n ≤ stTrace f t (n + 1) := by
    intro n
    have hfn : 0 ≤ f (stTrace f t n) := hnonneg _ (hinvar n).1 (hinvar n).2
    exact stStep_ge hfn
  have hmono : Monotone (fun n => stTrace f t n) := monotone_nat_of_le_succ hsucc
  have hbdd : BddAbove (Set.range fun n => stTrace f t n) :=
    ⟨root, by rintro _ ⟨n, rfl⟩; exact (hinvar n).2⟩
  let L := sSup (Set.range fun n => stTrace f t n)
  have hLle : L ≤ root := csSup_le (Set.range_nonempty _) (by rintro _ ⟨n, rfl⟩; exact (hinvar n).2)
  have htend : Tendsto (fun n => stTrace f t n) atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  have htend_succ : Tendsto (fun n => stTrace f t (n + 1)) atTop (𝓝 L) :=
    htend.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun n => stTrace f t (n + 1) - stTrace f t n) atTop (𝓝 (L - L)) :=
    htend_succ.sub htend
  have hfd : Tendsto (fun n => f (stTrace f t n)) atTop (𝓝 0) := by
    have heq : (fun n => stTrace f t (n + 1) - stTrace f t n) = fun n => f (stTrace f t n) := by
      funext n
      simp [stTrace, stStep]
    simpa [heq] using hdiff
  have hcont := continuous_of_Lipschitz1 hf
  have hftend : Tendsto (fun n => f (stTrace f t n)) atTop (𝓝 (f L)) :=
    hcont.continuousAt.tendsto.comp htend
  have : f L = 0 := tendsto_nhds_unique hftend hfd
  exact ⟨L, hLle, htend, this⟩

end LightRT.Geom
