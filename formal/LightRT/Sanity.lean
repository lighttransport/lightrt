/-
  Specification sanity checks (see PLAN.md §4): every main theorem's
  hypothesis set is satisfiable, and its conclusion is not trivially true.
  These are `example`s, so they cost nothing at use sites but break the build
  if a spec edit makes hypotheses contradictory or conclusions vacuous.
-/
import LightRT

namespace LightRT.Sanity
open LightRT.Geom LightRT.FP LightRT.Robust

/-- A concrete ray that geometrically hits a concrete box (premise of
    `slab_no_false_miss` is inhabited). -/
example : HitsBox ⟨0, fun _ => 1, 0, 10⟩ ⟨fun _ => 1, fun _ => 2⟩ :=
  ⟨1, by norm_num, by norm_num, fun i => by simp [Ray.at]⟩

/-- …and one that misses (so `HitsBox` is not trivially true). -/
example : ¬ HitsBox ⟨0, fun _ => 1, 0, 10⟩ ⟨fun _ => -2, fun _ => -1⟩ := by
  rintro ⟨t, ht0, -, hm⟩
  have := (hm 0).2
  simp [Ray.at] at this
  linarith

/-- `Accept` (Woop) is neither always true nor always false. -/
example : Accept ((1 : ℝ), (1 : ℝ), (1 : ℝ)) := ⟨Or.inl ⟨by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
example : ¬ Accept ((1 : ℝ), (-1 : ℝ), (1 : ℝ)) := by
  rintro ⟨h | h, -⟩ <;> norm_num at h

/-- The rounding-model class is consistent (non-vacuous). -/
example : ∃ R : RoundingModel, R.u = 2⁻¹ :=
  ⟨RoundingModel.exact 2⁻¹ (by norm_num) (by norm_num), rfl⟩

/-- The containment invariant is not trivial: a leaf whose box misses its prim fails it. -/
example : ¬ BVH.Tree.Contains (fun (_ : Unit) => (⟨fun _ => 0, fun _ => 1⟩ : Box))
    (.leaf ⟨fun _ => 2, fun _ => 3⟩ [()]) := by
  intro h
  have := (h () (by simp) 0).1
  norm_num at this


/-- The radius data for M14's Newton convergence theorem is satisfiable
    (non-vacuity of `exists_radius_of_data` / `newtonIter_tendsto_of_root_data`). -/
example : ∃ R > 0, (1:ℝ) * R ≤ 1 ∧
    4 * 0 * 1 * R + 4 * ((1:ℝ) * R)^2 ≤ 100/2 ∧
    2 * (0 + 1*R + 1)^2 / (100/2) < 1 ∧
    2 * (0 + 1*R + 1)^2 / (100/2) + 18 * (0 + 1*R + 1) * 1 / (100/2) * R < 1 := by
  exact LightRT.Geom.BezSys.exists_radius_of_data 1 0 100 (by norm_num) (by norm_num) (by norm_num)

end LightRT.Sanity
