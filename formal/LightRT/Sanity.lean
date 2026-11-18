/-
  Specification sanity checks (see PLAN.md §4): every main theorem's
  hypothesis set is satisfiable, and its conclusion is not trivially true.
  These are `example`s, so they cost nothing at use sites but break the build
  if a spec edit makes hypotheses contradictory or conclusions vacuous.
-/
import LightRT

namespace LightRT.Sanity
open LightRT.Geom LightRT.FP LightRT.Robust
open Filter Topology

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


/-- `ofCubicK` is positive whenever the ray direction has a nonzero lane
    and the length floor is positive (non-vacuity of `ofCubicK_pos`, hence of
    `ofCubic_newton_tendsto_of_control_points`'s `K > 0` data). -/
example : 0 < LightRT.Geom.ofCubicK
    (fun _ _ => (0:ℝ)) (fun _ : Fin 3 => (1:ℝ)) 1 2 := by
  apply LightRT.Geom.ofCubicK_pos
  · norm_num
  · norm_num [LightRT.Geom.dSup, Finset.sup']

/-- `ofCubicB0` is nonnegative (it bounds absolute values of partials). -/
example : 0 ≤ LightRT.Geom.ofCubicB0
    (fun _ _ => (0:ℝ)) (fun _ : Fin 3 => (1:ℝ)) 0 1 := by
  have hlen : 0 < (LightRT.Geom.BezSys.ofCubic (fun _ _ => (0:ℝ)) (fun _ : Fin 3 => (1:ℝ))).q 0 1 := by
    norm_num [LightRT.Geom.BezSys.q, LightRT.Geom.BezSys.Rx, LightRT.Geom.BezSys.Ry,
      LightRT.Geom.BezSys.Rz, LightRT.Geom.BezSys.ofCubic, LightRT.Geom.bezP]
  exact (LightRT.Geom.ofCubic_root_data_B0 (fun _ _ => (0:ℝ)) (fun _ : Fin 3 => (1:ℝ)) 0 1
    (by constructor <;> norm_num) hlen).1


/-- The sphere hit predicate is satisfiable (a ray from the origin along +x
    hits the unit sphere centred at (2,0,0) at t=1). -/
example : HitsSphereAt (fun _ => (0:ℝ)) (fun i => if i = 0 then 1 else 0)
    (fun i => if i = 0 then 2 else 0) 1 0 10 1 := by
  unfold HitsSphereAt OnSphere distSq
  norm_num [dotProduct, Fin.sum_univ_three]


/-- The ray-facing disc hit predicate is satisfiable (origin ray along +x,
    centre (2,0,0), radius 1: hits at t=2). -/
example : HitsRayDiscAt (fun _ => (0:ℝ)) (fun i => if i = 0 then 1 else 0)
    (fun i => if i = 0 then 2 else 0) 1 0 10 2 := by
  norm_num [HitsRayDiscAt, OnRayDisc, distSq, dotProduct, Fin.sum_univ_three]


/-- The cylinder-side hit predicate is satisfiable: ray from the origin along
    +x hits the radius-1 cylinder of axis (2,-1,0)->(2,1,0) at t=3. -/
example : HitsCylinderSideAt (fun _ => (0:ℝ)) (fun i => if i = 0 then 1 else 0)
    (fun i => if i = 0 then 2 else if i = 1 then -1 else 0)
    (fun i => if i = 0 then 2 else if i = 1 then 1 else 0) 1 0 10 3 := by
  norm_num [HitsCylinderSideAt, OnCylinderSide, perpSq, perpTo, dotProduct, Fin.sum_univ_three]


/-- The ellipse point predicate is satisfiable: a ray from origin along +x
    hits the ellipse centred at (2,0,0), normal +x, axes +y/+z (ru=rv=1)
    at t=2. -/
example : HitsEllipseAt (fun _ => (0:ℝ)) (fun i => if i = 0 then 1 else 0)
    (fun i => if i = 0 then 2 else 0)
    (fun i => if i = 0 then 1 else 0)
    (fun i => if i = 1 then 1 else 0)
    (fun i => if i = 2 then 1 else 0) 1 1 0 10 2 := by
  norm_num [HitsEllipseAt, OnEllipse, dotProduct, Fin.sum_univ_three]


/-- `HitsBezTubeRay` is satisfiable: the zero-direction ray from the curve's
    start point lies in the tube at the start parameter. -/
example : ∃ (S : LightRT.Geom.BezSys) (a b tmin tbest : ℝ),
    a ≤ b ∧ tmin ≤ 0 ∧ 0 < tbest ∧
    LightRT.Geom.HitsBezTubeRay S a b tmin tbest
      (LightRT.Geom.curvePt S a) (0 : EuclideanSpace ℝ (Fin 3)) := by
  let S : LightRT.Geom.BezSys := LightRT.Geom.BezSys.ofCubic
    (fun _ _ => (0:ℝ)) (fun _ : Fin 3 => (1:ℝ))
  refine ⟨S, 0, 1, -1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  refine ⟨0, by norm_num, by norm_num, ?_⟩
  have hrad : ∀ u ∈ Set.Icc (0:ℝ) 1, 0 ≤ S.rad u := by
    intro u hu
    simp [S, LightRT.Geom.BezSys.ofCubic, LightRT.Geom.bezP]
  have hphi : LightRT.Geom.bezPhi S (LightRT.Geom.curvePt S 0) 0 ≤ 0 := by
    simp [S, LightRT.Geom.curvePt, LightRT.Geom.BezSys.ofCubic,
      LightRT.Geom.bezP, LightRT.Geom.bezPhi, LightRT.Geom.bezQ]
  simpa using LightRT.Geom.mem_bezTubeSet_of_bezPhi_le S
    (LightRT.Geom.curvePt S 0) hrad (by norm_num : (0:ℝ) ∈ Set.Icc 0 1) hphi


/-- Sphere-trace convergence is non-vacuous: for `f t = 1 - t` on `[0,1]`,
    the trace from 0 converges to the contact at 1. -/
example : ∃ L ≤ (1:ℝ), Tendsto (fun n => stTrace (fun t : ℝ => 1 - t) 0 n) atTop (𝓝 L) ∧
    (1 - L) = 0 := by
  have hf : Lipschitz1 (fun t : ℝ => 1 - t) := by
    intro x y
    have heq : (1 - x) - (1 - y) = y - x := by ring
    rw [heq, abs_sub_comm]
  have hnonneg : ∀ s, (0:ℝ) ≤ s → s ≤ 1 → 0 ≤ 1 - s := by
    intro s h0 h1; linarith
  exact stTrace_tendsto_contact hf (by norm_num : 1 - (1:ℝ) ≤ 0) (by norm_num : (0:ℝ) ≤ 1) hnonneg


/-- The bilinear surface predicate is non-vacuous: (u,v)=(0,0) gives q00. -/
example : ∃ (q00 q10 q11 q01 p : Vec3), OnBilinearSurface q00 q10 q11 q01 p := by
  refine ⟨0, 0, 0, 0, 0, 0, by norm_num, 0, by norm_num, ?_⟩
  simp [bilinEval]

end LightRT.Sanity
