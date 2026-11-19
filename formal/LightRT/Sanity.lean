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


/-- Bilinear completeness' nondegeneracy hypothesis is satisfiable: a flat
    unit patch in z=0 and a ray along +z gives a positive ruling denominator. -/
example : ∃ (d q00 q01 q11 : Vec3) (u : ℝ),
    0 < (crossProduct d (q01 - q00 + u • (q11 - (fun i => if i = 0 then 1 else 0) - q01 + q00))) ⬝ᵥ
      (crossProduct d (q01 - q00 + u • (q11 - (fun i => if i = 0 then 1 else 0) - q01 + q00))) := by
  let d : Vec3 := fun i => if i = 2 then 1 else 0
  let q00 : Vec3 := fun i => 0
  let q10 : Vec3 := fun i => if i = 0 then 1 else 0
  let q11 : Vec3 := fun i => if i = 0 then 1 else if i = 1 then 1 else 0
  let q01 : Vec3 := fun i => if i = 1 then 1 else 0
  refine ⟨d, q00, q01, q11, 0.5, ?_⟩
  norm_num [d, q00, q10, q11, q01, crossProduct, dotProduct, Fin.sum_univ_three]


/-- Bicubic patch evaluation is non-vacuous: the corner control point is
    attained at (u,v)=(0,0). -/
example : ∃ (cp : Fin 16 → Vec3) (u v : ℝ),
    bicubicEval cp u v = cp 0 := by
  refine ⟨fun _ => 0, 0, 0, ?_⟩
  simp [bicubicEval, LightRT.Geom.Hull.bern33, LightRT.Geom.Hull.bern3]


/-- Culling completeness is non-vacuous: the corner control point is in its
    own control box, so a ray hitting it also hits the box. -/
example : ∃ (o d : Vec3) (cp : Fin 16 → Vec3) (lo hi : Vec3) (tmin tbest : ℝ),
    HitsBezPatchRay o d cp tmin tbest ∧
    (∀ k i, lo i ≤ cp k i) ∧ (∀ k i, cp k i ≤ hi i) := by
  let cp : Fin 16 → Vec3 := fun _ => 0
  refine ⟨0, 0, cp, 0, 0, 0, 10, ?_, ?_, ?_⟩
  · refine ⟨0, by norm_num, 0, by norm_num, 0, by norm_num, by norm_num, ?_⟩
    simp [bicubicEval, LightRT.Geom.Hull.bern33, LightRT.Geom.Hull.bern3, cp]
  · intro k i; simp [cp]
  · intro k i; simp [cp]


/-- de Casteljau row split is non-vacuous: splitting at t=0 reproduces the
    full curve (bez3Vec (splitLVec P 0) s = bez3Vec P (0*s)). -/
example : ∃ (P : Fin 4 → Vec3) (s : ℝ),
    bez3Vec (splitLVec P 0) s = bez3Vec P (0 * s) := by
  refine ⟨fun _ => 0, 0.5, ?_⟩
  exact bez3Vec_decasteljau_left (fun _ => 0) 0 0.5


/-- Full tensor de Casteljau split is non-vacuous: splitting at t=1 gives the
    full patch, and splitting at t=0 gives the corner. -/
example : ∃ (cp : Fin 16 → Vec3) (s v : ℝ),
    bicubicEval (splitBicubicU cp 1) s v = bicubicEval cp (1 * s) v := by
  refine ⟨fun _ => 0, 0.5, 0.5, ?_⟩
  exact bicubic_split_left (fun _ => 0) 1 0.5 0.5


/-- Nearest-hit existence is non-vacuous: the degenerate zero patch hit by the
    zero ray at t=0.5 has a minimal hit parameter. -/
example : ∃ tstar, (0:ℝ) ≤ tstar ∧ tstar ≤ 1 ∧
    (∀ t, (0:ℝ) ≤ t → t ≤ 1 →
      (∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1,
        (0:Vec3) + t • (0:Vec3) = bicubicEval (fun _ => (0:Vec3)) u v) → tstar ≤ t) := by
  have hhit : HitsBezPatchRay (0:Vec3) (0:Vec3) (fun _ => (0:Vec3)) 0 1 := by
    refine ⟨0, by norm_num, 0, by norm_num, 0.5, by norm_num, by norm_num, ?_⟩
    simp [bicubicEval, LightRT.Geom.Hull.bern33, LightRT.Geom.Hull.bern3]
  obtain ⟨tstar, _, hlo, hhi, hmin⟩ :=
    bezpatch_exists_nearest_hit (0:Vec3) (0:Vec3) (fun _ => (0:Vec3)) (by norm_num) hhit
  exact ⟨tstar, hlo, hhi, hmin⟩


/-- Newton contact bridge is non-vacuous: a zero residual at (u,v,t)=(0,0,0.5)
    on the zero patch is a genuine patch hit with t >= the nearest hit. -/
example : ∃ t, (0:ℝ) ≤ t ∧ t ≤ 1 ∧ ∃ tstar : ℝ, tstar ≤ t := by
  have hres : bezPatchContact (0:Vec3) (0:Vec3) (fun _ => (0:Vec3)) 0.5 0 0 = 0 := by
    simp [bezPatchContact, bicubicEval, LightRT.Geom.Hull.bern33, LightRT.Geom.Hull.bern3]
  have hge := newton_patch_contact_ge_nearest (0:Vec3) (0:Vec3) (fun _ => (0:Vec3))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num : (0:ℝ) ≤ 0.5) (by norm_num : (0.5:ℝ) < 1) hres
  rcases hge with ⟨tstar, htstar, hsh, hmin, hlet⟩
  exact ⟨0.5, by norm_num, by norm_num, tstar, hlet⟩


/-- The patch Newton instantiation is usable: at a root, the contraction bound
    gives zero error (via newton2Step_at_root and the quadratic theorem's shape). -/
example : ∃ (o d : Vec3) (cp : Fin 16 → Vec3) (t : ℝ),
    o + (0:ℝ) • d = bicubicEval cp 0 0 →
    newton2Step (patchF o d cp t) (patchG o d cp t) 0 0 = (0, 0) := by
  refine ⟨0, 0, fun _ => 0, 0, ?_⟩
  intro _
  apply newton2Step_at_root <;>
    simp [patchF, patchG, bezPatchContact, bicubicEval,
      LightRT.Geom.Hull.bern33, LightRT.Geom.Hull.bern3]


/-- The patch partial formulas are non-vacuous: on the zero patch the u-partial
    of patchF vanishes. -/
example (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) (hM : ∀ k i, cp k i = 0) :
    pd1 (patchF o d cp t) u v = (bicubicEval_du cp u v) 0 := by
  exact pd1_patchF o d cp t u v


/-- The patch C2Seg constructors are non-vacuous: the zero control net (M = 1)
    supplies a valid C2Seg for patchF and patchG with K = 192. -/
example (o d : Vec3) (t : ℝ) :
    C2Seg (patchF o d (fun _ : Fin 16 => (0 : Vec3)) t) 0 1 0 1 192 := by
  simpa using patchF_C2Seg o d (fun _ : Fin 16 => (0 : Vec3)) t 1 (by simp) (by norm_num)

example (o d : Vec3) (t : ℝ) :
    C2Seg (patchG o d (fun _ : Fin 16 => (0 : Vec3)) t) 0 1 0 1 192 := by
  simpa using patchG_C2Seg o d (fun _ : Fin 16 => (0 : Vec3)) t 1 (by simp) (by norm_num)


/-- The rational patch point lies in the control-net box (non-vacuous with
    positive weights), and uniform weights recover the Bézier patch. -/
example (P : Fin 16 → Vec3) (lo hi : Vec3)
    (hw : ∀ k : Fin 16, (1 : ℝ) > 0)
    (hlo : ∀ k i, lo i ≤ P k i) (hhi : ∀ k i, P k i ≤ hi i)
    {u v : ℝ} (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) :
    Box.Mem ⟨lo, hi⟩ (ratEval (fun _ => (1:ℝ)) P u v) := by
  exact ratEval_in_box (fun _ => (1:ℝ)) P lo hi hw hlo hhi hu0 hu1 hv0 hv1

example (P : Fin 16 → Vec3) (u v : ℝ) :
    ratEval (fun _ => (1:ℝ)) P u v = bicubicEval P u v := by
  exact ratEval_const_weight 1 one_ne_zero P u v


/-- Rational-patch nearest-hit existence is non-vacuous: the zero net with a
    zero ray at t=0.5 has a minimal hit parameter. -/
example : ∃ tstar, (0:ℝ) ≤ tstar ∧ tstar ≤ 1 ∧
    (∀ t, (0:ℝ) ≤ t → t ≤ 1 →
      (∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1,
        (0:Vec3) + t • (0:Vec3) =
          ratEval (fun _ : Fin 16 => (1:ℝ)) (fun _ : Fin 16 => (0:Vec3)) u v) → tstar ≤ t) := by
  have hhit : HitsRatPatchRay (0:Vec3) (0:Vec3)
      (fun _ : Fin 16 => (1:ℝ)) (fun _ : Fin 16 => (0:Vec3)) 0 1 := by
    refine ⟨0, by norm_num, 0, by norm_num, 0.5, by norm_num, by norm_num, ?_⟩
    simp [ratEval_zero_P (fun _ : Fin 16 => (1:ℝ)) (fun _ => by norm_num)]
  obtain ⟨tstar, _, hlo, hhi, hmin⟩ :=
    ratpatch_exists_nearest_hit (0:Vec3) (0:Vec3)
      (fun _ : Fin 16 => (1:ℝ)) (fun _ : Fin 16 => (0:Vec3))
      (fun _ => by norm_num) (by norm_num) hhit
  exact ⟨tstar, hlo, hhi, hmin⟩


/-- The c2lean sqrtf model is non-vacuous and matches the ISA on sample points:
    sqrt(1)=1, sqrt(2) nearest-even, sqrt(-0)=-0, sqrt(-inf)=default NaN. -/
example : LightRT.FP.Binary32.sqrtBits 0x3f800000 = 0x3f800000 := by decide +kernel
example : LightRT.FP.Binary32.sqrtBits 0x40000000 = 0x3fb504f3 := by decide +kernel
example : LightRT.FP.Binary32.sqrtBits 0x80000000 = 0x80000000 := by decide +kernel
example : LightRT.FP.Binary32.sqrtBits 0xff800000 = 0xffc00000 := by decide +kernel
example : LightRT.C.Ref.sqrt 0x40000000 = 0x3fb504f3 := by decide +kernel


/-- Patch Newton iteration is well-defined and non-trivial: the seed is the
    zeroth iterate, and the first iterate uses the contact system's Newton step. -/
example (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    patchNewtonIter o d cp t u v 0 = (u, v) := by rfl


/-- The v-split is non-vacuous: on the zero patch it stays zero, and the
    transpose is involutive. -/
example (cp : Fin 16 → Vec3) : transposeCP (transposeCP cp) = cp := by
  exact transposeCP_involutive cp
example : bicubicEval (splitBicubicV (fun _ : Fin 16 => (0 : Vec3)) (1/2 : ℝ)) 0 0 = 0 := by
  rw [bicubic_split_v_left]
  simp [bicubicEval, LightRT.Geom.Hull.bern33, LightRT.Geom.Hull.bern3]


/-- Subdivision cell representation and cull safety are non-vacuous: the root
    cell represents its own patch. -/
example (cp : Fin 16 → Vec3) : Represents cp ⟨0, 1, 0, 1, cp⟩ := by
  exact root_represents cp

end LightRT.Sanity
