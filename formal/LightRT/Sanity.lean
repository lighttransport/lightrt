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


/-- The abstract no-missed theorem is non-vacuous as a statement: the root cell
    of a patch with a contact root has representing control net bounded by M. -/
example (cp : Fin 16 → Vec3) (M : ℝ) (hM : ∀ k i, |cp k i| ≤ M) :
    ∀ k i, |(⟨0, 1, 0, 1, cp⟩ : PatchCell).cp k i| ≤ M := by
  exact hM


/-- B-spline foundation for NURBS: the Bezier knot vector gives the Bernstein
    basis, partition of unity, and the Bezier curve. -/
example (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineBasis (bezKnot 3) 0 3 u + bsplineBasis (bezKnot 3) 1 3 u +
    bsplineBasis (bezKnot 3) 2 3 u + bsplineBasis (bezKnot 3) 3 3 u = 1 := by
  exact bezKnot_sum u hu0 hu1

example (P : Fin 4 → Vec3) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineCurve (bezKnot 3) (fun i => if h : i < 4 then P ⟨i, h⟩ else 0) 3 3 u =
      bez3Vec P u := by
  exact bezKnot_curve P u hu0 hu1


/-- Trim invariant is non-vacuous: a hit inside a declared hole is rejected. -/
example (R : TrimRegion) (u v : ℝ) (h : TrimLoop) (hh : h ∈ R.holes)
    (hin : inLoop h u v) : ¬ trimVisible R u v := by
  exact hole_hit_rejected R h hh hin


/-- Knot insertion foundation is non-vacuous: inserting a knot inside a span
    splits the degree-0 B-spline basis function at that span. -/
example (U : ℕ → ℝ) (k : ℕ) (u x : ℝ) (hlo : U k ≤ u) (hhi : u < U (k+1)) :
    bsplineBasis U k 0 x =
      bsplineBasis (insertKnot U k u) k 0 x + bsplineBasis (insertKnot U k u) (k+1) 0 x := by
  exact (bsplineBasis_zero_refinement U k u x hlo hhi).2.1


/-- Boehm knot insertion is non-vacuous: inserting a knot into the linear
    Bezier knot vector preserves the curve for every interior knot. -/
example (P : Fin 2 → Vec3) (t u : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineCurve (insertKnot (bezKnot 1) 1 t)
      (fun i => if h : i < 3 then boehm1 P t ⟨i, h⟩ else 0) 1 2 u =
      bsplineCurve (bezKnot 1) (fun i => if h : i < 2 then P ⟨i, h⟩ else 0) 1 1 u := by
  exact boehm1_preserves P t ht0 ht1 u hu0 hu1


/-- Bezier extraction for surfaces: rational evaluation over the Bezier knot
    vector agrees with the rational bicubic patch of NURBSReal. -/
example (w : Fin 16 → ℝ) (P : Fin 16 → Vec3) (u v : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    (fun i => (∑ k : Fin 16,
        (bsplineBasis (bezKnot 3) (k.val % 4) 3 u *
         bsplineBasis (bezKnot 3) (k.val / 4) 3 v * w k) • P k i) /
      (∑ k : Fin 16,
        bsplineBasis (bezKnot 3) (k.val % 4) 3 u *
        bsplineBasis (bezKnot 3) (k.val / 4) 3 v * w k)) = ratEval w P u v := by
  exact bezKnot_ratEval w P u v hu0 hu1 hv0 hv1


/-- Even-odd trim rule is non-vacuous: the unit-square loop contains its center. -/
example : inLoop [Prod.mk (0:ℝ) 0, Prod.mk 1 0, Prod.mk 1 1, Prod.mk 0 1] (1/2) (1/2) := by
  unfold inLoop
  exact unit_square_crossing_center


/-- Reject-and-continue is non-vacuous: an invisible hit is skipped. -/
example (R : TrimRegion) (u v t : ℝ) (hvis : ¬ trimVisible R u v)
    (hits : List (ℝ × ℝ × ℝ)) :
    nearestVisibleT R ((u,v,t)::hits) = nearestVisibleT R hits := by
  exact nearestVisibleT_skip_invisible R u v t hvis hits


/-- Round-linear and flat curve hit predicates are non-vacuous. -/
example (o d p0 p1 : Vec3) (r0 r1 tmin tbest t : ℝ)
    (h : OnRoundLinear p0 p1 r0 r1 (o + t • d)) (htmin : tmin ≤ t) (htbest : t < tbest) :
    HitsRoundLinear o d p0 p1 r0 r1 tmin tbest t :=
  hitsRoundLinear_of_sample o d p0 p1 r0 r1 tmin tbest t htmin htbest h

example (o d p0 p1 b : Vec3) (r0 r1 tmin tbest t : ℝ)
    (h : OnFlatLinear p0 p1 r0 r1 d b (o + t • d)) (htmin : tmin ≤ t) (htbest : t < tbest) :
    HitsFlatLinear o d p0 p1 r0 r1 b tmin tbest t :=
  hitsFlatLinear_of_sample o d p0 p1 r0 r1 b tmin tbest t htmin htbest h


/-- Cubic-Bezier curve hit API is non-vacuous: any ray in the tube is a hit. -/
example (S : BezSys) (a b tmin tbest : ℝ) (x₀ v : EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (h : HitsBezCurveRay S a b tmin tbest x₀ v t) :
    tmin ≤ t ∧ t < tbest := ⟨h.1, h.2.1⟩


/-- SDF sphere-trace API is non-vacuous. -/
example {f : ℝ → ℝ} (hf : Lipschitz1 f) {root t : ℝ} (hr : f root ≤ 0) (ht : t ≤ root)
    (hn : ∀ s, t ≤ s → s ≤ root → 0 ≤ f s) :
    ∃ L ≤ root, Tendsto (fun n => stTrace f t n) atTop (𝓝 L) ∧ f L = 0 :=
  sdf_trace_sound hf hr ht hn


/-- Intersector contracts are non-vacuous by composition. -/
example (o d : Vec3) (cp : Fin 16 → Vec3) {tmin tbest u v t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hres : bezPatchContact o d cp t u v = 0) :
    HitsBezPatchRay o d cp tmin tbest :=
  surface_contract_sound o d cp hu0 hu1 hv0 hv1 htmin htbest hres


/-- The swept tube sets are closed, discharging the old closedness hypothesis. -/
example (p0 p1 : Vec3) (r0 r1 : ℝ) : IsClosed {x : Vec3 | OnRoundLinear p0 p1 r0 r1 x} :=
  isClosed_roundLinearTube p0 p1 r0 r1

example (p0 p1 b : Vec3) (r0 r1 : ℝ) : IsClosed {x : Vec3 | OnFlatLinear p0 p1 r0 r1 p0 b x} :=
  isClosed_flatLinearTube p0 p1 b r0 r1

/-- Round/flat nearest-hit existence no longer needs a closedness hypothesis. -/
example (o d p0 p1 : Vec3) (r0 r1 tmin tbest : ℝ)
    (hh : ∃ t, HitsRoundLinear o d p0 p1 r0 r1 tmin tbest t) :
    ∃ tstar, HitsRoundLinear o d p0 p1 r0 r1 tmin tbest tstar ∧
      ∀ t, HitsRoundLinear o d p0 p1 r0 r1 tmin tbest t → tstar ≤ t :=
  roundLinear_exists_nearest_hit o d p0 p1 r0 r1 tmin tbest hh

/-- Cubic-Bezier nearest-hit existence no longer needs a closedness hypothesis. -/
example (S : BezSys) (a b tmin tbest : ℝ) (x₀ v : EuclideanSpace ℝ (Fin 3))
    (hh : ∃ t, HitsBezCurveRay S a b tmin tbest x₀ v t) :
    ∃ tstar, HitsBezCurveRay S a b tmin tbest x₀ v tstar ∧
      ∀ t, HitsBezCurveRay S a b tmin tbest x₀ v t → tstar ≤ t :=
  bezCurve_exists_nearest_hit S a b tmin tbest x₀ v hh


/-- The nearest-visible-trim scan is non-vacuous: a visible hit makes the scan
    return that hit's parameter, which is minimal among visible hits. -/
example (R : TrimRegion) (u v t : ℝ) (hvis : trimVisible R u v) :
    nearestVisibleT R [(u, v, t)] = some t ∧
    (∃ u' v', (u', v', t) ∈ [(u, v, t)] ∧ trimVisible R u' v') ∧
    (∀ t', (∃ u' v', (u', v', t') ∈ [(u, v, t)] ∧ trimVisible R u' v') → t ≤ t') := by
  have hscan : nearestVisibleT R [(u, v, t)] = some t := by
    simp [nearestVisibleT, hvis]
  exact ⟨hscan, nearestVisibleT_spec R [(u, v, t)] hscan⟩


/-- The local-center seed hypotheses are jointly satisfiable for a sufficiently
    small control net: R >= 1 supplies the seed distance and K*R <= 1 holds. -/
example : ∃ M R : ℝ, 0 < M ∧ 1 ≤ R ∧ 192 * M * R ≤ 1 := by
  refine ⟨1/1000, 1, by norm_num, le_rfl, ?_⟩
  norm_num


/-- Round-linear / flat real models are non-vacuous. -/
example (o d p0 p1 : Vec3) (r0 r1 tmin tbest t : ℝ)
    (h : rlcReal o d p0 p1 r0 r1 tmin tbest = some t) :
    HitsRoundLinear o d p0 p1 r0 r1 tmin tbest t :=
  rlcReal_sound o d p0 p1 r0 r1 tmin tbest t h

example (o d p0 p1 b : Vec3) (r0 r1 tmin tbest t : ℝ)
    (h : flatReal o d p0 p1 b r0 r1 tmin tbest = some t) :
    HitsFlatLinear o d p0 p1 r0 r1 b tmin tbest t :=
  flatReal_sound o d p0 p1 b r0 r1 tmin tbest t h

/-- A point in the flat-ribbon two-triangle quad is on the ribbon. -/
example (p0 p1 b x : Vec3) (r0 r1 : ℝ) (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1)
    (hx : InQuad (p0 - r0 • b) (p0 + r0 • b) (p1 + r1 • b) (p1 - r1 • b) x) :
    OnFlatLinear p0 p1 r0 r1 p0 b x :=
  inQuad_flat_of_onFlatLinear p0 p1 b r0 r1 hr0 hr1 hx


/-- Crossing-number properties are non-vacuous. -/
example (p q : ℝ × ℝ) (y : ℝ) (h : edgeSpansY p q y) :
    min p.1 q.1 ≤ edgeCrossX p q y ∧ edgeCrossX p q y ≤ max p.1 q.1 :=
  edgeCrossX_between p q y h

example (loop : TrimLoop) (x y : ℝ) (hfar : ∀ p ∈ loop, p.1 < x) :
    crossingNumber loop x y = 0 :=
  crossingNumber_far_right loop x y hfar

example (x0 x1 y0 y1 x y : ℝ) (hx0 : x0 < x) (hx1 : x < x1)
    (hy0 : y0 ≤ y) (hy1 : y < y1) :
    crossingNumber [(x0,y0), (x1,y0), (x1,y1), (x0,y1)] x y % 2 = 1 :=
  rectangle_crossing_inside x0 x1 y0 y1 x y hx0 hx1 hy0 hy1


/-- The adaptive-search min fold is non-vacuous. -/
example (c : PatchCell) (t : ℝ) : adaptiveSearch [c] (fun _ => some t) = some t := by
  unfold adaptiveSearch
  change (List.minimum [t] : WithTop ℝ) = some t
  exact List.minimum_singleton t

example (c : PatchCell) (t t' : ℝ) (hle : t ≤ t') :
    adaptiveSearch [c] (fun _ => some t) = some t → t ≤ t' := by
  intro h
  exact hle


/-- Degree-2 Boehm insertion preserves the quadratic Bezier curve. -/
example (P : Fin 3 → Vec3) (t u : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bsplineCurve (insertKnot (bezKnot 2) 2 t)
      (fun i => if h : i < 4 then boehm2 P t ⟨i,h⟩ else 0) 2 3 u =
    bsplineCurve (bezKnot 2) (fun i => if h : i < 3 then P ⟨i,h⟩ else 0) 2 2 u :=
  boehm2_preserves P t ht0 ht1 u hu0 hu1


/-- Remaining intersector contracts are non-vacuous. -/
example (c : Vec3) (r : ℝ) : AbsLipschitz (fun p : Vec3 => dist p c - r) :=
  sdfSphere_AbsLipschitz c r

example (o dir p0 p1 : Vec3) (r tmin tbest t : ℝ)
    (h : capsuleReal o dir p0 p1 r tmin tbest = some t) :
    HitsCapsuleAt o dir p0 p1 r tmin tbest t :=
  crvReal_sound h

example (o d : Vec3) (w : Fin 16 → ℝ) (P : Fin 16 → Vec3)
    (R : TrimRegion) {tmin tbest : ℝ}
    (hits : List (ℝ × ℝ × ℝ))
    (hparam : ∀ u v t, (u, v, t) ∈ hits → tmin ≤ t ∧ t < tbest ∧
      o + t • d = ratEval w P u v)
    {t : ℝ} (hscan : nearestVisibleT R hits = some t) :
    ∃ u v, o + t • d = ratEval w P u v := by
  rcases trimmed_contract_spec o d w P R hits hparam hscan with ⟨_, _, h⟩
  exact h


/-- Crossing-number additivity and rotation invariance are non-vacuous. -/
example (l₁ l₂ : TrimLoop) (x y : ℝ) :
    crossingNumber (l₁ ++ l₂) x y =
      crossingNumber l₁ x y + loopBridge l₁ l₂ x y + crossingNumber l₂ x y :=
  crossingNumber_append l₁ l₂ x y

example (p : ℝ × ℝ) (l : TrimLoop) (x y : ℝ) (hne : l ≠ []) :
    crossingNumberClosed (p :: l) x y = crossingNumberClosed (l ++ [p]) x y :=
  crossingNumberClosed_rotate p l x y hne


/-- Torus SDF is 1-Lipschitz. -/
example (R r : ℝ) : AbsLipschitz (sdfTorus R r) := sdfTorus_AbsLipschitz R r


/-- General Cox–de Boor refinement and Boehm insertion are non-vacuous. -/
example (U : ℕ → ℝ) (k : ℕ) (u x : ℝ) (D : KnotData U k u) (p i : ℕ) :
    bsplineBasis U i p x =
      (1 - insertAlpha U k u i p) * bsplineBasis (insertKnot U k u) i p x +
      insertAlpha U k u (i+1) p * bsplineBasis (insertKnot U k u) (i+1) p x :=
  bsplineBasis_refine U k u x D p i

example (U : ℕ → ℝ) (k : ℕ) (u : ℝ) (D : KnotData U k u)
    (p n : ℕ) (hpk : p ≤ k) (hn : k ≤ n) (P : ℕ → Vec3) (u0 : ℝ) :
    bsplineCurve (insertKnot U k u) (boehmControl U k u p P) p (n+1) u0 =
      bsplineCurve U P p n u0 :=
  boehm_preserves U k u D p n hpk hn P u0


/-- Box SDF is 1-Lipschitz. -/
example (h : Fin 3 → ℝ) : AbsLipschitz (sdfBox h) := sdfBox_AbsLipschitz h


/-- Iterated Boehm insertion preserves the curve. -/
example (U : ℕ → ℝ) (p n : ℕ) (P : ℕ → Vec3) (x : ℝ)
    (ins : List (ℕ × ℝ)) (hval : ValidInserts U p n ins) :
    ∃ (U' : ℕ → ℝ) (P' : ℕ → Vec3) (n' : ℕ),
      U' = insertKnotList U ins ∧
      bsplineCurve U' P' p n' x = bsplineCurve U P p n x :=
  boehm_iterate U p n P x ins hval


/-- Tensor-product surface insertion and ratEval connection. -/
example (U V : ℕ → ℝ) (k : ℕ) (uk : ℝ) (D : KnotData U k uk)
    (pu pv nu nv : ℕ) (hpu : pu ≤ k) (hkn : k ≤ nu) (P : ℕ → ℕ → Vec3) (x y : ℝ) :
    tensorBspline (insertKnot U k uk) V
      (fun i j => boehmControl U k uk pu (fun ii => P ii j) i)
      pu pv (nu+1) nv x y = tensorBspline U V P pu pv nu nv x y :=
  tensorBspline_insert_u U V k uk D pu pv nu nv hpu hkn P x y

example (w : Fin 16 → ℝ) (P : Fin 16 → Vec3) (u v : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    rationalTensorBezier w P u v = ratEval w P u v :=
  rationalTensorBezier_eq_ratEval w P u v hu0 hu1 hv0 hv1

end LightRT.Sanity
