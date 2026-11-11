/-
  Two-level BVH (TLAS over instanced BLAS): `lrt_tlas_intersect1`.

  C structure: the TLAS is the same flat wide BVH, with instances as
  primitives. A TLAS leaf runs, per instance `i`, the full BLAS closest-hit
  query on the ray transformed to object space with `tmax = best`, and keeps
  the result if it is below `best`.

  1. `runT_eq_run` / `tlas_root`: that loop equals the single-level `Flat.run`
     over (instance, primitive) pairs, so `run_root` gives brute force over
     every reachable pair. The BLAS call is discharged by `blas_fold`
     (`run_root` per instance, with `tmax = best`).
  2. `hit_world_of_obj` / `hit_obj_of_world`: over ℝ an affine world→object
     map preserves the ray parameter exactly, so an object-space hit at `t` is
     a world-space hit at the same `t` on the object→world image.
  3. `xform_point_err` / `xform_vec_err`: rounding of `tlas_xform_point` /
     `tlas_xform_vec` (left-to-right sums, no FMA) in any `RoundingModel`,
     as a running absolute-error bound.
-/
import LightRT.BVH.Flat
import LightRT.Geom.Basic
import LightRT.FP.Model

namespace LightRT.BVH
variable {B ι α T : Type}

namespace Flat
section TwoLevel
variable [LinearOrder T]

/-- `lrt_tlas_intersect1`'s loop: as `run`, but a leaf folds the per-instance
    BLAS query `blas i best` over its instances. -/
def runT (F : Flat B ι) (test : B → T → Option T) (blas : ι → T → T)
    (order : List (CRef × T) → List (CRef × T)) : ℕ → List (CRef × T) → T → Option T
  | 0, _, _ => none
  | _ + 1, [], best => some best
  | f + 1, (r, tn) :: st, best =>
    if best ≤ tn then runT F test blas order f st best else
    match r with
    | .leaf blk n => runT F test blas order f st
        ((F.leafPrims blk n).foldl (fun b i => blas i b) best)
    | .node i => runT F test blas order f
        (order ((F.children i).filterMap fun c => (test c.1 best).map (c.2, ·)) ++ st) best

/-- The TLAS with each instance expanded to its (instance, primitive) pairs. -/
def flat2 (F : Flat B ι) (P : ι → List α) : Flat B (ι × α) :=
  ⟨F.nodes, fun b => (F.block b).flatMap fun i => (P i).map (i, ·), F.root⟩

def isect2 (isect : ι → α → Option T) : ι × α → Option T := fun x => isect x.1 x.2

theorem leafPrims_flat2 (F : Flat B ι) (P : ι → List α) (blk n : ℕ) :
    (flat2 F P).leafPrims blk n = (F.leafPrims blk n).flatMap fun i => (P i).map (i, ·) := by
  simp only [leafPrims, flat2, List.flatMap_assoc]

theorem fold_pairs (P : ι → List α) (isect : ι → α → Option T) :
    ∀ (L : List ι) (b : T),
      (L.flatMap fun i => (P i).map (i, ·)).foldl (step (isect2 isect)) b =
        L.foldl (fun b i => (P i).foldl (step (isect i)) b) b
  | [], _ => rfl
  | i :: L, b => by
    rw [List.flatMap_cons, List.foldl_append, List.foldl_cons, List.foldl_map]
    exact fold_pairs P isect L _

/-- **Two-level = one level over pairs**: if each BLAS query from `best` is the
    fold of its primitives (which `blas_fold` provides), the TLAS loop is
    exactly `run` on the expanded tree. -/
theorem runT_eq_run (F : Flat B ι) (test : B → T → Option T) (blas : ι → T → T)
    (order : List (CRef × T) → List (CRef × T)) (P : ι → List α) (isect : ι → α → Option T)
    (hb : ∀ i b, blas i b = (P i).foldl (step (isect i)) b) :
    ∀ f st best, runT F test blas order f st best =
      run (flat2 F P) test (isect2 isect) order f st best := by
  intro f
  induction f with
  | zero => intro st best; rfl
  | succ f ih =>
    intro st best
    match st with
    | [] => rfl
    | (r, tn) :: st =>
      simp only [runT, run]
      split_ifs
      · exact ih st best
      · cases r with
        | leaf blk n =>
          dsimp only
          have hf : (fun b i => blas i b) = (fun b i => (P i).foldl (step (isect i)) b) := by
            funext b i; exact hb i b
          rw [leafPrims_flat2, fold_pairs, hf, ih]
        | node i => exact ih _ best

/-- `visits` depends only on the node lists. -/
theorem visits_nodes {α' : Type} (F : Flat B α) (G : Flat B α') (h : F.nodes = G.nodes) (j : ℕ) :
    F.visits j = G.visits j := by
  suffices H : ∀ k j, F.nodes.length - j = k → F.visits j = G.visits j from H _ j rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hk
    rw [visits_eq, visits_eq]
    have hc : F.children j = G.children j := by simp [children, h]
    rw [hc, ← h]
    congr 2
    apply List.map_congr_left
    intro c _
    rcases c with ⟨b, r⟩; cases r with
    | leaf => rfl
    | node j' =>
      dsimp only
      split_ifs with hg
      · exact ih (F.nodes.length - j') (by omega) j' rfl
      · rfl

/-- The BLAS query is a fold (C: `lrt_tri_intersect1(blas, q)` with
    `q.tmax = best`, result kept iff below `best`): an instance of `run_root`. -/
theorem blas_fold {inside : α → B → Prop} {sub : B → B → Prop} (G : Flat B α)
    (hw : G.WF inside sub) (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l)
    (C1 : ∀ p b t best, inside p b → isect p = some t → t < best → (test b best).isSome)
    (C2 : ∀ p b t best tn, test b best = some tn → inside p b → isect p = some t → t < best → tn ≤ t)
    (tmin : T) (htmin : ∀ p ∈ G.denRef G.root, ∀ t, isect p = some t → tmin ≤ t) (best : T) :
    (run G test isect order (G.visitsRef G.root + 1) [(G.root, tmin)] best).getD best =
      (G.denRef G.root).foldl (step isect) best := by
  rw [run_root G hw mono test isect order hord C1 C2 tmin best htmin]; rfl

/-- **TLAS = brute force over every reachable (instance, primitive) pair**, under
    the TLAS conservativity conditions stated for pairs (world-space hits of
    instance `i`'s primitive `p` lie in the leaf boxes above `i`). -/
theorem tlas_root {inside : ι × α → B → Prop} {sub : B → B → Prop} (F : Flat B ι)
    (P : ι → List α) (isect : ι → α → Option T) (blas : ι → T → T)
    (hb : ∀ i b, blas i b = (P i).foldl (step (isect i)) b)
    (hw : (flat2 F P).WF inside sub) (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (test : B → T → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l)
    (C1 : ∀ p b t best, inside p b → isect2 isect p = some t → t < best → (test b best).isSome)
    (C2 : ∀ p b t best tn, test b best = some tn → inside p b → isect2 isect p = some t →
      t < best → tn ≤ t)
    (tmin tmax : T)
    (htmin : ∀ p ∈ (flat2 F P).denRef F.root, ∀ t, isect2 isect p = some t → tmin ≤ t) :
    runT F test blas order (F.visitsRef F.root + 1) [(F.root, tmin)] tmax =
      some (((flat2 F P).denRef F.root).foldl (step (isect2 isect)) tmax) := by
  rw [runT_eq_run F test blas order P isect hb]
  have hv : F.visitsRef F.root = (flat2 F P).visitsRef (flat2 F P).root := by
    show F.visitsRef F.root = (flat2 F P).visitsRef F.root
    generalize F.root = r
    cases r with
    | leaf => rfl
    | node j => exact visits_nodes F (flat2 F P) rfl j
  rw [hv]
  exact run_root (flat2 F P) hw mono test (isect2 isect) order hord C1 C2 tmin tmax htmin

end TwoLevel
end Flat

/-! ### Affine instance transforms over ℝ: the ray parameter is preserved -/

namespace TwoLevel
open LightRT.Geom

/-- 3×4 affine map `p ↦ L p + c` (`lrt_instance` / `world2obj`). -/
structure Aff where
  L : Matrix (Fin 3) (Fin 3) ℝ
  c : Vec3

def Aff.app (A : Aff) (p : Vec3) : Vec3 := A.L.mulVec p + A.c
def Aff.lin (A : Aff) (v : Vec3) : Vec3 := A.L.mulVec v

theorem Aff.app_ray (A : Aff) (o d : Vec3) (t : ℝ) :
    A.app (o + t • d) = A.app o + t • A.lin d := by
  simp only [Aff.app, Aff.lin, Matrix.mulVec_add, Matrix.mulVec_smul]; abel

theorem Aff.inTriangle (A : Aff) {v0 v1 v2 p : Vec3} (h : InTriangle v0 v1 v2 p) :
    InTriangle (A.app v0) (A.app v1) (A.app v2) (A.app p) := by
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := h
  refine ⟨u, v, hu, hv, huv, ?_⟩
  simp only [Aff.app, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  abel

/-- **Object-space hit ⇒ world-space hit at the same `t`.** `W` is world→object
    (the transform applied to the ray), `O` is object→world with `O ∘ W = id`;
    the world-space triangle is the image of the object-space one under `O`. -/
theorem hit_world_of_obj (W O : Aff) (hOW : ∀ p, O.app (W.app p) = p)
    {o d v0 v1 v2 : Vec3} {tmin tb t : ℝ}
    (h : HitsTriangleAt (W.app o) (W.lin d) v0 v1 v2 tmin tb t) :
    HitsTriangleAt o d (O.app v0) (O.app v1) (O.app v2) tmin tb t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  have := O.inTriangle h3
  rwa [← W.app_ray, hOW] at this

/-- **World-space hit ⇒ object-space hit at the same `t`** (`W ∘ O = id`). -/
theorem hit_obj_of_world (W O : Aff) (hWO : ∀ p, W.app (O.app p) = p)
    {o d v0 v1 v2 : Vec3} {tmin tb t : ℝ}
    (h : HitsTriangleAt o d (O.app v0) (O.app v1) (O.app v2) tmin tb t) :
    HitsTriangleAt (W.app o) (W.lin d) v0 v1 v2 tmin tb t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  have := W.inTriangle h3
  rwa [hWO, hWO, hWO, W.app_ray] at this

/-- Hence the nearest hit over instances is the same set of `t`s in both spaces:
    closest-hit in object space (per instance, exact arithmetic) = closest-hit in
    world space over the transformed triangles. -/
theorem hit_iff (W O : Aff) (hOW : ∀ p, O.app (W.app p) = p) (hWO : ∀ p, W.app (O.app p) = p)
    (o d v0 v1 v2 : Vec3) (tmin tb t : ℝ) :
    HitsTriangleAt (W.app o) (W.lin d) v0 v1 v2 tmin tb t ↔
      HitsTriangleAt o d (O.app v0) (O.app v1) (O.app v2) tmin tb t :=
  ⟨hit_world_of_obj W O hOW, hit_obj_of_world W O hWO⟩

/-- Corner `b` of the box `[lo, hi]` (`b j`: take `hi` on axis `j`). -/
def corner (lo hi : Vec3) (b : Fin 3 → Bool) : Vec3 := fun j => if b j then hi j else lo j

theorem term_lower (L lo hi x : ℝ) (h1 : lo ≤ x) (h2 : x ≤ hi) :
    (if L * hi < L * lo then L * hi else L * lo) ≤ L * x := by
  split_ifs with h
  · rcases le_or_gt 0 L with hL | hL
    · nlinarith
    · nlinarith
  · rcases le_or_gt 0 L with hL | hL
    · nlinarith
    · nlinarith

theorem term_upper (L lo hi x : ℝ) (h1 : lo ≤ x) (h2 : x ≤ hi) :
    L * x ≤ (if L * lo < L * hi then L * hi else L * lo) := by
  split_ifs with h
  · rcases le_or_gt 0 L with hL | hL
    · nlinarith
    · nlinarith
  · rcases le_or_gt 0 L with hL | hL
    · nlinarith
    · nlinarith

/-- **Affine image of a box ⊆ the min/max box of its 8 transformed corners**
    (`tlas_transform_aabb`): per axis, if every transformed corner lies in
    `[wlo, whi]`, so does the image of every point of the box. Each coordinate
    of `A p` is affine, so its minimum over the box is attained at the corner
    that takes, per input axis, whichever bound makes `L a j * p j` smaller. -/
theorem aff_in_corner_box (A : Aff) (lo hi p : Vec3) (hp : ∀ j, lo j ≤ p j ∧ p j ≤ hi j)
    (a : Fin 3) (wlo whi : ℝ)
    (hc : ∀ b : Fin 3 → Bool, wlo ≤ A.app (corner lo hi b) a ∧ A.app (corner lo hi b) a ≤ whi) :
    wlo ≤ A.app p a ∧ A.app p a ≤ whi := by
  have expand : ∀ q : Vec3, A.app q a = A.L a 0 * q 0 + A.L a 1 * q 1 + A.L a 2 * q 2 + A.c a := by
    intro q
    simp [Aff.app, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  constructor
  · let b : Fin 3 → Bool := fun j => decide (A.L a j * hi j < A.L a j * lo j)
    have hb : ∀ j, A.L a j * corner lo hi b j = if A.L a j * hi j < A.L a j * lo j
        then A.L a j * hi j else A.L a j * lo j := by
      intro j; simp only [corner, b]; split_ifs <;> simp_all
    refine (hc b).1.trans ?_
    rw [expand, expand, hb 0, hb 1, hb 2]
    have := term_lower (A.L a 0) (lo 0) (hi 0) (p 0) (hp 0).1 (hp 0).2
    have := term_lower (A.L a 1) (lo 1) (hi 1) (p 1) (hp 1).1 (hp 1).2
    have := term_lower (A.L a 2) (lo 2) (hi 2) (p 2) (hp 2).1 (hp 2).2
    linarith
  · let b : Fin 3 → Bool := fun j => decide (A.L a j * lo j < A.L a j * hi j)
    have hb : ∀ j, A.L a j * corner lo hi b j = if A.L a j * lo j < A.L a j * hi j
        then A.L a j * hi j else A.L a j * lo j := by
      intro j; simp only [corner, b]; split_ifs <;> simp_all
    refine le_trans ?_ (hc b).2
    rw [expand, expand, hb 0, hb 1, hb 2]
    have := term_upper (A.L a 0) (lo 0) (hi 0) (p 0) (hp 0).1 (hp 0).2
    have := term_upper (A.L a 1) (lo 1) (hi 1) (p 1) (hp 1).1 (hp 1).2
    have := term_upper (A.L a 2) (lo 2) (hi 2) (p 2) (hp 2).1 (hp 2).2
    linarith

end TwoLevel

/-! ### Rounding of the instance ray transform -/

namespace TwoLevel
open LightRT.FP
variable (R : RoundingModel)

/-- One rounded addition of two approximations `x ≈ X`, `y ≈ Y`. -/
theorem add_err {x y X Y : ℝ} (hr : R.InRange (x + y)) :
    |R.fl (x + y) - (X + Y)| ≤ |x - X| + |y - Y| + R.u * |x + y| := by
  have h := R.abs_err hr
  calc |R.fl (x + y) - (X + Y)| = |(R.fl (x + y) - (x + y)) + (x - X) + (y - Y)| := by ring_nf
    _ ≤ |R.fl (x + y) - (x + y)| + |x - X| + |y - Y| := abs_add_three _ _ _
    _ ≤ _ := by linarith

theorem mul_err {a b : ℝ} (hr : R.InRange (a * b)) : |R.fl (a * b) - a * b| ≤ R.u * |a * b| :=
  R.abs_err hr

/-- `tlas_xform_vec` component: `fl(fl(fl(m0 v0) + fl(m1 v1)) + fl(m2 v2))`
    (C evaluates left to right; built with `-ffp-contract=off`, no FMA). The
    error is bounded by `u` times the exact products plus `u` times the two
    rounded partial sums. -/
theorem xform_vec_err (m0 m1 m2 v0 v1 v2 : ℝ)
    (h0 : R.InRange (m0 * v0)) (h1 : R.InRange (m1 * v1)) (h2 : R.InRange (m2 * v2))
    (hs1 : R.InRange (R.fl (m0 * v0) + R.fl (m1 * v1)))
    (hs2 : R.InRange (R.fl (R.fl (m0 * v0) + R.fl (m1 * v1)) + R.fl (m2 * v2))) :
    let s1 := R.fl (m0 * v0) + R.fl (m1 * v1)
    let s2 := R.fl s1 + R.fl (m2 * v2)
    |R.fl s2 - (m0 * v0 + m1 * v1 + m2 * v2)| ≤
      R.u * (|m0 * v0| + |m1 * v1| + |m2 * v2|) + R.u * (|s1| + |s2|) := by
  intro s1 s2
  have e0 := mul_err R h0
  have e1 := mul_err R h1
  have e2 := mul_err R h2
  have a1 := add_err R (X := m0 * v0) (Y := m1 * v1) hs1
  have a2 := add_err R (x := R.fl s1) (y := R.fl (m2 * v2)) (X := m0 * v0 + m1 * v1)
    (Y := m2 * v2) hs2
  have : |R.fl s1 - (m0 * v0 + m1 * v1)| ≤ R.u * |m0 * v0| + R.u * |m1 * v1| + R.u * |s1| := by
    linarith
  nlinarith [abs_nonneg s1, abs_nonneg s2, R.u_pos]

/-- `tlas_xform_point` component: as `xform_vec_err` plus the translation
    `+ m3` (one more rounding of the third partial sum). -/
theorem xform_point_err (m0 m1 m2 m3 p0 p1 p2 : ℝ)
    (h0 : R.InRange (m0 * p0)) (h1 : R.InRange (m1 * p1)) (h2 : R.InRange (m2 * p2))
    (hs1 : R.InRange (R.fl (m0 * p0) + R.fl (m1 * p1)))
    (hs2 : R.InRange (R.fl (R.fl (m0 * p0) + R.fl (m1 * p1)) + R.fl (m2 * p2)))
    (hs3 : R.InRange (R.fl (R.fl (R.fl (m0 * p0) + R.fl (m1 * p1)) + R.fl (m2 * p2)) + m3)) :
    let s1 := R.fl (m0 * p0) + R.fl (m1 * p1)
    let s2 := R.fl s1 + R.fl (m2 * p2)
    let s3 := R.fl s2 + m3
    |R.fl s3 - (m0 * p0 + m1 * p1 + m2 * p2 + m3)| ≤
      R.u * (|m0 * p0| + |m1 * p1| + |m2 * p2|) + R.u * (|s1| + |s2| + |s3|) := by
  intro s1 s2 s3
  have hv := xform_vec_err R m0 m1 m2 p0 p1 p2 h0 h1 h2 hs1 hs2
  have a3 := add_err R (x := R.fl s2) (y := m3) (X := m0 * p0 + m1 * p1 + m2 * p2) (Y := m3) hs3
  simp only [sub_self, abs_zero, add_zero] at a3
  nlinarith [abs_nonneg s1, abs_nonneg s2, abs_nonneg s3, R.u_pos]

end TwoLevel
end LightRT.BVH
