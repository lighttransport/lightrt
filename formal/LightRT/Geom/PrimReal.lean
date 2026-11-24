/-
  Real-number soundness/completeness/nearest for simple scalar primitives:
  sphere, quad (two MT triangles), tetra (four MT faces). Extends the
  `Geom/MTReal.lean` baseline; Tier 1 item 1 of the formalization roadmap.
-/
import Mathlib
import LightRT.Geom.Basic
import LightRT.Geom.MTReal

namespace LightRT.Geom
noncomputable section
open Matrix

def distSq (a b : Vec3) : ℝ := (a - b) ⬝ᵥ (a - b)

theorem distSq_nonneg (a b : Vec3) : 0 ≤ distSq a b := by
  unfold distSq; simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (a 2 - b 2)]

def OnSphere (c : Vec3) (rad : ℝ) (p : Vec3) : Prop := distSq p c = rad ^ 2

def HitsSphereAt (o d c : Vec3) (rad tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnSphere c rad (o + t • d)

theorem sphere_distSq (o d c : Vec3) (rad t : ℝ) :
    distSq (o + t • d) c =
      (d ⬝ᵥ d) * t ^ 2 + 2 * ((o - c) ⬝ᵥ d) * t + (distSq o c - rad ^ 2) + rad ^ 2 := by
  unfold distSq
  simp only [dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem dotProduct_self_pos (d : Vec3) (hd : d ≠ 0) : 0 < d ⬝ᵥ d := by
  simp only [dotProduct, Fin.sum_univ_three]
  by_contra h; push_neg at h
  have h0 : d 0 = 0 := by nlinarith [sq_nonneg (d 0)]
  have h1 : d 1 = 0 := by nlinarith [sq_nonneg (d 1)]
  have h2 : d 2 = 0 := by nlinarith [sq_nonneg (d 2)]
  apply hd; funext i; fin_cases i <;> simp [h0, h1, h2]

/-- Generic "nearest root in `[tmin,tbest)`" for a quadratic. -/
def quadRoots (a b cc tmin tbest : ℝ) : Option ℝ :=
  if ha : a = 0 then none else
  if hΔ : b ^ 2 - 4 * a * cc < 0 then none else
  let s := Real.sqrt (b ^ 2 - 4 * a * cc)
  let t1 := (-b - s) / (2 * a)
  let t2 := (-b + s) / (2 * a)
  if tmin ≤ t1 ∧ t1 < tbest then some t1
  else if tmin ≤ t2 ∧ t2 < tbest then some t2
  else none

def sphereReal (o d c : Vec3) (rad tmin tbest : ℝ) : Option ℝ :=
  quadRoots (d ⬝ᵥ d) (2 * ((o - c) ⬝ᵥ d)) (distSq o c - rad ^ 2) tmin tbest

theorem sphere_quad_roots {a b cc t : ℝ} (ha : a ≠ 0) (hΔ : 0 ≤ b ^ 2 - 4 * a * cc) :
    a * t ^ 2 + b * t + cc = 0 ↔
      t = (-b - Real.sqrt (b ^ 2 - 4 * a * cc)) / (2 * a) ∨
      t = (-b + Real.sqrt (b ^ 2 - 4 * a * cc)) / (2 * a) := by
  set Δ := b ^ 2 - 4 * a * cc with hΔdef
  set s := Real.sqrt Δ with hsdef
  have hs2 : s ^ 2 = Δ := by rw [hsdef, Real.sq_sqrt hΔ]
  have hfac : 4 * a * (a * t ^ 2 + b * t + cc) = (2 * a * t + b) ^ 2 - s ^ 2 := by
    rw [hs2, hΔdef]; ring
  constructor
  · intro h
    have heq : (2 * a * t + b) ^ 2 = s ^ 2 := by
      have : (2 * a * t + b) ^ 2 - s ^ 2 = 0 := by rw [← hfac, h, mul_zero]
      linarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp heq) with hp | hm
    · right; rw [hsdef, hΔdef] at hp ⊢; field_simp [ha] at hp ⊢; linarith
    · left; rw [hsdef, hΔdef] at hm ⊢; field_simp [ha] at hm ⊢; linarith
  · rintro (ht | ht)
    · rw [ht]; field_simp [ha]; nlinarith [hs2, hΔdef]
    · rw [ht]; field_simp [ha]; nlinarith [hs2, hΔdef]

theorem quadRoots_sound {a b cc tmin tbest t : ℝ}
    (h : quadRoots a b cc tmin tbest = some t) :
    a * t ^ 2 + b * t + cc = 0 ∧ tmin ≤ t ∧ t < tbest := by
  unfold quadRoots at h
  by_cases ha : a = 0
  · simp [ha] at h
  by_cases hΔ : b ^ 2 - 4 * a * cc < 0
  · simp [ha, hΔ] at h
  by_cases h1 : tmin ≤ (-b - Real.sqrt (b^2 - 4*a*cc))/(2*a) ∧
      (-b - Real.sqrt (b^2 - 4*a*cc))/(2*a) < tbest
  · simp [ha, hΔ, h1] at h
    have ht : t = (-b - Real.sqrt (b^2 - 4*a*cc))/(2*a) := by simpa using h.symm
    have hroot := (sphere_quad_roots ha (le_of_not_gt hΔ)).2 (Or.inl ht)
    subst t
    exact ⟨hroot, h1.1, h1.2⟩
  · by_cases h2 : tmin ≤ (-b + Real.sqrt (b^2 - 4*a*cc))/(2*a) ∧
        (-b + Real.sqrt (b^2 - 4*a*cc))/(2*a) < tbest
    · simp [ha, hΔ, h1, h2] at h
      have ht : t = (-b + Real.sqrt (b^2 - 4*a*cc))/(2*a) := by simpa using h.symm
      have hroot := (sphere_quad_roots ha (le_of_not_gt hΔ)).2 (Or.inr ht)
      subst t
      exact ⟨hroot, h2.1, h2.2⟩
    · simp [ha, hΔ, h1, h2] at h

theorem sphere_root_le {a b Δ : ℝ} (ha : 0 < a) :
    (-b - Real.sqrt Δ) / (2 * a) ≤ (-b + Real.sqrt Δ) / (2 * a) := by
  have h2a : 0 < 2 * a := by positivity
  rw [div_le_div_iff_of_pos_right h2a]
  linarith [Real.sqrt_nonneg Δ]

theorem quadRoots_complete {a b cc tmin tbest t : ℝ} (ha : 0 < a)
    (hquad : a * t ^ 2 + b * t + cc = 0) (hlo : tmin ≤ t) (hhi : t < tbest) :
    ∃ t', quadRoots a b cc tmin tbest = some t' ∧ t' ≤ t := by
  have hΔnonneg : 0 ≤ b ^ 2 - 4 * a * cc := by
    have heq : b ^ 2 - 4 * a * cc = (b + 2 * a * t) ^ 2 := by nlinarith
    rw [heq]; positivity
  have hroots := (sphere_quad_roots (ne_of_gt ha) hΔnonneg).1 hquad
  have ht1le : (-b - Real.sqrt (b^2-4*a*cc))/(2*a) ≤ (-b + Real.sqrt (b^2-4*a*cc))/(2*a) := sphere_root_le ha
  rcases hroots with ht1 | ht2
  · refine ⟨t, ?_, le_rfl⟩
    unfold quadRoots
    rw [dif_neg (ne_of_gt ha), dif_neg (not_lt.mpr hΔnonneg)]
    have h1 : tmin ≤ (-b - Real.sqrt (b^2-4*a*cc))/(2*a) ∧ (-b - Real.sqrt (b^2-4*a*cc))/(2*a) < tbest := by
      rw [← ht1]; exact ⟨hlo, hhi⟩
    rw [if_pos h1]
    simpa using ht1.symm
  · by_cases h1 : tmin ≤ (-b - Real.sqrt (b^2-4*a*cc))/(2*a) ∧ (-b - Real.sqrt (b^2-4*a*cc))/(2*a) < tbest
    · refine ⟨(-b - Real.sqrt (b^2-4*a*cc))/(2*a), ?_, ?_⟩
      · unfold quadRoots; rw [dif_neg (ne_of_gt ha), dif_neg (not_lt.mpr hΔnonneg), if_pos h1]
      · simpa [ht2] using ht1le
    · refine ⟨t, ?_, le_rfl⟩
      unfold quadRoots
      rw [dif_neg (ne_of_gt ha), dif_neg (not_lt.mpr hΔnonneg), if_neg h1]
      have h2 : tmin ≤ (-b + Real.sqrt (b^2-4*a*cc))/(2*a) ∧ (-b + Real.sqrt (b^2-4*a*cc))/(2*a) < tbest := by
        rw [← ht2]; exact ⟨hlo, hhi⟩
      rw [if_pos h2]
      simpa using ht2.symm

theorem sphereReal_sound {o d c : Vec3} {rad tmin tbest t : ℝ}
    (h : sphereReal o d c rad tmin tbest = some t) :
    HitsSphereAt o d c rad tmin tbest t := by
  have hs := quadRoots_sound h
  refine ⟨hs.2.1, hs.2.2, ?_⟩
  have hdist := sphere_distSq o d c rad t
  unfold OnSphere
  rw [hdist]
  nlinarith [hs.1]

theorem sphereReal_complete {o d c : Vec3} {rad tmin tbest t : ℝ} (hd : d ≠ 0)
    (hhit : HitsSphereAt o d c rad tmin tbest t) :
    ∃ t', sphereReal o d c rad tmin tbest = some t' ∧ t' ≤ t := by
  have hapos : 0 < d ⬝ᵥ d := dotProduct_self_pos d hd
  have hquad : (d ⬝ᵥ d) * t^2 + 2*((o-c) ⬝ᵥ d)*t + (distSq o c - rad^2) = 0 := by
    have hdist := sphere_distSq o d c rad t
    unfold HitsSphereAt OnSphere at hhit
    unfold distSq at hhit hdist ⊢
    nlinarith [hhit.2.2]
  exact quadRoots_complete hapos hquad hhit.1 hhit.2.1



/-- A quad is the union of two triangles sharing the diagonal `v0–v2`. -/
def InQuad (v0 v1 v2 v3 p : Vec3) : Prop :=
  InTriangle v0 v1 v2 p ∨ InTriangle v0 v2 v3 p

def HitsQuadAt (o dir v0 v1 v2 v3 : Vec3) (tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ InQuad v0 v1 v2 v3 (o + t • dir)

/-- Quad intersection = nearest of two Möller–Trumbore triangle hits. -/
def quadReal (o dir v0 v1 v2 v3 : Vec3) (ε tmin tbest : ℝ) : Option ℝ :=
  let r1 := (mtReal o dir v0 v1 v2 ε tmin tbest).map Prod.fst
  let r2 := (mtReal o dir v0 v2 v3 ε tmin tbest).map Prod.fst
  match r1, r2 with
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

theorem quadReal_sound {o dir v0 v1 v2 v3 : Vec3} {ε tmin tbest t : ℝ}
    (hε : 0 < ε) (h : quadReal o dir v0 v1 v2 v3 ε tmin tbest = some t) :
    HitsQuadAt o dir v0 v1 v2 v3 tmin tbest t := by
  unfold quadReal at h
  cases hm1 : mtReal o dir v0 v1 v2 ε tmin tbest with
  | none =>
      simp [hm1] at h
      cases hm2 : mtReal o dir v0 v2 v3 ε tmin tbest with
      | none => simp [hm2] at h
      | some r2 =>
          simp [hm2] at h
          subst t
          have hs := mtReal_sound hε hm2
          exact ⟨hs.1.1, hs.1.2.1, Or.inr hs.1.2.2⟩
  | some r1 =>
      cases hm2 : mtReal o dir v0 v2 v3 ε tmin tbest with
      | none =>
          simp [hm1, hm2] at h
          subst t
          have hs := mtReal_sound hε hm1
          exact ⟨hs.1.1, hs.1.2.1, Or.inl hs.1.2.2⟩
      | some r2 =>
          simp [hm1, hm2] at h
          by_cases hle : r2.1 ≤ r1.1
          · rw [min_eq_right hle] at h
            subst t
            have hs := mtReal_sound hε hm2
            exact ⟨hs.1.1, hs.1.2.1, Or.inr hs.1.2.2⟩
          · have hle' : r1.1 ≤ r2.1 := le_of_not_ge hle
            rw [min_eq_left hle'] at h
            subst t
            have hs := mtReal_sound hε hm1
            exact ⟨hs.1.1, hs.1.2.1, Or.inl hs.1.2.2⟩

theorem quadReal_complete {o dir v0 v1 v2 v3 : Vec3} {ε tmin tbest t : ℝ}
    (hd1 : ε ≤ |(v1 - v0) ⬝ᵥ (crossProduct dir (v2 - v0))|)
    (hn1 : (v1 - v0) ⬝ᵥ (crossProduct dir (v2 - v0)) ≠ 0)
    (hd2 : ε ≤ |(v2 - v0) ⬝ᵥ (crossProduct dir (v3 - v0))|)
    (hn2 : (v2 - v0) ⬝ᵥ (crossProduct dir (v3 - v0)) ≠ 0)
    (hhit : HitsQuadAt o dir v0 v1 v2 v3 tmin tbest t) :
    ∃ t', quadReal o dir v0 v1 v2 v3 ε tmin tbest = some t' ∧ t' ≤ t := by
  rcases hhit.2.2 with htri | htri
  · have hm1hit : HitsTriangleAt o dir v0 v1 v2 tmin tbest t := ⟨hhit.1, hhit.2.1, htri⟩
    obtain ⟨u1, v1', hm1res⟩ := mtReal_complete hd1 hn1 hm1hit
    unfold quadReal
    cases hm2 : mtReal o dir v0 v2 v3 ε tmin tbest with
    | none =>
        refine ⟨t, ?_, le_rfl⟩
        simp [hm1res, hm2]
    | some r2 =>
        refine ⟨min t r2.1, ?_, min_le_left _ _⟩
        simp [hm1res, hm2]
  · have hm2hit : HitsTriangleAt o dir v0 v2 v3 tmin tbest t := ⟨hhit.1, hhit.2.1, htri⟩
    obtain ⟨u2, v2', hm2res⟩ := mtReal_complete hd2 hn2 hm2hit
    unfold quadReal
    cases hm1 : mtReal o dir v0 v1 v2 ε tmin tbest with
    | none =>
        refine ⟨t, ?_, le_rfl⟩
        simp [hm1, hm2res]
    | some r1 =>
        refine ⟨min r1.1 t, ?_, min_le_right _ _⟩
        simp [hm1, hm2res]



/-- Nearest of a list of optional parameters. -/
def nearestOpt : List (Option ℝ) → Option ℝ
  | [] => none
  | none :: rest => nearestOpt rest
  | some t :: rest => match nearestOpt rest with
      | some s => some (min t s)
      | none => some t

theorem nearestOpt_mem {l : List (Option ℝ)} {t : ℝ} (h : nearestOpt l = some t) :
    ∃ o ∈ l, o = some t := by
  induction l with
  | nil => simp [nearestOpt] at h
  | cons hd tl ih =>
      cases hd with
      | none =>
          simp [nearestOpt] at h
          rcases ih h with ⟨o, ho, hot⟩
          exact ⟨o, by simp [ho], hot⟩
      | some a =>
          cases hrest : nearestOpt tl with
          | none =>
              simp [nearestOpt, hrest] at h
              subst t
              exact ⟨some a, by simp, rfl⟩
          | some s =>
              simp [nearestOpt, hrest] at h
              rcases min_choice a s with hmin | hmin
              · rw [hmin] at h; subst t
                exact ⟨some a, by simp, rfl⟩
              · rw [hmin] at h; subst t
                rcases ih hrest with ⟨o, ho, hot⟩
                exact ⟨o, by simp [ho], hot⟩

theorem nearestOpt_le {l : List (Option ℝ)} {t : ℝ} (hmem : ∃ o ∈ l, o = some t) :
    ∃ t', nearestOpt l = some t' ∧ t' ≤ t := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
      cases hd with
      | none =>
          apply ih
          rcases hmem with ⟨o, ho, hot⟩
          rcases List.mem_cons.mp ho with hhead | htail
          · rw [hhead] at hot; cases hot
          · exact ⟨o, htail, hot⟩
      | some a =>
          rcases hmem with ⟨o, ho, hot⟩
          rcases List.mem_cons.mp ho with hhead | htail
          · rw [hhead] at hot
            injection hot with hat
            subst t
            cases hrest : nearestOpt tl with
            | none => exact ⟨a, by simp [nearestOpt, hrest], le_rfl⟩
            | some s => exact ⟨min a s, by simp [nearestOpt, hrest], min_le_left _ _⟩
          · rcases ih ⟨o, htail, hot⟩ with ⟨t', ht', htle⟩
            refine ⟨min a t', ?_, (min_le_right _ _).trans htle⟩
            simp [nearestOpt, ht']

/-- A tetrahedron is the union of its four triangular faces. -/
def InTetra (v0 v1 v2 v3 p : Vec3) : Prop :=
  InTriangle v0 v1 v2 p ∨ InTriangle v0 v1 v3 p ∨
  InTriangle v0 v2 v3 p ∨ InTriangle v1 v2 v3 p

def HitsTetraAt (o dir v0 v1 v2 v3 : Vec3) (tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ InTetra v0 v1 v2 v3 (o + t • dir)

def tetraReal (o dir v0 v1 v2 v3 : Vec3) (ε tmin tbest : ℝ) : Option ℝ :=
  nearestOpt [
    (mtReal o dir v0 v1 v2 ε tmin tbest).map Prod.fst,
    (mtReal o dir v0 v1 v3 ε tmin tbest).map Prod.fst,
    (mtReal o dir v0 v2 v3 ε tmin tbest).map Prod.fst,
    (mtReal o dir v1 v2 v3 ε tmin tbest).map Prod.fst]

theorem tetraReal_sound {o dir v0 v1 v2 v3 : Vec3} {ε tmin tbest t : ℝ}
    (hε : 0 < ε) (h : tetraReal o dir v0 v1 v2 v3 ε tmin tbest = some t) :
    HitsTetraAt o dir v0 v1 v2 v3 tmin tbest t := by
  rcases nearestOpt_mem h with ⟨o', ho, hot⟩
  simp at ho
  rcases ho with ho | ho | ho | ho
  · have hmap : Option.map Prod.fst (mtReal o dir v0 v1 v2 ε tmin tbest) = some t := ho.symm.trans hot
    rcases Option.map_eq_some_iff.mp hmap with ⟨⟨t,u,v⟩, hm, hfst⟩
    simp at hfst; subst t
    have hs := mtReal_sound hε hm
    exact ⟨hs.1.1, hs.1.2.1, Or.inl hs.1.2.2⟩
  · have hmap : Option.map Prod.fst (mtReal o dir v0 v1 v3 ε tmin tbest) = some t := ho.symm.trans hot
    rcases Option.map_eq_some_iff.mp hmap with ⟨⟨t,u,v⟩, hm, hfst⟩
    simp at hfst; subst t
    have hs := mtReal_sound hε hm
    exact ⟨hs.1.1, hs.1.2.1, Or.inr (Or.inl hs.1.2.2)⟩
  · have hmap : Option.map Prod.fst (mtReal o dir v0 v2 v3 ε tmin tbest) = some t := ho.symm.trans hot
    rcases Option.map_eq_some_iff.mp hmap with ⟨⟨t,u,v⟩, hm, hfst⟩
    simp at hfst; subst t
    have hs := mtReal_sound hε hm
    exact ⟨hs.1.1, hs.1.2.1, Or.inr (Or.inr (Or.inl hs.1.2.2))⟩
  · have hmap : Option.map Prod.fst (mtReal o dir v1 v2 v3 ε tmin tbest) = some t := ho.symm.trans hot
    rcases Option.map_eq_some_iff.mp hmap with ⟨⟨t,u,v⟩, hm, hfst⟩
    simp at hfst; subst t
    have hs := mtReal_sound hε hm
    exact ⟨hs.1.1, hs.1.2.1, Or.inr (Or.inr (Or.inr hs.1.2.2))⟩

theorem tetraReal_complete {o dir v0 v1 v2 v3 : Vec3} {ε tmin tbest t : ℝ}
    (hd1 : ε ≤ |(v1 - v0) ⬝ᵥ (crossProduct dir (v2 - v0))|)
    (hn1 : (v1 - v0) ⬝ᵥ (crossProduct dir (v2 - v0)) ≠ 0)
    (hd2 : ε ≤ |(v1 - v0) ⬝ᵥ (crossProduct dir (v3 - v0))|)
    (hn2 : (v1 - v0) ⬝ᵥ (crossProduct dir (v3 - v0)) ≠ 0)
    (hd3 : ε ≤ |(v2 - v0) ⬝ᵥ (crossProduct dir (v3 - v0))|)
    (hn3 : (v2 - v0) ⬝ᵥ (crossProduct dir (v3 - v0)) ≠ 0)
    (hd4 : ε ≤ |(v2 - v1) ⬝ᵥ (crossProduct dir (v3 - v1))|)
    (hn4 : (v2 - v1) ⬝ᵥ (crossProduct dir (v3 - v1)) ≠ 0)
    (hhit : HitsTetraAt o dir v0 v1 v2 v3 tmin tbest t) :
    ∃ t', tetraReal o dir v0 v1 v2 v3 ε tmin tbest = some t' ∧ t' ≤ t := by
  unfold tetraReal
  apply nearestOpt_le
  rcases hhit.2.2 with h1 | h2 | h3 | h4
  · obtain ⟨u, v, hm⟩ := mtReal_complete hd1 hn1 ⟨hhit.1, hhit.2.1, h1⟩
    exact ⟨(mtReal o dir v0 v1 v2 ε tmin tbest).map Prod.fst, by simp [hm], by simp [hm]⟩
  · obtain ⟨u, v, hm⟩ := mtReal_complete hd2 hn2 ⟨hhit.1, hhit.2.1, h2⟩
    exact ⟨(mtReal o dir v0 v1 v3 ε tmin tbest).map Prod.fst, by simp [hm], by simp [hm]⟩
  · obtain ⟨u, v, hm⟩ := mtReal_complete hd3 hn3 ⟨hhit.1, hhit.2.1, h3⟩
    exact ⟨(mtReal o dir v0 v2 v3 ε tmin tbest).map Prod.fst, by simp [hm], by simp [hm]⟩
  · obtain ⟨u, v, hm⟩ := mtReal_complete hd4 hn4 ⟨hhit.1, hhit.2.1, h4⟩
    exact ⟨(mtReal o dir v1 v2 v3 ε tmin tbest).map Prod.fst, by simp [hm], by simp [hm]⟩

end
end LightRT.Geom
