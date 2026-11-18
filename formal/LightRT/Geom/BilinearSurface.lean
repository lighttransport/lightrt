/-
  Bilinear patch ray-intersection soundness over ℝ (`tri_bilin_one` in
  lightrt_c_tri.c): coplanarity quadratic in u, Cramer solve for (t,v),
  reported hit implies a genuine point on the bilinear surface inside the
  parameter square. Includes the dual-basis reconstruction identity used
  for the Cramer solve. Tier 1 item 1 (parametric surfaces).
-/
import Mathlib
import LightRT.Geom.CylinderReal

namespace LightRT.Geom
noncomputable section
open Matrix

theorem cross_reconstruct {d D n x : Vec3} (hn : n = crossProduct d D) :
    (n ⬝ᵥ n) • x =
      (x ⬝ᵥ d) • crossProduct D n - (x ⬝ᵥ D) • crossProduct d n + (x ⬝ᵥ n) • n := by
  subst n
  ext i
  fin_cases i <;>
    simp [dotProduct, cross_apply, Fin.sum_univ_three, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring


theorem cross_cramer_rhs {d D pa n : Vec3} (hn : n = crossProduct d D) :
    (pa ⬝ᵥ d) • crossProduct D n - (pa ⬝ᵥ D) • crossProduct d n =
      (crossProduct pa D ⬝ᵥ n) • d - (crossProduct pa d ⬝ᵥ n) • D := by
  subst n
  ext i
  fin_cases i <;>
    simp [dotProduct, cross_apply, Fin.sum_univ_three, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

theorem cramer_solve {d D pa n : Vec3} {t v : ℝ}
    (hn : n = crossProduct d D) (hpa : pa ⬝ᵥ n = 0)
    (hden : n ⬝ᵥ n ≠ 0)
    (ht : t = (crossProduct pa D ⬝ᵥ n) / (n ⬝ᵥ n))
    (hv : v = (crossProduct pa d ⬝ᵥ n) / (n ⬝ᵥ n)) :
    t • d - v • D = pa := by
  have hrec := cross_reconstruct (x := pa) hn
  rw [hpa] at hrec
  simp only [zero_smul, add_zero] at hrec
  rw [cross_cramer_rhs hn] at hrec
  subst t
  subst v
  ext i
  have hi := congrFun hrec i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  field_simp [hden]
  nlinarith [hi]


theorem bilin_pa_dot_n (d Q0 e10 e00 dd : Vec3) (u : ℝ)
    (hroot : (Q0 ⬝ᵥ crossProduct d e00) +
        (Q0 ⬝ᵥ crossProduct d dd + e10 ⬝ᵥ crossProduct d e00) * u +
        (e10 ⬝ᵥ crossProduct d dd) * u ^ 2 = 0) :
    (Q0 + u • e10) ⬝ᵥ crossProduct d (e00 + u • dd) = 0 := by
  have heq : (Q0 + u • e10) ⬝ᵥ crossProduct d (e00 + u • dd) =
      (Q0 ⬝ᵥ crossProduct d e00) +
        (Q0 ⬝ᵥ crossProduct d dd + e10 ⬝ᵥ crossProduct d e00) * u +
        (e10 ⬝ᵥ crossProduct d dd) * u ^ 2 := by
    simp [dotProduct, cross_apply, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact hroot



def firstSome {α : Type*} : List (Option α) → Option α
  | [] => none
  | some a :: _ => some a
  | none :: rest => firstSome rest

theorem firstSome_mem {α : Type*} {l : List (Option α)} {a : α}
    (h : firstSome l = some a) : ∃ o ∈ l, o = some a := by
  induction l with
  | nil => simp [firstSome] at h
  | cons hd tl ih =>
      cases hd with
      | none =>
          have hih : ∃ o ∈ tl, o = some a := ih (by simpa [firstSome] using h)
          rcases hih with ⟨o, ho, hoa⟩
          exact ⟨o, by simp [ho], hoa⟩
      | some b =>
          simp [firstSome] at h
          subst a
          exact ⟨some b, by simp, rfl⟩

theorem firstSome_exists {α : Type*} {l : List (Option α)} {a : α}
    (ha : some a ∈ l) : ∃ b, firstSome l = some b := by
  induction l with
  | nil => simp at ha
  | cons hd tl ih =>
      cases hd with
      | none => simpa [firstSome] using ih (by simpa using ha)
      | some b => exact ⟨b, by simp [firstSome]⟩

def bilinSolve (d Q0 e10 e00 dd : Vec3) (tmin tbest u : ℝ) : Option (ℝ × ℝ × ℝ) :=
  let pa := Q0 + u • e10
  let D := e00 + u • dd
  let n := crossProduct d D
  let den := n ⬝ᵥ n
  if den ≤ 0 then none else
  let t := (crossProduct pa D ⬝ᵥ n) / den
  let v := (crossProduct pa d ⬝ᵥ n) / den
  if 0 ≤ v ∧ v ≤ 1 ∧ tmin ≤ t ∧ t < tbest then some (t, u, v) else none

def bilinReal (o d q00 q10 q11 q01 : Vec3) (tmin tbest : ℝ) : Option (ℝ × ℝ × ℝ) :=
  let e10 := q10 - q00
  let e00 := q01 - q00
  let dd := q11 - q10 - q01 + q00
  let Q0 := q00 - o
  let A := e10 ⬝ᵥ crossProduct d dd
  let B := Q0 ⬝ᵥ crossProduct d dd + e10 ⬝ᵥ crossProduct d e00
  let C := Q0 ⬝ᵥ crossProduct d e00
  let results := (quadRootsList A B C 0 2).filter (fun u => u ≤ 1)
  firstSome (results.map (bilinSolve d Q0 e10 e00 dd tmin tbest))

def bilinEval (q00 q10 q11 q01 : Vec3) (u v : ℝ) : Vec3 :=
  q00 + u • (q10 - q00) + v • (q01 - q00) + (u * v) • (q11 - q10 - q01 + q00)

def OnBilinearSurface (q00 q10 q11 q01 p : Vec3) : Prop :=
  ∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1, p = bilinEval q00 q10 q11 q01 u v

def HitsBilinearAt (o d q00 q10 q11 q01 : Vec3) (tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnBilinearSurface q00 q10 q11 q01 (o + t • d)

theorem bilinSolve_sound {d Q0 e10 e00 dd : Vec3} {tmin tbest u u' t v : ℝ}
    (hroot : (Q0 ⬝ᵥ crossProduct d e00) +
        (Q0 ⬝ᵥ crossProduct d dd + e10 ⬝ᵥ crossProduct d e00) * u +
        (e10 ⬝ᵥ crossProduct d dd) * u ^ 2 = 0)
    (h : bilinSolve d Q0 e10 e00 dd tmin tbest u = some (t, u', v)) :
    u' = u ∧ (t • d - v • (e00 + u • dd) = Q0 + u • e10) ∧
    0 ≤ v ∧ v ≤ 1 ∧ tmin ≤ t ∧ t < tbest := by
  unfold bilinSolve at h
  dsimp only at h
  set pa := Q0 + u • e10
  set D := e00 + u • dd
  set n := crossProduct d D
  set den := n ⬝ᵥ n
  by_cases hden : den ≤ 0
  · simp [hden] at h
  · simp [hden] at h
    set tc := (crossProduct pa D ⬝ᵥ n) / den
    set vc := (crossProduct pa d ⬝ᵥ n) / den
    by_cases hcond : 0 ≤ vc ∧ vc ≤ 1 ∧ tmin ≤ tc ∧ tc < tbest
    · simp [hcond] at h
      rcases h with ⟨hteq, hueq, hveq⟩
      subst t
      subst u'
      subst v
      have hcr := cramer_solve (d := d) (D := D) (pa := pa) (n := n)
        rfl (by simpa [pa, D, n] using bilin_pa_dot_n d Q0 e10 e00 dd u hroot)
        (ne_of_gt (lt_of_not_ge hden)) rfl rfl
      exact ⟨rfl, hcr, hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2⟩
    · simp [hcond] at h


theorem bilinReal_sound {o d q00 q10 q11 q01 : Vec3} {tmin tbest t u v : ℝ}
    (h : bilinReal o d q00 q10 q11 q01 tmin tbest = some (t, u, v)) :
    HitsBilinearAt o d q00 q10 q11 q01 tmin tbest t := by
  unfold bilinReal at h
  dsimp only at h
  set e10 := q10 - q00
  set e00 := q01 - q00
  set dd := q11 - q10 - q01 + q00
  set Q0 := q00 - o
  set A := e10 ⬝ᵥ crossProduct d dd
  set B := Q0 ⬝ᵥ crossProduct d dd + e10 ⬝ᵥ crossProduct d e00
  set C := Q0 ⬝ᵥ crossProduct d e00
  set results := (quadRootsList A B C 0 2).filter (fun u => u ≤ 1)
  have hmem := firstSome_mem h
  rcases hmem with ⟨ores, hores, horeq⟩
  simp only [List.mem_map] at hores
  rcases hores with ⟨u', hu'mem, hu'solve⟩
  subst ores
  have hu'roots : u' ∈ quadRootsList A B C 0 2 := (List.mem_filter.mp hu'mem).1
  have hu'le1 : u' ≤ 1 := by simpa using (List.mem_filter.mp hu'mem).2
  have hroot0 := (quadRootsList_mem hu'roots).1
  have hroot : Q0 ⬝ᵥ crossProduct d e00 +
      (Q0 ⬝ᵥ crossProduct d dd + e10 ⬝ᵥ crossProduct d e00) * u' +
      (e10 ⬝ᵥ crossProduct d dd) * u' ^ 2 = 0 := by
    dsimp [A, B, C] at hroot0 ⊢
    ring_nf at hroot0 ⊢
    exact hroot0
  have hu'0 := (quadRootsList_mem hu'roots).2.1
  have hs := bilinSolve_sound hroot hu'solve
  have htu : u = u' := hs.1
  subst u'
  have htd : t • d = (Q0 + u • e10) + v • (e00 + u • dd) := by
    have hh := hs.2.1
    rw [sub_eq_iff_eq_add] at hh
    exact hh
  have hpt : o + t • d = bilinEval q00 q10 q11 q01 u v := by
    rw [htd]
    dsimp [bilinEval, Q0, e10, e00, dd]
    ext i
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨hs.2.2.2.2.1, hs.2.2.2.2.2, u, ⟨hu'0, hu'le1⟩, v,
    ⟨hs.2.2.1, hs.2.2.2.1⟩, hpt⟩


theorem bilin_pa_dot_n_of_point {o d q00 q10 q11 q01 : Vec3} {t u v : ℝ}
    (hpt : o + t • d = bilinEval q00 q10 q11 q01 u v) :
    (q00 - o + u • (q10 - q00)) ⬝ᵥ
      crossProduct d (q01 - q00 + u • (q11 - q10 - q01 + q00)) = 0 := by
  let e10 := q10 - q00
  let e00 := q01 - q00
  let dd := q11 - q10 - q01 + q00
  let Q0 := q00 - o
  let pa := Q0 + u • e10
  let D := e00 + u • dd
  let n := crossProduct d D
  have heq : t • d = pa + v • D := by
    have h0 : t • d = bilinEval q00 q10 q11 q01 u v - o := by
      rw [← hpt]
      abel
    rw [h0]
    dsimp [bilinEval, pa, D, e10, e00, dd, Q0]
    ext i
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hd : d ⬝ᵥ n = 0 := by
    dsimp [n]
    simp [dotProduct, cross_apply, Fin.sum_univ_three]
    ring
  have hD : D ⬝ᵥ n = 0 := by
    dsimp [n]
    simp [dotProduct, cross_apply, Fin.sum_univ_three]
    ring
  have hh := congrArg (fun x : Vec3 => x ⬝ᵥ n) heq
  rw [smul_dotProduct, add_dotProduct, smul_dotProduct, hd, hD] at hh
  -- hh : t * 0 = pa·n + v*0 -> 0 = pa·n
  simpa [pa, Q0, e10, D, e00, dd, n] using hh.symm


/-- A geometric bilinear hit gives a nonpositive ray parameter and the Cramer
    formulas, hence `bilinSolve` reports it (assuming the ruling is not
    parallel to the ray). -/
theorem bilinSolve_of_point {o d q00 q10 q11 q01 : Vec3} {t u v : ℝ}
    (hden : 0 < (crossProduct d (q01 - q00 + u • (q11 - q10 - q01 + q00))) ⬝ᵥ
      (crossProduct d (q01 - q00 + u • (q11 - q10 - q01 + q00))))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    {tmin tbest : ℝ} (htmin : tmin ≤ t) (htbest : t < tbest)
    (hpt : o + t • d = bilinEval q00 q10 q11 q01 u v) :
    bilinSolve d (q00 - o) (q10 - q00) (q01 - q00) (q11 - q10 - q01 + q00)
      tmin tbest u = some (t, u, v) := by
  unfold bilinSolve
  dsimp only
  set e10 := q10 - q00
  set e00 := q01 - q00
  set dd := q11 - q10 - q01 + q00
  set Q0 := q00 - o
  set pa := Q0 + u • e10
  set D := e00 + u • dd
  set n := crossProduct d D
  set den := n ⬝ᵥ n
  have hdenpos : 0 < den := by simpa [den, n, D, e00, dd] using hden
  have hden0 : den ≠ 0 := ne_of_gt hdenpos
  rw [if_neg (not_le.mpr hdenpos)]
  have heq : t • d = pa + v • D := by
    have h0 : t • d = bilinEval q00 q10 q11 q01 u v - o := by
      rw [← hpt]
      abel
    rw [h0]
    dsimp [bilinEval, pa, D, e10, e00, dd, Q0]
    ext i
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcrossD : crossProduct (t • d - v • D) D = t • n := by
    dsimp [n]
    ext i
    fin_cases i <;>
      simp [cross_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three] <;>
      ring
  have hcrossd : crossProduct (t • d - v • D) d = v • n := by
    dsimp [n]
    ext i
    fin_cases i <;>
      simp [cross_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three] <;>
      ring
  have heq' : t • d - v • D = pa := by
    rw [sub_eq_iff_eq_add]
    exact heq
  have htd : t = (crossProduct pa D ⬝ᵥ n) / den := by
    have hh := congrArg (fun x : Vec3 => crossProduct x D ⬝ᵥ n) heq'
    rw [hcrossD] at hh
    simp only [smul_dotProduct] at hh
    field_simp [hden0]
    simpa [den] using hh
  have hvd : v = (crossProduct pa d ⬝ᵥ n) / den := by
    have hh := congrArg (fun x : Vec3 => crossProduct x d ⬝ᵥ n) heq'
    rw [hcrossd] at hh
    simp only [smul_dotProduct] at hh
    field_simp [hden0]
    simpa [den] using hh
  rw [← htd, ← hvd]
  rw [if_pos ⟨hv0, hv1, htmin, htbest⟩]

theorem bilin_quad_of_pa (d Q0 e10 e00 dd : Vec3) (u : ℝ)
    (h : (Q0 + u • e10) ⬝ᵥ crossProduct d (e00 + u • dd) = 0) :
    (e10 ⬝ᵥ crossProduct d dd) * u ^ 2 +
      (Q0 ⬝ᵥ crossProduct d dd + e10 ⬝ᵥ crossProduct d e00) * u +
      (Q0 ⬝ᵥ crossProduct d e00) = 0 := by
  have heq : (Q0 + u • e10) ⬝ᵥ crossProduct d (e00 + u • dd) =
      (Q0 ⬝ᵥ crossProduct d e00) +
        (Q0 ⬝ᵥ crossProduct d dd + e10 ⬝ᵥ crossProduct d e00) * u +
        (e10 ⬝ᵥ crossProduct d dd) * u ^ 2 := by
    simp [dotProduct, cross_apply, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq] at h
  ring_nf at h ⊢
  exact h

theorem bilinReal_complete {o d q00 q10 q11 q01 : Vec3} {tmin tbest t u v : ℝ}
    (hA : (q10 - q00) ⬝ᵥ crossProduct d (q11 - q10 - q01 + q00) ≠ 0)
    (hden : 0 < (crossProduct d (q01 - q00 + u • (q11 - q10 - q01 + q00))) ⬝ᵥ
      (crossProduct d (q01 - q00 + u • (q11 - q10 - q01 + q00))))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hpt : o + t • d = bilinEval q00 q10 q11 q01 u v) :
    ∃ (t' u' v' : ℝ), bilinReal o d q00 q10 q11 q01 tmin tbest = some (t', u', v') := by
  let e10 := q10 - q00
  let e00 := q01 - q00
  let dd := q11 - q10 - q01 + q00
  let Q0 := q00 - o
  let A := e10 ⬝ᵥ crossProduct d dd
  let B := Q0 ⬝ᵥ crossProduct d dd + e10 ⬝ᵥ crossProduct d e00
  let C := Q0 ⬝ᵥ crossProduct d e00
  let results := (quadRootsList A B C 0 2).filter (fun u => u ≤ 1)
  have hA' : A ≠ 0 := by
    intro hz
    apply hA
    dsimp [A, e10, dd] at hz
    ring_nf at hz ⊢
    exact hz
  have hpa := bilin_pa_dot_n_of_point hpt
  have hquad : A * u ^ 2 + B * u + C = 0 := by
    dsimp [A, B, C, e10, e00, dd, Q0]
    exact bilin_quad_of_pa d (q00 - o) (q10 - q00) (q01 - q00)
      (q11 - q10 - q01 + q00) u hpa
  have hult2 : u < 2 := by linarith
  have hu_roots : u ∈ quadRootsList A B C 0 2 :=
    quadRootsList_complete hA' hquad hu0 hult2
  have hu_results : u ∈ results := by
    unfold results
    simp [hu_roots, hu1]
  have hsolve : bilinSolve d Q0 e10 e00 dd tmin tbest u = some (t, u, v) := by
    simpa [Q0, e10, e00, dd] using bilinSolve_of_point hden hu0 hu1 hv0 hv1 htmin htbest hpt
  have hmem : some (t, u, v) ∈ results.map (bilinSolve d Q0 e10 e00 dd tmin tbest) := by
    exact List.mem_map.mpr ⟨u, hu_results, hsolve⟩
  obtain ⟨⟨t', u', v'⟩, hres⟩ := firstSome_exists hmem
  exact ⟨t', u', v', by
    unfold bilinReal
    simpa only [e10, e00, dd, Q0, A, B, C, results] using hres⟩

end
end LightRT.Geom
