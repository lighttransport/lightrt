/-
  Real-number soundness/completeness/nearest for a finite ray-cylinder side
  (axis p0->p1, radius r). Uses a root-list solver so completeness holds even
  when the nearest quadratic root fails the axial-in-[0,1] test. Reusable for
  round-linear/capsule curve intersectors. Tier 1 item 1.
-/
import Mathlib
import LightRT.Geom.PointReal

namespace LightRT.Geom
noncomputable section
open Matrix

def perpTo (x a : Vec3) : Vec3 :=
  x - ((x ⬝ᵥ a) / (a ⬝ᵥ a)) • a

def perpSq (x a : Vec3) : ℝ := perpTo x a ⬝ᵥ perpTo x a

theorem perpTo_lin (x y a : Vec3) (t : ℝ) :
    perpTo (x + t • y) a = perpTo x a + t • perpTo y a := by
  unfold perpTo
  rw [add_dotProduct, smul_dotProduct]
  ext i
  simp only [dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf

theorem perpSq_lin (x y a : Vec3) (t : ℝ) :
    perpSq (x + t • y) a = (perpTo x a + t • perpTo y a) ⬝ᵥ (perpTo x a + t • perpTo y a) := by
  unfold perpSq
  rw [perpTo_lin]

theorem dot_add_smul_sq (u v : Vec3) (t : ℝ) :
    (u + t • v) ⬝ᵥ (u + t • v) = (v ⬝ᵥ v) * t ^ 2 + 2 * (u ⬝ᵥ v) * t + u ⬝ᵥ u := by
  simp [dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  ring

def quadRootsList (A B C tmin tbest : ℝ) : List ℝ :=
  if A = 0 then [] else
  let Δ := B ^ 2 - 4 * A * C
  if Δ < 0 then [] else
  let s := Real.sqrt Δ
  [(-B - s) / (2 * A), (-B + s) / (2 * A)].filter (fun t => tmin ≤ t ∧ t < tbest)

theorem quadRootsList_mem {A B C tmin tbest t : ℝ} (h : t ∈ quadRootsList A B C tmin tbest) :
    A * t ^ 2 + B * t + C = 0 ∧ tmin ≤ t ∧ t < tbest := by
  unfold quadRootsList at h
  by_cases hA : A = 0
  · simp [hA] at h
  by_cases hΔ : B ^ 2 - 4 * A * C < 0
  · simp [hA, hΔ] at h
  simp [hA, hΔ] at h
  rcases h with ⟨hEq, hlo, hhi⟩
  rcases hEq with hr | hr
  · exact ⟨(sphere_quad_roots hA (le_of_not_gt hΔ)).2 (Or.inl hr), hlo, hhi⟩
  · exact ⟨(sphere_quad_roots hA (le_of_not_gt hΔ)).2 (Or.inr hr), hlo, hhi⟩

theorem quadRootsList_complete {A B C tmin tbest t : ℝ} (hA : A ≠ 0)
    (hquad : A * t ^ 2 + B * t + C = 0) (hlo : tmin ≤ t) (hhi : t < tbest) :
    t ∈ quadRootsList A B C tmin tbest := by
  unfold quadRootsList
  rw [if_neg hA]
  have hΔnonneg : 0 ≤ B ^ 2 - 4 * A * C := by
    have hC : C = -A * t ^ 2 - B * t := by linarith
    rw [hC]
    nlinarith [sq_nonneg (B + 2 * A * t)]
  rw [if_neg (not_lt.mpr hΔnonneg)]
  have hroots := (sphere_quad_roots hA hΔnonneg).1 hquad
  simp only [List.mem_filter, List.mem_cons, List.mem_nil_iff, or_false]
  rcases hroots with ht | ht
  · rw [← ht]; simp [hlo, hhi]
  · rw [← ht]; simp [hlo, hhi]

def cylinderCandidates (A B C tmin tbest : ℝ) (axial : ℝ → ℝ) : List ℝ :=
  (quadRootsList A B C tmin tbest).filter (fun t => 0 ≤ axial t ∧ axial t ≤ 1)

def solveCylinder (aa A B C : ℝ) (axial : ℝ → ℝ) (tmin tbest : ℝ) : Option ℝ :=
  if aa = 0 then none else if A = 0 then none else
  nearestOpt ((cylinderCandidates A B C tmin tbest axial).map some)

theorem solveCylinder_sound {aa A B C tmin tbest t : ℝ} (axial : ℝ → ℝ)
    (haa : aa ≠ 0) (hA : A ≠ 0)
    (h : solveCylinder aa A B C axial tmin tbest = some t) :
    t ∈ cylinderCandidates A B C tmin tbest axial := by
  unfold solveCylinder at h
  rw [if_neg haa, if_neg hA] at h
  have hmem := nearestOpt_mem h
  rcases hmem with ⟨o', ho', hot⟩
  simp only [List.mem_map] at ho'
  rcases ho' with ⟨tc, htc, hotc⟩
  subst o'
  have htc_eq : tc = t := Option.some.inj hotc
  subst tc
  exact htc

theorem solveCylinder_complete {aa A B C tmin tbest t : ℝ} (axial : ℝ → ℝ)
    (haa : aa ≠ 0) (hA : A ≠ 0) (hquad : A * t ^ 2 + B * t + C = 0)
    (hlo : tmin ≤ t) (hhi : t < tbest) (hax : 0 ≤ axial t ∧ axial t ≤ 1) :
    ∃ t', solveCylinder aa A B C axial tmin tbest = some t' ∧ t' ≤ t := by
  have htmem : t ∈ quadRootsList A B C tmin tbest :=
    quadRootsList_complete hA hquad hlo hhi
  have htCands : t ∈ cylinderCandidates A B C tmin tbest axial := by
    unfold cylinderCandidates
    simp [htmem, hax]
  unfold solveCylinder
  rw [if_neg haa, if_neg hA]
  apply nearestOpt_le
  exact ⟨some t, by simp [htCands], rfl⟩

def OnCylinderSide (p0 p1 : Vec3) (r : ℝ) (p : Vec3) : Prop :=
  let a := p1 - p0
  perpSq (p - p0) a = r ^ 2 ∧
  0 ≤ ((p - p0) ⬝ᵥ a) / (a ⬝ᵥ a) ∧ ((p - p0) ⬝ᵥ a) / (a ⬝ᵥ a) ≤ 1

def HitsCylinderSideAt (o dir p0 p1 : Vec3) (r tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnCylinderSide p0 p1 r (o + t • dir)

def cylinderReal (o dir p0 p1 : Vec3) (r tmin tbest : ℝ) : Option ℝ :=
  solveCylinder
    ((p1 - p0) ⬝ᵥ (p1 - p0))
    (perpTo dir (p1 - p0) ⬝ᵥ perpTo dir (p1 - p0))
    (2 * (perpTo (o - p0) (p1 - p0) ⬝ᵥ perpTo dir (p1 - p0)))
    (perpTo (o - p0) (p1 - p0) ⬝ᵥ perpTo (o - p0) (p1 - p0) - r ^ 2)
    (fun s => ((o - p0) ⬝ᵥ (p1 - p0)) / ((p1 - p0) ⬝ᵥ (p1 - p0)) +
      s * (dir ⬝ᵥ (p1 - p0)) / ((p1 - p0) ⬝ᵥ (p1 - p0)))
    tmin tbest

theorem cylinderReal_sound {o dir p0 p1 : Vec3} {r tmin tbest t : ℝ}
    (h : cylinderReal o dir p0 p1 r tmin tbest = some t) :
    HitsCylinderSideAt o dir p0 p1 r tmin tbest t := by
  unfold cylinderReal at h
  by_cases haa : (p1 - p0) ⬝ᵥ (p1 - p0) = 0
  · simp [solveCylinder, haa] at h
  by_cases hA : perpTo dir (p1 - p0) ⬝ᵥ perpTo dir (p1 - p0) = 0
  · simp [solveCylinder, haa, hA] at h
  have hcand := solveCylinder_sound (axial := fun s =>
      ((o - p0) ⬝ᵥ (p1 - p0)) / ((p1 - p0) ⬝ᵥ (p1 - p0)) +
      s * (dir ⬝ᵥ (p1 - p0)) / ((p1 - p0) ⬝ᵥ (p1 - p0))) haa hA h
  have hrootmem : t ∈ quadRootsList
      (perpTo dir (p1-p0) ⬝ᵥ perpTo dir (p1-p0))
      (2 * (perpTo (o-p0) (p1-p0) ⬝ᵥ perpTo dir (p1-p0)))
      (perpTo (o-p0) (p1-p0) ⬝ᵥ perpTo (o-p0) (p1-p0) - r^2) tmin tbest :=
    (List.mem_filter.mp hcand).1
  have hroot := quadRootsList_mem hrootmem
  have hax_dec := (List.mem_filter.mp hcand).2
  have hax : 0 ≤ ((o - p0) ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) +
        t * (dir ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) ∧
      ((o - p0) ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) +
        t * (dir ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) ≤ 1 := by
    simpa using hax_dec
  have hperp : perpSq ((o - p0) + t • dir) (p1 - p0) =
      (perpTo (o-p0) (p1-p0) + t • perpTo dir (p1-p0)) ⬝ᵥ
      (perpTo (o-p0) (p1-p0) + t • perpTo dir (p1-p0)) := by
    exact perpSq_lin (o-p0) dir (p1-p0) t
  have hquad_exp : (perpTo (o-p0) (p1-p0) + t • perpTo dir (p1-p0)) ⬝ᵥ
      (perpTo (o-p0) (p1-p0) + t • perpTo dir (p1-p0)) =
      (perpTo dir (p1-p0) ⬝ᵥ perpTo dir (p1-p0)) * t^2 +
      (2 * (perpTo (o-p0) (p1-p0) ⬝ᵥ perpTo dir (p1-p0))) * t +
      (perpTo (o-p0) (p1-p0) ⬝ᵥ perpTo (o-p0) (p1-p0) - r^2) + r^2 := by
    rw [dot_add_smul_sq]
    ring
  have hpsq : perpSq (o + t • dir - p0) (p1 - p0) = r ^ 2 := by
    have heqv : o + t • dir - p0 = (o - p0) + t • dir := by abel
    rw [heqv, hperp, hquad_exp]
    nlinarith [hroot.1]
  have hax' : 0 ≤ ((o + t • dir - p0) ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) ∧
      ((o + t • dir - p0) ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) ≤ 1 := by
    have heqv : o + t • dir - p0 = (o - p0) + t • dir := by abel
    rw [heqv, add_dotProduct, smul_dotProduct]
    have heqform : (((o - p0) ⬝ᵥ (p1-p0)) + t • (dir ⬝ᵥ (p1-p0))) /
        ((p1-p0) ⬝ᵥ (p1-p0)) = ((o - p0) ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) +
        t * ((dir ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0))) := by ring
    rw [heqform]
    simpa [mul_div_assoc] using hax
  exact ⟨hroot.2.1, hroot.2.2, hpsq, hax'.1, hax'.2⟩

theorem cylinderReal_complete {o dir p0 p1 : Vec3} {r tmin tbest t : ℝ}
    (hp0p1 : p0 ≠ p1) (hdir : perpTo dir (p1 - p0) ≠ 0)
    (hhit : HitsCylinderSideAt o dir p0 p1 r tmin tbest t) :
    ∃ t', cylinderReal o dir p0 p1 r tmin tbest = some t' ∧ t' ≤ t := by
  have haa : (p1 - p0) ⬝ᵥ (p1 - p0) ≠ 0 := by
    intro hz
    by_cases hzero : p1 - p0 = 0
    · apply hp0p1
      ext i
      have hzi : p1 i - p0 i = 0 := by
        simpa [Pi.sub_apply] using congrFun hzero i
      linarith
    · have hpos := dotProduct_self_pos (p1 - p0) hzero
      linarith
  have hA : perpTo dir (p1-p0) ⬝ᵥ perpTo dir (p1-p0) ≠ 0 :=
    ne_of_gt (dotProduct_self_pos (perpTo dir (p1-p0)) hdir)
  have hperp : perpSq ((o - p0) + t • dir) (p1 - p0) =
      (perpTo (o-p0) (p1-p0) + t • perpTo dir (p1-p0)) ⬝ᵥ
      (perpTo (o-p0) (p1-p0) + t • perpTo dir (p1-p0)) := by
    exact perpSq_lin (o-p0) dir (p1-p0) t
  have hquad_exp : (perpTo (o-p0) (p1-p0) + t • perpTo dir (p1-p0)) ⬝ᵥ
      (perpTo (o-p0) (p1-p0) + t • perpTo dir (p1-p0)) =
      (perpTo dir (p1-p0) ⬝ᵥ perpTo dir (p1-p0)) * t^2 +
      (2 * (perpTo (o-p0) (p1-p0) ⬝ᵥ perpTo dir (p1-p0))) * t +
      (perpTo (o-p0) (p1-p0) ⬝ᵥ perpTo (o-p0) (p1-p0) - r^2) + r^2 := by
    rw [dot_add_smul_sq]
    ring
  have hpsq := hhit.2.2.1
  have hquad : (perpTo dir (p1-p0) ⬝ᵥ perpTo dir (p1-p0)) * t^2 +
      (2 * (perpTo (o-p0) (p1-p0) ⬝ᵥ perpTo dir (p1-p0))) * t +
      (perpTo (o-p0) (p1-p0) ⬝ᵥ perpTo (o-p0) (p1-p0) - r^2) = 0 := by
    have heqv : o + t • dir - p0 = (o - p0) + t • dir := by abel
    rw [heqv, hperp, hquad_exp] at hpsq
    nlinarith
  have hax : 0 ≤ ((o - p0) ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) +
        t * (dir ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) ∧
      ((o - p0) ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) +
        t * (dir ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) ≤ 1 := by
    unfold HitsCylinderSideAt OnCylinderSide at hhit
    dsimp only at hhit
    have heqv : o + t • dir - p0 = (o - p0) + t • dir := by abel
    rw [heqv, add_dotProduct, smul_dotProduct] at hhit
    have heqform : (((o - p0) ⬝ᵥ (p1-p0)) + t • (dir ⬝ᵥ (p1-p0))) /
        ((p1-p0) ⬝ᵥ (p1-p0)) = ((o - p0) ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0)) +
        t * ((dir ⬝ᵥ (p1-p0)) / ((p1-p0) ⬝ᵥ (p1-p0))) := by ring
    rw [heqform] at hhit
    simpa [mul_div_assoc] using hhit.2.2.2
  unfold cylinderReal
  exact solveCylinder_complete (axial := fun s =>
      ((o - p0) ⬝ᵥ (p1 - p0)) / ((p1 - p0) ⬝ᵥ (p1 - p0)) +
      s * (dir ⬝ᵥ (p1 - p0)) / ((p1 - p0) ⬝ᵥ (p1 - p0))) haa hA hquad hhit.1 hhit.2.1 hax

end
end LightRT.Geom
