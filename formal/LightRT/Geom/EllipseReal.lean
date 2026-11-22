/-
  Ellipse point intersector (`TRI_POINT_ELLIPSE` in tri_point_isect_one):
  plane intersection through the centre with a normal, then membership in
  an ellipse with semi-axes ru/rv along the in-plane vectors u/v. Soundness
  and completeness over ℝ. Tier 1 item 1 of the formalization roadmap.
-/
import Mathlib
import LightRT.Geom.CapsuleReal

namespace LightRT.Geom
noncomputable section
open Matrix

/-- An ellipse point: the plane through `c` with normal `n`, carrying an
    ellipse with semi-axes `ru` (along `u`) and `rv` (along `v`). `u`, `v`
    span the plane. Mirrors `TRI_POINT_ELLIPSE` in `tri_point_isect_one`. -/
def OnEllipse (c n u v : Vec3) (ru rv : ℝ) (p : Vec3) : Prop :=
  let h := p - c
  h ⬝ᵥ n = 0 ∧ (h ⬝ᵥ u / ru) ^ 2 + (h ⬝ᵥ v / rv) ^ 2 < 1

def HitsEllipseAt (o dir c n u v : Vec3) (ru rv tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnEllipse c n u v ru rv (o + t • dir)

def ellipseReal (o dir c n u v : Vec3) (ru rv tmin tbest : ℝ) : Option ℝ :=
  let dn := dir ⬝ᵥ n
  if dn = 0 then none else
  let t := ((c - o) ⬝ᵥ n) / dn
  if tmin ≤ t ∧ t < tbest then
    let h := o + t • dir - c
    if (h ⬝ᵥ u / ru) ^ 2 + (h ⬝ᵥ v / rv) ^ 2 < 1 then some t else none
  else none

theorem ellipseReal_sound {o dir c n u v : Vec3} {ru rv tmin tbest t : ℝ}
    (h : ellipseReal o dir c n u v ru rv tmin tbest = some t) :
    HitsEllipseAt o dir c n u v ru rv tmin tbest t := by
  unfold ellipseReal at h
  dsimp only at h
  set tt := ((c - o) ⬝ᵥ n) / (dir ⬝ᵥ n) with htp
  by_cases hdn : dir ⬝ᵥ n = 0
  · simp [hdn] at h
  · simp [hdn] at h
    by_cases hrange : tmin ≤ tt ∧ tt < tbest
    · simp [hrange] at h
      have ht : t = tt := h.right.symm
      subst t
      have hplane : (o + tt • dir - c) ⬝ᵥ n = 0 := by
        rw [htp]
        rw [show o + (((c - o) ⬝ᵥ n) / (dir ⬝ᵥ n)) • dir - c =
            (o - c) + (((c - o) ⬝ᵥ n) / (dir ⬝ᵥ n)) • dir by abel]
        rw [add_dotProduct, smul_dotProduct]
        change (o - c) ⬝ᵥ n + ((c - o) ⬝ᵥ n / (dir ⬝ᵥ n)) * (dir ⬝ᵥ n) = 0
        rw [div_mul_cancel₀ _ hdn]
        rw [show c - o = -(o - c) by abel, neg_dotProduct]
        ring
      have hu_eq : (o + tt • dir - c) ⬝ᵥ u = o ⬝ᵥ u + tt * (dir ⬝ᵥ u) - c ⬝ᵥ u := by
        rw [show o + tt • dir - c = (o - c) + tt • dir by abel]
        rw [add_dotProduct, sub_dotProduct, smul_dotProduct]
        ring
      have hv_eq : (o + tt • dir - c) ⬝ᵥ v = o ⬝ᵥ v + tt * (dir ⬝ᵥ v) - c ⬝ᵥ v := by
        rw [show o + tt • dir - c = (o - c) + tt • dir by abel]
        rw [add_dotProduct, sub_dotProduct, smul_dotProduct]
        ring
      have hell : ((o + tt • dir - c) ⬝ᵥ u / ru) ^ 2 + ((o + tt • dir - c) ⬝ᵥ v / rv) ^ 2 < 1 := by
        rw [hu_eq, hv_eq]
        simpa [dotProduct, Fin.sum_univ_three] using h.left
      exact ⟨hrange.1, hrange.2, hplane, hell⟩
    · simp [hrange] at h

theorem ellipseReal_complete {o dir c n u v : Vec3} {ru rv tmin tbest t : ℝ}
    (hdn : dir ⬝ᵥ n ≠ 0) (hhit : HitsEllipseAt o dir c n u v ru rv tmin tbest t) :
    ellipseReal o dir c n u v ru rv tmin tbest = some t := by
  unfold ellipseReal
  dsimp only
  rw [if_neg hdn]
  have hplane := hhit.2.2.1
  rw [show o + t • dir - c = (o - c) + t • dir by abel] at hplane
  rw [add_dotProduct, smul_dotProduct] at hplane
  change (o - c) ⬝ᵥ n + t * (dir ⬝ᵥ n) = 0 at hplane
  have hprojEq : (c - o) ⬝ᵥ n = t * (dir ⬝ᵥ n) := by
    rw [show c - o = -(o - c) by abel, neg_dotProduct]
    linarith
  rw [hprojEq]
  rw [mul_div_cancel_right₀ _ hdn]
  have hell := hhit.2.2
  dsimp only [OnEllipse] at hell
  rw [if_pos ⟨hhit.1, hhit.2.1⟩]
  -- need the ellipse bound at tt = t; after the rw tt is t
  simpa using hell.2

end
end LightRT.Geom
