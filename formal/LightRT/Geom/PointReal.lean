/-
  Real-number soundness/completeness for point primitives: ray-facing disc
  and oriented disc (mirrors `tri_point_isect_one` in lightrt_c_tri.c).
  Point spheres are already covered by `Geom/PrimReal.lean`'s `sphereReal`.
  Tier 1 item 1 of the formalization roadmap.
-/
import Mathlib
import LightRT.Geom.PrimReal

namespace LightRT.Geom
noncomputable section
open Matrix

def OnRayDisc (dir c : Vec3) (r : ℝ) (p : Vec3) : Prop :=
  (p - c) ⬝ᵥ dir = 0 ∧ distSq p c ≤ r ^ 2

def HitsRayDiscAt (o dir c : Vec3) (r tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnRayDisc dir c r (o + t • dir)

def rayDiscReal (o dir c : Vec3) (r tmin tbest : ℝ) : Option ℝ :=
  let dd := dir ⬝ᵥ dir
  if dd = 0 then none else
  let proj := ((c - o) ⬝ᵥ dir) / dd
  let perp := (c - o) - proj • dir
  let l2 := perp ⬝ᵥ perp
  if l2 ≤ r ^ 2 ∧ tmin ≤ proj ∧ proj < tbest then some proj else none

theorem rayDiscReal_sound {o dir c : Vec3} {r tmin tbest t : ℝ}
    (h : rayDiscReal o dir c r tmin tbest = some t) :
    HitsRayDiscAt o dir c r tmin tbest t := by
  unfold rayDiscReal at h
  dsimp only at h
  set proj := ((c - o) ⬝ᵥ dir) / (dir ⬝ᵥ dir) with hp
  set l2 := ((c - o) - proj • dir) ⬝ᵥ ((c - o) - proj • dir) with hl
  by_cases hdd : dir ⬝ᵥ dir = 0
  · simp [hdd] at h
  · simp [hdd] at h
    by_cases hcond : l2 ≤ r ^ 2 ∧ tmin ≤ proj ∧ proj < tbest
    · simp [hcond] at h
      have ht : t = proj := by simpa using h.symm
      subst t
      have hplane : (o + proj • dir - c) ⬝ᵥ dir = 0 := by
        rw [ht, hp]
        rw [show o + (((c - o) ⬝ᵥ dir) / (dir ⬝ᵥ dir)) • dir - c =
            (o - c) + (((c - o) ⬝ᵥ dir) / (dir ⬝ᵥ dir)) • dir by abel]
        rw [add_dotProduct, smul_dotProduct]
        change (o - c) ⬝ᵥ dir + ((c - o) ⬝ᵥ dir / (dir ⬝ᵥ dir)) * (dir ⬝ᵥ dir) = 0
        rw [div_mul_cancel₀ _ hdd]
        rw [show c - o = -(o - c) by abel, neg_dotProduct]
        ring
      have hds : distSq (o + proj • dir) c ≤ r ^ 2 := by
        have heq : distSq (o + proj • dir) c = l2 := by
          rw [hl]
          unfold distSq
          rw [show o + proj • dir - c = -((c - o) - proj • dir) by abel]
          apply Finset.sum_congr rfl
          intro x hx
          simp only [Pi.neg_apply]
          ring
        rw [heq]
        exact hcond.1
      exact ⟨hcond.2.1, hcond.2.2, hplane, hds⟩
    · simp [hcond] at h

theorem rayDiscReal_complete {o dir c : Vec3} {r tmin tbest t : ℝ} (hdir : dir ≠ 0)
    (hhit : HitsRayDiscAt o dir c r tmin tbest t) :
    rayDiscReal o dir c r tmin tbest = some t := by
  unfold rayDiscReal
  dsimp only
  have hdd : dir ⬝ᵥ dir ≠ 0 := ne_of_gt (dotProduct_self_pos dir hdir)
  rw [if_neg hdd]
  have hplane := hhit.2.2.1
  rw [show o + t • dir - c = (o - c) + t • dir by abel] at hplane
  rw [add_dotProduct, smul_dotProduct] at hplane
  change (o - c) ⬝ᵥ dir + t * (dir ⬝ᵥ dir) = 0 at hplane
  have hprojEq : (c - o) ⬝ᵥ dir = t * (dir ⬝ᵥ dir) := by
    rw [show c - o = -(o - c) by abel, neg_dotProduct]
    linarith
  rw [hprojEq]
  have hcancel : t * (dir ⬝ᵥ dir) / (dir ⬝ᵥ dir) = t := by
    rw [mul_div_cancel_right₀ _ hdd]
  rw [hcancel]
  have hl2 : (((c - o) - t • dir) ⬝ᵥ ((c - o) - t • dir)) ≤ r ^ 2 := by
    have hds := hhit.2.2
    unfold distSq at hds
    have heq : distSq (o + t • dir) c = ((c - o) - t • dir) ⬝ᵥ ((c - o) - t • dir) := by
      unfold distSq
      rw [show o + t • dir - c = -((c - o) - t • dir) by abel]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Pi.neg_apply]
      ring
    have hds2 := hds.2
    rw [heq] at hds2
    exact hds2
  rw [if_pos ⟨hl2, hhit.1, hhit.2.1⟩]

def OnOrientedDisc (c n : Vec3) (r : ℝ) (p : Vec3) : Prop :=
  (p - c) ⬝ᵥ n = 0 ∧ distSq p c ≤ r ^ 2

def HitsOrientedDiscAt (o dir c n : Vec3) (r tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnOrientedDisc c n r (o + t • dir)

def orientedDiscReal (o dir c n : Vec3) (r tmin tbest : ℝ) : Option ℝ :=
  let dn := dir ⬝ᵥ n
  if dn = 0 then none else
  let t := ((c - o) ⬝ᵥ n) / dn
  if tmin ≤ t ∧ t < tbest ∧ distSq (o + t • dir) c ≤ r ^ 2 then some t else none

theorem orientedDiscReal_sound {o dir c n : Vec3} {r tmin tbest t : ℝ}
    (h : orientedDiscReal o dir c n r tmin tbest = some t) :
    HitsOrientedDiscAt o dir c n r tmin tbest t := by
  unfold orientedDiscReal at h
  dsimp only at h
  set tt := ((c - o) ⬝ᵥ n) / (dir ⬝ᵥ n) with htp
  by_cases hdn : dir ⬝ᵥ n = 0
  · simp [hdn] at h
  · simp [hdn] at h
    by_cases hcond : tmin ≤ tt ∧ tt < tbest ∧ distSq (o + tt • dir) c ≤ r ^ 2
    · simp [hcond] at h
      have ht : t = tt := by simpa using h.symm
      subst t
      have hplane : (o + tt • dir - c) ⬝ᵥ n = 0 := by
        rw [ht, htp]
        rw [show o + (((c - o) ⬝ᵥ n) / (dir ⬝ᵥ n)) • dir - c =
            (o - c) + (((c - o) ⬝ᵥ n) / (dir ⬝ᵥ n)) • dir by abel]
        rw [add_dotProduct, smul_dotProduct]
        change (o - c) ⬝ᵥ n + ((c - o) ⬝ᵥ n / (dir ⬝ᵥ n)) * (dir ⬝ᵥ n) = 0
        rw [div_mul_cancel₀ _ hdn]
        rw [show c - o = -(o - c) by abel, neg_dotProduct]
        ring
      refine ⟨hcond.1, hcond.2.1, hplane, ?_⟩
      exact hcond.2.2
    · simp [hcond] at h

theorem orientedDiscReal_complete {o dir c n : Vec3} {r tmin tbest t : ℝ}
    (hdn : dir ⬝ᵥ n ≠ 0) (hhit : HitsOrientedDiscAt o dir c n r tmin tbest t) :
    orientedDiscReal o dir c n r tmin tbest = some t := by
  unfold orientedDiscReal
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
  rw [if_pos ⟨hhit.1, hhit.2.1, hhit.2.2.2⟩]

end
end LightRT.Geom
