/-
  Capsule surface intersector: nearest of a finite ray-cylinder side and the
  two end spheres. Mirrors the sphere+cylinder components of the round-linear
  curve intersector in lightrt_c_tri.c; soundness/completeness/nearest over ℝ.
  Tier 1 item 1 of the formalization roadmap.
-/
import Mathlib
import LightRT.Geom.CylinderReal

namespace LightRT.Geom
noncomputable section
open Matrix

/-- A capsule surface is the cylinder side plus the two end spheres. -/
def OnCapsule (p0 p1 : Vec3) (r : ℝ) (p : Vec3) : Prop :=
  OnCylinderSide p0 p1 r p ∨ distSq p p0 = r ^ 2 ∨ distSq p p1 = r ^ 2

def HitsCapsuleAt (o dir p0 p1 : Vec3) (r tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnCapsule p0 p1 r (o + t • dir)

def capsuleReal (o dir p0 p1 : Vec3) (r tmin tbest : ℝ) : Option ℝ :=
  nearestOpt [
    cylinderReal o dir p0 p1 r tmin tbest,
    sphereReal o dir p0 r tmin tbest,
    sphereReal o dir p1 r tmin tbest]

theorem capsuleReal_sound {o dir p0 p1 : Vec3} {r tmin tbest t : ℝ}
    (h : capsuleReal o dir p0 p1 r tmin tbest = some t) :
    HitsCapsuleAt o dir p0 p1 r tmin tbest t := by
  unfold capsuleReal at h
  rcases nearestOpt_mem h with ⟨o', ho', hot⟩
  simp at ho'
  rcases ho' with ho | ho | ho
  · have hs := cylinderReal_sound (ho.symm.trans hot)
    exact ⟨hs.1, hs.2.1, Or.inl hs.2.2⟩
  · have hs := sphereReal_sound (ho.symm.trans hot)
    exact ⟨hs.1, hs.2.1, Or.inr (Or.inl hs.2.2)⟩
  · have hs := sphereReal_sound (ho.symm.trans hot)
    exact ⟨hs.1, hs.2.1, Or.inr (Or.inr hs.2.2)⟩

theorem capsuleReal_complete {o dir p0 p1 : Vec3} {r tmin tbest t : ℝ}
    (hp0p1 : p0 ≠ p1) (hdir : perpTo dir (p1 - p0) ≠ 0)
    (hhit : HitsCapsuleAt o dir p0 p1 r tmin tbest t) :
    ∃ t', capsuleReal o dir p0 p1 r tmin tbest = some t' ∧ t' ≤ t := by
  unfold capsuleReal
  rcases hhit.2.2 with hcyl | hsph0 | hsph1
  · obtain ⟨tc, htc, hct⟩ := cylinderReal_complete hp0p1 hdir
      ⟨hhit.1, hhit.2.1, hcyl⟩
    obtain ⟨tres, hnear, hle⟩ := nearestOpt_le
      (l := [cylinderReal o dir p0 p1 r tmin tbest,
             sphereReal o dir p0 r tmin tbest,
             sphereReal o dir p1 r tmin tbest]) (t := tc)
      ⟨cylinderReal o dir p0 p1 r tmin tbest, by simp, htc⟩
    exact ⟨tres, hnear, hle.trans hct⟩
  · have hdir0 : dir ≠ 0 := by
      intro hd
      apply hdir
      simp [perpTo, hd]
    obtain ⟨tc, htc, hct⟩ := sphereReal_complete hdir0
      ⟨hhit.1, hhit.2.1, hsph0⟩
    obtain ⟨tres, hnear, hle⟩ := nearestOpt_le
      (l := [cylinderReal o dir p0 p1 r tmin tbest,
             sphereReal o dir p0 r tmin tbest,
             sphereReal o dir p1 r tmin tbest]) (t := tc)
      ⟨sphereReal o dir p0 r tmin tbest, by simp, htc⟩
    exact ⟨tres, hnear, hle.trans hct⟩
  · have hdir0 : dir ≠ 0 := by
      intro hd
      apply hdir
      simp [perpTo, hd]
    obtain ⟨tc, htc, hct⟩ := sphereReal_complete hdir0
      ⟨hhit.1, hhit.2.1, hsph1⟩
    obtain ⟨tres, hnear, hle⟩ := nearestOpt_le
      (l := [cylinderReal o dir p0 p1 r tmin tbest,
             sphereReal o dir p0 r tmin tbest,
             sphereReal o dir p1 r tmin tbest]) (t := tc)
      ⟨sphereReal o dir p1 r tmin tbest, by simp, htc⟩
    exact ⟨tres, hnear, hle.trans hct⟩

end
end LightRT.Geom
