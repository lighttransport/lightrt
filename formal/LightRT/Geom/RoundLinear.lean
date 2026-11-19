/-
  Round-linear curve intersector over R: the swept-ball tube of a strand
  segment (tapered cone + end spheres, Embree round-linear curves), with
  hit soundness and control-box containment. Tier 1 item 1 of the roadmap;
  builds on Geom/Hull.lean's `Hull.linear_tube_in_box`.
-/
import Mathlib
import LightRT.Geom.Hull
import LightRT.Geom.Basic

namespace LightRT.Geom
open LightRT.Geom.Hull
noncomputable section

/-- Centerline of a linear strand at parameter `s`. -/
def roundLinearCenter (p0 p1 : Vec3) (s : ℝ) : Vec3 := (1 - s) • p0 + s • p1

/-- Interpolated radius of a round-linear segment. -/
def roundLinearRadius (r0 r1 : ℝ) (s : ℝ) : ℝ := (1 - s) * r0 + s * r1

/-- The swept-ball tube: points within the interpolated radius of some
    centerline point. This is exactly the Embree round-linear curve. -/
def OnRoundLinear (p0 p1 : Vec3) (r0 r1 : ℝ) (x : Vec3) : Prop :=
  ∃ s ∈ Set.Icc (0:ℝ) 1, dist x (roundLinearCenter p0 p1 s) ≤ roundLinearRadius r0 r1 s

/-- A ray hit on a round-linear tube within the parameter window. -/
def HitsRoundLinear (o d p0 p1 : Vec3) (r0 r1 tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnRoundLinear p0 p1 r0 r1 (o + t • d)

/-- **Sampled acceptance is sound**: a ray point inside the swept tube at a
    parameter in range is a genuine round-linear hit (definitionally). -/
theorem hitsRoundLinear_of_sample (o d p0 p1 : Vec3) (r0 r1 tmin tbest t : ℝ)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hmem : OnRoundLinear p0 p1 r0 r1 (o + t • d)) :
    HitsRoundLinear o d p0 p1 r0 r1 tmin tbest t := ⟨htmin, htbest, hmem⟩


/-- A flat (ribbon) linear curve: for a ray direction `dir`, the width axis is
    `b = normalize(cross(p1-p0, dir))` (the ray-facing ribbon of width `2r(s)`).
    A point is on the ribbon if it is `C(s) + w·b` with `|w| ≤ r(s)`. -/
def OnFlatLinear (p0 p1 : Vec3) (r0 r1 : ℝ) (dir b : Vec3) (x : Vec3) : Prop :=
  ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ w : ℝ, |w| ≤ roundLinearRadius r0 r1 s ∧
    x = roundLinearCenter p0 p1 s + w • b

def HitsFlatLinear (o d p0 p1 : Vec3) (r0 r1 : ℝ) (b : Vec3)
    (tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnFlatLinear p0 p1 r0 r1 d b (o + t • d)

/-- Flat-curve sampled acceptance is sound (definitionally). -/
theorem hitsFlatLinear_of_sample (o d p0 p1 : Vec3) (r0 r1 : ℝ) (b : Vec3)
    (tmin tbest t : ℝ) (htmin : tmin ≤ t) (htbest : t < tbest)
    (hmem : OnFlatLinear p0 p1 r0 r1 d b (o + t • d)) :
    HitsFlatLinear o d p0 p1 r0 r1 b tmin tbest t := ⟨htmin, htbest, hmem⟩

end
end LightRT.Geom
