/-
  Stage 1: Möller–Trumbore over ℝ (baseline, non-watertight in floating point).
  Mirrors `tri_mt_one` in lightrt_c_tri.c, including the `|det| < ε` rejection.
-/
import LightRT.Geom.Basic

namespace LightRT.Geom
noncomputable section
open Matrix

/-- Möller–Trumbore with determinant threshold `ε`; returns `(t, u, v)`. -/
def mtReal (o d v0 v1 v2 : Vec3) (ε tmin tbest : ℝ) : Option (ℝ × ℝ × ℝ) :=
  let e1 := v1 - v0
  let e2 := v2 - v0
  let p := crossProduct d e2
  let det := e1 ⬝ᵥ p
  if -ε < det ∧ det < ε then none else
  let tv := o - v0
  let u := (tv ⬝ᵥ p) / det
  if u < 0 ∨ 1 < u then none else
  let q := crossProduct tv e1
  let v := (d ⬝ᵥ q) / det
  if v < 0 ∨ 1 < u + v then none else
  let t := (e2 ⬝ᵥ q) / det
  if t < tmin ∨ tbest ≤ t then none else some (t, u, v)

/-- Soundness: a reported hit is a geometric hit with the reported barycentrics. -/
theorem mtReal_sound {o d v0 v1 v2 : Vec3} {ε tmin tbest t u v : ℝ} (hε : 0 ≤ ε)
    (h : mtReal o d v0 v1 v2 ε tmin tbest = some (t, u, v)) :
    HitsTriangleAt o d v0 v1 v2 tmin tbest t ∧
      o + t • d = v0 + u • (v1 - v0) + v • (v2 - v0) := by
  sorry

/-- Completeness away from the threshold: if `|det| ≥ ε` (and `ε > 0`, or the
    ray is not parallel to the plane when `ε = 0`) every geometric hit is found. -/
theorem mtReal_complete {o d v0 v1 v2 : Vec3} {ε tmin tbest t : ℝ}
    (hdet : ε ≤ |(v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0))|) (hdet0 : (v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0)) ≠ 0)
    (h : HitsTriangleAt o d v0 v1 v2 tmin tbest t) :
    ∃ u v, mtReal o d v0 v1 v2 ε tmin tbest = some (t, u, v) := by
  sorry

/-- Helper: Cramer's rule for the 3×3 system `[-d | e1 | e2] (t,u,v) = o - v0`. -/
theorem mt_cramer (o d v0 v1 v2 : Vec3) (t u v : ℝ)
    (hdet : (v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0)) ≠ 0) :
    o + t • d = v0 + u • (v1 - v0) + v • (v2 - v0) ↔
      (u = ((o - v0) ⬝ᵥ (crossProduct d (v2 - v0))) / ((v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0))) ∧
       v = (d ⬝ᵥ (crossProduct (o - v0) (v1 - v0))) / ((v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0))) ∧
       t = ((v2 - v0) ⬝ᵥ (crossProduct (o - v0) (v1 - v0))) / ((v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0)))) := by
  sorry

end
end LightRT.Geom
