/-
  Stage 1: real-number geometry over ℝ³ (`Fin 3 → ℝ`, Mathlib's `⬝ᵥ` and `×₃`).
-/
import Mathlib

namespace LightRT.Geom

abbrev Vec3 := Fin 3 → ℝ

/-- A ray segment `{o + t d | tmin ≤ t ≤ tmax}`. -/
structure Ray where
  o : Vec3
  d : Vec3
  tmin : ℝ
  tmax : ℝ

def Ray.at (r : Ray) (t : ℝ) : Vec3 := r.o + t • r.d

/-- Axis-aligned box `[lo, hi]` (may be empty when some `lo i > hi i`). -/
structure Box where
  lo : Vec3
  hi : Vec3

def Box.Mem (b : Box) (p : Vec3) : Prop := ∀ i, b.lo i ≤ p i ∧ p i ≤ b.hi i

def Box.Subset (a b : Box) : Prop := ∀ i, b.lo i ≤ a.lo i ∧ a.hi i ≤ b.hi i

theorem Box.Subset.trans {a b c : Box} (h1 : a.Subset b) (h2 : b.Subset c) : a.Subset c :=
  fun i => ⟨(h2 i).1.trans (h1 i).1, (h1 i).2.trans (h2 i).2⟩

noncomputable def Box.union (a b : Box) : Box :=
  ⟨fun i => min (a.lo i) (b.lo i), fun i => max (a.hi i) (b.hi i)⟩

theorem Box.Subset.mem {a b : Box} (h : a.Subset b) {p : Vec3} (hp : a.Mem p) : b.Mem p :=
  fun i => ⟨(h i).1.trans (hp i).1, (hp i).2.trans (h i).2⟩

theorem Box.subset_union_left (a b : Box) : a.Subset (a.union b) :=
  fun _ => ⟨min_le_left _ _, le_max_left _ _⟩

theorem Box.subset_union_right (a b : Box) : b.Subset (a.union b) :=
  fun _ => ⟨min_le_right _ _, le_max_right _ _⟩

/-- Geometric ground truth for ray/box: some parameter in range lands in the box. -/
def HitsBox (r : Ray) (b : Box) : Prop :=
  ∃ t, r.tmin ≤ t ∧ t ≤ r.tmax ∧ b.Mem (r.at t)

/-- Closed triangle as the convex hull of three points (barycentric form). -/
def InTriangle (v0 v1 v2 p : Vec3) : Prop :=
  ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 ∧ p = v0 + u • (v1 - v0) + v • (v2 - v0)

/-- Geometric ground truth for ray/triangle on a half-open range `[tmin, tbest)`
    (matches LightRT's `tt < tmin || tt >= tbest` rejection). -/
def HitsTriangleAt (o d v0 v1 v2 : Vec3) (tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ InTriangle v0 v1 v2 (o + t • d)

end LightRT.Geom
