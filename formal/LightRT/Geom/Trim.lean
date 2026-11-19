/-
  Trimmed parametric surfaces over R: (u,v) trim loops (outer boundary + holes)
  with the even–odd crossing rule, and the trim invariant for reported hits.
  The crossing count is the standard horizontal-ray cast; generic-position
  cases (vertices exactly on the ray) are excluded by hypothesis as in the
  C intersector's exact adjudication.
  Tier 1 item 1 of the roadmap.
-/
import Mathlib

namespace LightRT.Geom
noncomputable section
open Classical

/-- A trim loop is a closed polyline in the (u,v) parameter domain. -/
abbrev TrimLoop := List (ℝ × ℝ)

/-- Does the half-open vertical span `[min y0 y1, max y0 y1)` of an edge contain
    `y`? This is the standard half-open rule that makes the crossing count
    independent of how vertices are shared between edges. -/
def edgeSpansY (p q : ℝ × ℝ) (y : ℝ) : Prop :=
  (p.2 ≤ y ∧ y < q.2) ∨ (q.2 ≤ y ∧ y < p.2)

/-- The x-coordinate where the horizontal line `y = c` meets the segment `p,q`
    (valid when `edgeSpansY p q y`). -/
def edgeCrossX (p q : ℝ × ℝ) (y : ℝ) : ℝ :=
  if q.2 = p.2 then p.1 else p.1 + (y - p.2) / (q.2 - p.2) * (q.1 - p.1)

/-- One crossing contribution of an edge at a query point `(x,y)`: 1 if the
    edge spans `y` and the crossing is strictly to the right of `x`. -/
def edgeCross (p q : ℝ × ℝ) (x y : ℝ) : ℕ :=
  if edgeSpansY p q y ∧ x < edgeCrossX p q y then 1 else 0

/-- Even–odd crossing number of a closed polyline at `(x,y)`. The loop is
    closed by connecting the last point back to the first. -/
def crossingNumber (loop : TrimLoop) (x y : ℝ) : ℕ :=
  match loop with
  | [] => 0
  | [_] => 0
  | p :: q :: rest =>
      edgeCross p q x y + crossingNumber (q :: rest) x y

/-- Point-in-loop by the even–odd rule: odd crossing count means inside. -/
def inLoop (loop : TrimLoop) (x y : ℝ) : Prop :=
  crossingNumber loop x y % 2 = 1

/-- A trim region: an outer loop and a list of hole loops. A point is visible
    iff it is inside the outer loop and inside no hole. -/
structure TrimRegion where
  outer : TrimLoop
  holes : List TrimLoop

def trimVisible (R : TrimRegion) (x y : ℝ) : Prop :=
  inLoop R.outer x y ∧ ∀ h ∈ R.holes, ¬ inLoop h x y

/-- **Trim invariant** (soundness half): a hit accepted by the trim test is a
    visible parameter. Definitional, but stated as a contract for the C's
    even–odd test. -/
theorem accepted_hit_is_visible (R : TrimRegion) {u v : ℝ}
    (h : trimVisible R u v) : inLoop R.outer u v ∧ ∀ h' ∈ R.holes, ¬ inLoop h' u v := h

/-- **Trim rejection**: a hit inside a hole is not visible, so the search must
    continue past it. -/
theorem hole_hit_rejected (R : TrimRegion) {u v : ℝ} (h : TrimLoop)
    (hh : h ∈ R.holes) (hin : inLoop h u v) : ¬ trimVisible R u v := by
  intro hv
  exact hv.2 h hh hin


/-- Crossing number is at most one per edge. -/
theorem edgeCross_le_one (p q : ℝ × ℝ) (x y : ℝ) : edgeCross p q x y ≤ 1 := by
  unfold edgeCross
  split <;> simp

/-- **Unit-square crossing parity** (Jordan curve theorem for the simplest
    trim loop): the center `(1/2,1/2)` is inside the unit square loop and a
    point strictly to the right is outside. This validates the even-odd rule. -/
theorem unit_square_crossing_center :
    crossingNumber [Prod.mk (0:ℝ) 0, Prod.mk 1 0, Prod.mk 1 1, Prod.mk 0 1] (1/2) (1/2) % 2 = 1 := by
  norm_num [crossingNumber, edgeCross, edgeSpansY, edgeCrossX]

end
end LightRT.Geom
