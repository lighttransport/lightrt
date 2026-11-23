/-
  Point-to-triangle squared distance over ℝ, defined as the infimum of
  `distSq p q` over the closed triangle. Used by the kNN/closest-point
  contracts: the infimum needs no explicit minimizer formula, but it is still
  bounded below by every enclosing box's point distance, which is what makes
  box pruning conservative.
-/
import Mathlib
import LightRT.Geom.Basic
import LightRT.Geom.PrimReal
import LightRT.Geom.Region

namespace LightRT.Geom
noncomputable section
open Matrix

theorem distSq_comm (a b : Vec3) : distSq a b = distSq b a := by
  unfold distSq
  simp only [dotProduct, Fin.sum_univ_three, Pi.sub_apply]
  ring

/-- The exact squared distance from `p` to the closed triangle `v0 v1 v2`. -/
def pointTriDistSq (p v0 v1 v2 : Vec3) : ℝ :=
  sInf { d : ℝ | ∃ q, InTriangle v0 v1 v2 q ∧ d = distSq p q }

theorem pointTriSet_bddBelow (p v0 v1 v2 : Vec3) :
    BddBelow { d : ℝ | ∃ q, InTriangle v0 v1 v2 q ∧ d = distSq p q } := by
  refine ⟨0, ?_⟩
  intro d hd
  rcases hd with ⟨q, hq, rfl⟩
  exact distSq_nonneg p q

theorem pointTriSet_nonempty (p v0 v1 v2 : Vec3) :
    ({ d : ℝ | ∃ q, InTriangle v0 v1 v2 q ∧ d = distSq p q } : Set ℝ).Nonempty := by
  refine ⟨distSq p v0, v0, ?_, rfl⟩
  refine ⟨0, 0, le_rfl, le_rfl, by norm_num, ?_⟩
  simp

theorem pointTriDistSq_nonneg (p v0 v1 v2 : Vec3) : 0 ≤ pointTriDistSq p v0 v1 v2 := by
  unfold pointTriDistSq
  exact le_csInf (pointTriSet_nonempty p v0 v1 v2)
    (by intro d hd; rcases hd with ⟨q, hq, rfl⟩; exact distSq_nonneg p q)

theorem pointTriDistSq_le_of_mem (p v0 v1 v2 q : Vec3) (hq : InTriangle v0 v1 v2 q) :
    pointTriDistSq p v0 v1 v2 ≤ distSq p q := by
  unfold pointTriDistSq
  exact csInf_le (pointTriSet_bddBelow p v0 v1 v2) ⟨q, hq, rfl⟩

/-- If the triangle lies in a box, the box's point distance is a lower bound
    on the exact triangle distance (the pruning key for kNN). -/
theorem boxPointDistSq_le_pointTriDistSq (p v0 v1 v2 : Vec3) (b : Box)
    (htri : ∀ q, InTriangle v0 v1 v2 q → b.Mem q) :
    boxPointDistSq b p ≤ pointTriDistSq p v0 v1 v2 := by
  unfold pointTriDistSq
  apply le_csInf (pointTriSet_nonempty p v0 v1 v2)
  intro d hd
  rcases hd with ⟨q, hq, rfl⟩
  rw [distSq_comm]
  exact boxPointDistSq_le_of_mem (b := b) (q := q) (c := p) (htri q hq)

/-- A box containing the triangle is conservative for the box-point distance. -/
theorem boxPointDistSq_le_of_tri_subset (p v0 v1 v2 : Vec3) (b b' : Box)
    (hsub : b'.Subset b) (htri : ∀ q, InTriangle v0 v1 v2 q → b'.Mem q) :
    boxPointDistSq b p ≤ pointTriDistSq p v0 v1 v2 := by
  apply boxPointDistSq_le_pointTriDistSq p v0 v1 v2 b
  intro q hq
  exact hsub.mem (htri q hq)

end
end LightRT.Geom
