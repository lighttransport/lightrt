/-
  De Casteljau subdivision of bicubic Bezier patches, over R. The u-split
  already exists in `BezPatchReal.lean`; here we add the v-split (by control-net
  transpose) and prove that a subpatch's control net represents the original
  patch on the corresponding parameter sub-box. This is the structural half of
  subdivision-plus-Newton completeness: culling a subcell by its control hull
  can never remove a true hit.
  Tier 1 item 1 of the roadmap.
-/
import Mathlib
import LightRT.Geom.BezPatchReal

namespace LightRT.Geom
open LightRT.Geom.Hull
noncomputable section

/-- Transpose the 4x4 control net (swap u and v), expressed via the Fin product
    equivalence so index arithmetic is by `simp` on the equivalence. -/
def transposeCP (cp : Fin 16 → Vec3) : Fin 16 → Vec3 :=
  fun k => let ji := (finProdFinEquiv (m:=4) (n:=4)).symm k
           cp ((finProdFinEquiv (m:=4) (n:=4)) (ji.2, ji.1))

theorem transposeCP_apply (cp : Fin 16 → Vec3) (j i : Fin 4) :
    transposeCP cp ((finProdFinEquiv (m:=4) (n:=4)) (j, i)) = cp ((finProdFinEquiv (m:=4) (n:=4)) (i, j)) := by
  simp [transposeCP]

theorem transposeCP_involutive (cp : Fin 16 → Vec3) :
    transposeCP (transposeCP cp) = cp := by
  ext k
  have hk : (finProdFinEquiv (m:=4) (n:=4)) ((finProdFinEquiv (m:=4) (n:=4)).symm k) = k :=
    (finProdFinEquiv (m:=4) (n:=4)).apply_symm_apply k
  rw [← hk]
  simp [transposeCP]

/-- The tensor Bernstein evaluation swaps with transposition. -/
theorem bicubicEval_transpose (cp : Fin 16 → Vec3) (u v : ℝ) :
    bicubicEval (transposeCP cp) u v = bicubicEval cp v u := by
  unfold bicubicEval
  -- Reindex the LHS through (j,i) ↦ equiv(i,j), so transposeCP_apply applies.
  rw [← Equiv.sum_comp ((Equiv.prodComm (Fin 4) (Fin 4)).trans
      (finProdFinEquiv (m:=4) (n:=4)))]
  rw [← Equiv.sum_comp (finProdFinEquiv (m:=4) (n:=4))]
  apply Finset.sum_congr rfl
  intro ji hj
  rcases ji with ⟨j, i⟩
  have hswap : ((Equiv.prodComm (Fin 4) (Fin 4)).trans
      (finProdFinEquiv (m:=4) (n:=4))) (j, i) =
      (finProdFinEquiv (m:=4) (n:=4)) (i, j) := by rfl
  rw [hswap]
  rw [transposeCP_apply]
  simp only [bern33]
  -- bern33 u v (equiv(i,j)) = bern3 u j * bern3 v i;
  -- bern33 v u (equiv(j,i)) = bern3 v i * bern3 u j
  have h1 : ((finProdFinEquiv (m:=4) (n:=4)) (i, j) : Fin 16).val % 4 = j.val := by
    simp [finProdFinEquiv]
  have h2 : ((finProdFinEquiv (m:=4) (n:=4)) (i, j) : Fin 16).val / 4 = i.val := by
    simp [finProdFinEquiv]; omega
  have h3 : ((finProdFinEquiv (m:=4) (n:=4)) (j, i) : Fin 16).val % 4 = i.val := by
    simp [finProdFinEquiv]
  have h4 : ((finProdFinEquiv (m:=4) (n:=4)) (j, i) : Fin 16).val / 4 = j.val := by
    simp [finProdFinEquiv]; omega
  simp only [h1, h2, h3, h4]
  rw [mul_comm (bern3 u j) (bern3 v i)]

/-- Split a bicubic patch's control net in the v direction at t (left half). -/
def splitBicubicV (cp : Fin 16 → Vec3) (t : ℝ) : Fin 16 → Vec3 :=
  transposeCP (splitBicubicU (transposeCP cp) t)

theorem bicubic_split_v_left (cp : Fin 16 → Vec3) (u t s : ℝ) :
    bicubicEval (splitBicubicV cp t) u s = bicubicEval cp u (t * s) := by
  unfold splitBicubicV
  rw [bicubicEval_transpose, bicubic_split_left, bicubicEval_transpose]

end
end LightRT.Geom
