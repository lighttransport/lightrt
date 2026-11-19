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


/-- A parameter cell: a sub-box of `[0,1]²` together with the de Casteljau
    control net of the patch restricted to that sub-box. -/
structure PatchCell where
  u0 : ℝ
  u1 : ℝ
  v0 : ℝ
  v1 : ℝ
  cp : Fin 16 → Vec3

/-- A cell represents a global patch if its local evaluation at `(s,r)` equals
    the global patch at the affine-mapped parameter. -/
def Represents (global : Fin 16 → Vec3) (c : PatchCell) : Prop :=
  ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ r ∈ Set.Icc (0:ℝ) 1,
    bicubicEval c.cp s r =
      bicubicEval global (c.u0 + (c.u1 - c.u0) * s) (c.v0 + (c.v1 - c.v0) * r)

/-- The root cell `[0,1]²` represents its own patch. -/
theorem root_represents (cp : Fin 16 → Vec3) :
    Represents cp ⟨0, 1, 0, 1, cp⟩ := by
  intro s hs r hr
  simp

/-- Splitting a representing cell in u at the midpoint yields a representing
    left subcell. -/
theorem split_u_left_represents (global : Fin 16 → Vec3) (c : PatchCell)
    (hc : Represents global c) (hu : c.u0 ≤ c.u1) :
    Represents global ⟨c.u0, (c.u0 + c.u1)/2, c.v0, c.v1,
      splitBicubicU c.cp (1/2 : ℝ)⟩ := by
  intro s hs r hr
  rw [bicubic_split_left]
  have hs' : (1/2 : ℝ) * s ∈ Set.Icc (0:ℝ) 1 := by constructor <;> nlinarith [hs.1, hs.2]
  rw [hc ((1/2 : ℝ) * s) hs' r hr]
  congr 1 <;> ring

/-- Splitting a representing cell in v at the midpoint yields a representing
    lower subcell. -/
theorem split_v_left_represents (global : Fin 16 → Vec3) (c : PatchCell)
    (hc : Represents global c) (hv : c.v0 ≤ c.v1) :
    Represents global ⟨c.u0, c.u1, c.v0, (c.v0 + c.v1)/2,
      splitBicubicV c.cp (1/2 : ℝ)⟩ := by
  intro s hs r hr
  rw [bicubic_split_v_left]
  have hr' : (1/2 : ℝ) * r ∈ Set.Icc (0:ℝ) 1 := by constructor <;> nlinarith [hr.1, hr.2]
  rw [hc s hs ((1/2 : ℝ) * r) hr']
  congr 1 <;> ring

/-- A cull test: there are bounds containing the cell's control net such that
    the ray misses that box on `[tmin, tbest)`. -/
def CellCulled (o d : Vec3) (tmin tbest : ℝ) (c : PatchCell) : Prop :=
  ∃ lo hi : Vec3, (∀ k i, lo i ≤ c.cp k i) ∧ (∀ k i, c.cp k i ≤ hi i) ∧
    ∀ t, tmin ≤ t → t < tbest → ¬ Box.Mem ⟨lo, hi⟩ (o + t • d)

/-- **Cull safety**: a representing cell that contains a true hit of the global
    patch is never culled. This is the key step for subdivision completeness:
    the cell containing the nearest hit survives every cull test. -/
theorem cell_not_culled_of_hit (o d : Vec3) (tmin tbest : ℝ)
    (global : Fin 16 → Vec3) (c : PatchCell) (hc : Represents global c)
    {u v t : ℝ} (hu : u ∈ Set.Icc c.u0 c.u1) (hv : v ∈ Set.Icc c.v0 c.v1)
    (huv : u ∈ Set.Icc (0:ℝ) 1) (hvv : v ∈ Set.Icc (0:ℝ) 1)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hpt : o + t • d = bicubicEval global u v)
    (huwidth : c.u0 < c.u1) (hvwidth : c.v0 < c.v1) :
    ¬ CellCulled o d tmin tbest c := by
  rintro ⟨lo, hi, hlo, hhi, hmiss⟩
  let s := (u - c.u0) / (c.u1 - c.u0)
  let r := (v - c.v0) / (c.v1 - c.v0)
  have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr (le_of_lt huwidth))
  have hs1 : s ≤ 1 := (div_le_one (sub_pos.mpr huwidth)).mpr (by linarith [hu.2])
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hv.1) (sub_nonneg.mpr (le_of_lt hvwidth))
  have hr1 : r ≤ 1 := (div_le_one (sub_pos.mpr hvwidth)).mpr (by linarith [hv.2])
  have hmap_u : c.u0 + (c.u1 - c.u0) * s = u := by
    dsimp [s]; field_simp [ne_of_gt (sub_pos.mpr huwidth)]; ring
  have hmap_v : c.v0 + (c.v1 - c.v0) * r = v := by
    dsimp [r]; field_simp [ne_of_gt (sub_pos.mpr hvwidth)]; ring
  have hrep := hc s ⟨hs0, hs1⟩ r ⟨hr0, hr1⟩
  rw [hmap_u, hmap_v] at hrep
  apply hmiss t htmin htbest
  rw [hpt, ← hrep]
  exact bicubicEval_in_box c.cp lo hi hlo hhi hs0 hs1 hr0 hr1
end
end LightRT.Geom
