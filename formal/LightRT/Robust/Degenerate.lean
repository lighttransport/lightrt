/-
  Degenerate triangles are never hit (any `RoundingModel`).

  * Möller–Trumbore (`tri_isect_lane` / `tri_mt_one`, C operation order):
    if `e1 = 0` or `e2 = 0` (i.e. `v1 = v0` or `v2 = v0`; for finite floats
    `fl(x - y) = 0 ↔ x = y`), the computed `det` is exactly `0`, and the
    det test `!(-rel < det < rel)` rejects it because `rel ≥ 1e-12 > 0`.
  * Woop (`tri_woop_one`): if ANY two of the sheared vertices coincide, one
    edge function is `fl(x·y) - fl(y·x) = 0`, the other two are exact
    negatives of each other (`sub_antisymm` + `mul_comm'`, the antisymmetry the
    watertightness proof uses), so `det = ue + ve + we` is exactly `0` and
    `det == 0` rejects it.
  Consequence for traversal: such a primitive's `isect` is `none`, so it never
  changes a closest-hit or any-hit result (`Flat.foldl_nohit` / `runAny`);
  the spatial queries (closest point, kNN, region) still see it, which is why
  the builder keeps degenerate triangles. Bit level: `tools/cdiff.py`
  `degenerate` vectors (C, MiniC and `Ref` all miss, including ±0, ∞, NaN).
-/
import LightRT.FP.Model

namespace LightRT.Robust.Degenerate
open LightRT.FP

variable (R : RoundingModel)

theorem mul_zero_left (x : ℝ) : R.mul 0 x = 0 := by
  simp [RoundingModel.mul, R.fl_zero]

theorem mul_zero_right (x : ℝ) : R.mul x 0 = 0 := by
  simp [RoundingModel.mul, R.fl_zero]

theorem add_zero_zero : R.add 0 0 = 0 := by
  simp [RoundingModel.add, R.fl_zero]

theorem sub_zero_zero : R.sub 0 0 = 0 := by
  simp [RoundingModel.sub, R.fl_zero]

/-- `p = d × e2` as `tri_isect_lane` computes it. -/
noncomputable def mtP (d e2 : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![R.sub (R.mul (d 1) (e2 2)) (R.mul (d 2) (e2 1)),
    R.sub (R.mul (d 2) (e2 0)) (R.mul (d 0) (e2 2)),
    R.sub (R.mul (d 0) (e2 1)) (R.mul (d 1) (e2 0))]

/-- `det = (e1x·px + e1y·py) + e1z·pz`, C order. -/
noncomputable def mtDet (d e1 e2 : Fin 3 → ℝ) : ℝ :=
  let p := mtP R d e2
  R.add (R.add (R.mul (e1 0) (p 0)) (R.mul (e1 1) (p 1))) (R.mul (e1 2) (p 2))

theorem mtDet_e1_zero (d e2 : Fin 3 → ℝ) : mtDet R d 0 e2 = 0 := by
  simp [mtDet, mul_zero_left, add_zero_zero]

theorem mtDet_e2_zero (d e1 : Fin 3 → ℝ) : mtDet R d e1 0 = 0 := by
  simp [mtDet, mtP, mul_zero_right, sub_zero_zero, add_zero_zero]

/-- The MT det test `tri_isect_det_parallel`: reject unless `|det| ≥ rel`. -/
def mtParallel (rel det : ℝ) : Prop := -rel < det ∧ det < rel

/-- **MT never hits a triangle with a zero edge** (`rel` is clamped to
    `[1e-12, 1e-6]`, so `0 < rel`). -/
theorem mt_rejects_degenerate (d e1 e2 : Fin 3 → ℝ) (rel : ℝ) (hrel : 0 < rel)
    (h : e1 = 0 ∨ e2 = 0) : mtParallel rel (mtDet R d e1 e2) := by
  rcases h with rfl | rfl
  · rw [mtDet_e1_zero]; exact ⟨by linarith, hrel⟩
  · rw [mtDet_e2_zero]; exact ⟨by linarith, hrel⟩

/-- Woop edge functions on the sheared 2D vertices `a b c`, C expressions. -/
noncomputable def woopUE (b c : Fin 2 → ℝ) : ℝ := R.sub (R.mul (c 0) (b 1)) (R.mul (c 1) (b 0))
noncomputable def woopVE (a c : Fin 2 → ℝ) : ℝ := R.sub (R.mul (a 0) (c 1)) (R.mul (a 1) (c 0))
noncomputable def woopWE (a b : Fin 2 → ℝ) : ℝ := R.sub (R.mul (b 0) (a 1)) (R.mul (b 1) (a 0))
noncomputable def woopDet (a b c : Fin 2 → ℝ) : ℝ :=
  R.add (R.add (woopUE R b c) (woopVE R a c)) (woopWE R a b)

theorem edge_self (x : Fin 2 → ℝ) :
    R.sub (R.mul (x 0) (x 1)) (R.mul (x 1) (x 0)) = 0 := by
  rw [R.mul_comm' (x 1) (x 0)]; simp [RoundingModel.sub, R.fl_zero]

theorem add_neg_self (u : ℝ) : R.add u (-u) = 0 := by
  simp [RoundingModel.add, R.fl_zero]

theorem add_neg_self' (u : ℝ) : R.add (-u) u = 0 := by
  simp [RoundingModel.add, R.fl_zero]

/-- **Woop never hits a triangle with two coincident vertices** (`det = 0`). -/
theorem woop_det_ab (a c : Fin 2 → ℝ) : woopDet R a a c = 0 := by
  have hv : woopVE R a c = -woopUE R a c := by
    simp only [woopVE, woopUE]
    rw [R.mul_comm' (a 0) (c 1), R.mul_comm' (a 1) (c 0)]
    exact R.sub_antisymm _ _
  have hw : woopWE R a a = 0 := by
    simp only [woopWE]; rw [R.mul_comm' (a 0) (a 1)]; simp [RoundingModel.sub, R.fl_zero]
  simp only [woopDet, hv, hw, add_neg_self, add_zero_zero]

theorem woop_det_ac (a b : Fin 2 → ℝ) : woopDet R a b a = 0 := by
  have hv : woopVE R a a = 0 := by
    simp only [woopVE]; rw [R.mul_comm' (a 1) (a 0)]; simp [RoundingModel.sub, R.fl_zero]
  have hw : woopWE R a b = -woopUE R b a := by
    simp only [woopWE, woopUE]
    rw [R.mul_comm' (b 0) (a 1), R.mul_comm' (b 1) (a 0)]
    exact R.sub_antisymm _ _
  simp only [woopDet, hv, hw, woopUE, RoundingModel.sub, RoundingModel.add, add_zero, R.fl_idem,
    add_neg_cancel, R.fl_zero]

theorem woop_det_bc (a b : Fin 2 → ℝ) : woopDet R a b b = 0 := by
  have hu : woopUE R b b = 0 := by
    simp only [woopUE]; rw [R.mul_comm' (b 1) (b 0)]; simp [RoundingModel.sub, R.fl_zero]
  have hw : woopWE R a b = -woopVE R a b := by
    simp only [woopWE, woopVE]
    rw [R.mul_comm' (b 0) (a 1), R.mul_comm' (b 1) (a 0)]
    exact R.sub_antisymm _ _
  simp only [woopDet, hu, hw, woopVE, RoundingModel.sub, RoundingModel.add, zero_add, R.fl_idem,
    add_neg_cancel, R.fl_zero]

end LightRT.Robust.Degenerate
