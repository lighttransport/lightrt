/-
  The false miss of the uninflated slab test, as a theorem about the abstract
  rounding model instantiated at binary32 (`Binary32.model`), over ℝ.
-/
import LightRT.Robust.Slab
namespace LightRT.Robust
open LightRT.FP LightRT.Geom LightRT.FP.Binary32

def wq (w : UInt32) : ℚ := ((decode w).toQ?).getD 0
def wo : Fin 3 → ℚ := ![wq 0x4214f160, wq 0x40ba8c35, wq 0xc02359b9]
def wd : Fin 3 → ℚ := ![wq 0x3a0c6eed, wq 0xbb3a8fe3, wq 0xc0c945fd]
def wlo : Fin 3 → ℚ := ![wq 0x4215a949, wq 0x409c01e8, wq 0xc503fec2]
def whi : Fin 3 → ℚ := ![wq 0x42180434, wq 0x4133809d, wq 0xc503f416]
def wtmax : ℚ := 2 ^ 64

def tQ (x : ℚ) (i : Fin 3) : ℚ := rne (rne (x - wo i) * rne (1 / wd i))
def nearQ (i : Fin 3) : ℚ := min (tQ (wlo i) i) (tQ (whi i) i)
def farQ (i : Fin 3) : ℚ := max (tQ (wlo i) i) (tQ (whi i) i)
def slabQ : Bool := decide (max (max (nearQ 0) (nearQ 1)) (max (nearQ 2) 0) ≤
    rne (min (min (farQ 0) (farQ 1)) (min (farQ 2) wtmax) * 1))

set_option maxRecDepth 100000 in
theorem slabQ_false : slabQ = false := by decide +kernel

def exactQ : Bool :=
  let a := fun i : Fin 3 => (wlo i - wo i) / wd i
  let b := fun i : Fin 3 => (whi i - wo i) / wd i
  decide (max (max (min (a 0) (b 0)) (min (a 1) (b 1))) (max (min (a 2) (b 2)) 0) ≤
    min (min (max (a 0) (b 0)) (max (a 1) (b 1))) (min (max (a 2) (b 2)) wtmax))

set_option maxRecDepth 100000 in
theorem exactQ_true : exactQ = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem w_repr : ∀ i, rne (wo i) = wo i ∧ rne (wd i) = wd i ∧ rne (wlo i) = wlo i ∧
    rne (whi i) = whi i := by decide +kernel

set_option maxRecDepth 100000 in
theorem w_facts : ∀ i, wd i ≠ 0 ∧ wlo i ≤ whi i := by decide +kernel

def wRay : Ray := ⟨fun i => (wo i : ℝ), fun i => (wd i : ℝ), 0, (wtmax : ℝ)⟩
def wBox : Box := ⟨fun i => (wlo i : ℝ), fun i => (whi i : ℝ)⟩

theorem wBox_lo (i : Fin 3) : wBox.lo i = (wlo i : ℝ) := rfl
theorem wBox_hi (i : Fin 3) : wBox.hi i = (whi i : ℝ) := rfl
theorem wRay_o (i : Fin 3) : wRay.o i = (wo i : ℝ) := rfl
theorem wRay_d (i : Fin 3) : wRay.d i = (wd i : ℝ) := rfl

theorem fl_cast (q : ℚ) : Binary32.model.fl (q : ℝ) = ((rne q : ℚ) : ℝ) := rne_cast q

theorem tQ_cast (x : ℚ) (i : Fin 3) : fpT Binary32.model wRay (x : ℝ) i = (tQ x i : ℝ) := by
  simp only [fpT, RoundingModel.mul, RoundingModel.sub, fpInvd, RoundingModel.div, wRay, tQ]
  rw [← Rat.cast_sub, fl_cast, ← Rat.cast_one, ← Rat.cast_div, fl_cast, ← Rat.cast_mul, fl_cast]

/-- Without inflation the slab test can miss a real hit in binary32 (`K = 1`, exactly
    `tri_slab_scalar` up to the `invd` clamp, which is inactive here). Witness found by
    `tools/cdiff.py --search-miss`; the arithmetic is checked by the kernel
    (`decide +kernel`, no `native_decide`) on exact rationals and lifted to ℝ via `rne_cast`. -/
theorem tri_slab_scalar_false_miss_exists : ∃ (r : Ray) (b : Box), (∀ i, r.d i ≠ 0) ∧ 0 ≤ r.tmin ∧
      (∀ i, Binary32.model.Repr (r.o i) ∧ Binary32.model.Repr (r.d i) ∧
            Binary32.model.Repr (b.lo i) ∧ Binary32.model.Repr (b.hi i)) ∧
      HitsBox r b ∧ ¬ fpSlab Binary32.model r b 1 := by
  refine ⟨wRay, wBox, fun i => by simpa [wRay] using (w_facts i).1, le_refl _, fun i => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := w_repr i
    simp only [RoundingModel.Repr, wRay, wBox, fl_cast, h1, h2, h3, h4, and_self]
  · rw [← slabReal_iff wRay wBox (fun i => by simpa [wRay] using (w_facts i).1)
      (fun i => by simpa [wBox] using (w_facts i).2)]
    have := exactQ_true
    simp only [exactQ, decide_eq_true_eq] at this
    unfold slabReal tNear tFar slabNear slabFar
    have h2 := (Rat.cast_le (K := ℝ)).2 this
    push_cast at h2
    simpa [wBox_lo, wBox_hi, wRay_o, wRay_d, wRay] using h2
  · have := slabQ_false
    simp only [slabQ, decide_eq_false_iff_not] at this
    unfold fpSlab fpNear fpFar
    simp only [wBox_lo, wBox_hi, tQ_cast]
    rw [show wRay.tmin = ((0:ℚ):ℝ) by simp [wRay], show wRay.tmax = ((wtmax:ℚ):ℝ) by simp [wRay]]
    simp only [RoundingModel.mul, mul_one] at this ⊢
    norm_cast
    rw [fl_cast]
    exact_mod_cast this
end LightRT.Robust
