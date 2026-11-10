/-
  Stage 1: the slab test over ℝ is exact.
-/
import LightRT.Geom.Basic

namespace LightRT.Geom
noncomputable section

/-- Per-axis entry/exit parameters (`d i ≠ 0`). -/
def slabNear (r : Ray) (b : Box) (i : Fin 3) : ℝ :=
  min ((b.lo i - r.o i) / r.d i) ((b.hi i - r.o i) / r.d i)
def slabFar (r : Ray) (b : Box) (i : Fin 3) : ℝ :=
  max ((b.lo i - r.o i) / r.d i) ((b.hi i - r.o i) / r.d i)

def tNear (r : Ray) (b : Box) : ℝ :=
  max (max (slabNear r b 0) (slabNear r b 1)) (max (slabNear r b 2) r.tmin)
def tFar (r : Ray) (b : Box) : ℝ :=
  min (min (slabFar r b 0) (slabFar r b 1)) (min (slabFar r b 2) r.tmax)

/-- Real slab algorithm (same shape as `tri_slab_scalar`). -/
def slabReal (r : Ray) (b : Box) : Prop := tNear r b ≤ tFar r b

/-- Forward direction of the per-axis test, valid even for empty slabs. -/
theorem slab_axis_of_mem (r : Ray) (b : Box) (i : Fin 3) (hd : r.d i ≠ 0) (t : ℝ)
    (h : b.lo i ≤ r.at t i ∧ r.at t i ≤ b.hi i) :
    ∃ v w, v ≤ t ∧ t ≤ w ∧
      (v = (b.lo i - r.o i) / r.d i ∨ v = (b.hi i - r.o i) / r.d i) ∧
      (w = (b.lo i - r.o i) / r.d i ∨ w = (b.hi i - r.o i) / r.d i) := by
  simp only [Ray.at, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rcases hd.lt_or_gt with hn | hp
  · refine ⟨_, _, ?_, ?_, Or.inr rfl, Or.inl rfl⟩
    · rw [div_le_iff_of_neg hn]; linarith
    · rw [le_div_iff_of_neg hn]; linarith
  · refine ⟨_, _, ?_, ?_, Or.inl rfl, Or.inr rfl⟩
    · rw [div_le_iff₀ hp]; linarith
    · rw [le_div_iff₀ hp]; linarith

/-- Helper: one axis. The `lo ≤ hi` hypothesis is necessary: for an empty slab
    (`lo > hi`) the right side can hold while the left cannot. -/
theorem slab_axis_iff (r : Ray) (b : Box) (i : Fin 3) (hd : r.d i ≠ 0)
    (hb : b.lo i ≤ b.hi i) (t : ℝ) :
    (b.lo i ≤ r.at t i ∧ r.at t i ≤ b.hi i) ↔ (slabNear r b i ≤ t ∧ t ≤ slabFar r b i) := by
  simp only [Ray.at, Pi.add_apply, Pi.smul_apply, smul_eq_mul, slabNear, slabFar,
    min_le_iff, le_max_iff]
  rcases hd.lt_or_gt with h | h
  · rw [div_le_iff_of_neg h, div_le_iff_of_neg h, le_div_iff_of_neg h, le_div_iff_of_neg h]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inr (by linarith), Or.inl (by linarith)⟩
    · rintro ⟨h1 | h1, h2 | h2⟩ <;> constructor <;> linarith
  · rw [div_le_iff₀ h, div_le_iff₀ h, le_div_iff₀ h, le_div_iff₀ h]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inl (by linarith), Or.inr (by linarith)⟩
    · rintro ⟨h1 | h1, h2 | h2⟩ <;> constructor <;> linarith

/-- **Stage 1 main theorem (slab).** With no zero direction component, the slab
    test answers exactly the geometric question. -/
theorem slabReal_iff (r : Ray) (b : Box) (hd : ∀ i, r.d i ≠ 0)
    (hb : ∀ i, b.lo i ≤ b.hi i) :
    slabReal r b ↔ HitsBox r b := by
  constructor
  · intro h
    refine ⟨tNear r b, ?_, ?_, fun i => ?_⟩
    · unfold tNear; exact le_max_of_le_right (le_max_right _ _)
    · refine h.trans ?_; unfold tFar; exact min_le_of_right_le (min_le_right _ _)
    · refine (slab_axis_iff r b i (hd i) (hb i) _).2 ⟨?_, h.trans ?_⟩
      · unfold tNear; fin_cases i <;> simp
      · unfold tFar; fin_cases i <;> simp
  · rintro ⟨t, h0, h1, hm⟩
    have hx := fun i => (slab_axis_iff r b i (hd i) (hb i) t).1 (hm i)
    unfold slabReal tNear tFar
    exact (max_le (max_le (hx 0).1 (hx 1).1) (max_le (hx 2).1 h0)).trans
      (le_min (le_min (hx 0).2 (hx 1).2) (le_min (hx 2).2 h1))

/-- Axis-parallel case: if `d i = 0`, the ray meets the slab iff the origin is in it
    (LightRT encodes this with `invd = ±1e18`; see `Robust.Slab`). -/
theorem hitsBox_parallel (r : Ray) (b : Box) (i : Fin 3) (hd : r.d i = 0) :
    HitsBox r b → b.lo i ≤ r.o i ∧ r.o i ≤ b.hi i := by
  rintro ⟨t, -, -, hm⟩
  simpa [Ray.at, hd] using hm i

end
end LightRT.Geom
