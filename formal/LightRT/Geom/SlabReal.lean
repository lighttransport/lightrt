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

/-- Helper: one axis. -/
theorem slab_axis_iff (r : Ray) (b : Box) (i : Fin 3) (hd : r.d i ≠ 0) (t : ℝ) :
    (b.lo i ≤ r.at t i ∧ r.at t i ≤ b.hi i) ↔ (slabNear r b i ≤ t ∧ t ≤ slabFar r b i) := by
  sorry

/-- **Stage 1 main theorem (slab).** With no zero direction component, the slab
    test answers exactly the geometric question. -/
theorem slabReal_iff (r : Ray) (b : Box) (hd : ∀ i, r.d i ≠ 0) :
    slabReal r b ↔ HitsBox r b := by
  sorry

/-- Axis-parallel case: if `d i = 0`, the ray meets the slab iff the origin is in it
    (LightRT encodes this with `invd = ±1e18`; see `Robust.Slab`). -/
theorem hitsBox_parallel (r : Ray) (b : Box) (i : Fin 3) (hd : r.d i = 0) :
    HitsBox r b → b.lo i ≤ r.o i ∧ r.o i ≤ b.hi i := by
  rintro ⟨t, -, -, hm⟩
  simpa [Ray.at, hd] using hm i

end
end LightRT.Geom
