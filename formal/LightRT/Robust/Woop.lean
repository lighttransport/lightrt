/-
  Stage 4: Woop–Benthin–Wald watertight ray/triangle test, as a Lean
  reference implementation over an abstract rounding model.

  Vertices are translated to the ray origin and sheared so the ray becomes the
  +z axis; the 2D edge functions `U, V, W` are then evaluated in floating point.
  Watertightness rests on: (1) a vertex's 2D image depends only on the vertex
  and the ray, not the triangle; (2) the edge function is exactly antisymmetric
  in floating point. The double-precision fallback for `U = V = W = 0`-style
  ties in the paper is NOT modelled (accepted hits on ties may be duplicated,
  never lost).
-/
import LightRT.FP.Model
import LightRT.Geom.Basic

namespace LightRT.Robust
open LightRT.FP LightRT.Geom
noncomputable section

variable (R : RoundingModel)

/-- Per-ray precomputation: dominant axis `kz`, the other two, shear constants. -/
structure WoopRay where
  o : Vec3
  kx : Fin 3
  ky : Fin 3
  kz : Fin 3
  Sx : ℝ
  Sy : ℝ

/-- 2D image of a vertex in ray space (independent of the triangle). -/
def shear (w : WoopRay) (v : Vec3) : ℝ × ℝ :=
  let a := fun k => R.sub (v k) (w.o k)
  (R.sub (a w.kx) (R.mul w.Sx (a w.kz)), R.sub (a w.ky) (R.mul w.Sy (a w.kz)))

/-- 2D edge function `p.x q.y - p.y q.x`, two products and one subtraction. -/
def edgeFn (p q : ℝ × ℝ) : ℝ := R.sub (R.mul p.1 q.2) (R.mul p.2 q.1)

/-- `(U, V, W)` for triangle `(A, B, C)` as in the paper. -/
def woopUVW (w : WoopRay) (A B C : Vec3) : ℝ × ℝ × ℝ :=
  let a := shear R w A; let b := shear R w B; let c := shear R w C
  (edgeFn R c b, edgeFn R a c, edgeFn R b a)

/-- Acceptance (backface culling off): all same sign, not all zero. -/
def Accept (e : ℝ × ℝ × ℝ) : Prop :=
  ((0 ≤ e.1 ∧ 0 ≤ e.2.1 ∧ 0 ≤ e.2.2) ∨ (e.1 ≤ 0 ∧ e.2.1 ≤ 0 ∧ e.2.2 ≤ 0)) ∧
    ¬ (e.1 = 0 ∧ e.2.1 = 0 ∧ e.2.2 = 0)

/-- **Milestone M1.** The floating-point edge function is exactly antisymmetric. -/
theorem woop_edge_antisymm (p q : ℝ × ℝ) : edgeFn R p q = -edgeFn R q p := by
  simp only [edgeFn]
  rw [R.mul_comm' q.1, R.mul_comm' q.2]
  exact R.sub_antisymm _ _

/-- Shared edge: triangles `(a,b,c)` and `(b,a,d)` see exactly opposite `W`. -/
theorem woop_shared_edge_W (w : WoopRay) (a b c d : Vec3) :
    (woopUVW R w b a d).2.2 = -(woopUVW R w a b c).2.2 := by
  simp only [woopUVW]
  exact woop_edge_antisymm R _ _

/-- **No gap across a shared edge.** If the two non-shared edges of each of the
    two adjacent triangles accept the ray strictly, at least one triangle hits. -/
theorem woop_no_gap (w : WoopRay) (a b c d : Vec3)
    (h1 : 0 < (woopUVW R w a b c).1 ∧ 0 ≤ (woopUVW R w a b c).2.1)
    (h2 : 0 < (woopUVW R w b a d).1 ∧ 0 ≤ (woopUVW R w b a d).2.1) :
    Accept (woopUVW R w a b c) ∨ Accept (woopUVW R w b a d) := by
  have hW := woop_shared_edge_W R w a b c d
  rcases le_total 0 (woopUVW R w a b c).2.2 with h | h
  · exact Or.inl ⟨Or.inl ⟨h1.1.le, h1.2, h⟩, fun h0 => h1.1.ne' h0.1⟩
  · refine Or.inr ⟨Or.inl ⟨h2.1.le, h2.2, by rw [hW]; linarith⟩, fun h0 => h2.1.ne' h0.1⟩

/-- Helper: computed edge-function signs weakly agree with the exact sign over the
    (already rounded) 2D coordinates — from monotonicity and oddness of rounding. -/
theorem edgeFn_sign_weak (p q : ℝ × ℝ) :
    (0 ≤ p.1 * q.2 - p.2 * q.1 → 0 ≤ edgeFn R p q) ∧
    (p.1 * q.2 - p.2 * q.1 ≤ 0 → edgeFn R p q ≤ 0) := by
  constructor
  · intro h; unfold edgeFn RoundingModel.sub RoundingModel.mul
    apply R.fl_nonneg; have := R.mono (show p.2 * q.1 ≤ p.1 * q.2 by linarith); linarith
  · intro h; unfold edgeFn RoundingModel.sub RoundingModel.mul
    apply R.fl_nonpos; have := R.mono (show p.1 * q.2 ≤ p.2 * q.1 by linarith); linarith

/-- **Vertex consistency (fan).** Around a shared vertex `v` with ring
    `w 0, …, w n` (cyclic), triangles `(v, w i, w (i+1))`. If the outer edges
    accept strictly and, in exact arithmetic over the rounded 2D images, the ray
    lies in some closed sector, then some triangle of the fan accepts. -/
theorem woop_vertex_fan (wr : WoopRay) {n : ℕ} (v : Vec3) (w : Fin (n + 1) → Vec3)
    (hout : ∀ i, 0 < (woopUVW R wr v (w i) (w (i + 1))).1)
    (hsector : ∃ i, let s := fun j => (shear R wr v).1 * (shear R wr (w j)).2 -
                                      (shear R wr v).2 * (shear R wr (w j)).1
                    s i ≤ 0 ∧ 0 ≤ s (i + 1)) :
    ∃ i, Accept (woopUVW R wr v (w i) (w (i + 1))) := by
  obtain ⟨i, hi, hi1⟩ := hsector
  refine ⟨i, Or.inl ⟨(hout i).le, ?_, ?_⟩, fun h0 => (hout i).ne' h0.1⟩
  · exact (edgeFn_sign_weak R _ _).1 hi1
  · show 0 ≤ edgeFn R _ _
    rw [woop_edge_antisymm R]
    have := (edgeFn_sign_weak R (shear R wr v) (shear R wr (w i))).2 hi
    linarith

end
end LightRT.Robust
