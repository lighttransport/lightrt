/-
  Möller–Trumbore (`tri_mt_one`) is NOT watertight in binary32: a ray that
  crosses the shared edge of two adjacent triangles is rejected by both, although
  in exact arithmetic it hits the first one. Witness found by random search
  (gcc -ffp-contract=off reproduces it); checked here with `decide +kernel`
  (no `native_decide`) and lifted to ℝ.
-/
import LightRT.C.Proofs.Refines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32 LightRT.Geom

def gO : Fin 3 → Ref.F := ![0xc011fcf8, 0xbf6687ce, 0xbe9006b6]
def gD : Fin 3 → Ref.F := ![0x3f5eb8d8, 0x3ebcdf28, 0xbe6f3af4]
/-- Shared edge `A–C`; triangles `(A, C, P)` and `(C, A, Q)`. -/
def gA : Fin 3 → Ref.F := ![0xbdd8f350, 0x3de73190, 0xbf4b2d26]
def gC : Fin 3 → Ref.F := ![0xbf0c3bc0, 0xbe2b0160, 0xbf3f730e]
def gP : Fin 3 → Ref.F := ![0xbf1ffba9, 0xbf292942, 0xbc154a00]
def gQ : Fin 3 → Ref.F := ![0xbcebd020, 0x3f1b4f1c, 0xbfc42586]
def gTbest : Ref.F := 0x40800000   -- 4.0

set_option maxRecDepth 100000 in
/-- The bit-level reference kernel rejects both triangles. -/
theorem mt_gap_bits :
    Ref.mt gO gD gA gC gP 0 gTbest = none ∧ Ref.mt gO gD gC gA gQ 0 gTbest = none := by
  decide +kernel

/-- Exact rational value of a word. -/
def wq (w : Ref.F) : ℚ := ((decode w).toQ?).getD 0

def qv (v : Fin 3 → Ref.F) : Fin 3 → ℚ := fun i => wq (v i)

def qsub (x y : Fin 3 → ℚ) : Fin 3 → ℚ := fun i => x i - y i
def qcross (x y : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]
def qdot (x y : Fin 3 → ℚ) : ℚ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2

/-- Exact Cramer solution for triangle `(A, C, P)`. -/
def gE1 := qsub (qv gC) (qv gA)
def gE2 := qsub (qv gP) (qv gA)
def gTv := qsub (qv gO) (qv gA)
def gDet := qdot gE1 (qcross (qv gD) gE2)
def gU : ℚ := qdot gTv (qcross (qv gD) gE2) / gDet
def gV : ℚ := qdot (qv gD) (qcross gTv gE1) / gDet
def gT : ℚ := qdot gE2 (qcross gTv gE1) / gDet

set_option maxRecDepth 100000 in
theorem g_bary : 0 ≤ gU ∧ 0 ≤ gV ∧ gU + gV ≤ 1 ∧ 0 ≤ gT ∧ gT < wq gTbest := by decide +kernel

set_option maxRecDepth 100000 in
theorem g_eq : ∀ i, wq (gO i) + gT * wq (gD i) =
    wq (gA i) + gU * (wq (gC i) - wq (gA i)) + gV * (wq (gP i) - wq (gA i)) := by decide +kernel

def rv (v : Fin 3 → Ref.F) : Vec3 := fun i => (wq (v i) : ℝ)

/-- **Möller–Trumbore leaks through a shared edge.** In exact arithmetic the ray
    `o + t d` hits triangle `(A, C, P)` at a parameter in `[0, 4)`, yet the
    binary32 kernel rejects both `(A, C, P)` and the adjacent `(C, A, Q)`; by
    `tri_mt_one_refines` the C function `tri_mt_one` returns 0 on both. -/
theorem mt_not_watertight :
    (∃ t, HitsTriangleAt (rv gO) (rv gD) (rv gA) (rv gC) (rv gP) 0 (wq gTbest : ℝ) t) ∧
      Ref.mt gO gD gA gC gP 0 gTbest = none ∧ Ref.mt gO gD gC gA gQ 0 gTbest = none := by
  refine ⟨⟨(gT : ℝ), ?_, ?_, (gU : ℝ), (gV : ℝ), ?_, ?_, ?_, ?_⟩, mt_gap_bits⟩
  · exact_mod_cast g_bary.2.2.2.1
  · exact_mod_cast g_bary.2.2.2.2
  · exact_mod_cast g_bary.1
  · exact_mod_cast g_bary.2.1
  · exact_mod_cast g_bary.2.2.1
  · funext i
    have := g_eq i
    simp only [rv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    exact_mod_cast this

/-- Whenever `Ref.mt` rejects, the translated C `tri_mt_one` returns 0 and leaves memory unchanged. -/
theorem tri_mt_one_returns_zero (o d v0 v1 v2 : Fin 3 → Ref.F) (tmin tbest : Ref.F) (m : Mem)
    (bo bd b0 b1 b2 bt bu bvv : Nat)
    (ho : m bo = some (f32Block (vecWords o))) (hd : m bd = some (f32Block (vecWords d)))
    (h0 : m b0 = some (f32Block (vecWords v0))) (h1 : m b1 = some (f32Block (vecWords v1)))
    (h2 : m b2 = some (f32Block (vecWords v2)))
    (ht : ∃ blk, m bt = some blk ∧ blk.length = 4) (hu : ∃ blk, m bu = some blk ∧ blk.length = 4)
    (hvv : ∃ blk, m bvv = some blk ∧ blk.length = 4)
    (hne : bt ≠ bu ∧ bt ≠ bvv ∧ bu ≠ bvv) (hmiss : Ref.mt o d v0 v1 v2 tmin tbest = none) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_mt_one
        [.ptr bo 0, .ptr bd 0, .ptr b0 0, .ptr b1 0, .ptr b2 0,
         .f32 tmin.toNat, .f32 tbest.toNat, .ptr bt 0, .ptr bu 0, .ptr bvv 0] m =
        .ok (some (.int ⟨32, true⟩ 0), m) := by
  obtain ⟨m', ⟨K, hK⟩, hp⟩ :=
    tri_mt_one_refines o d v0 v1 v2 tmin tbest m bo bd b0 b1 b2 bt bu bvv ho hd h0 h1 h2 ht hu hvv hne
  rw [hmiss] at hK hp
  simp only at hp
  subst hp
  exact ⟨K, fun n hn => by simpa using hK n hn⟩
end LightRT.C.Proofs
