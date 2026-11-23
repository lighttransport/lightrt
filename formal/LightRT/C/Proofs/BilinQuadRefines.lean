/-
  Refinement for `tri_bilin_quad_core`: the coefficients `(a, b, c)` of the
  bilinear-patch coplanarity quadratic. The c2lean translation is straight-line
  fp32 with three output stores; the witness is the frame after the `set`s, and
  the final memory is the three 4-byte output writes.
-/
import LightRT.C.Proofs.MTRefines
import LightRT.C.Proofs.RaySetupRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

set_option maxHeartbeats 8000000 in
theorem tri_bilin_quad_core_refines' (o d q00 q10 q11 q01 : Fin 3 → Ref.F)
    (m : Mem) (bo bd b00 b10 b11 b01 ba bb bc : Nat)
    (ho : m bo = some (f32Block (vecWords o)))
    (hd : m bd = some (f32Block (vecWords d)))
    (h00 : m b00 = some (f32Block (vecWords q00)))
    (h10 : m b10 = some (f32Block (vecWords q10)))
    (h11 : m b11 = some (f32Block (vecWords q11)))
    (h01 : m b01 = some (f32Block (vecWords q01)))
    (ha : ∃ blk, m ba = some blk ∧ blk.length = 4)
    (hb : ∃ blk, m bb = some blk ∧ blk.length = 4)
    (hc : ∃ blk, m bc = some blk ∧ blk.length = 4)
    (hne : ba ≠ bb ∧ ba ≠ bc ∧ bb ≠ bc) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_bilin_quad_core.params
        [.ptr bo 0, .ptr bd 0, .ptr b00 0, .ptr b10 0, .ptr b11 0, .ptr b01 0,
         .ptr ba 0, .ptr bb 0, .ptr bc 0], m, false⟩
      Gen.tri_bilin_quad_core.body Outcome.normal s' ∧
      s'.mem = ((m.upd ba (encodeLE 4 (Ref.bilinQuadCore o d q00 q10 q11 q01).1.toNat)).upd
        bb (encodeLE 4 (Ref.bilinQuadCore o d q00 q10 q11 q01).2.1.toNat)).upd
        bc (encodeLE 4 (Ref.bilinQuadCore o d q00 q10 q11 q01).2.2.toNat) := by
  have ho' : m bo = some (f32Block (vecWords o) ++ []) := by simpa using ho
  have hd' : m bd = some (f32Block (vecWords d) ++ []) := by simpa using hd
  have h00' : m b00 = some (f32Block (vecWords q00) ++ []) := by simpa using h00
  have h10' : m b10 = some (f32Block (vecWords q10) ++ []) := by simpa using h10
  have h11' : m b11 = some (f32Block (vecWords q11) ++ []) := by simpa using h11
  have h01' : m b01 = some (f32Block (vecWords q01) ++ []) := by simpa using h01
  obtain ⟨blkA, hA, hAl⟩ := ha
  obtain ⟨blkB, hB, hBl⟩ := hb
  obtain ⟨blkC, hC, hCl⟩ := hc
  let e10 := fun k => subBits (q10 k) (q00 k)
  let e00 := fun k => subBits (q01 k) (q00 k)
  let e11 := fun k => subBits (q11 k) (q10 k)
  let dd := fun k => subBits (e11 k) (e00 k)
  let q0 := fun k => subBits (q00 k) (o k)
  let ax := subBits (mulBits (d 1) (e00 2)) (mulBits (d 2) (e00 1))
  let ay := subBits (mulBits (d 2) (e00 0)) (mulBits (d 0) (e00 2))
  let az := subBits (mulBits (d 0) (e00 1)) (mulBits (d 1) (e00 0))
  let bx := subBits (mulBits (d 1) (dd 2)) (mulBits (d 2) (dd 1))
  let bcy := subBits (mulBits (d 2) (dd 0)) (mulBits (d 0) (dd 2))
  let bz := subBits (mulBits (d 0) (dd 1)) (mulBits (d 1) (dd 0))
  let av := addBits (addBits (mulBits (q0 0) ax) (mulBits (q0 1) ay)) (mulBits (q0 2) az)
  let cv := addBits (addBits (mulBits (e10 0) bx) (mulBits (e10 1) bcy)) (mulBits (e10 2) bz)
  let bv := addBits
    (addBits (addBits (mulBits (q0 0) bx) (mulBits (q0 1) bcy)) (mulBits (q0 2) bz))
    (addBits (addBits (mulBits (e10 0) ax) (mulBits (e10 1) ay)) (mulBits (e10 2) az))
  have hres : Ref.bilinQuadCore o d q00 q10 q11 q01 = (av, bv, cv) := by
    rfl
  rw [hres]
  let s0 : State := ⟨frameLocals Gen.tri_bilin_quad_core.params
      [.ptr bo 0, .ptr bd 0, .ptr b00 0, .ptr b10 0, .ptr b11 0, .ptr b01 0,
       .ptr ba 0, .ptr bb 0, .ptr bc 0], m, false⟩
  let sf : State := ⟨s0.locals
      |>.upd 9 (.f32 (e10 0).toNat) |>.upd 10 (.f32 (e10 1).toNat) |>.upd 11 (.f32 (e10 2).toNat)
      |>.upd 12 (.f32 (e00 0).toNat) |>.upd 13 (.f32 (e00 1).toNat) |>.upd 14 (.f32 (e00 2).toNat)
      |>.upd 15 (.f32 (e11 0).toNat) |>.upd 16 (.f32 (e11 1).toNat) |>.upd 17 (.f32 (e11 2).toNat)
      |>.upd 18 (.f32 (dd 0).toNat) |>.upd 19 (.f32 (dd 1).toNat) |>.upd 20 (.f32 (dd 2).toNat)
      |>.upd 21 (.f32 (q0 0).toNat) |>.upd 22 (.f32 (q0 1).toNat) |>.upd 23 (.f32 (q0 2).toNat)
      |>.upd 24 (.f32 ax.toNat) |>.upd 25 (.f32 ay.toNat) |>.upd 26 (.f32 az.toNat)
      |>.upd 27 (.f32 bx.toNat) |>.upd 28 (.f32 bcy.toNat) |>.upd 29 (.f32 bz.toNat)
      |>.upd 30 (.f32 av.toNat) |>.upd 31 (.f32 cv.toNat) |>.upd 32 (.f32 bv.toNat),
      ((m.upd ba (encodeLE 4 av.toNat)).upd bb (encodeLE 4 bv.toNat)).upd bc (encodeLE 4 cv.toNat), false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_bilin_quad_core
  dsimp only
  -- 24 straight-line sets, then three stores.
  sets
  apply ExS.seq
  · apply ExS.store
    · ev
    · ev
    · rfl
    · exact store_word m ba blkA av.toNat hA hAl
  apply ExS.seq
  · apply ExS.store
    · ev
    · ev
    · rfl
    · exact store_word _ bb blkB bv.toNat (by simp [Mem.upd, hne.1.symm, hB]) hBl
  · apply ExS.store
    · ev
    · ev
    · rfl
    · exact store_word _ bc blkC cv.toNat (by simp [Mem.upd, hne.2.1.symm, hne.2.2.symm, hC]) hCl

/-- `callFunc` form: the call writes `(a, b, c)` to the three output blocks. -/
theorem tri_bilin_quad_core_refines (o d q00 q10 q11 q01 : Fin 3 → Ref.F)
    (m : Mem) (bo bd b00 b10 b11 b01 ba bb bc : Nat)
    (ho : m bo = some (f32Block (vecWords o)))
    (hd : m bd = some (f32Block (vecWords d)))
    (h00 : m b00 = some (f32Block (vecWords q00)))
    (h10 : m b10 = some (f32Block (vecWords q10)))
    (h11 : m b11 = some (f32Block (vecWords q11)))
    (h01 : m b01 = some (f32Block (vecWords q01)))
    (ha : ∃ blk, m ba = some blk ∧ blk.length = 4)
    (hb : ∃ blk, m bb = some blk ∧ blk.length = 4)
    (hc : ∃ blk, m bc = some blk ∧ blk.length = 4)
    (hne : ba ≠ bb ∧ ba ≠ bc ∧ bb ≠ bc) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_bilin_quad_core
        [.ptr bo 0, .ptr bd 0, .ptr b00 0, .ptr b10 0, .ptr b11 0, .ptr b01 0,
         .ptr ba 0, .ptr bb 0, .ptr bc 0] m =
      .ok (none, ((m.upd ba (encodeLE 4 (Ref.bilinQuadCore o d q00 q10 q11 q01).1.toNat)).upd
        bb (encodeLE 4 (Ref.bilinQuadCore o d q00 q10 q11 q01).2.1.toNat)).upd
        bc (encodeLE 4 (Ref.bilinQuadCore o d q00 q10 q11 q01).2.2.toNat)) := by
  obtain ⟨s', hx, hmem⟩ := tri_bilin_quad_core_refines' o d q00 q10 q11 q01 m
      bo bd b00 b10 b11 b01 ba bb bc ho hd h00 h10 h11 h01 ha hb hc hne
  obtain ⟨K, hK⟩ := callFunc_of_ExS_normal (p := Gen.prog) (f := Gen.fid_tri_bilin_quad_core)
      (fn := Gen.tri_bilin_quad_core)
      (args := [.ptr bo 0, .ptr bd 0, .ptr b00 0, .ptr b10 0, .ptr b11 0, .ptr b01 0,
                .ptr ba 0, .ptr bb 0, .ptr bc 0])
      (m := m) (s' := s') rfl rfl hx
  refine ⟨K, ?_⟩
  intro n hn
  simpa [hmem] using hK n hn

end LightRT.C.Proofs
