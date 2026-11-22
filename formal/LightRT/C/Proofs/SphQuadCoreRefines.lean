/-
  Refinement for `tri_sph_quad_core`, the fp32 quadratic core extracted from
  `tri_sph_isect_lane`: the c2lean translation equals `Ref.sphQuadCore`
  bit-for-bit. The witness state is the frame after the nine straight-line
  `set`s (locals 6..14 written, memory unchanged).
-/
import LightRT.C.Proofs.MTRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

set_option maxHeartbeats 4000000 in
theorem tri_sph_quad_core_refines' (org dir : Fin 3 → Ref.F) (cx cy cz r : Ref.F) (m : Mem)
    (bo bd : Nat)
    (ho : m bo = some (f32Block (vecWords org)))
    (hd : m bd = some (f32Block (vecWords dir))) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_sph_quad_core.params
        [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat, .f32 r.toNat], m, false⟩
      Gen.tri_sph_quad_core.body
      (.ret (some (.f32 (Ref.sphQuadCore org dir cx cy cz r).toNat))) s' ∧ s'.mem = m := by
  have ho' : m bo = some (f32Block (vecWords org) ++ []) := by simpa using ho
  have hd' : m bd = some (f32Block (vecWords dir) ++ []) := by simpa using hd
  let ocx := subBits (org 0) cx
  let ocy := subBits (org 1) cy
  let ocz := subBits (org 2) cz
  let a := addBits (addBits (mulBits (dir 0) (dir 0)) (mulBits (dir 1) (dir 1))) (mulBits (dir 2) (dir 2))
  let b := addBits (addBits (mulBits ocx (dir 0)) (mulBits ocy (dir 1))) (mulBits ocz (dir 2))
  let c := subBits (addBits (addBits (mulBits ocx ocx) (mulBits ocy ocy)) (mulBits ocz ocz)) (mulBits r r)
  let disc := subBits (mulBits b b) (mulBits a c)
  let sq := Ref.sqrt disc
  let inv_a := divBits Ref.one a
  have hres : Ref.sphQuadCore org dir cx cy cz r = mulBits (subBits (Ref.neg b) sq) inv_a := by
    rfl
  let s0 : State := ⟨frameLocals Gen.tri_sph_quad_core.params
      [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat, .f32 r.toNat], m, false⟩
  let sf : State := ⟨s0.locals.upd 6 (.f32 ocx.toNat) |>.upd 7 (.f32 ocy.toNat)
      |>.upd 8 (.f32 ocz.toNat) |>.upd 9 (.f32 a.toNat) |>.upd 10 (.f32 b.toNat)
      |>.upd 11 (.f32 c.toNat) |>.upd 12 (.f32 disc.toNat) |>.upd 13 (.f32 sq.toNat)
      |>.upd 14 (.f32 inv_a.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_sph_quad_core
  dsimp only
  rw [hres]
  apply ExS.seq
  · apply ExS.seq
    · apply ExS.set; ev
    · apply ExS.seq
      · apply ExS.set; ev
      · apply ExS.set; ev
  · apply ExS.seq
    · apply ExS.set; ev
    · apply ExS.seq
      · apply ExS.set; ev
      · apply ExS.seq
        · apply ExS.set; ev
        · apply ExS.seq
          · apply ExS.set; ev
          · apply ExS.seq
            · apply ExS.set; ev
            · apply ExS.seq
              · apply ExS.set; ev
              · apply ExS.ret
                ev

/-- `callFunc` form: the call returns the reference quadratic core. -/
theorem tri_sph_quad_core_refines (org dir : Fin 3 → Ref.F) (cx cy cz r : Ref.F) (m : Mem)
    (bo bd : Nat)
    (ho : m bo = some (f32Block (vecWords org)))
    (hd : m bd = some (f32Block (vecWords dir))) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_sph_quad_core
        [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat, .f32 r.toNat] m =
      .ok (some (.f32 (Ref.sphQuadCore org dir cx cy cz r).toNat), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_sph_quad_core_refines' org dir cx cy cz r m bo bd ho hd
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_sph_quad_core)
      (fn := Gen.tri_sph_quad_core)
      (args := [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat, .f32 r.toNat])
      (m := m) (v := some (.f32 (Ref.sphQuadCore org dir cx cy cz r).toNat)) (s' := s')
      rfl rfl hx
  simpa [hmem] using h
