/-
  Refinements for the two disc-branch cores of `tri_point_isect_one`:
  `tri_point_oriented_core` (plane-hit parameter) and `tri_point_raydisc_core`
  (nearest-point parameter). Both are branch-free fp32 cores, so the c2lean
  translation equals the reference bit-for-bit by a straight-line state walk.
-/
import LightRT.C.Proofs.MTRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

set_option maxHeartbeats 4000000 in
theorem tri_point_oriented_core_refines' (org dir : Fin 3 → Ref.F)
    (cx cy cz nx ny nz : Ref.F) (m : Mem) (bo bd : Nat)
    (ho : m bo = some (f32Block (vecWords org)))
    (hd : m bd = some (f32Block (vecWords dir))) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_point_oriented_core.params
        [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat,
         .f32 nx.toNat, .f32 ny.toNat, .f32 nz.toNat], m, false⟩
      Gen.tri_point_oriented_core.body
      (.ret (some (.f32 (Ref.pointOrientedCore org dir cx cy cz nx ny nz).toNat))) s' ∧ s'.mem = m := by
  have ho' : m bo = some (f32Block (vecWords org) ++ []) := by simpa using ho
  have hd' : m bd = some (f32Block (vecWords dir) ++ []) := by simpa using hd
  let c0x := subBits cx (org 0)
  let c0y := subBits cy (org 1)
  let c0z := subBits cz (org 2)
  let divisor := addBits (addBits (mulBits (dir 0) nx) (mulBits (dir 1) ny)) (mulBits (dir 2) nz)
  have hres : Ref.pointOrientedCore org dir cx cy cz nx ny nz =
      divBits (addBits (addBits (mulBits c0x nx) (mulBits c0y ny)) (mulBits c0z nz)) divisor := by
    rfl
  let s0 : State := ⟨frameLocals Gen.tri_point_oriented_core.params
      [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat,
       .f32 nx.toNat, .f32 ny.toNat, .f32 nz.toNat], m, false⟩
  let sf : State := ⟨s0.locals.upd 8 (.f32 c0x.toNat) |>.upd 9 (.f32 c0y.toNat)
      |>.upd 10 (.f32 c0z.toNat) |>.upd 11 (.f32 divisor.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_point_oriented_core
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
    · apply ExS.ret
      ev

theorem tri_point_oriented_core_refines (org dir : Fin 3 → Ref.F)
    (cx cy cz nx ny nz : Ref.F) (m : Mem) (bo bd : Nat)
    (ho : m bo = some (f32Block (vecWords org)))
    (hd : m bd = some (f32Block (vecWords dir))) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_point_oriented_core
        [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat,
         .f32 nx.toNat, .f32 ny.toNat, .f32 nz.toNat] m =
      .ok (some (.f32 (Ref.pointOrientedCore org dir cx cy cz nx ny nz).toNat), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_point_oriented_core_refines' org dir cx cy cz nx ny nz m bo bd ho hd
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_point_oriented_core)
      (fn := Gen.tri_point_oriented_core)
      (args := [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat,
                .f32 nx.toNat, .f32 ny.toNat, .f32 nz.toNat])
      (m := m) (v := some (.f32 (Ref.pointOrientedCore org dir cx cy cz nx ny nz).toNat)) (s' := s')
      rfl rfl hx
  simpa [hmem] using h

set_option maxHeartbeats 4000000 in
theorem tri_point_raydisc_core_refines' (org dir : Fin 3 → Ref.F)
    (cx cy cz : Ref.F) (m : Mem) (bo bd : Nat)
    (ho : m bo = some (f32Block (vecWords org)))
    (hd : m bd = some (f32Block (vecWords dir))) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_point_raydisc_core.params
        [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat], m, false⟩
      Gen.tri_point_raydisc_core.body
      (.ret (some (.f32 (Ref.pointRayDiscCore org dir cx cy cz).toNat))) s' ∧ s'.mem = m := by
  have ho' : m bo = some (f32Block (vecWords org) ++ []) := by simpa using ho
  have hd' : m bd = some (f32Block (vecWords dir) ++ []) := by simpa using hd
  let dx := dir 0
  let dy := dir 1
  let dz := dir 2
  let dOdO := addBits (addBits (mulBits dx dx) (mulBits dy dy)) (mulBits dz dz)
  let c0x := subBits cx (org 0)
  let c0y := subBits cy (org 1)
  let c0z := subBits cz (org 2)
  let rd2 := divBits Ref.one dOdO
  have hres : Ref.pointRayDiscCore org dir cx cy cz =
      mulBits (addBits (addBits (mulBits c0x dx) (mulBits c0y dy)) (mulBits c0z dz)) rd2 := by
    rfl
  let s0 : State := ⟨frameLocals Gen.tri_point_raydisc_core.params
      [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat], m, false⟩
  let sf : State := ⟨s0.locals.upd 5 (.f32 dx.toNat) |>.upd 6 (.f32 dy.toNat)
      |>.upd 7 (.f32 dz.toNat) |>.upd 8 (.f32 dOdO.toNat) |>.upd 9 (.f32 c0x.toNat)
      |>.upd 10 (.f32 c0y.toNat) |>.upd 11 (.f32 c0z.toNat) |>.upd 12 (.f32 rd2.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_point_raydisc_core
  dsimp only
  rw [hres]
  repeat (first | apply ExS.seq | (apply ExS.set; ev) | (apply ExS.ret; ev))

theorem tri_point_raydisc_core_refines (org dir : Fin 3 → Ref.F)
    (cx cy cz : Ref.F) (m : Mem) (bo bd : Nat)
    (ho : m bo = some (f32Block (vecWords org)))
    (hd : m bd = some (f32Block (vecWords dir))) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_point_raydisc_core
        [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat] m =
      .ok (some (.f32 (Ref.pointRayDiscCore org dir cx cy cz).toNat), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_point_raydisc_core_refines' org dir cx cy cz m bo bd ho hd
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_point_raydisc_core)
      (fn := Gen.tri_point_raydisc_core)
      (args := [.ptr bo 0, .ptr bd 0, .f32 cx.toNat, .f32 cy.toNat, .f32 cz.toNat])
      (m := m) (v := some (.f32 (Ref.pointRayDiscCore org dir cx cy cz).toNat)) (s' := s')
      rfl rfl hx
  simpa [hmem] using h
