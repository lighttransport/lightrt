/-
  Refinements for the branch-free cores of the round-linear curve CSG tests:
  `tri_rlc_plane_y_core` (axial coordinate of a point on the cone) and
  `tri_rlc_cone_test_core` (cone-side test). The early-outs stay in the callers;
  these straight-line fp32 cores are translated and refined bit-for-bit.
-/
import LightRT.C.Proofs.MTRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

set_option maxHeartbeats 8000000 in
theorem tri_rlc_plane_y_core_refines' (cp0 cp1 p : Fin 3 → Ref.F) (m : Mem)
    (b0 b1 bp : Nat)
    (h0 : m b0 = some (f32Block (vecWords cp0)))
    (h1 : m b1 = some (f32Block (vecWords cp1)))
    (hp : m bp = some (f32Block (vecWords p))) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_rlc_plane_y_core.params
        [.ptr b0 0, .ptr b1 0, .ptr bp 0], m, false⟩
      Gen.tri_rlc_plane_y_core.body
      (.ret (some (.f32 (Ref.rlcPlaneY cp0 cp1 p).toNat))) s' ∧ s'.mem = m := by
  have h0' : m b0 = some (f32Block (vecWords cp0) ++ []) := by simpa using h0
  have h1' : m b1 = some (f32Block (vecWords cp1) ++ []) := by simpa using h1
  have hp' : m bp = some (f32Block (vecWords p) ++ []) := by simpa using hp
  let dPx := subBits (cp1 0) (cp0 0)
  let dPy := subBits (cp1 1) (cp0 1)
  let dPz := subBits (cp1 2) (cp0 2)
  let p0px := subBits (p 0) (cp0 0)
  let p0py := subBits (p 1) (cp0 1)
  let p0pz := subBits (p 2) (cp0 2)
  have hres : Ref.rlcPlaneY cp0 cp1 p =
      addBits (addBits (mulBits p0px dPx) (mulBits p0py dPy)) (mulBits p0pz dPz) := by
    rfl
  let s0 : State := ⟨frameLocals Gen.tri_rlc_plane_y_core.params
      [.ptr b0 0, .ptr b1 0, .ptr bp 0], m, false⟩
  let sf : State := ⟨s0.locals.upd 3 (.f32 dPx.toNat) |>.upd 4 (.f32 dPy.toNat)
      |>.upd 5 (.f32 dPz.toNat) |>.upd 6 (.f32 p0px.toNat) |>.upd 7 (.f32 p0py.toNat)
      |>.upd 8 (.f32 p0pz.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_rlc_plane_y_core
  dsimp only
  rw [hres]
  sets
  apply ExS.ret
  ev

theorem tri_rlc_plane_y_core_refines (cp0 cp1 p : Fin 3 → Ref.F) (m : Mem)
    (b0 b1 bp : Nat)
    (h0 : m b0 = some (f32Block (vecWords cp0)))
    (h1 : m b1 = some (f32Block (vecWords cp1)))
    (hp : m bp = some (f32Block (vecWords p))) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_rlc_plane_y_core
        [.ptr b0 0, .ptr b1 0, .ptr bp 0] m =
      .ok (some (.f32 (Ref.rlcPlaneY cp0 cp1 p).toNat), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_rlc_plane_y_core_refines' cp0 cp1 p m b0 b1 bp h0 h1 hp
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_rlc_plane_y_core)
      (fn := Gen.tri_rlc_plane_y_core)
      (args := [.ptr b0 0, .ptr b1 0, .ptr bp 0])
      (m := m) (v := some (.f32 (Ref.rlcPlaneY cp0 cp1 p).toNat)) (s' := s') rfl rfl hx
  simpa [hmem] using h

set_option maxHeartbeats 8000000 in
theorem tri_rlc_cone_test_core_refines' (cp0 : Fin 3 → Ref.F) (cr0 : Ref.F)
    (cp1 : Fin 3 → Ref.F) (cr1 : Ref.F) (p : Fin 3 → Ref.F) (m : Mem)
    (b0 b1 bp : Nat)
    (h0 : m b0 = some (f32Block (vecWords cp0)))
    (h1 : m b1 = some (f32Block (vecWords cp1)))
    (hp : m bp = some (f32Block (vecWords p))) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_rlc_cone_test_core.params
        [.ptr b0 0, .f32 cr0.toNat, .ptr b1 0, .f32 cr1.toNat, .ptr bp 0], m, false⟩
      Gen.tri_rlc_cone_test_core.body
      (.ret (some (.int ⟨32, true⟩
        (if Ref.rlcConeTest cp0 cr0 cp1 cr1 p then 1 else 0)))) s' ∧ s'.mem = m := by
  have h0' : m b0 = some (f32Block (vecWords cp0) ++ []) := by simpa using h0
  have h1' : m b1 = some (f32Block (vecWords cp1) ++ []) := by simpa using h1
  have hp' : m bp = some (f32Block (vecWords p) ++ []) := by simpa using hp
  let dPx := subBits (cp1 0) (cp0 0)
  let dPy := subBits (cp1 1) (cp0 1)
  let dPz := subBits (cp1 2) (cp0 2)
  let dPdP := addBits (addBits (mulBits dPx dPx) (mulBits dPy dPy)) (mulBits dPz dPz)
  let dr := subBits cr1 cr0
  let r0dr := mulBits cr0 dr
  let g := subBits dPdP (mulBits dr dr)
  let p0px := subBits (p 0) (cp0 0)
  let p0py := subBits (p 1) (cp0 1)
  let p0pz := subBits (p 2) (cp0 2)
  let y := addBits (addBits (mulBits p0px dPx) (mulBits p0py dPy)) (mulBits p0pz dPz)
  let p0p2 := addBits (addBits (mulBits p0px p0px) (mulBits p0py p0py)) (mulBits p0pz p0pz)
  have hres : Ref.rlcConeTest cp0 cr0 cp1 cr1 p =
      ltBits (subBits (mulBits p0p2 g) (mulBits y y))
        (addBits (mulBits (mulBits dPdP cr0) cr0) (mulBits (mulBits 0x40000000 r0dr) y)) := by
    rfl
  let s0 : State := ⟨frameLocals Gen.tri_rlc_cone_test_core.params
      [.ptr b0 0, .f32 cr0.toNat, .ptr b1 0, .f32 cr1.toNat, .ptr bp 0], m, false⟩
  let sf : State := ⟨s0.locals.upd 5 (.f32 dPx.toNat) |>.upd 6 (.f32 dPy.toNat)
      |>.upd 7 (.f32 dPz.toNat) |>.upd 8 (.f32 dPdP.toNat) |>.upd 9 (.f32 dr.toNat)
      |>.upd 10 (.f32 r0dr.toNat) |>.upd 11 (.f32 g.toNat)
      |>.upd 12 (.f32 p0px.toNat) |>.upd 13 (.f32 p0py.toNat) |>.upd 14 (.f32 p0pz.toNat)
      |>.upd 15 (.f32 y.toNat) |>.upd 16 (.f32 p0p2.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_rlc_cone_test_core
  dsimp only
  rw [hres]
  sets
  apply ExS.ret
  ev

theorem tri_rlc_cone_test_core_refines (cp0 : Fin 3 → Ref.F) (cr0 : Ref.F)
    (cp1 : Fin 3 → Ref.F) (cr1 : Ref.F) (p : Fin 3 → Ref.F) (m : Mem)
    (b0 b1 bp : Nat)
    (h0 : m b0 = some (f32Block (vecWords cp0)))
    (h1 : m b1 = some (f32Block (vecWords cp1)))
    (hp : m bp = some (f32Block (vecWords p))) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_rlc_cone_test_core
        [.ptr b0 0, .f32 cr0.toNat, .ptr b1 0, .f32 cr1.toNat, .ptr bp 0] m =
      .ok (some (.int ⟨32, true⟩
        (if Ref.rlcConeTest cp0 cr0 cp1 cr1 p then 1 else 0)), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_rlc_cone_test_core_refines' cp0 cr0 cp1 cr1 p m b0 b1 bp h0 h1 hp
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_rlc_cone_test_core)
      (fn := Gen.tri_rlc_cone_test_core)
      (args := [.ptr b0 0, .f32 cr0.toNat, .ptr b1 0, .f32 cr1.toNat, .ptr bp 0])
      (m := m) (v := some (.int ⟨32, true⟩
        (if Ref.rlcConeTest cp0 cr0 cp1 cr1 p then 1 else 0))) (s' := s') rfl rfl hx
  simpa [hmem] using h

end LightRT.C.Proofs
