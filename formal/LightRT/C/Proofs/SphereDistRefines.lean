/-
  Refinement for `tri_sphere_dist_f`: the c2lean translation of the C helper
  returns exactly `Ref.sphereDistF` (bit-for-bit), for every input, including
  NaN/∞/subnormal — the `sqrtf` call is modelled by `sqrtBits`.

  The witness state is the frame after the seven straight-line `set`s (locals
  4..10 written, memory unchanged); it must be given explicitly because
  `ExS.set` updates the locals.
-/
import LightRT.C.Proofs.MTRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

set_option maxHeartbeats 4000000 in
theorem tri_sphere_dist_f_refines' (o d c : Fin 3 → Ref.F) (r : Ref.F) (m : Mem)
    (bo bd bc : Nat)
    (ho : m bo = some (f32Block (vecWords o)))
    (hd : m bd = some (f32Block (vecWords d)))
    (hc : m bc = some (f32Block (vecWords c))) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_sphere_dist_f.params
        [.ptr bo 0, .ptr bd 0, .ptr bc 0, .f32 r.toNat], m, false⟩
      Gen.tri_sphere_dist_f.body
      (.ret (some (.f32 (Ref.sphereDistF o d c r).toNat))) s' ∧ s'.mem = m := by
  have ho' : m bo = some (f32Block (vecWords o) ++ []) := by simpa using ho
  have hd' : m bd = some (f32Block (vecWords d) ++ []) := by simpa using hd
  have hc' : m bc = some (f32Block (vecWords c) ++ []) := by simpa using hc
  let ex := subBits (c 0) (o 0)
  let ey := subBits (c 1) (o 1)
  let ez := subBits (c 2) (o 2)
  let proj := addBits (addBits (mulBits ex (d 0)) (mulBits ey (d 1))) (mulBits ez (d 2))
  let l2 := addBits (addBits (mulBits ex ex) (mulBits ey ey)) (mulBits ez ez)
  let perp2 := subBits l2 (mulBits proj proj)
  let disc := subBits (mulBits r r) perp2
  have hdisc : Ref.sphereDistF o d c r =
      (if ltBits disc Ref.zero then Ref.neg Ref.one else subBits proj (Ref.sqrt disc)) := by
    rfl
  let s0 : State := ⟨frameLocals Gen.tri_sphere_dist_f.params
      [.ptr bo 0, .ptr bd 0, .ptr bc 0, .f32 r.toNat], m, false⟩
  let sf : State := ⟨s0.locals.upd 4 (.f32 ex.toNat) |>.upd 5 (.f32 ey.toNat)
      |>.upd 6 (.f32 ez.toNat) |>.upd 7 (.f32 proj.toNat) |>.upd 8 (.f32 l2.toNat)
      |>.upd 9 (.f32 perp2.toNat) |>.upd 10 (.f32 disc.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_sphere_dist_f
  dsimp only
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
          · by_cases hlt : ltBits disc Ref.zero = true
            · have hres : Ref.sphereDistF o d c r = Ref.neg Ref.one := by simp [hdisc, hlt]
              rw [hres]
              apply ExS.seq_ret
              apply ExS.ite
              · ev
              · exact truthy_boolVal _
              · apply ExS.if_true hlt
                apply ExS.ret
                apply EvE.fneg'
                exact EvE.constF 1065353216 (by norm_num)
            · have hlt' : ltBits disc Ref.zero = false := by simpa using hlt
              have hres : Ref.sphereDistF o d c r = subBits proj (Ref.sqrt disc) := by
                simp [hdisc, hlt']
              rw [hres]
              apply ExS.seq
              · apply ExS.ite
                · ev
                · exact truthy_boolVal _
                · exact ExS.if_false hlt' ExS.skip
              · apply ExS.ret
                ev

/-- `callFunc` form: the call returns the reference distance and leaves memory
    untouched, for all sufficiently large fuel. -/
theorem tri_sphere_dist_f_refines (o d c : Fin 3 → Ref.F) (r : Ref.F) (m : Mem)
    (bo bd bc : Nat)
    (ho : m bo = some (f32Block (vecWords o)))
    (hd : m bd = some (f32Block (vecWords d)))
    (hc : m bc = some (f32Block (vecWords c))) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_sphere_dist_f
        [.ptr bo 0, .ptr bd 0, .ptr bc 0, .f32 r.toNat] m =
      .ok (some (.f32 (Ref.sphereDistF o d c r).toNat), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_sphere_dist_f_refines' o d c r m bo bd bc ho hd hc
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_sphere_dist_f)
      (fn := Gen.tri_sphere_dist_f)
      (args := [.ptr bo 0, .ptr bd 0, .ptr bc 0, .f32 r.toNat])
      (m := m) (v := some (.f32 (Ref.sphereDistF o d c r).toNat)) (s' := s')
      rfl rfl hx
  simpa [hmem] using h

end LightRT.C.Proofs
