/-
  Refinement for `tri_isect_det_parallel`, the relative-determinant cull used
  by the flat-curve and quantized-triangle paths. The C's two clamp `if`s are
  expressed as `tri_maxf`/`tri_minf` calls, so the whole kernel is straight-line
  and the existing callMin/callMax evaluation lemmas close it.
-/
import LightRT.C.Proofs.MTRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

set_option maxHeartbeats 8000000 in
theorem tri_isect_det_parallel_refines' (e1 e2 : Fin 3 → Ref.F) (det : Ref.F)
    (m : Mem) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_isect_det_parallel.params
        [.f32 (e1 0).toNat, .f32 (e1 1).toNat, .f32 (e1 2).toNat,
         .f32 (e2 0).toNat, .f32 (e2 1).toNat, .f32 (e2 2).toNat,
         .f32 det.toNat], m, false⟩
      Gen.tri_isect_det_parallel.body
      (.ret (some (.int ⟨32, true⟩
        (if Ref.isectDetParallel e1 e2 det then 1 else 0)))) s' ∧ s'.mem = m := by
  let e1_len := Ref.sqrt (addBits (addBits (mulBits (e1 0) (e1 0)) (mulBits (e1 1) (e1 1))) (mulBits (e1 2) (e1 2)))
  let e2_len := Ref.sqrt (addBits (addBits (mulBits (e2 0) (e2 0)) (mulBits (e2 1) (e2 1))) (mulBits (e2 2) (e2 2)))
  let scale := addBits e1_len e2_len
  let rel := Ref.fmax 0x2b8cbccc (Ref.fmin 0x358637bd (mulBits (mulBits 0x322bcc77 scale) scale))
  have hres : Ref.isectDetParallel e1 e2 det =
      !(leBits det (Ref.neg rel) || leBits rel det) := by
    rfl
  let s0 : State := ⟨frameLocals Gen.tri_isect_det_parallel.params
      [.f32 (e1 0).toNat, .f32 (e1 1).toNat, .f32 (e1 2).toNat,
       .f32 (e2 0).toNat, .f32 (e2 1).toNat, .f32 (e2 2).toNat,
       .f32 det.toNat], m, false⟩
  let sf : State := ⟨s0.locals.upd 7 (.f32 e1_len.toNat) |>.upd 8 (.f32 e2_len.toNat)
      |>.upd 9 (.f32 scale.toNat) |>.upd 10 (.f32 rel.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_isect_det_parallel
  dsimp only
  rw [hres]
  apply ExS.seq
  · apply ExS.set; ev
  · apply ExS.seq
    · apply ExS.set; ev
    · apply ExS.seq
      · apply ExS.set; ev
      · apply ExS.seq
        · apply ExS.set; ev
        · apply ExS.ret
          ev

theorem tri_isect_det_parallel_refines (e1 e2 : Fin 3 → Ref.F) (det : Ref.F)
    (m : Mem) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_isect_det_parallel
        [.f32 (e1 0).toNat, .f32 (e1 1).toNat, .f32 (e1 2).toNat,
         .f32 (e2 0).toNat, .f32 (e2 1).toNat, .f32 (e2 2).toNat,
         .f32 det.toNat] m =
      .ok (some (.int ⟨32, true⟩
        (if Ref.isectDetParallel e1 e2 det then 1 else 0)), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_isect_det_parallel_refines' e1 e2 det m
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_isect_det_parallel)
      (fn := Gen.tri_isect_det_parallel)
      (args := [.f32 (e1 0).toNat, .f32 (e1 1).toNat, .f32 (e1 2).toNat,
                .f32 (e2 0).toNat, .f32 (e2 1).toNat, .f32 (e2 2).toNat,
                .f32 det.toNat])
      (m := m) (v := some (.int ⟨32, true⟩
        (if Ref.isectDetParallel e1 e2 det then 1 else 0))) (s' := s') rfl rfl hx
  simpa [hmem] using h

end LightRT.C.Proofs
