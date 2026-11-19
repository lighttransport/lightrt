/-
  Refinement for two more scalar C kernels translated by c2lean:
  `tri_surface_area` (fp32 box face-area sum) and `tri_longest_axis`
  (fp32 box longest-extent axis). Both are bit-exact over the whole fp32
  domain (NaN/∞/subnormal included).
-/
import LightRT.C.Proofs.MTRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

namespace Ref
open LightRT.FP.Binary32

/-- `tri_surface_area`: 0 if any extent is negative, else 2(dx·dy + dy·dz + dz·dx). -/
def surfaceArea (lo hi : Fin 3 → UInt32) : UInt32 :=
  let dx := subBits (hi 0) (lo 0)
  let dy := subBits (hi 1) (lo 1)
  let dz := subBits (hi 2) (lo 2)
  if ltBits dx 0 || ltBits dy 0 || ltBits dz 0 then 0
  else mulBits (Nat.toUInt32 1073741824)
    (addBits (addBits (mulBits dx dy) (mulBits dy dz)) (mulBits dz dx))

/-- `tri_longest_axis`: index 0/1/2 of the largest extent (ties → later axis). -/
def longestAxis (lo hi : Fin 3 → UInt32) : Nat :=
  let dx := subBits (hi 0) (lo 0)
  let dy := subBits (hi 1) (lo 1)
  let dz := subBits (hi 2) (lo 2)
  if ltBits dy dx && ltBits dz dx then 0
  else if ltBits dz dy then 1
  else 2

end Ref

set_option maxHeartbeats 4000000 in
theorem tri_surface_area_refines' (lo hi : Fin 3 → Ref.F) (m : Mem)
    (blo bhi : Nat)
    (hlo : m blo = some (f32Block (vecWords lo)))
    (hhi : m bhi = some (f32Block (vecWords hi))) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_surface_area.params
        [.ptr blo 0, .ptr bhi 0], m, false⟩ Gen.tri_surface_area.body
      (.ret (some (.f32 (Ref.surfaceArea lo hi).toNat))) s' ∧ s'.mem = m := by
  have hlo' : m blo = some (f32Block (vecWords lo) ++ []) := by simpa using hlo
  have hhi' : m bhi = some (f32Block (vecWords hi) ++ []) := by simpa using hhi
  let dx := subBits (hi 0) (lo 0)
  let dy := subBits (hi 1) (lo 1)
  let dz := subBits (hi 2) (lo 2)
  let s0 : State := ⟨frameLocals Gen.tri_surface_area.params
      [.ptr blo 0, .ptr bhi 0], m, false⟩
  let sf : State := ⟨s0.locals.upd 2 (.f32 dx.toNat) |>.upd 3 (.f32 dy.toNat)
      |>.upd 4 (.f32 dz.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_surface_area
  dsimp only
  apply ExS.seq
  · apply ExS.seq
    · apply ExS.set; ev
    · apply ExS.seq
      · apply ExS.set; ev
      · apply ExS.set; ev
  by_cases hneg : (ltBits dx Ref.zero || ltBits dy Ref.zero || ltBits dz Ref.zero) = true
  · have hres : Ref.surfaceArea lo hi = Ref.zero := by
      unfold Ref.surfaceArea
      dsimp only
      have hc : (ltBits (subBits (hi 0) (lo 0)) (0:UInt32) ||
          ltBits (subBits (hi 1) (lo 1)) (0:UInt32) ||
          ltBits (subBits (hi 2) (lo 2)) (0:UInt32)) = true := by
        simpa [dx, dy, dz, Ref.zero] using hneg
      exact if_pos hc ▸ rfl
    rw [hres]
    apply ExS.seq_ret
    apply ExS.ite
    · ev
    · exact truthy_boolVal _
    · apply ExS.if_true hneg
      apply ExS.ret
      exact EvE.constF 0 (by norm_num)
  · have hneg' : (ltBits dx Ref.zero || ltBits dy Ref.zero || ltBits dz Ref.zero) = false := by
      simpa using hneg
    have hres : Ref.surfaceArea lo hi =
        mulBits (Nat.toUInt32 1073741824)
          (addBits (addBits (mulBits dx dy) (mulBits dy dz)) (mulBits dz dx)) := by
      unfold Ref.surfaceArea
      dsimp only
      have hc : ¬((ltBits (subBits (hi 0) (lo 0)) (0:UInt32) ||
          ltBits (subBits (hi 1) (lo 1)) (0:UInt32) ||
          ltBits (subBits (hi 2) (lo 2)) (0:UInt32)) = true) := by
        simpa [dx, dy, dz, Ref.zero] using hneg'
      exact if_neg hc ▸ rfl
    rw [hres]
    apply ExS.seq
    · apply ExS.ite
      · ev
      · exact truthy_boolVal _
      · exact ExS.if_false hneg' ExS.skip
    · apply ExS.ret
      ev

set_option maxHeartbeats 4000000 in
theorem tri_longest_axis_refines' (lo hi : Fin 3 → Ref.F) (m : Mem)
    (blo bhi : Nat)
    (hlo : m blo = some (f32Block (vecWords lo)))
    (hhi : m bhi = some (f32Block (vecWords hi))) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_longest_axis.params
        [.ptr blo 0, .ptr bhi 0], m, false⟩ Gen.tri_longest_axis.body
      (.ret (some (.int ⟨32, true⟩ (Ref.longestAxis lo hi)))) s' ∧ s'.mem = m := by
  have hlo' : m blo = some (f32Block (vecWords lo) ++ []) := by simpa using hlo
  have hhi' : m bhi = some (f32Block (vecWords hi) ++ []) := by simpa using hhi
  let dx := subBits (hi 0) (lo 0)
  let dy := subBits (hi 1) (lo 1)
  let dz := subBits (hi 2) (lo 2)
  let s0 : State := ⟨frameLocals Gen.tri_longest_axis.params
      [.ptr blo 0, .ptr bhi 0], m, false⟩
  let sf : State := ⟨s0.locals.upd 2 (.f32 dx.toNat) |>.upd 3 (.f32 dy.toNat)
      |>.upd 4 (.f32 dz.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_longest_axis
  dsimp only
  apply ExS.seq
  · apply ExS.seq
    · apply ExS.set; ev
    · apply ExS.seq
      · apply ExS.set; ev
      · apply ExS.set; ev
  by_cases h1 : (ltBits dy dx && ltBits dz dx) = true
  · have hres : Ref.longestAxis lo hi = 0 := by simp [Ref.longestAxis, dx, dy, dz, h1]
    rw [hres]
    apply ExS.seq_ret
    apply ExS.ite
    · ev
    · exact truthy_boolVal _
    · apply ExS.if_true h1
      apply ExS.ret
      exact EvE.const _
  · have h1' : (ltBits dy dx && ltBits dz dx) = false := by simpa using h1
    have hres1 : Ref.longestAxis lo hi =
        if ltBits dz dy then 1 else 2 := by simp [Ref.longestAxis, dx, dy, dz, h1']
    by_cases h2 : ltBits dz dy = true
    · have hres : Ref.longestAxis lo hi = 1 := by simp [hres1, h2]
      rw [hres]
      apply ExS.seq
      · apply ExS.ite
        · ev
        · exact truthy_boolVal _
        · exact ExS.if_false h1' ExS.skip
      · apply ExS.seq_ret
        apply ExS.ite
        · ev
        · exact truthy_boolVal _
        · apply ExS.if_true h2
          apply ExS.ret
          exact EvE.const _
    · have h2' : ltBits dz dy = false := by simpa using h2
      have hres : Ref.longestAxis lo hi = 2 := by simp [hres1, h2']
      rw [hres]
      apply ExS.seq
      · apply ExS.ite
        · ev
        · exact truthy_boolVal _
        · exact ExS.if_false h1' ExS.skip
      · apply ExS.seq
        · apply ExS.ite
          · ev
          · exact truthy_boolVal _
          · exact ExS.if_false h2' ExS.skip
        · apply ExS.ret
          exact EvE.const _


/-- `callFunc` wrappers. -/
theorem tri_surface_area_refines (lo hi : Fin 3 → Ref.F) (m : Mem) (blo bhi : Nat)
    (hlo : m blo = some (f32Block (vecWords lo)))
    (hhi : m bhi = some (f32Block (vecWords hi))) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_surface_area
        [.ptr blo 0, .ptr bhi 0] m =
      .ok (some (.f32 (Ref.surfaceArea lo hi).toNat), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_surface_area_refines' lo hi m blo bhi hlo hhi
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_surface_area)
      (fn := Gen.tri_surface_area) (args := [.ptr blo 0, .ptr bhi 0])
      (m := m) (v := some (.f32 (Ref.surfaceArea lo hi).toNat)) (s' := s') rfl rfl hx
  simpa [hmem] using h

theorem tri_longest_axis_refines (lo hi : Fin 3 → Ref.F) (m : Mem) (blo bhi : Nat)
    (hlo : m blo = some (f32Block (vecWords lo)))
    (hhi : m bhi = some (f32Block (vecWords hi))) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_longest_axis
        [.ptr blo 0, .ptr bhi 0] m =
      .ok (some (.int ⟨32, true⟩ (Ref.longestAxis lo hi)), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_longest_axis_refines' lo hi m blo bhi hlo hhi
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_longest_axis)
      (fn := Gen.tri_longest_axis) (args := [.ptr blo 0, .ptr bhi 0])
      (m := m) (v := some (.int ⟨32, true⟩ (Ref.longestAxis lo hi))) (s' := s') rfl rfl hx
  simpa [hmem] using h

end LightRT.C.Proofs
