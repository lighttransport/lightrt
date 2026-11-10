/-
  Refinement for `tri_mt_one`: the c2lean translation of the C function returns
  exactly the verdict of `Ref.mt`, and writes `t, u, v` only on a hit.
-/
import LightRT.C.Proofs.SlabRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

theorem c_detEps : (730643660 : Nat).toUInt32 = Ref.detEps := rfl
theorem c_one : (1065353216 : Nat).toUInt32 = Ref.one := rfl
theorem c_zero : (0 : Nat).toUInt32 = Ref.zero := rfl

theorem ExS.if_true {p : Prog} {s s' : State} {a b : Stmt} {r : Outcome} {B : Bool}
    (h : B = true) (hx : ExS p s a r s') : ExS p s (if B = true then a else b) r s' := by
  simpa [h] using hx
theorem ExS.if_false {p : Prog} {s s' : State} {a b : Stmt} {r : Outcome} {B : Bool}
    (h : B = false) (hx : ExS p s b r s') : ExS p s (if B = true then a else b) r s' := by
  simpa [h] using hx

/-- Straight-line `set` statements. -/
macro "sets" : tactic => `(tactic| repeat (first
  | (apply ExS.seq
     · apply ExS.seq
       · apply ExS.set; ev
       · apply ExS.seq
         · apply ExS.set; ev
         · apply ExS.set; ev)
  | (apply ExS.seq
     · apply ExS.seq
       · apply ExS.set; ev
       · apply ExS.set; ev)
  | (apply ExS.seq
     · apply ExS.set; ev)))

/-- A guard `if (c) return 0;` that does not fire (`hc : c = false`). -/
macro "pass" hc:ident : tactic => `(tactic| (
  apply ExS.seq
  · apply ExS.ite
    · ev
    · exact truthy_boolVal _
    exact ExS.if_false $hc:ident ExS.skip))

/-- A guard that fires (`hc : c = true`). -/
macro "reject" hc:ident : tactic => `(tactic| (
  apply ExS.seq_ret
  apply ExS.ite
  · ev
  · exact truthy_boolVal _
  exact ExS.if_true $hc:ident (ExS.ret (EvE.const _))))

theorem store_word (mem : Mem) (b : Nat) (blk : Block) (n : Nat) (hm : mem b = some blk)
    (hl : blk.length = 4) : store mem .f32 (.ptr b 0) (.f32 n) = .ok (mem.upd b (encodeLE 4 n)) := by
  simp [store, writeBytes, hm, hl, List.drop_eq_nil_of_le]

/-- All `mt*` definitions, for unfolding guard hypotheses into the raw form the
    symbolic execution produces. -/
macro "mtunfold" "at" h:ident : tactic => `(tactic|
  simp only [Ref.mtRej1, Ref.mtRej2, Ref.mtRej3, Ref.mtRej4, Ref.mtDet, Ref.mtInv, Ref.mtU, Ref.mtV,
    Ref.mtT, Ref.mtE1, Ref.mtE2, Ref.mtPx, Ref.mtPy, Ref.mtPz, Ref.mtTv, Ref.mtQx, Ref.mtQy,
    Ref.mtQz, Bool.not_eq_true] at $h:ident)

set_option maxHeartbeats 4000000 in
theorem tri_mt_one_refines' (o d v0 v1 v2 : Fin 3 → Ref.F) (tmin tbest : Ref.F) (m : Mem)
    (bo bd b0 b1 b2 bt bu bvv : Nat)
    (ho : m bo = some (f32Block (vecWords o))) (hd : m bd = some (f32Block (vecWords d)))
    (h0 : m b0 = some (f32Block (vecWords v0))) (h1 : m b1 = some (f32Block (vecWords v1)))
    (h2 : m b2 = some (f32Block (vecWords v2)))
    (ht : ∃ blk, m bt = some blk ∧ blk.length = 4) (hu : ∃ blk, m bu = some blk ∧ blk.length = 4)
    (hvv : ∃ blk, m bvv = some blk ∧ blk.length = 4)
    (hne : bt ≠ bu ∧ bt ≠ bvv ∧ bu ≠ bvv) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_mt_one.params
        [.ptr bo 0, .ptr bd 0, .ptr b0 0, .ptr b1 0, .ptr b2 0,
         .f32 tmin.toNat, .f32 tbest.toNat, .ptr bt 0, .ptr bu 0, .ptr bvv 0], m, false⟩
      Gen.tri_mt_one.body
      (.ret (some (.int ⟨32, true⟩ (if (Ref.mt o d v0 v1 v2 tmin tbest).isSome then 1 else 0)))) s' ∧
      (match Ref.mt o d v0 v1 v2 tmin tbest with
       | some (t, u, v) => s'.mem bt = some (f32Block [t.toNat]) ∧ s'.mem bu = some (f32Block [u.toNat]) ∧
                           s'.mem bvv = some (f32Block [v.toNat]) ∧
                           ∀ b, b ≠ bt → b ≠ bu → b ≠ bvv → s'.mem b = m b
       | none => s'.mem = m) := by
  have ho' : m bo = some (f32Block (vecWords o) ++ []) := by simpa using ho
  have hd' : m bd = some (f32Block (vecWords d) ++ []) := by simpa using hd
  have h0' : m b0 = some (f32Block (vecWords v0) ++ []) := by simpa using h0
  have h1' : m b1 = some (f32Block (vecWords v1) ++ []) := by simpa using h1
  have h2' : m b2 = some (f32Block (vecWords v2) ++ []) := by simpa using h2
  clear ho hd h0 h1 h2
  obtain ⟨blkT, hT, hTl⟩ := ht
  obtain ⟨blkU, hU, hUl⟩ := hu
  obtain ⟨blkV, hV, hVl⟩ := hvv
  by_cases c1 : Ref.mtRej1 d v0 v1 v2 = true
  · have hm : Ref.mt o d v0 v1 v2 tmin tbest = none := by simp [Ref.mt, c1]
    rw [hm]; dsimp only
    apply Exists.intro; refine ⟨?_, ?_⟩
    · unfold Gen.tri_mt_one; dsimp only
      sets
      reject c1
    · rfl
  replace c1 : Ref.mtRej1 d v0 v1 v2 = false := by simpa using c1
  by_cases c2 : Ref.mtRej2 o d v0 v1 v2 = true
  · have hm : Ref.mt o d v0 v1 v2 tmin tbest = none := by simp [Ref.mt, c1, c2]
    rw [hm]; dsimp only
    apply Exists.intro; refine ⟨?_, ?_⟩
    · unfold Gen.tri_mt_one; dsimp only
      sets; pass c1; sets; reject c2
    · rfl
  replace c2 : Ref.mtRej2 o d v0 v1 v2 = false := by simpa using c2
  by_cases c3 : Ref.mtRej3 o d v0 v1 v2 = true
  · have hm : Ref.mt o d v0 v1 v2 tmin tbest = none := by simp [Ref.mt, c1, c2, c3]
    rw [hm]; dsimp only
    apply Exists.intro; refine ⟨?_, ?_⟩
    · unfold Gen.tri_mt_one; dsimp only
      sets; pass c1; sets; pass c2; sets; reject c3
    · rfl
  replace c3 : Ref.mtRej3 o d v0 v1 v2 = false := by simpa using c3
  by_cases c4 : Ref.mtRej4 o d v0 v1 v2 tmin tbest = true
  · have hm : Ref.mt o d v0 v1 v2 tmin tbest = none := by simp [Ref.mt, c1, c2, c3, c4]
    rw [hm]; dsimp only
    apply Exists.intro; refine ⟨?_, ?_⟩
    · unfold Gen.tri_mt_one; dsimp only
      sets; pass c1; sets; pass c2; sets; pass c3; sets; reject c4
    · rfl
  replace c4 : Ref.mtRej4 o d v0 v1 v2 tmin tbest = false := by simpa using c4
  have hm : Ref.mt o d v0 v1 v2 tmin tbest =
      some (Ref.mtT o d v0 v1 v2, Ref.mtU o d v0 v1 v2, Ref.mtV o d v0 v1 v2) := by
    simp [Ref.mt, c1, c2, c3, c4]
  rw [hm]; dsimp only
  have key : ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_mt_one.params
        [.ptr bo 0, .ptr bd 0, .ptr b0 0, .ptr b1 0, .ptr b2 0,
         .f32 tmin.toNat, .f32 tbest.toNat, .ptr bt 0, .ptr bu 0, .ptr bvv 0], m, false⟩
      Gen.tri_mt_one.body (.ret (some (.int ⟨32, true⟩ 1))) s' ∧
      s'.mem = ((m.upd bt (encodeLE 4 (Ref.mtT o d v0 v1 v2).toNat)).upd bu
        (encodeLE 4 (Ref.mtU o d v0 v1 v2).toNat)).upd bvv (encodeLE 4 (Ref.mtV o d v0 v1 v2).toNat) := by
    apply Exists.intro; refine ⟨?_, ?_⟩
    · unfold Gen.tri_mt_one; dsimp only
      sets; pass c1; sets; pass c2; sets; pass c3; sets; pass c4
      apply ExS.seq
      · apply ExS.store
        · ev
        · ev
        · rfl
        · exact store_word m bt blkT _ hT hTl
      apply ExS.seq
      · apply ExS.store
        · ev
        · ev
        · rfl
        · exact store_word _ bu blkU _ (by simp [Mem.upd, hne.1.symm, hU]) hUl
      apply ExS.seq
      · apply ExS.store
        · ev
        · ev
        · rfl
        · exact store_word _ bvv blkV _ (by simp [Mem.upd, hne.2.1.symm, hne.2.2.symm, hV]) hVl
      exact ExS.ret (EvE.const _)
    · rfl
  obtain ⟨s', hx, hmem⟩ := key
  refine ⟨s', by simpa using hx, ?_⟩
  rw [hmem]
  obtain ⟨n1, n2, n3⟩ := hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Mem.upd, n1, n2, f32Block]
  · simp [Mem.upd, n3, f32Block]
  · simp [Mem.upd, f32Block]
  · intro b e1 e2 e3; simp [Mem.upd, e1, e2, e3]
end LightRT.C.Proofs
