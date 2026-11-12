/-
  Refinement for `tri_exn_key` (the `LRT_TRI_EXACT_NEAREST` pruning key),
  translated into `GenExn` (the `-DLRT_TRI_EXACT_NEAREST` configuration).

  The C function reads `tri_exn_ctx { int on; int kz; float sz; float oz; }`,
  returns `tmin` when `on == 0`, and otherwise computes

      dl = lo - oz;  dh = hi - oz        (float)
      za = sz * dl;  zb = sz * dh
      m  = za < zb ? za : zb
      aa = fabsf za; ab = fabsf zb;  M = aa > ab ? aa : ab
      key = m - 2^-19 * M
      return key > tmin ? key : tmin

  `fabsf` is translated as `copysignf(x, +1.0f)` (exact at the bit level).
  This file proves the compiled function computes `exnKey`; the semantic
  bound that makes the key safe lives in `LightRT/BVH/ExactPrune.lean`
  (`woop_key_le_t`).
-/
import LightRT.C.Proofs.Eval
import LightRT.C.Proofs.RaySetupRefines
import LightRT.C.GenExn

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

/-- `tri_exn_ctx` layout: `on` @0, `kz` @4, `sz` @8, `oz` @12 (16 bytes). -/
def exnBlock (on kz sz oz : Ref.F) : Block :=
  f32Block [on.toNat, kz.toNat, sz.toNat, oz.toNat]

/-- The pruning key `tri_exn_key` computes, in binary32 bit operations. -/
def exnKey (on sz oz lo hi tmin : Ref.F) : Ref.F :=
  if on = Ref.zero then tmin
  else
    let dl := subBits lo oz
    let dh := subBits hi oz
    let za := mulBits sz dl
    let zb := mulBits sz dh
    let m := Ref.fmin za zb
    let aa := Ref.copysign za Ref.one
    let ab := Ref.copysign zb Ref.one
    let M := Ref.fmax aa ab
    let key := subBits m (mulBits 0x36000000 M)
    if ltBits tmin key then key else tmin

theorem toNat_beq_zero_true {x : Ref.F} (h : x = Ref.zero) : (x.toNat == 0) = true := by
  subst h; rfl

theorem toNat_beq_zero_false {x : Ref.F} (h : x ≠ Ref.zero) : (x.toNat == 0) = false := by
  have hn : x.toNat ≠ 0 := fun hn =>
    h (UInt32.toNat_inj.mp (by simpa [Ref.zero] using hn))
  simp [hn]

section
variable {p : Prog} {s : State}

/-- Integer load of word `j` of a block made of 32-bit words. -/
theorem EvE.loadWordI {a} {b : Nat} {ws : List Nat} {tl : Block} {j : Nat} {w : UInt32}
    (ha : EvE p s a (.ptr b (4 * j))) (hm : s.mem b = some (f32Block ws ++ tl))
    (hj : ws[j]? = some w.toNat) :
    EvE p s (.load (.int ⟨32, true⟩) a) (.int ⟨32, true⟩ w.toNat) := by
  obtain ⟨h1, h2⟩ := word_at ws tl j w.toNat hj
  refine EvE.load ha ?_
  simp only [load, readBytes, hm, Ty.size, IntTy.bytes, h2, ite_true, h1]
  show Res.ok (Val.int ⟨32, true⟩ (decodeLE (encodeLE 4 w.toNat))) = _
  rw [decodeLE_encodeLE4, Nat.mod_eq_of_lt w.toNat_lt]

/-- Integer load of the word at byte offset `o` (`o` a multiple of 4). -/
theorem EvE.loadAtI {a} {b o : Nat} {ws : List Nat} {tl : Block} {w : UInt32}
    (ha : EvE p s a (.ptr b o)) (hm : s.mem b = some (f32Block ws ++ tl))
    (h4 : o % 4 = 0) (hj : ws[o / 4]? = some w.toNat) :
    EvE p s (.load (.int ⟨32, true⟩) a) (.int ⟨32, true⟩ w.toNat) :=
  EvE.loadWordI (j := o / 4) (by rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)]) hm hj

/-- `!x` on a 32-bit integer is the test `x == 0`. -/
theorem EvE.lnotInt {a} {n : Nat} (ha : EvE p s a (.int ⟨32, true⟩ n)) :
    EvE p s (.un .lnot ⟨32, true⟩ a) (boolVal (n == 0)) := by
  refine EvE.un ha ?_
  have hb : truthy (.int ⟨32, true⟩ n) = .ok (n != 0) := rfl
  rw [evalUn, hb]
  change Res.ok (boolVal (!(n != 0))) = Res.ok (boolVal (n == 0))
  rw [show (!(n != 0)) = (n == 0) by cases n <;> rfl]

end

/-- Locals of a fresh `tri_exn_key` call. -/
def initL (b : Nat) (lo hi tmin : Ref.F) : Locals :=
  frameLocals GenExn.tri_exn_key.params
    [.ptr b 0, .f32 lo.toNat, .f32 hi.toNat, .f32 tmin.toNat]

/-- Locals after the straight-line key computation (locals 4..12). -/
def exnUpd (b : Nat) (on sz oz lo hi tmin : Ref.F) : Locals :=
  let dl := subBits lo oz
  let dh := subBits hi oz
  let za := mulBits sz dl
  let zb := mulBits sz dh
  let m := Ref.fmin za zb
  let aa := Ref.copysign za Ref.one
  let ab := Ref.copysign zb Ref.one
  let M := Ref.fmax aa ab
  let key := subBits m (mulBits 0x36000000 M)
  let l9 := (initL b lo hi tmin).upd 4 (.f32 dl.toNat)
  let l10 := l9.upd 5 (.f32 dh.toNat)
  let l11 := l10.upd 6 (.f32 za.toNat)
  let l12 := l11.upd 7 (.f32 zb.toNat)
  let l13 := l12.upd 8 (.f32 m.toNat)
  let l14 := l13.upd 9 (.f32 aa.toNat)
  let l15 := l14.upd 10 (.f32 ab.toNat)
  let l16 := l15.upd 11 (.f32 M.toNat)
  l16.upd 12 (.f32 key.toNat)

/-- Final locals: the guard's early return leaves the frame untouched. -/
def exnFinal (b : Nat) (on sz oz lo hi tmin : Ref.F) : Locals :=
  if on = Ref.zero then initL b lo hi tmin else exnUpd b on sz oz lo hi tmin

/-- `min`-shaped conditional: `c ? a : b` where `c` tests `a < b`. -/
theorem EvE.condMin {p : Prog} {s : State} {c a b : Expr} {x y : UInt32}
    (hc : EvE p s c (boolVal (ltBits x y)))
    (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.cond c a b) (.f32 (Ref.fmin x y).toNat) := by
  refine EvE.cond hc (truthy_boolVal _) ?_
  unfold Ref.fmin
  by_cases h : ltBits x y = true
  · rw [if_pos h, if_pos h]; exact ha
  · rw [if_neg h, if_neg h]; exact hb

/-- `max`-shaped conditional: `c ? a : b` where `c` tests `a > b`. -/
theorem EvE.condMax {p : Prog} {s : State} {c a b : Expr} {x y : UInt32}
    (hc : EvE p s c (boolVal (ltBits y x)))
    (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.cond c a b) (.f32 (Ref.fmax x y).toNat) := by
  refine EvE.cond hc (truthy_boolVal _) ?_
  unfold Ref.fmax
  by_cases h : ltBits y x = true
  · rw [if_pos h, if_pos h]; exact ha
  · rw [if_neg h, if_neg h]; exact hb

/-- `evX` for `GenExn` (its own loads, `copysign` and min/max conditionals). -/
syntax "evX" : tactic
macro_rules
  | `(tactic| evX) => `(tactic| first
      | (apply EvE.var; first | rfl | assumption)
      | (apply EvE.f32sub <;> evX) | (apply EvE.f32mul <;> evX)
      | (apply EvE.f32lt <;> evX) | (apply EvE.f32gt <;> evX)
      | (apply EvE.condMin
         · (apply EvE.f32lt <;> evX)
         · evX
         · evX)
      | (apply EvE.condMax
         · (apply EvE.f32gt <;> evX)
         · evX
         · evX)
      | (apply EvE.copysign' <;> evX)
      | (apply EvE.constF; norm_num)
      | (exact EvE.const _)
      | (apply EvE.fieldN
         · (apply EvE.var; first | rfl | assumption)
         · assumption
         · (simp only [List.length_append, length_f32Block, List.length_cons, List.length_nil]; omega))
      | (apply EvE.loadAt
         · evX
         · assumption
         · (norm_num; done)
         · rfl)
      | (apply EvE.loadAtI
         · evX
         · assumption
         · (norm_num; done)
         · rfl)
      | (apply EvE.loadWordI
         · evX
         · assumption
         · rfl))

/-- One straight-line assignment with its value pinned (the forward chain of
    `ExS.set` leaves the result value unconstrained, so conditionals and loads
    could not otherwise infer their operands). -/
macro "setX" v:term : tactic => `(tactic| (apply ExS.set (v := $v); evX))

/-- The function body, from the freshly built frame, computes `exnKey`. -/
theorem exn_body (on kz sz oz lo hi tmin : Ref.F) (m : Mem) (b : Nat)
    (hm : m b = some (exnBlock on kz sz oz)) :
    ∃ s', ExS GenExn.prog ⟨initL b lo hi tmin, m, false⟩ GenExn.tri_exn_key.body
        (.ret (some (.f32 (exnKey on sz oz lo hi tmin).toNat))) s' ∧ s'.mem = m := by
  have hm' : m b = some (f32Block [on.toNat, kz.toNat, sz.toNat, oz.toNat] ++ []) := by
    simpa [exnBlock] using hm
  have h0 : initL b lo hi tmin 0 = some (.ptr b 0) := by
    show frameLocals [0, 1, 2, 3]
      [.ptr b 0, .f32 lo.toNat, .f32 hi.toNat, .f32 tmin.toNat] 0 = _
    simp only [frameLocals]; rfl
  have h1 : initL b lo hi tmin 1 = some (.f32 lo.toNat) := by
    show frameLocals [0, 1, 2, 3]
      [.ptr b 0, .f32 lo.toNat, .f32 hi.toNat, .f32 tmin.toNat] 1 = _
    simp only [frameLocals]; rfl
  have h2 : initL b lo hi tmin 2 = some (.f32 hi.toNat) := by
    show frameLocals [0, 1, 2, 3]
      [.ptr b 0, .f32 lo.toNat, .f32 hi.toNat, .f32 tmin.toNat] 2 = _
    simp only [frameLocals]; rfl
  have h3 : initL b lo hi tmin 3 = some (.f32 tmin.toNat) := by
    show frameLocals [0, 1, 2, 3]
      [.ptr b 0, .f32 lo.toNat, .f32 hi.toNat, .f32 tmin.toNat] 3 = _
    simp only [frameLocals]; rfl
  have hcond : EvE GenExn.prog ⟨initL b lo hi tmin, m, false⟩
      (.un .lnot ⟨32, true⟩ (.load (.int ⟨32, true⟩) (.field (.var 0) 0)))
      (boolVal (on.toNat == 0)) := by
    have hl : EvE GenExn.prog ⟨initL b lo hi tmin, m, false⟩
        (.load (.int ⟨32, true⟩) (.field (.var 0) 0)) (.int ⟨32, true⟩ on.toNat) := by
      apply EvE.loadAtI
      · apply EvE.fieldN (EvE.var h0) hm'
        simp [length_f32Block]
      · exact hm'
      · norm_num
      · rfl
    exact EvE.lnotInt hl
  have hbody : ExS GenExn.prog ⟨initL b lo hi tmin, m, false⟩ GenExn.tri_exn_key.body
      (.ret (some (.f32 (exnKey on sz oz lo hi tmin).toNat)))
      ⟨exnFinal b on sz oz lo hi tmin, m, false⟩ := by
    unfold GenExn.tri_exn_key
    dsimp only
    by_cases hne : on = Ref.zero
    · -- `on == 0`: the guard returns `tmin` immediately.
      apply ExS.seq_ret
      apply ExS.ite hcond
      · exact truthy_boolVal _
      · simp only [exnKey, exnFinal, if_pos hne]
        exact ExS.if_true (toNat_beq_zero_true hne) (ExS.ret (EvE.var h3))
    · -- `on != 0`: fall through to the straight-line key computation.
      apply ExS.seq
      · apply ExS.ite hcond
        · exact truthy_boolVal _
        · exact ExS.if_false (toNat_beq_zero_false hne) ExS.skip
      · simp only [exnKey, exnFinal, if_neg hne, exnUpd]
        apply ExS.seq
        · apply ExS.seq
          · setX (.f32 (subBits lo oz).toNat)
          · setX (.f32 (subBits hi oz).toNat)
        · apply ExS.seq
          · apply ExS.seq
            · setX (.f32 (mulBits sz (subBits lo oz)).toNat)
            · setX (.f32 (mulBits sz (subBits hi oz)).toNat)
          · apply ExS.seq
            · setX (.f32 (Ref.fmin (mulBits sz (subBits lo oz))
                  (mulBits sz (subBits hi oz))).toNat)
            · apply ExS.seq
              · apply ExS.seq
                · setX (.f32 (Ref.copysign (mulBits sz (subBits lo oz)) Ref.one).toNat)
                · setX (.f32 (Ref.copysign (mulBits sz (subBits hi oz)) Ref.one).toNat)
              · apply ExS.seq
                · setX (.f32 (Ref.fmax (Ref.copysign (mulBits sz (subBits lo oz)) Ref.one)
                      (Ref.copysign (mulBits sz (subBits hi oz)) Ref.one)).toNat)
                · apply ExS.seq
                  · setX (.f32 (subBits (Ref.fmin (mulBits sz (subBits lo oz))
                          (mulBits sz (subBits hi oz)))
                        (mulBits 0x36000000 (Ref.fmax (Ref.copysign (mulBits sz (subBits lo oz)) Ref.one)
                          (Ref.copysign (mulBits sz (subBits hi oz)) Ref.one)))).toNat)
                  · apply ExS.ret
                    evX
  exact ⟨_, hbody, rfl⟩

/-- **`tri_exn_key` refinement**: the compiled function returns `exnKey`. -/
theorem tri_exn_key_refines (on kz sz oz lo hi tmin : Ref.F) (m : Mem) (b : Nat)
    (hm : m b = some (exnBlock on kz sz oz)) :
    ∃ K, ∀ n, K ≤ n →
      callFunc GenExn.prog n GenExn.fid_tri_exn_key
        [.ptr b 0, .f32 lo.toNat, .f32 hi.toNat, .f32 tmin.toNat] m =
      .ok (some (.f32 (exnKey on sz oz lo hi tmin).toNat), m) := by
  obtain ⟨s', h, hmem⟩ := exn_body on kz sz oz lo hi tmin m b hm
  obtain ⟨K, hK⟩ := callFunc_of_ExS (p := GenExn.prog) (f := GenExn.fid_tri_exn_key) rfl rfl h
  exact ⟨K, fun n hn => by rw [hK n hn, hmem]⟩

end LightRT.C.Proofs