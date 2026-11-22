/-
  Reusable evaluation lemmas for the binary32 fragment of MiniC
  (f32 loads from word blocks, f32 arithmetic, `tri_minf`/`tri_maxf` calls).
-/
import LightRT.C.Gen
import LightRT.C.Logic
import LightRT.C.Hoare
import LightRT.C.Ref

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

def f32Block (ws : List Nat) : Block := ws.flatMap (fun w => encodeLE 4 w)

@[simp] theorem toUInt32_toNat (x : UInt32) : x.toNat.toUInt32 = x := by
  simp [Nat.toUInt32]

theorem decodeLE_encodeLE4 (n : Nat) : decodeLE (encodeLE 4 n) = n % 2 ^ 32 := by
  simp only [encodeLE, decodeLE]
  have h : ∀ k : Nat, (k % 256).toUInt8.toNat = k % 256 := fun k => by
    simp [Nat.toUInt8]
  simp only [h]; omega

@[simp] theorem length_encodeLE (k n : Nat) : (encodeLE k n).length = k := by
  induction k generalizing n <;> simp [encodeLE, *]

theorem f32Block_cons (w : Nat) (ws : List Nat) : f32Block (w :: ws) = encodeLE 4 w ++ f32Block ws := by
  simp [f32Block]

theorem length_f32Block (ws : List Nat) : (f32Block ws).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [f32Block_cons, List.length_append, ih]; simp; ring

theorem word_at (ws : List Nat) (tl : Block) (j w : Nat) (hj : ws[j]? = some w) :
    ((f32Block ws ++ tl).drop (4 * j)).take 4 = encodeLE 4 w ∧ 4 * j + 4 ≤ (f32Block ws ++ tl).length := by
  induction ws generalizing j with
  | nil => simp at hj
  | cons x ws ih =>
    rw [f32Block_cons, List.append_assoc]
    cases j with
    | zero =>
      simp at hj; subst hj
      simp
    | succ j =>
      simp at hj
      obtain ⟨h1, h2⟩ := ih j hj
      rw [show 4 * (j + 1) = 4 + 4 * j by ring, ← List.drop_drop,
        List.drop_left' (length_encodeLE 4 x)]
      refine ⟨h1, ?_⟩
      simp only [List.length_append, length_encodeLE] at h2 ⊢; omega

section
variable {p : Prog} {s : State}

theorem EvE.f32bin {op a b x y v} (ha : EvE p s a (.f32 (x : UInt32).toNat))
    (hb : EvE p s b (.f32 (y : UInt32).toNat)) (hv : binF32 op x.toNat y.toNat = .ok v) :
    EvE p s (.bin op none a b) v :=
  EvE.bin ha hb (by simpa [evalBin, isPtr, evalBinInt] using hv)

theorem EvE.f32sub {a b} {x y : UInt32} (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.bin .sub none a b) (.f32 (subBits x y).toNat) := EvE.f32bin ha hb (by simp [binF32])
theorem EvE.f32mul {a b} {x y : UInt32} (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.bin .mul none a b) (.f32 (mulBits x y).toNat) := EvE.f32bin ha hb (by simp [binF32])
theorem EvE.f32add {a b} {x y : UInt32} (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.bin .add none a b) (.f32 (addBits x y).toNat) := EvE.f32bin ha hb (by simp [binF32])
theorem EvE.f32div {a b} {x y : UInt32} (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.bin .div none a b) (.f32 (divBits x y).toNat) := EvE.f32bin ha hb (by simp [binF32])
theorem EvE.sqrt' {a} {x : UInt32} (ha : EvE p s a (.f32 x.toNat)) :
    EvE p s (.sqrt a) (.f32 (Ref.sqrt x).toNat) := by
  obtain ⟨K, hK⟩ := ha
  refine ⟨K + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [evalExpr, hK m (by omega), Res.bind_eq, Res.bind_ok, Ref.sqrt, toUInt32_toNat]
  rfl
theorem EvE.f32lt {a b} {x y : UInt32} (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.bin .lt none a b) (boolVal (ltBits x y)) := EvE.f32bin ha hb (by simp [binF32])
theorem EvE.f32le {a b} {x y : UInt32} (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.bin .le none a b) (boolVal (leBits x y)) := EvE.f32bin ha hb (by simp [binF32])
theorem EvE.f32gt {a b} {x y : UInt32} (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.bin .gt none a b) (boolVal (ltBits y x)) := EvE.f32bin ha hb (by simp [binF32])
theorem EvE.f32ge {a b} {x y : UInt32} (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.bin .ge none a b) (boolVal (leBits y x)) := EvE.f32bin ha hb (by simp [binF32])

@[simp] theorem truthy_boolVal (b : Bool) : truthy (boolVal b) = .ok b := by
  cases b <;> rfl

/-- A `float` load of word `j` of a block made of 32-bit words. -/
theorem EvE.loadWord {a} {b : Nat} {ws : List Nat} {tl : Block} {j : Nat} {w : UInt32}
    (ha : EvE p s a (.ptr b (4 * j))) (hm : s.mem b = some (f32Block ws ++ tl)) 
    (hj : ws[j]? = some w.toNat) :
    EvE p s (.load .f32 a) (.f32 w.toNat) := by
  obtain ⟨h1, h2⟩ := word_at ws tl j w.toNat hj
  refine EvE.load ha ?_
  simp only [load, readBytes, hm, Ty.size, h2, ite_true, h1]
  show Res.ok (Val.f32 (decodeLE (encodeLE 4 w.toNat))) = _
  rw [decodeLE_encodeLE4, Nat.mod_eq_of_lt w.toNat_lt]
end
end LightRT.C.Proofs

namespace LightRT.C.Proofs
open LightRT.C
section
variable {p : Prog} {s : State}

theorem EvE.indexI32 {base idx} {b o k : Nat} {blk : Block}
    (hb : EvE p s base (.ptr b o)) (hi : EvE p s idx (.int ⟨32, true⟩ k)) (hk : k < 2 ^ 31)
    (hm : s.mem b = some blk) (hl : o + 4 * k ≤ blk.length) :
    EvE p s (.index base idx 4) (.ptr b (o + 4 * k)) := by
  refine EvE.index hb hi ?_
  simp only [ite_true, ptrAdd, hm, IntTy.toInt]
  split_ifs <;> first | omega | (simp only [Res.ok.injEq, Val.ptr.injEq, true_and]; omega)

theorem EvE.fieldN {base} {b o off : Nat} {blk : Block}
    (hb : EvE p s base (.ptr b o)) (hm : s.mem b = some blk) (hl : o + off ≤ blk.length) :
    EvE p s (.field base off) (.ptr b (o + off)) :=
  EvE.field hb (by simp [ptrAddN, hm, hl])

theorem EvE.callMin {a b} {x y : UInt32} (ha : EvE Gen.prog s a (.f32 x.toNat))
    (hb : EvE Gen.prog s b (.f32 y.toNat)) :
    EvE Gen.prog s (.call Gen.fid_tri_minf [a, b]) (.f32 (Ref.fmin x y).toNat) := by
  refine EvE.call (EvArgs.cons ha (EvArgs.cons hb EvArgs.nil)) rfl rfl (ExS.ret ?_)
  refine EvE.cond (EvE.f32lt (EvE.var rfl) (EvE.var rfl)) (truthy_boolVal _) ?_
  unfold Ref.fmin; cases FP.Binary32.ltBits x y <;> exact EvE.var rfl

theorem EvE.callMax {a b} {x y : UInt32} (ha : EvE Gen.prog s a (.f32 x.toNat))
    (hb : EvE Gen.prog s b (.f32 y.toNat)) :
    EvE Gen.prog s (.call Gen.fid_tri_maxf [a, b]) (.f32 (Ref.fmax x y).toNat) := by
  refine EvE.call (EvArgs.cons ha (EvArgs.cons hb EvArgs.nil)) rfl rfl (ExS.ret ?_)
  refine EvE.cond (EvE.f32gt (EvE.var rfl) (EvE.var rfl)) (truthy_boolVal _) ?_
  unfold Ref.fmax; cases FP.Binary32.ltBits y x <;> exact EvE.var rfl

/-- Load word `o / 4` of a word block (form convenient for automation). -/
theorem EvE.loadAt {a} {b o : Nat} {ws : List Nat} {tl : Block} {w : UInt32}
    (ha : EvE p s a (.ptr b o)) (hm : s.mem b = some (f32Block ws ++ tl))
    (h4 : o % 4 = 0) (hj : ws[o / 4]? = some w.toNat) :
    EvE p s (.load .f32 a) (.f32 w.toNat) :=
  EvE.loadWord (j := o / 4) (by rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)]) hm hj

@[simp] theorem upd_same' (l : Locals) (i : Nat) (v : Val) : l.upd i v i = some v := by
  simp [Locals.upd]
theorem upd_ne' (l : Locals) {i j : Nat} (v : Val) (h : j ≠ i) : l.upd i v j = l j := by
  simp [Locals.upd, h]

theorem EvE.land' {a b} {x y : Bool} (ha : EvE p s a (boolVal x)) (hb : EvE p s b (boolVal y)) :
    EvE p s (.land a b) (boolVal (x && y)) := by
  cases x
  · exact EvE.land_false ha (truthy_boolVal _)
  · exact EvE.land_true ha (truthy_boolVal _) hb (truthy_boolVal _)

theorem EvE.lor' {a b} {x y : Bool} (ha : EvE p s a (boolVal x)) (hb : EvE p s b (boolVal y)) :
    EvE p s (.lor a b) (boolVal (x || y)) := by
  cases x
  · exact EvE.lor_false ha (truthy_boolVal _) hb (truthy_boolVal _)
  · exact EvE.lor_true ha (truthy_boolVal _)

theorem EvE.lnot' {a} {b : Bool} (ha : EvE p s a (boolVal b)) :
    EvE p s (.un .lnot ⟨32, true⟩ a) (boolVal (!b)) :=
  EvE.un ha (by simp [evalUn, truthy_boolVal])

theorem EvE.constF (n : Nat) (h : n < 2 ^ 32) :
    EvE p s (.const (.f32 n)) (.f32 (n.toUInt32).toNat) := by
  have : (n.toUInt32).toNat = n := by simp [Nat.toUInt32]; omega
  rw [this]; exact EvE.const _

theorem EvE.fneg' {a} {x : UInt32} (ha : EvE p s a (.f32 x.toNat)) :
    EvE p s (.fneg a) (.f32 (Ref.neg x).toNat) := by
  obtain ⟨K, h⟩ := ha
  refine ⟨K + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [evalExpr, h m (by omega), Res.bind_eq, Res.bind_ok, Ref.neg, UInt32.toNat_xor]
  rfl

end
end LightRT.C.Proofs
