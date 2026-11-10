/-
  Watertightness of the bit-level `tri_woop_one` (hence of the C function, by
  `tri_woop_one_refines`), for ALL inputs (NaN/∞/subnormal/overflow included):
  two triangles sharing an edge see that edge's function with exactly opposite
  sign, so a ray strictly inside the two non-shared edges of each triangle is
  accepted by the edge test of at least one of them.
-/
import LightRT.C.Proofs.WoopRefines
import LightRT.C.Proofs.SlabFP
import LightRT.C.Proofs.MTGap

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

/-! ### NaN bits -/

theorem decode_nan_iff (w : UInt32) : decode w = .nan ↔ isNaNBits w = true := by
  constructor
  · intro h
    rw [decode_fields] at h
    unfold isNaNBits
    split_ifs at h with h1 h2 <;> try cases h
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    constructor
    · apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_and, show (0x7f800000 : UInt32).toNat = 0x7f800000 by decide, and_exp_mask, h1]
      decide
    · intro h0
      have := congrArg UInt32.toNat h0
      rw [UInt32.toNat_and, show (0x7fffff : UInt32).toNat = 2 ^ 23 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod] at this
      exact h2 this
  · intro h
    unfold isNaNBits at h
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 := congrArg UInt32.toNat h1
    rw [UInt32.toNat_and, show (0x7f800000 : UInt32).toNat = 0x7f800000 by decide, and_exp_mask] at e1
    have e2 : (w &&& 0x7fffff).toNat ≠ 0 := fun hh => h2 (UInt32.toNat_inj.mp (by rw [hh]; rfl))
    rw [UInt32.toNat_and, show (0x7fffff : UInt32).toNat = 2 ^ 23 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod] at e2
    rw [decode_fields, if_pos (by omega), if_neg e2]

theorem decode_quiet (w : UInt32) (h : isNaNBits w = true) : decode (w ||| 0x400000) = .nan := by
  rw [← decode_nan_iff] at h
  rw [decode_fields] at h ⊢
  have hw : (w ||| 0x400000).toNat = w.toNat ||| 2 ^ 22 := by
    rw [UInt32.toNat_or]; rfl
  have hd : (w.toNat ||| 2 ^ 22) / 2 ^ 23 = w.toNat / 2 ^ 23 := by
    rw [Nat.or_div_two_pow, show (2 ^ 22 : Nat) / 2 ^ 23 = 0 by norm_num, Nat.or_zero]
  have hm : (w.toNat ||| 2 ^ 22) % 2 ^ 23 ≠ 0 := by
    rw [Nat.or_mod_two_pow, show (2 ^ 22 : Nat) % 2 ^ 23 = 2 ^ 22 by norm_num]
    intro h0
    have := Nat.left_le_or (n := 2 ^ 22) (m := w.toNat % 2 ^ 23)
    rw [Nat.lor_comm] at this; omega
  rw [hw, hd]
  split_ifs at h ⊢ with h1 h2 <;> first | rfl | cases h | exact absurd ‹_› hm

/-! ### `decode ∘ encode` on operation results -/

theorem dec_enc_inf (n : Bool) : decode (encode (.inf n)) = .inf n := by cases n <;> decide +kernel
theorem dec_enc_nan : decode (encode .nan) = .nan := by decide +kernel

theorem dec_enc_roundQ (p : ℚ) (z : Bool) : decode (encode (roundQ p z)) = roundQ p z := by
  by_cases h0 : p = 0
  · have e : roundQ p z = .num z 0 := by unfold roundQ; rw [if_pos h0]
    rw [e]
    exact decode_encode_num z 0 ⟨0, -149, le_refl _, by norm_num, by simp⟩ (by unfold maxFinite; norm_num)
  · by_cases h1 : |rne p| > maxFinite
    · have e : roundQ p z = .inf (decide (p < 0)) := by unfold roundQ; rw [if_neg h0]; dsimp only; rw [if_pos h1]
      rw [e]; exact dec_enc_inf _
    · have e : roundQ p z = .num (decide (p < 0)) |rne p| := by
        unfold roundQ; rw [if_neg h0]; dsimp only; rw [if_neg h1]
      rw [e]; exact decode_encode_num _ _ (abs_rne_grid p) (not_lt.1 h1)

theorem dec_enc_add (X Y : V) : decode (encode (X.add Y)) = X.add Y := by
  cases X <;> cases Y <;> simp only [V.add] <;> (try split_ifs) <;>
    simp only [dec_enc_nan, dec_enc_inf, dec_enc_roundQ]

theorem dec_enc_mul (X Y : V) : decode (encode (X.mul Y)) = X.mul Y := by
  cases X <;> cases Y <;> simp only [V.mul] <;> (try split_ifs) <;>
    simp only [dec_enc_nan, dec_enc_inf, dec_enc_roundQ]

/-- The decoded result of a binary32 operation depends only on the decoded operands. -/
theorem decode_prop (a b : UInt32) (f : V → V → V) (hf : ∀ X Y, decode (encode (f X Y)) = f X Y) :
    decode (propagate a b fun _ => encode (f (decode a) (decode b))) =
      if decode a = .nan ∨ decode b = .nan then .nan else f (decode a) (decode b) := by
  unfold propagate
  by_cases ha : isNaNBits a = true
  · rw [if_pos ha, decode_quiet a ha, if_pos (Or.inl ((decode_nan_iff a).2 ha))]
  · rw [if_neg ha]
    by_cases hb : isNaNBits b = true
    · rw [if_pos hb, decode_quiet b hb, if_pos (Or.inr ((decode_nan_iff b).2 hb))]
    · rw [if_neg hb, hf, if_neg]
      rintro (h | h)
      · exact ha ((decode_nan_iff a).1 h)
      · exact hb ((decode_nan_iff b).1 h)

theorem decode_sub (a b : UInt32) : decode (subBits a b) =
    if decode a = .nan ∨ decode b = .nan then .nan else (decode a).sub (decode b) :=
  decode_prop a b V.sub (fun X Y => dec_enc_add X Y.negate)

theorem decode_mul (a b : UInt32) : decode (mulBits a b) =
    if decode a = .nan ∨ decode b = .nan then .nan else (decode a).mul (decode b) :=
  decode_prop a b V.mul dec_enc_mul

theorem V.mul_comm' (X Y : V) : X.mul Y = Y.mul X := by
  cases X <;> cases Y <;> simp only [V.mul, bne_comm, mul_comm]

theorem decode_mul_comm (a b : UInt32) : decode (mulBits a b) = decode (mulBits b a) := by
  simp only [decode_mul, V.mul_comm' (decode a), or_comm]

/-! ### Signs -/

theorem rne_neg_q (p : ℚ) : rne (-p) = -rne p := by
  have h := rneR_neg (p : ℝ)
  rw [show (-(p : ℝ)) = ((-p : ℚ) : ℝ) by push_cast; rfl, rne_cast, rne_cast] at h
  exact_mod_cast h

def Zv : V := .num false 0

theorem cmp_roundQ (p : ℚ) (z : Bool) :
    V.cmp true Zv (roundQ p z) = decide (0 < rne p) ∧ V.cmp true (roundQ p z) Zv = decide (rne p < 0) := by
  have hs := rne_sign_q p
  have hmax : (0 : ℚ) < maxFinite := by unfold maxFinite; norm_num
  by_cases h0 : p = 0
  · have e : roundQ p z = .num z 0 := by unfold roundQ; rw [if_pos h0]
    rw [e, h0]; cases z <;> simp [V.cmp, Zv, V.toQ?, rne]
  · by_cases h1 : |rne p| > maxFinite
    · have e : roundQ p z = .inf (decide (p < 0)) := by unfold roundQ; rw [if_neg h0]; dsimp only; rw [if_pos h1]
      rw [e]
      by_cases hn : p < 0
      · have : rne p < 0 := by
          rcases lt_or_eq_of_le (hs.1 hn) with h | h
          · exact h
          · rw [h] at h1; simp at h1; linarith
        simp [V.cmp, Zv, V.toQ?, hn, this, not_lt.2 this.le]
      · have : 0 < rne p := by
          rcases lt_or_eq_of_le (hs.2 (not_lt.1 hn)) with h | h
          · exact h
          · rw [← h] at h1; simp at h1; linarith
        simp [V.cmp, Zv, V.toQ?, hn, this, not_lt.2 this.le]
    · have e : roundQ p z = .num (decide (p < 0)) |rne p| := by
        unfold roundQ; rw [if_neg h0]; dsimp only; rw [if_neg h1]
      rw [e]
      have hv : (if decide (p < 0) = true then -|rne p| else |rne p|) = rne p := by
        by_cases hn : p < 0
        · simp [hn, abs_of_nonpos (hs.1 hn)]
        · simp [hn, abs_of_nonneg (hs.2 (not_lt.1 hn))]
      simp only [V.cmp, Zv, V.toQ?, Option.getD_some]
      simp only [ne_eq, not_true_eq_false, ite_false, Bool.false_eq_true, hv]
      simp

theorem sub_sign (X Y : V) :
    V.cmp true Zv (if X = .nan ∨ Y = .nan then .nan else X.sub Y) =
      V.cmp true (if Y = .nan ∨ X = .nan then .nan else Y.sub X) Zv ∧
    V.cmp true (if X = .nan ∨ Y = .nan then .nan else X.sub Y) Zv =
      V.cmp true Zv (if Y = .nan ∨ X = .nan then .nan else Y.sub X) := by
  cases X with
  | nan => simp [V.cmp, Zv]
  | inf a =>
    cases Y with
    | nan => simp [V.cmp, Zv]
    | inf b => cases a <;> cases b <;> simp [V.sub, V.add, V.negate, V.cmp, Zv, V.toQ?]
    | num b y => cases a <;> simp [V.sub, V.add, V.negate, V.cmp, Zv, V.toQ?]
  | num a x =>
    cases Y with
    | nan => simp [V.cmp, Zv]
    | inf b => cases b <;> simp [V.sub, V.add, V.negate, V.cmp, Zv, V.toQ?]
    | num b y =>
      simp only [V.sub, V.add, V.negate, reduceCtorEq, or_self, ite_false]
      have hp : ((V.num b y).toQ?.getD 0 + (V.num (!a) x).toQ?.getD 0) =
          -((V.num a x).toQ?.getD 0 + (V.num (!b) y).toQ?.getD 0) := by
        cases a <;> cases b <;> simp [V.toQ?] <;> ring
      rw [hp]
      obtain ⟨c1, c2⟩ := cmp_roundQ ((V.num a x).toQ?.getD 0 + (V.num (!b) y).toQ?.getD 0) (a && !b)
      obtain ⟨d1, d2⟩ := cmp_roundQ (-((V.num a x).toQ?.getD 0 + (V.num (!b) y).toQ?.getD 0)) (b && !a)
      rw [c1, c2, d1, d2, rne_neg_q]
      constructor <;> simp [neg_pos, neg_lt_zero]

/-! ### Watertightness -/

theorem decode_zero : decode Ref.zero = Zv := by decide +kernel

/-- The binary32 edge function is sign-antisymmetric, for every input. -/
theorem edge_sign (px py qx qy : UInt32) :
    ltBits Ref.zero (Ref.woopEdge px py qx qy) = ltBits (Ref.woopEdge qx qy px py) Ref.zero ∧
    ltBits (Ref.woopEdge px py qx qy) Ref.zero = ltBits Ref.zero (Ref.woopEdge qx qy px py) := by
  unfold ltBits Ref.woopEdge
  rw [decode_zero, decode_sub, decode_sub, decode_mul_comm qx py, decode_mul_comm qy px]
  exact sub_sign _ _

theorem ltBits_asymm {a b : UInt32} (h : ltBits a b = true) : ltBits b a = false := by
  unfold ltBits at *
  cases ha : decode a <;> cases hb : decode b <;> rw [ha, hb] at h <;> simp [V.cmp] at h ⊢ <;>
    first | (split_ifs at h ⊢ <;> simp_all) | (intro; simp_all) | (simp_all; try linarith) | linarith

/-- Two triangles sharing the edge `a–b` see its edge function with opposite sign. -/
theorem woop_shared_edge_W_bits (k : Ref.Axes) (o d a b c c' : Fin 3 → Ref.F) :
    ltBits (Ref.woopW k o d a b c) Ref.zero = ltBits Ref.zero (Ref.woopW k o d b a c') ∧
    ltBits Ref.zero (Ref.woopW k o d a b c) = ltBits (Ref.woopW k o d b a c') Ref.zero := by
  unfold Ref.woopW
  exact ⟨(edge_sign _ _ _ _).2, (edge_sign _ _ _ _).1⟩

/-- **Watertightness of `tri_woop_one` (bit level, every input).** If the ray is
    strictly inside the non-shared edges of two triangles `(a,b,c)` and `(b,a,c')`
    that share the edge `a–b` (`U > 0`, `V` not negative for both), the sign test
    of at least one of them passes: no ray slips through the shared edge. -/
theorem woop_no_gap_bits (k : Ref.Axes) (o d a b c c' : Fin 3 → Ref.F)
    (h1 : ltBits Ref.zero (Ref.woopU k o d a b c) = true)
    (h1' : ltBits (Ref.woopV k o d a b c) Ref.zero = false)
    (h2 : ltBits Ref.zero (Ref.woopU k o d b a c') = true)
    (h2' : ltBits (Ref.woopV k o d b a c') Ref.zero = false) :
    Ref.woopRej1 k o d a b c = false ∨ Ref.woopRej1 k o d b a c' = false := by
  have e1 : Ref.woopRej1 k o d a b c = ltBits (Ref.woopW k o d a b c) Ref.zero := by
    unfold Ref.woopRej1; rw [ltBits_asymm h1, h1', h1]; simp
  have e2 : Ref.woopRej1 k o d b a c' = ltBits (Ref.woopW k o d b a c') Ref.zero := by
    unfold Ref.woopRej1; rw [ltBits_asymm h2, h2', h2]; simp
  obtain ⟨s1, -⟩ := woop_shared_edge_W_bits k o d a b c c'
  rw [e1, e2, s1]
  cases h : ltBits Ref.zero (Ref.woopW k o d b a c')
  · exact Or.inl rfl
  · exact Or.inr (ltBits_asymm h)

set_option maxRecDepth 100000 in
/-- On the ray that leaks through Möller–Trumbore (`mt_not_watertight`), the Woop
    test accepts the triangle the exact ray hits. -/
theorem woop_closes_mt_gap : (Ref.woop gO gD gA gC gP 0 gTbest).isSome = true := by
  decide +kernel
end LightRT.C.Proofs
