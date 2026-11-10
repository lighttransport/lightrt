/-
  Refinement for `tri_ray_setup`: the c2lean translation (a 3-iteration loop
  with struct stores, then reads of the freshly written `invd`) writes exactly
  `ctxBlock (Ref.raySetup …)` into `*rc`, for every input.
-/
import LightRT.C.Proofs.MTRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

/-! ### Bit-level helpers -/

theorem copysign_toNat (x y : UInt32) :
    x.toNat % 2147483648 + y.toNat / 2147483648 * 2147483648 = (Ref.copysign x y).toNat := by
  unfold Ref.copysign
  rw [UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_and,
    show (0x7fffffff : UInt32).toNat = 2 ^ 31 - 1 by decide,
    show (0x80000000 : UInt32).toNat = 2 ^ 31 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow]
  have hy := y.toNat_lt
  have hb : (y.toNat.testBit 31).toNat = y.toNat / 2 ^ 31 := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.lt_or_ge y.toNat (2 ^ 31) with h | h
    · have : y.toNat / 2 ^ 31 = 0 := Nat.div_eq_of_lt h
      rw [this]; rfl
    · have : y.toNat / 2 ^ 31 = 1 := by omega
      rw [this]; rfl
  rw [hb, Nat.lor_comm, show y.toNat / 2 ^ 31 * 2 ^ 31 = 2 ^ 31 * (y.toNat / 2 ^ 31) from mul_comm _ _,
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by norm_num))]
  omega

theorem f32eq_eqF (a b : UInt32) :
    (!((decode a == .nan) || (decode b == .nan)) && leBits a b && leBits b a) = Ref.eqF a b := by
  unfold Ref.eqF leBits
  have e1 : ∀ n m, (V.num n m == V.nan) = false := fun _ _ => beq_eq_false_iff_ne.2 (by simp)
  have e2 : ∀ n, (V.inf n == V.nan) = false := fun _ => beq_eq_false_iff_ne.2 (by simp)
  cases decode a <;> cases decode b <;> simp [V.cmp, e1, e2]

/-- Writing word `j` of a word block. -/
theorem f32Block_set (ws : List Nat) (j w : Nat) (hj : j < ws.length) :
    (f32Block ws).take (4 * j) ++ encodeLE 4 w ++ (f32Block ws).drop (4 * j + 4) =
      f32Block (ws.set j w) := by
  induction ws generalizing j with
  | nil => simp at hj
  | cons x ws ih =>
    cases j with
    | zero => simp [f32Block_cons, List.drop_left' (length_encodeLE 4 x)]
    | succ j =>
      simp only [List.length_cons] at hj
      have hE : (encodeLE 4 x).length = 4 := length_encodeLE 4 x
      rw [List.set_cons_succ, f32Block_cons, f32Block_cons,
        show 4 * (j + 1) = (encodeLE 4 x).length + 4 * j by rw [hE]; ring,
        show (encodeLE 4 x).length + 4 * j + 4 = (encodeLE 4 x).length + (4 * j + 4) by ring,
        List.take_append, List.drop_append, ← ih j (by omega)]
      simp [List.take_of_length_le (show (encodeLE 4 x).length ≤ 4 + 4 * j by omega),
        List.drop_eq_nil_of_le (show (encodeLE 4 x).length ≤ 4 + (4 * j + 4) by omega)]

theorem store_rcF (M : Mem) (b : Nat) (ws : List Nat) (o w : Nat) (hm : M b = some (f32Block ws ++ []))
    (h4 : o % 4 = 0) (hj : o / 4 < ws.length) :
    store M .f32 (.ptr b o) (.f32 w) = .ok (M.upd b (f32Block (ws.set (o / 4) w) ++ [])) := by
  have ho : o = 4 * (o / 4) := by omega
  have hl := length_f32Block ws
  simp only [store, writeBytes, hm, List.append_nil, length_encodeLE]
  rw [ite_cond_eq_true _ _ (by simp; omega)]
  rw [ho, f32Block_set ws _ w hj]
  simp [← ho]

theorem store_rcI (M : Mem) (b : Nat) (ws : List Nat) (o w : Nat) (hm : M b = some (f32Block ws ++ []))
    (h4 : o % 4 = 0) (hj : o / 4 < ws.length) :
    store M (.int ⟨32, true⟩) (.ptr b o) (.int ⟨32, true⟩ w) =
      .ok (M.upd b (f32Block (ws.set (o / 4) w) ++ [])) := by
  have := store_rcF M b ws o w hm h4 hj
  simpa [store, IntTy.bytes] using this

section
variable {p : Prog} {s : State}

theorem EvE.lnot' {a} {b : Bool} (ha : EvE p s a (boolVal b)) :
    EvE p s (.un .lnot ⟨32, true⟩ a) (boolVal (!b)) :=
  EvE.un ha (by simp [evalUn, truthy_boolVal])

theorem EvE.copysign' {a b} {x y : UInt32} (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.copysign a b) (.f32 (Ref.copysign x y).toNat) := by
  obtain ⟨K1, h1⟩ := ha
  obtain ⟨K2, h2⟩ := hb
  refine ⟨max K1 K2 + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [evalExpr, h1 m (by omega), h2 m (by omega), Res.bind_eq, Res.bind_ok]
  rw [← copysign_toNat]; rfl

theorem EvE.f32eq {a b} {x y : UInt32} (ha : EvE p s a (.f32 x.toNat)) (hb : EvE p s b (.f32 y.toNat)) :
    EvE p s (.bin .eq none a b) (boolVal (Ref.eqF x y)) :=
  EvE.f32bin ha hb (by simp only [binF32, toUInt32_toNat]; rw [← f32eq_eqF])

end

/-! ### Chunks of the loop body, over an arbitrary state -/

def rayWords (org dir : Fin 3 → Ref.F) (tmin tmax : Ref.F) : List Nat :=
  vecWords org ++ [tmin.toNat] ++ vecWords dir ++ [tmax.toNat]

/-- Common hypotheses on the state at a loop iteration with index `k`. -/
structure Hyp (s : State) (bRay bRc k : Nat) (R ws : List Nat) : Prop where
  l0 : s.locals 0 = some (.ptr bRay 0)
  l1 : s.locals 1 = some (.ptr bRc 0)
  l2 : s.locals 2 = some (.int ⟨32, true⟩ k)
  mray : s.mem bRay = some (f32Block R ++ [])
  mrc : s.mem bRc = some (f32Block ws ++ [])
  rlen : R.length = 8
  wlen : ws.length = 14
  ro : s.ro = false
  hk : k ≤ 3

theorem Hyp.ptrRay {s bRay bRc k R ws} (H : Hyp s bRay bRc k R ws) (S : Nat) (hS : S + 4 * k + 4 ≤ 32) :
    EvE Gen.prog s (.index (.field (.var 0) S) (.var 2) 4) (.ptr bRay (0 + S + 4 * k)) := by
  have hl := length_f32Block R
  rw [H.rlen] at hl
  exact EvE.indexI32 (EvE.fieldN (EvE.var H.l0) H.mray (by simp; omega)) (EvE.var H.l2)
    (by have := H.hk; omega) H.mray (by simp; omega)

theorem Hyp.ptrRc {s bRay bRc k R ws} (H : Hyp s bRay bRc k R ws) (D : Nat) (hD : D + 4 * k + 4 ≤ 56) :
    EvE Gen.prog s (.index (.field (.var 1) D) (.var 2) 4) (.ptr bRc (0 + D + 4 * k)) := by
  have hl := length_f32Block ws
  exact EvE.indexI32 (EvE.fieldN (EvE.var H.l1) H.mrc (by simp; rw [H.wlen] at hl; omega)) (EvE.var H.l2)
    (by have := H.hk; omega) H.mrc (by simp; rw [H.wlen] at hl; omega)

theorem Hyp.loadRay {s bRay bRc k R ws} (H : Hyp s bRay bRc k R ws) (S : Nat) (hS : S + 4 * k + 4 ≤ 32)
    (hS4 : S % 4 = 0) (w : UInt32) (hw : R[S / 4 + k]? = some w.toNat) :
    EvE Gen.prog s (.load .f32 (.index (.field (.var 0) S) (.var 2) 4)) (.f32 w.toNat) :=
  EvE.loadAt (H.ptrRay S hS) H.mray (by omega) (by rwa [show (0 + S + 4 * k) / 4 = S / 4 + k by omega])

theorem Hyp.store {s bRay bRc k R ws} (H : Hyp s bRay bRc k R ws) (D : Nat) (hD : D + 4 * k + 4 ≤ 56)
    (hD4 : D % 4 = 0) {e : Expr} {w : UInt32} (he : EvE Gen.prog s e (.f32 w.toNat)) :
    ExS Gen.prog s (.store .f32 (.index (.field (.var 1) D) (.var 2) 4) e) .normal
      { s with mem := s.mem.upd bRc (f32Block (ws.set (D / 4 + k) w.toNat) ++ []) } := by
  have := store_rcF s.mem bRc ws (0 + D + 4 * k) w.toNat H.mrc (by omega) (by rw [H.wlen]; omega)
  rw [show (0 + D + 4 * k) / 4 = D / 4 + k by omega] at this
  exact ExS.store (H.ptrRc D hD) he H.ro this

theorem upd_self (l : Locals) (i : Nat) (v : Val) (h : l i = some v) : l.upd i v = l := by
  funext j; by_cases hj : j = i <;> simp [Locals.upd, hj, h]

/-- The `invd` clamp. -/
def clampInv (inv d : Ref.F) : Ref.F :=
  if !(leBits (Ref.neg Ref.invdMax) inv && leBits inv Ref.invdMax) then
    Ref.copysign Ref.invdMax (if Ref.eqF d Ref.zero then Ref.one else d)
  else inv

/-- The `oinv` clamp. -/
def clampOi (oi : Ref.F) : Ref.F :=
  if !(leBits (Ref.neg Ref.oinvMax) oi && leBits oi Ref.oinvMax) then Ref.copysign Ref.oinvMax oi else oi

theorem chunk_clampInv {s bRay bRc k R ws} (H : Hyp s bRay bRc k R ws) (inv d : Ref.F)
    (h3 : s.locals 3 = some (.f32 inv.toNat)) (hw : R[16 / 4 + k]? = some d.toNat) :
    ExS Gen.prog s (.ite (.un .lnot ⟨32, true⟩ (.land (.bin .ge none (.var 3) (.fneg (.const (.f32 1566444395)))) (.bin .le none (.var 3) (.const (.f32 1566444395))))) (.set 3 (.copysign (.const (.f32 1566444395)) (.cond (.bin .eq none (.load .f32 (.index (.field (.var 0) 16) (.var 2) 4)) (.const (.f32 0))) (.const (.f32 1065353216)) (.load .f32 (.index (.field (.var 0) 16) (.var 2) 4))))) .skip)
      .normal { s with locals := s.locals.upd 3 (.f32 (clampInv inv d).toNat) } := by
  have hk := H.hk
  have hd := H.loadRay 16 (by omega) (by norm_num) d hw
  refine ExS.ite (EvE.lnot' (EvE.land' (EvE.f32ge (EvE.var h3) (EvE.fneg' (EvE.constF _ (by norm_num))))
    (EvE.f32le (EvE.var h3) (EvE.constF _ (by norm_num))))) (truthy_boolVal _) ?_
  unfold clampInv
  cases hc : (!(leBits (Ref.neg Ref.invdMax) inv && leBits inv Ref.invdMax))
  · have hc' : (!(leBits (Ref.neg (1566444395 : Nat).toUInt32) inv && leBits inv (1566444395 : Nat).toUInt32)) = false := hc
    rw [hc']; simp only [Bool.false_eq_true, ite_false]
    rw [upd_self _ _ _ h3]; exact ExS.skip
  · have hc' : (!(leBits (Ref.neg (1566444395 : Nat).toUInt32) inv && leBits inv (1566444395 : Nat).toUInt32)) = true := hc
    rw [hc']; simp only [ite_true]
    apply ExS.set
    refine EvE.copysign' (EvE.constF _ (by norm_num)) ?_
    refine EvE.cond (EvE.f32eq hd (EvE.constF 0 (by norm_num))) (truthy_boolVal _) ?_
    rw [show (0 : Nat).toUInt32 = Ref.zero from rfl]
    cases Ref.eqF d Ref.zero
    · exact hd
    · exact EvE.constF 1065353216 (by norm_num)

theorem chunk_clampOi {s : State} (oi : Ref.F) (h4 : s.locals 4 = some (.f32 oi.toNat)) :
    ExS Gen.prog s (.ite (.un .lnot ⟨32, true⟩ (.land (.bin .ge none (.var 4) (.fneg (.const (.f32 2096152002)))) (.bin .le none (.var 4) (.const (.f32 2096152002))))) (.set 4 (.copysign (.const (.f32 2096152002)) (.var 4))) .skip)
      .normal { s with locals := s.locals.upd 4 (.f32 (clampOi oi).toNat) } := by
  refine ExS.ite (EvE.lnot' (EvE.land' (EvE.f32ge (EvE.var h4) (EvE.fneg' (EvE.constF _ (by norm_num))))
    (EvE.f32le (EvE.var h4) (EvE.constF _ (by norm_num))))) (truthy_boolVal _) ?_
  unfold clampOi
  cases hc : (!(leBits (Ref.neg Ref.oinvMax) oi && leBits oi Ref.oinvMax))
  · have hc' : (!(leBits (Ref.neg (2096152002 : Nat).toUInt32) oi && leBits oi (2096152002 : Nat).toUInt32)) = false := hc
    rw [hc']; simp only [Bool.false_eq_true, ite_false]
    rw [upd_self _ _ _ h4]; exact ExS.skip
  · have hc' : (!(leBits (Ref.neg (2096152002 : Nat).toUInt32) oi && leBits oi (2096152002 : Nat).toUInt32)) = true := hc
    rw [hc']; simp only [ite_true]
    exact ExS.set (EvE.copysign' (EvE.constF _ (by norm_num)) (EvE.var h4))

theorem Hyp.afterStore {s bRay bRc k R ws} (H : Hyp s bRay bRc k R ws) (hne : bRay ≠ bRc) (j w : Nat) :
    Hyp { s with mem := s.mem.upd bRc (f32Block (ws.set j w) ++ []) } bRay bRc k R (ws.set j w) :=
  { l0 := H.l0, l1 := H.l1, l2 := H.l2,
    mray := by simp [Mem.upd, hne, H.mray]
    mrc := by simp [Mem.upd]
    rlen := H.rlen, wlen := by simp [H.wlen], ro := H.ro, hk := H.hk }

theorem Hyp.afterSet {s bRay bRc k R ws} (H : Hyp s bRay bRc k R ws) (i : Nat) (hi : 3 ≤ i) (v : Val) :
    Hyp { s with locals := s.locals.upd i v } bRay bRc k R ws :=
  { l0 := by simp [Locals.upd, show (0:Nat) ≠ i by omega, H.l0]
    l1 := by simp [Locals.upd, show (1:Nat) ≠ i by omega, H.l1]
    l2 := by simp [Locals.upd, show (2:Nat) ≠ i by omega, H.l2]
    mray := H.mray, mrc := H.mrc, rlen := H.rlen, wlen := H.wlen, ro := H.ro, hk := H.hk }

def rsBody : Stmt := match Gen.tri_ray_setup_loop0 with | .loop (.ite _ b _) _ => b | _ => .skip
def rsCond : Expr := match Gen.tri_ray_setup_loop0 with | .loop (.ite c _ _) _ => c | _ => .const .null
def rsStep : Stmt := match Gen.tri_ray_setup_loop0 with | .loop _ st => st | _ => .skip
theorem loop0_eq : Gen.tri_ray_setup_loop0 = .loop (.ite rsCond rsBody .brk) rsStep := rfl

/-- Context words written by iteration `k`. -/
def setK (org dir : Fin 3 → Ref.F) (tmin : Ref.F) (ws : List Nat) (k : Fin 3) : List Nat :=
  (((ws.set k (org k).toNat).set (3 + k) (dir k).toNat).set (6 + k)
    ((Ref.raySetup org dir tmin).invd k).toNat).set (9 + k) ((Ref.raySetup org dir tmin).oinv k).toNat

theorem invd_eq (org dir : Fin 3 → Ref.F) (tmin : Ref.F) (k : Fin 3) :
    (Ref.raySetup org dir tmin).invd k = clampInv (divBits Ref.one (dir k)) (dir k) := rfl
theorem oinv_eq (org dir : Fin 3 → Ref.F) (tmin : Ref.F) (k : Fin 3) :
    (Ref.raySetup org dir tmin).oinv k = clampOi (mulBits (org k) ((Ref.raySetup org dir tmin).invd k)) := rfl

theorem iter (org dir : Fin 3 → Ref.F) (tmin tmax : Ref.F) (k : Nat) (hk : k < 3) (s : State)
    (bRay bRc : Nat) (ws : List Nat) (hne : bRay ≠ bRc)
    (H : Hyp s bRay bRc k (rayWords org dir tmin tmax) ws) :
    ∃ s', ExS Gen.prog s rsBody .normal s' ∧
      Hyp s' bRay bRc k (rayWords org dir tmin tmax) (setK org dir tmin ws ⟨k, hk⟩) ∧
      ∀ b, b ≠ bRc → s'.mem b = s.mem b := by
  have wo : (rayWords org dir tmin tmax)[0 / 4 + k]? = some (org ⟨k, hk⟩).toNat := by
    interval_cases k <;> rfl
  have wd : (rayWords org dir tmin tmax)[16 / 4 + k]? = some (dir ⟨k, hk⟩).toNat := by
    interval_cases k <;> rfl
  -- 1. rc->org[k] = ray->org[k]
  have e1 := H.store 0 (by omega) rfl (H.loadRay 0 (by omega) rfl _ wo)
  have H1 := H.afterStore hne (0 / 4 + k) (org ⟨k, hk⟩).toNat
  -- 2. rc->dir[k] = ray->dir[k]
  have e2 := H1.store 12 (by omega) rfl (H1.loadRay 16 (by omega) rfl _ wd)
  have H2 := H1.afterStore hne (12 / 4 + k) (dir ⟨k, hk⟩).toNat
  -- 3. inv = 1 / ray->dir[k]
  have e3 := ExS.set (i := 3) (EvE.f32div (EvE.constF 1065353216 (by norm_num)) (H2.loadRay 16 (by omega) rfl _ wd))
  have H3 := H2.afterSet 3 le_rfl (.f32 (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)).toNat)
  -- 4. clamp
  have e4 := chunk_clampInv H3 (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)) (dir ⟨k, hk⟩) (by simp [Locals.upd]) wd
  have H4 := H3.afterSet 3 le_rfl (.f32 (clampInv (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)) (dir ⟨k, hk⟩)).toNat)
  -- 5. rc->invd[k] = inv
  have e5 := H4.store 24 (by omega) rfl (w := clampInv (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)) (dir ⟨k, hk⟩)) (EvE.var (i := 3) (by simp [Locals.upd]))
  have H5 := H4.afterStore hne (24 / 4 + k) (clampInv (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)) (dir ⟨k, hk⟩)).toNat
  -- 6. oi = ray->org[k] * inv
  have e6 := ExS.set (i := 4) (EvE.f32mul (y := clampInv (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)) (dir ⟨k, hk⟩)) (H5.loadRay 0 (by omega) rfl _ wo) (EvE.var (i := 3) (by simp [Locals.upd])))
  have H6 := H5.afterSet 4 (by norm_num) (.f32 (mulBits (org ⟨k, hk⟩) (clampInv (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)) (dir ⟨k, hk⟩))).toNat)
  -- 7. clamp, 8. rc->oinv[k] = oi
  have H7 := H6.afterSet 4 (by norm_num)
    (.f32 (clampOi (mulBits (org ⟨k, hk⟩) (clampInv (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)) (dir ⟨k, hk⟩)))).toNat)
  have e8 := H7.store 36 (by omega) rfl (w := clampOi (mulBits (org ⟨k, hk⟩) (clampInv (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)) (dir ⟨k, hk⟩)))) (EvE.var (i := 4) (by simp [Locals.upd]))
  have H8 := H7.afterStore hne (36 / 4 + k)
    (clampOi (mulBits (org ⟨k, hk⟩) (clampInv (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)) (dir ⟨k, hk⟩)))).toNat
  refine ⟨?st, ?ex, ?hy, ?fr⟩
  case ex =>
    unfold rsBody Gen.tri_ray_setup_loop0
    refine ExS.seq e1 (ExS.seq e2 (ExS.seq e3 (ExS.seq e4 (ExS.seq e5 (ExS.seq e6 (ExS.seq
      (chunk_clampOi (mulBits (org ⟨k, hk⟩) (clampInv (divBits (1065353216 : Nat).toUInt32 (dir ⟨k, hk⟩)) (dir ⟨k, hk⟩))) ?_) ?_))))))
    · simp [Locals.upd]
    · convert e8 using 2
  case fr => intro b hb; simp [Mem.upd, hb]
  case hy =>
    convert H8 using 1
    simp only [setK, invd_eq, oinv_eq]
    norm_num
    rfl

/-! ### Loop, tail, and the whole function -/

theorem encodeLE4_decode (a b c d : UInt8) : encodeLE 4 (decodeLE [a, b, c, d]) = [a, b, c, d] := by
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
  simp only [encodeLE, decodeLE, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> simp [Nat.toUInt8] <;> omega

theorem block_words : ∀ (n : Nat) (blk : Block), blk.length = 4 * n →
    ∃ ws : List Nat, ws.length = n ∧ blk = f32Block ws
  | 0, blk, h => ⟨[], rfl, by simp at h; simp [h, f32Block]⟩
  | n + 1, a :: b :: c :: d :: rest, h => by
    obtain ⟨ws, hl, hr⟩ := block_words n rest (by simp at h; omega)
    refine ⟨decodeLE [a, b, c, d] :: ws, by simp [hl], ?_⟩
    rw [f32Block_cons, encodeLE4_decode, ← hr]; rfl
  | n + 1, [], h | n + 1, [_], h | n + 1, [_, _], h | n + 1, [_, _, _], h => by simp at h <;> omega

theorem Hyp.step {s bRay bRc k R ws} (H : Hyp s bRay bRc k R ws) (hk3 : k + 1 ≤ 3) :
    Hyp { s with locals := s.locals.upd 2 (.int ⟨32, true⟩ (k + 1)) } bRay bRc (k + 1) R ws :=
  { l0 := by simp [Locals.upd, H.l0]
    l1 := by simp [Locals.upd, H.l1]
    l2 := by simp [Locals.upd]
    mray := H.mray, mrc := H.mrc, rlen := H.rlen, wlen := H.wlen, ro := H.ro, hk := hk3 }

theorem exec_step {s : State} (k : Nat) (hk : k < 3) (h2 : s.locals 2 = some (.int ⟨32, true⟩ k)) :
    ExS Gen.prog s rsStep .normal { s with locals := s.locals.upd 2 (.int ⟨32, true⟩ (k + 1)) } := by
  apply ExS.set
  refine EvE.cast (va := .int ⟨32, true⟩ (k + 1)) (EvE.bin (EvE.cast (EvE.var h2) rfl) (EvE.const _) ?_) ?_
  · interval_cases k <;> rfl
  · interval_cases k <;> rfl

theorem cond_val {s : State} (k : Nat) (h2 : s.locals 2 = some (.int ⟨32, true⟩ k)) (hk : k ≤ 3) :
    EvE Gen.prog s rsCond (boolVal (decide (k < 3))) := by
  refine EvE.bin (EvE.var h2) (EvE.const _) ?_
  interval_cases k <;> rfl

theorem setK_length (org dir : Fin 3 → Ref.F) (tmin : Ref.F) (ws : List Nat) (k : Fin 3) :
    (setK org dir tmin ws k).length = ws.length := by simp [setK]

/-- One full iteration of the `for` loop. -/
theorem loop_iter {org dir : Fin 3 → Ref.F} {tmin tmax : Ref.F} {s : State} {bRay bRc : Nat}
    {ws : List Nat} (k : Nat) (hk : k < 3) (hne : bRay ≠ bRc)
    (H : Hyp s bRay bRc k (rayWords org dir tmin tmax) ws) :
    ∃ s1, Hyp s1 bRay bRc (k + 1) (rayWords org dir tmin tmax) (setK org dir tmin ws ⟨k, hk⟩) ∧
      (∀ b, b ≠ bRc → s1.mem b = s.mem b) ∧ ∀ r sf, ExS Gen.prog s1 Gen.tri_ray_setup_loop0 r sf → ExS Gen.prog s Gen.tri_ray_setup_loop0 r sf := by
  obtain ⟨s1, e1, H1, f1⟩ := iter org dir tmin tmax k hk s bRay bRc ws hne H
  refine ⟨_, Hyp.step H1 (by omega), f1, ?_⟩
  intro r sf hl
  rw [loop0_eq] at hl ⊢
  refine ExS.loop_next (ExS.ite (cond_val k H.l2 (by omega)) (truthy_boolVal _) ?_) (Or.inl rfl)
    (exec_step k hk H1.l2) hl
  simp only [decide_eq_true hk]; exact e1

theorem loop_done {s : State} (h2 : s.locals 2 = some (.int ⟨32, true⟩ 3)) :
    ExS Gen.prog s Gen.tri_ray_setup_loop0 .normal s := by
  rw [loop0_eq]
  exact ExS.loop_brk (ExS.ite (cond_val 3 h2 le_rfl) (truthy_boolVal _) ExS.brk)

theorem EvE.bor' {p : Prog} {s : State} {a b} {x y : Nat} (ha : EvE p s a (.int ⟨32, true⟩ x))
    (hb : EvE p s b (.int ⟨32, true⟩ y)) :
    EvE p s (.bin .bor (some ⟨32, true⟩) a b) (.int ⟨32, true⟩ (x ||| y)) :=
  EvE.bin ha hb (by simp [evalBin, isPtr, evalBinInt, binInt, intOf])

def negBit (x : Ref.F) (v : Nat) : Nat := if ltBits x Ref.zero then v else 0

theorem octant_term {s bRay bRc R ws} (H : Hyp s bRay bRc 3 R ws) (i v : Nat) (hi : i < 3) (x : Ref.F)
    (hw : ws[6 + i]? = some x.toNat) :
    EvE Gen.prog s (.cond (.bin .lt none (.load .f32 (.index (.field (.var 1) 24) (.const (.int ⟨32, true⟩ i)) 4)) (.const (.f32 0))) (.const (.int ⟨32, true⟩ v)) (.const (.int ⟨32, true⟩ 0)))
      (.int ⟨32, true⟩ (negBit x v)) := by
  have hl := length_f32Block ws
  rw [H.wlen] at hl
  have hp : EvE Gen.prog s (.index (.field (.var 1) 24) (.const (.int ⟨32, true⟩ i)) 4) (.ptr bRc (0 + 24 + 4 * i)) :=
    EvE.indexI32 (EvE.fieldN (EvE.var H.l1) H.mrc (by simp; omega)) (EvE.const _) (by omega) H.mrc
      (by simp; omega)
  have hx := EvE.loadAt hp H.mrc (by omega) (by rwa [show (0 + 24 + 4 * i) / 4 = 6 + i by omega])
  refine EvE.cond (EvE.f32lt hx (EvE.constF 0 (by norm_num))) (truthy_boolVal _) ?_
  unfold negBit; rw [show (0 : Nat).toUInt32 = Ref.zero from rfl]
  cases ltBits x Ref.zero <;> exact EvE.const _

theorem callFunc_of_ExS_normal {p : Prog} {f : Nat} {fn : Func} {args : List Val} {m : Mem} {s' : State}
    (hf : p f = some fn) (hlen : fn.params.length = args.length)
    (h : ExS p ⟨frameLocals fn.params args, m, false⟩ fn.body .normal s') :
    ∃ K, ∀ n, K ≤ n → callFunc p n f args m = .ok (none, s'.mem) := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun n hn => by simp only [callFunc, hf, hlen, ite_true, hK n hn]⟩

theorem f32Block_append (a b : List Nat) : f32Block (a ++ b) = f32Block a ++ f32Block b := by
  simp [f32Block]

set_option maxHeartbeats 1000000 in
theorem tri_ray_setup_refines' (org dir : Fin 3 → Ref.F) (tmin tmax : Ref.F) (m : Mem)
    (bRay bRc : Nat) (hne : bRay ≠ bRc)
    (hray : m bRay = some (f32Block (vecWords org ++ [tmin.toNat] ++ vecWords dir ++ [tmax.toNat])))
    (hrc : ∃ blk, m bRc = some blk ∧ blk.length = 56) :
    ∃ m', (∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_ray_setup [.ptr bRay 0, .ptr bRc 0] m =
        .ok (none, m')) ∧
      m' bRc = some (ctxBlock (Ref.raySetup org dir tmin)) ∧ ∀ b, b ≠ bRc → m' b = m b := by
  obtain ⟨blk, hb, hbl⟩ := hrc
  obtain ⟨ws0, hl0, rfl⟩ := block_words 14 blk (by omega)
  set R := rayWords org dir tmin tmax
  set rc := Ref.raySetup org dir tmin
  let s0 : State := ⟨frameLocals Gen.tri_ray_setup.params [.ptr bRay 0, .ptr bRc 0], m, false⟩
  have H0 : Hyp { s0 with locals := s0.locals.upd 2 (.int ⟨32, true⟩ 0) } bRay bRc 0 R ws0 :=
    { l0 := rfl, l1 := rfl, l2 := by simp [Locals.upd]
      mray := by show m bRay = some (f32Block (rayWords org dir tmin tmax) ++ []); rw [List.append_nil]; exact hray
      mrc := by simpa using hb
      rlen := rfl, wlen := hl0, ro := rfl, hk := by norm_num }
  obtain ⟨s1, H1, f1, k1⟩ := loop_iter 0 (by norm_num) hne H0
  obtain ⟨s2, H2, f2, k2⟩ := loop_iter 1 (by norm_num) hne H1
  obtain ⟨s3, H3, f3, k3⟩ := loop_iter 2 (by norm_num) hne H2
  set ws3 := setK org dir tmin (setK org dir tmin (setK org dir tmin ws0 0) 1) 2 with hws3
  have g : ∀ i (hi : i < 3), ws3[6 + i]? = some (rc.invd ⟨i, hi⟩).toNat := by
    intro i hi
    have : ws0.length = 14 := hl0
    interval_cases i <;> simp [hws3, setK, List.getElem?_set, this] <;> rfl
  have hw3 : ws3.length = 14 := by simp [hws3, setK_length, hl0]
  have hoct := EvE.bor' (EvE.bor' (octant_term H3 0 1 (by norm_num) _ (g 0 (by norm_num)))
    (octant_term H3 1 2 (by norm_num) _ (g 1 (by norm_num)))) (octant_term H3 2 4 (by norm_num) _ (g 2 (by norm_num)))
  have st1 := ExS.store (s := s3) (ty := .int ⟨32, true⟩) (EvE.fieldN (EvE.var H3.l1) H3.mrc
      (by simp [length_f32Block, setK_length, hl0])) hoct H3.ro
    (store_rcI s3.mem bRc ws3 (0 + 52) _ H3.mrc (by norm_num) (by simp [hw3]))
  have H4 := H3.afterStore hne ((0 + 52) / 4)
    (negBit (rc.invd ⟨0, by norm_num⟩) 1 ||| negBit (rc.invd ⟨1, by norm_num⟩) 2 ||| negBit (rc.invd ⟨2, by norm_num⟩) 4)
  have hl4 := length_f32Block (ws3.set ((0 + 52) / 4)
    (negBit (rc.invd ⟨0, by norm_num⟩) 1 ||| negBit (rc.invd ⟨1, by norm_num⟩) 2 ||| negBit (rc.invd ⟨2, by norm_num⟩) 4))
  simp only [List.length_set, hw3] at hl4
  have st2 := ExS.store (p := Gen.prog) (EvE.fieldN (off := 48) (EvE.var H4.l1) H4.mrc (by simp [length_f32Block, setK_length, hl0]))
    (EvE.loadAt (w := tmin) (EvE.fieldN (off := 12) (EvE.var H4.l0) H4.mray (by simp [length_f32Block, H4.rlen]))
      H4.mray (by norm_num) rfl) H4.ro
    (store_rcF _ bRc _ (0 + 48) tmin.toNat H4.mrc (by norm_num) (by simp [setK_length, hl0]))
  have body := ExS.seq (ExS.seq (ExS.set (i := 2) (s := s0) (EvE.const (.int ⟨32, true⟩ 0)))
    (k1 _ _ (k2 _ _ (k3 _ _ (loop_done H3.l2))))) (ExS.seq st1 st2)
  refine ⟨_, callFunc_of_ExS_normal rfl rfl body, ?_, ?_⟩
  · simp only [Mem.upd, ite_true, List.append_nil]
    have hoctEq : negBit (rc.invd 0) 1 ||| negBit (rc.invd 1) 2 ||| negBit (rc.invd 2) 4 = rc.octant := by
      show _ = (if ltBits (rc.invd 0) Ref.zero then 1 else 0) |||
        ((if ltBits (rc.invd 1) Ref.zero then 1 else 0) * 2) ||| ((if ltBits (rc.invd 2) Ref.zero then 1 else 0) * 4)
      unfold negBit; split_ifs <;> rfl
    have hc : ctxBlock rc = f32Block (vecWords rc.org ++ vecWords rc.dir ++ vecWords rc.invd ++
        vecWords rc.oinv ++ [rc.tmin.toNat, rc.octant]) := by
      unfold ctxBlock
      rw [show vecWords rc.org ++ vecWords rc.dir ++ vecWords rc.invd ++ vecWords rc.oinv ++
        [rc.tmin.toNat, rc.octant] = (vecWords rc.org ++ vecWords rc.dir ++ vecWords rc.invd ++
        vecWords rc.oinv ++ [rc.tmin.toNat]) ++ [rc.octant] by simp, f32Block_append]
      simp [f32Block]
    rw [hc, ← hoctEq]
    congr 2
    have hl14 : ws0.length = 14 := hl0
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_or_ge i 14 with hi | hi
    · interval_cases i <;> simp [setK, hl14, vecWords] <;> rfl
    · rw [List.getElem?_eq_none (by simp [setK_length, hl14]; omega),
        List.getElem?_eq_none (by simp [vecWords]; omega)]
  · intro b hb
    simp only [Mem.upd, hb, ite_false]
    rw [f3 b hb, f2 b hb, f1 b hb]
end LightRT.C.Proofs
