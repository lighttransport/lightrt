/-
  Refinement for `tri_woop_one` (watertight ray/triangle, opt-in
  `LRT_TRI_WATERTIGHT`): the c2lean translation returns exactly `Ref.woop`.
  Split into the integer axis selection (8 cases) and a single symbolic
  execution of the floating-point body for arbitrary axes.
-/
import LightRT.C.Proofs.RaySetupRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

def stTail : Stmt → Stmt
  | .seq _ b => b
  | s => s

/-- Everything after the 11 axis-selection statements. -/
def woopRest : Stmt := stTail^[11] Gen.tri_woop_one.body

theorem vw (v : Fin 3 → Ref.F) (j : Fin 3) : (vecWords v)[(0 + 4 * (j : Nat)) / 4]? = some (v j).toNat := by
  fin_cases j <;> rfl

syntax "evptrW" : tactic
syntax "evsideW" : tactic
macro_rules
  | `(tactic| evptrW) => `(tactic| first
      | (apply EvE.var; rfl)
      | (apply EvE.indexI32 <;> evsideW))
macro_rules
  | `(tactic| evsideW) => `(tactic| first
      | evptrW | exact EvE.const _ | assumption | (norm_num; done)
      | (exact lt_of_lt_of_le (Fin.isLt _) (by norm_num))
      | (simp only [List.length_append, length_f32Block, vecWords, List.length_cons, List.length_nil]; omega))

syntax "evW" : tactic
macro_rules
  | `(tactic| evW) => `(tactic| first
      | (apply EvE.var; rfl)
      | (apply EvE.f32mul <;> evW) | (apply EvE.f32sub <;> evW) | (apply EvE.f32add <;> evW)
      | (apply EvE.f32div <;> evW) | (apply EvE.f32le <;> evW) | (apply EvE.f32lt <;> evW)
      | (apply EvE.f32gt <;> evW) | (apply EvE.f32ge <;> evW) | (apply EvE.f32eq <;> evW)
      | (apply EvE.land' <;> evW) | (apply EvE.lor' <;> evW) | (apply EvE.lnot' <;> evW)
      | (apply EvE.copysign' <;> evW)
      | (apply EvE.constF; norm_num)
      | (exact EvE.const (.int _ _))
      | (apply EvE.loadAt
         · evptrW
         · assumption
         · first | (norm_num; done) | omega
         · first | rfl | exact vw _ _ | (simp [vecWords]; rfl)))

syntax "allS" : tactic
macro_rules
  | `(tactic| allS) => `(tactic| first
      | (apply ExS.set; evW)
      | (apply ExS.seq
         · allS
         · allS))

macro "setW" : tactic => `(tactic| (apply ExS.seq; · allS))

macro "passW" hc:ident : tactic => `(tactic| (
  apply ExS.seq
  · apply ExS.ite
    · evW
    · exact truthy_boolVal _
    exact ExS.if_false $hc:ident ExS.skip))

macro "rejectW" hc:ident : tactic => `(tactic| (
  apply ExS.seq_ret
  apply ExS.ite
  · evW
  · exact truthy_boolVal _
  exact ExS.if_true $hc:ident (ExS.ret (EvE.const _))))

/-- Locals `0..9` are the parameters; everything else is the junk `J`. -/
def Lj (args : List Val) (J : Locals) : Locals := fun i =>
  if i < 10 then frameLocals Gen.tri_woop_one.params args i else J i


/-- Arguments of a `tri_woop_one` call. -/
def wArgs (bo bd b0 b1 b2 bt bu bvv : Nat) (tmin tbest : Ref.F) : List Val :=
  [.ptr bo 0, .ptr bd 0, .ptr b0 0, .ptr b1 0, .ptr b2 0,
   .f32 tmin.toNat, .f32 tbest.toNat, .ptr bt 0, .ptr bu 0, .ptr bvv 0]

def wLoc (args : List Val) (J : Locals) (k : Ref.Axes) : Locals :=
  (((Lj args J).upd 13 (.int ⟨32, true⟩ k.2.2.val)).upd 14 (.int ⟨32, true⟩ k.1.val)).upd 15
    (.int ⟨32, true⟩ k.2.1.val)

macro "wunfold" "at" h:ident : tactic => `(tactic|
  simp only [Ref.woopRej1, Ref.woopRej2, Ref.woopRej3, Ref.woopDet, Ref.woopT, Ref.woopU, Ref.woopV,
    Ref.woopW, Ref.woopEdge, Ref.woopVx, Ref.woopVy, Ref.woopVz, Ref.woopSx, Ref.woopSy, Ref.woopSz,
    Bool.not_eq_true] at $h:ident)

set_option maxHeartbeats 8000000 in
theorem woop_rest (k : Ref.Axes) (o d v0 v1 v2 : Fin 3 → Ref.F) (tmin tbest : Ref.F) (m : Mem)
    (bo bd b0 b1 b2 bt bu bvv : Nat) (J : Locals)
    (ho : m bo = some (f32Block (vecWords o) ++ [])) (hd : m bd = some (f32Block (vecWords d) ++ []))
    (h0 : m b0 = some (f32Block (vecWords v0) ++ [])) (h1 : m b1 = some (f32Block (vecWords v1) ++ []))
    (h2 : m b2 = some (f32Block (vecWords v2) ++ []))
    (ht : ∃ blk, m bt = some blk ∧ blk.length = 4) (hu : ∃ blk, m bu = some blk ∧ blk.length = 4)
    (hvv : ∃ blk, m bvv = some blk ∧ blk.length = 4)
    (hne : bt ≠ bu ∧ bt ≠ bvv ∧ bu ≠ bvv) :
    ∃ s', ExS Gen.prog ⟨wLoc (wArgs bo bd b0 b1 b2 bt bu bvv tmin tbest) J k, m, false⟩ woopRest
      (.ret (some (.int ⟨32, true⟩ (if (Ref.woopK k o d v0 v1 v2 tmin tbest).isSome then 1 else 0)))) s' ∧
      (match Ref.woopK k o d v0 v1 v2 tmin tbest with
       | some (t, u, v) => s'.mem bt = some (f32Block [t.toNat]) ∧ s'.mem bu = some (f32Block [u.toNat]) ∧
                           s'.mem bvv = some (f32Block [v.toNat]) ∧
                           ∀ b, b ≠ bt → b ≠ bu → b ≠ bvv → s'.mem b = m b
       | none => s'.mem = m) := by
  have hk1 := k.1.isLt; have hk2 := k.2.1.isLt; have hk3 := k.2.2.isLt
  obtain ⟨blkT, hT, hTl⟩ := ht
  obtain ⟨blkU, hU, hUl⟩ := hu
  obtain ⟨blkV, hV, hVl⟩ := hvv
  by_cases c1 : Ref.woopRej1 k o d v0 v1 v2 = true
  · have hm : Ref.woopK k o d v0 v1 v2 tmin tbest = none := by simp [Ref.woopK, c1]
    rw [hm]; dsimp only
    apply Exists.intro; refine ⟨?_, ?_⟩
    · unfold woopRest; simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
        id_eq, Gen.tri_woop_one, stTail]
      repeat setW
      rejectW c1
    · rfl
  replace c1 : Ref.woopRej1 k o d v0 v1 v2 = false := by simpa using c1
  by_cases c2 : Ref.woopRej2 k o d v0 v1 v2 = true
  · have hm : Ref.woopK k o d v0 v1 v2 tmin tbest = none := by simp [Ref.woopK, c1, c2]
    rw [hm]; dsimp only
    apply Exists.intro; refine ⟨?_, ?_⟩
    · unfold woopRest; simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
        id_eq, Gen.tri_woop_one, stTail]
      repeat setW
      passW c1; setW; rejectW c2
    · rfl
  replace c2 : Ref.woopRej2 k o d v0 v1 v2 = false := by simpa using c2
  by_cases c3 : Ref.woopRej3 k o d v0 v1 v2 tmin tbest = true
  · have hm : Ref.woopK k o d v0 v1 v2 tmin tbest = none := by simp [Ref.woopK, c1, c2, c3]
    rw [hm]; dsimp only
    apply Exists.intro; refine ⟨?_, ?_⟩
    · unfold woopRest; simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
        id_eq, Gen.tri_woop_one, stTail]
      repeat setW
      passW c1; setW; passW c2; setW; rejectW c3
    · rfl
  replace c3 : Ref.woopRej3 k o d v0 v1 v2 tmin tbest = false := by simpa using c3
  have hm : Ref.woopK k o d v0 v1 v2 tmin tbest =
      some (Ref.woopT k o d v0 v1 v2, divBits (Ref.woopV k o d v0 v1 v2) (Ref.woopDet k o d v0 v1 v2),
        divBits (Ref.woopW k o d v0 v1 v2) (Ref.woopDet k o d v0 v1 v2)) := by
    simp [Ref.woopK, c1, c2, c3]
  rw [hm]; dsimp only
  have key : ∃ s', ExS Gen.prog ⟨wLoc (wArgs bo bd b0 b1 b2 bt bu bvv tmin tbest) J k, m, false⟩ woopRest
      (.ret (some (.int ⟨32, true⟩ 1))) s' ∧
      s'.mem = ((m.upd bt (encodeLE 4 (Ref.woopT k o d v0 v1 v2).toNat)).upd bu
        (encodeLE 4 (divBits (Ref.woopV k o d v0 v1 v2) (Ref.woopDet k o d v0 v1 v2)).toNat)).upd bvv
        (encodeLE 4 (divBits (Ref.woopW k o d v0 v1 v2) (Ref.woopDet k o d v0 v1 v2)).toNat) := by
    apply Exists.intro; refine ⟨?_, ?_⟩
    · unfold woopRest; simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
        id_eq, Gen.tri_woop_one, stTail]
      repeat setW
      passW c1; setW; passW c2; setW; passW c3
      apply ExS.seq
      · apply ExS.store
        · evW
        · evW
        · rfl
        · exact store_word m bt blkT _ hT hTl
      apply ExS.seq
      · apply ExS.store
        · evW
        · evW
        · rfl
        · exact store_word _ bu blkU _ (by simp [Mem.upd, hne.1.symm, hU]) hUl
      apply ExS.seq
      · apply ExS.store
        · evW
        · evW
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

theorem ExS_of_eq {p : Prog} {s s' s2 : State} {st st' : Stmt} {r : Outcome} (hs : s = s')
    (hst : st = st') (h : ExS p s' st' r s2) : ExS p s st r s2 := by subst hs hst; exact h

theorem state_eq {L L' : Locals} {m : Mem} {ro : Bool} (h : L = L') :
    (⟨L, m, ro⟩ : State) = ⟨L', m, ro⟩ := by rw [h]

/-- Select the branch of an `if` whose condition is decided by a hypothesis or by `rfl`. -/
macro "branch" : tactic => `(tactic| first
  | (apply ExS.if_true (by assumption))
  | (apply ExS.if_false (by assumption))
  | (apply ExS.if_true rfl)
  | (apply ExS.if_false rfl))

/-- One statement of the axis-selection prefix. -/
macro "pstep" : tactic => `(tactic| (apply ExS.seq; · first
  | allS
  | (apply ExS.set; exact EvE.bin (EvE.var rfl) (EvE.const _) rfl)
  | (apply ExS.ite
     · first | evW | exact EvE.bin (EvE.var rfl) (EvE.const _) rfl
     · exact truthy_boolVal _
     branch
     first | exact ExS.skip | allS | exact ExS.set (EvE.const _)
     all_goals (try exact Stmt.skip))))

theorem wLoc_self (args : List Val) (L : Locals) (k : Ref.Axes)
    (h13 : L 13 = some (.int ⟨32, true⟩ k.2.2.val)) (h14 : L 14 = some (.int ⟨32, true⟩ k.1.val))
    (h15 : L 15 = some (.int ⟨32, true⟩ k.2.1.val))
    (hp : ∀ i, i < 10 → L i = frameLocals Gen.tri_woop_one.params args i) :
    L = wLoc args L k := by
  funext i
  unfold wLoc Lj
  simp only [Locals.upd]
  split_ifs with a b c e <;> subst_vars <;> first | assumption | exact hp _ ‹_› | rfl | omega

theorem woopAxes_eq (d : Fin 3 → Ref.F) (b1 b2 b3 : Bool)
    (h1 : ltBits (Ref.copysign (d 0) Ref.one) (Ref.copysign (d 1) Ref.one) = b1)
    (h2 : (ltBits (Ref.copysign (d 0) Ref.one) (Ref.copysign (d 2) Ref.one) &&
           ltBits (Ref.copysign (d 1) Ref.one) (Ref.copysign (d 2) Ref.one)) = b2)
    (h3 : ltBits (d (if b2 then 2 else if b1 then 1 else 0)) Ref.zero = b3) :
    Ref.woopAxes d =
      let kz : Fin 3 := if b2 then 2 else if b1 then 1 else 0
      let kx := Ref.fin3succ kz
      let ky := Ref.fin3succ kx
      if b3 then (ky, kx, kz) else (kx, ky, kz) := by
  have hz : Ref.woopKz d = if b2 then 2 else if b1 then 1 else 0 := by
    unfold Ref.woopKz; simp only [h1, h2]
  unfold Ref.woopAxes; simp only [hz, h3]

set_option maxHeartbeats 8000000 in
theorem woop_prefix (d : Fin 3 → Ref.F) (m : Mem) (bo bd b0 b1 b2 bt bu bvv : Nat) (tmin tbest : Ref.F)
    (hd : m bd = some (f32Block (vecWords d) ++ [])) :
    ∃ J, ∀ r s2, ExS Gen.prog ⟨wLoc (wArgs bo bd b0 b1 b2 bt bu bvv tmin tbest) J (Ref.woopAxes d), m, false⟩
        woopRest r s2 →
      ExS Gen.prog ⟨frameLocals Gen.tri_woop_one.params (wArgs bo bd b0 b1 b2 bt bu bvv tmin tbest), m, false⟩
        Gen.tri_woop_one.body r s2 := by
  cases e1 : ltBits (Ref.copysign (d 0) Ref.one) (Ref.copysign (d 1) Ref.one) <;>
  cases e2 : (ltBits (Ref.copysign (d 0) Ref.one) (Ref.copysign (d 2) Ref.one) &&
           ltBits (Ref.copysign (d 1) Ref.one) (Ref.copysign (d 2) Ref.one)) <;>
  cases e3 : ltBits (d (if e2v : (ltBits (Ref.copysign (d 0) Ref.one) (Ref.copysign (d 2) Ref.one) &&
           ltBits (Ref.copysign (d 1) Ref.one) (Ref.copysign (d 2) Ref.one)) = true then 2 else
           if ltBits (Ref.copysign (d 0) Ref.one) (Ref.copysign (d 1) Ref.one) = true then 1 else 0)) Ref.zero <;>
  · simp only [e1, e2, dite_true, dite_false, ite_true, ite_false, Bool.false_eq_true] at e3
    have hax := woopAxes_eq d _ _ _ e1 e2 (by simpa using e3)
    apply Exists.intro; intro r s2 h
    try simp only [Gen.tri_woop_one]
    pstep; pstep; pstep; pstep; pstep; pstep; pstep; pstep; pstep; pstep; pstep
    refine ExS_of_eq (st' := woopRest) ?_ rfl h
    apply state_eq
    apply wLoc_self
    all_goals first
      | (intro i hi; simp only [Locals.upd]; split_ifs <;> first | omega | rfl)
      | (rw [hax]; rfl)

/-- **`tri_woop_one` refines `Ref.woop`** for every input (NaN/∞/subnormal
    included): it returns the reference verdict, writes `t,u,v` only on a hit,
    and touches nothing else. -/
theorem tri_woop_one_refines (o d v0 v1 v2 : Fin 3 → Ref.F) (tmin tbest : Ref.F) (m : Mem)
    (bo bd b0 b1 b2 bt bu bvv : Nat)
    (ho : m bo = some (f32Block (vecWords o))) (hd : m bd = some (f32Block (vecWords d)))
    (h0 : m b0 = some (f32Block (vecWords v0))) (h1 : m b1 = some (f32Block (vecWords v1)))
    (h2 : m b2 = some (f32Block (vecWords v2)))
    (ht : ∃ blk, m bt = some blk ∧ blk.length = 4) (hu : ∃ blk, m bu = some blk ∧ blk.length = 4)
    (hvv : ∃ blk, m bvv = some blk ∧ blk.length = 4)
    (hne : bt ≠ bu ∧ bt ≠ bvv ∧ bu ≠ bvv) :
    ∃ m', (∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_woop_one
        [.ptr bo 0, .ptr bd 0, .ptr b0 0, .ptr b1 0, .ptr b2 0,
         .f32 tmin.toNat, .f32 tbest.toNat, .ptr bt 0, .ptr bu 0, .ptr bvv 0] m =
        .ok (some (.int ⟨32, true⟩ (if (Ref.woop o d v0 v1 v2 tmin tbest).isSome then 1 else 0)), m')) ∧
      (match Ref.woop o d v0 v1 v2 tmin tbest with
       | some (t, u, v) => m' bt = some (f32Block [t.toNat]) ∧ m' bu = some (f32Block [u.toNat]) ∧
                           m' bvv = some (f32Block [v.toNat]) ∧
                           ∀ b, b ≠ bt → b ≠ bu → b ≠ bvv → m' b = m b
       | none => m' = m) := by
  have e : ∀ {b : Nat} {ws : List Nat}, m b = some (f32Block ws) → m b = some (f32Block ws ++ []) :=
    fun h => by simpa using h
  obtain ⟨J, hJ⟩ := woop_prefix d m bo bd b0 b1 b2 bt bu bvv tmin tbest (e hd)
  obtain ⟨s', hx, hp⟩ := woop_rest (Ref.woopAxes d) o d v0 v1 v2 tmin tbest m bo bd b0 b1 b2 bt bu bvv J
    (e ho) (e hd) (e h0) (e h1) (e h2) ht hu hvv hne
  exact ⟨s'.mem, callFunc_of_ExS (p := Gen.prog) rfl rfl (hJ _ _ hx), hp⟩
end LightRT.C.Proofs
