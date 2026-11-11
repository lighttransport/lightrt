import LightRT.C.Proofs.Eval

namespace LightRT.C.Proofs
open LightRT.C

def vecWords (v : Fin 3 → Ref.F) : List Nat := [(v 0).toNat, (v 1).toNat, (v 2).toNat]

/-- Bytes of a `tri_ray_ctx` (56 B, layout from the c2lean probe). -/
def ctxBlock (rc : Ref.RayCtx) : Block :=
  f32Block (vecWords rc.org ++ vecWords rc.dir ++ vecWords rc.invd ++ vecWords rc.oinv ++
    [rc.tmin.toNat]) ++ encodeLE 4 rc.octant

syntax "evptr" : tactic
syntax "evside" : tactic
macro_rules
  | `(tactic| evptr) => `(tactic| first
      | (apply EvE.var; rfl)
      | (apply EvE.indexI32 <;> evside)
      | (apply EvE.fieldN <;> evside))
macro_rules
  | `(tactic| evside) => `(tactic| first
      | evptr | exact EvE.const _ | assumption | (norm_num; done)
      | (simp only [ctxBlock, List.length_append, length_f32Block, vecWords, List.length_cons, List.length_nil, length_encodeLE]; omega))

/-- Solve one `EvE` goal of straight-line binary32 code. -/
syntax "ev" : tactic
macro_rules
  | `(tactic| ev) => `(tactic| first
      | (apply EvE.var; rfl)
      | (apply EvE.f32mul <;> ev) | (apply EvE.f32sub <;> ev) | (apply EvE.f32add <;> ev)
      | (apply EvE.f32div <;> ev) | (apply EvE.f32le <;> ev) | (apply EvE.f32lt <;> ev)
      | (apply EvE.f32gt <;> ev) | (apply EvE.f32ge <;> ev)
      | (apply EvE.land' <;> ev) | (apply EvE.lor' <;> ev) | (apply EvE.fneg' <;> ev)
      | (apply EvE.lnot' <;> ev)
      | (apply EvE.constF; norm_num)
      | (apply EvE.callMin <;> ev) | (apply EvE.callMax <;> ev)
      | (apply EvE.loadAt
         · evptr
         · assumption
         · (norm_num; done)
         · first | rfl | (simp [vecWords]; rfl)))

macro "step" : tactic => `(tactic| first
  | (refine ExS.seq (ExS.set ?_) ?_; · ev)
  | (refine ExS.seq (ExS.seq (ExS.set ?_) (ExS.set ?_)) ?_; · ev
     · ev))

theorem tri_slab_scalar_refines' (rc : Ref.RayCtx) (lo hi : Fin 3 → Ref.F) (tbest : Ref.F)
    (m : Mem) (bRc : Nat) (bs : Fin 6 → Nat) (bOut : Nat)
    (hrc : m bRc = some (ctxBlock rc))
    (hlo : ∀ k : Fin 3, m (bs ⟨k, by omega⟩) = some (f32Block [(lo k).toNat]))
    (hhi : ∀ k : Fin 3, m (bs ⟨k + 3, by omega⟩) = some (f32Block [(hi k).toNat]))
    (hout : ∃ blk, m bOut = some blk ∧ blk.length = 4) :
    ∃ m', (∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_slab_scalar
        [.ptr (bs 0) 0, .ptr (bs 1) 0, .ptr (bs 2) 0, .ptr (bs 3) 0, .ptr (bs 4) 0, .ptr (bs 5) 0,
         .int ⟨32, true⟩ 0, .ptr bRc 0, .f32 tbest.toNat, .ptr bOut 0] m =
        .ok (some (.int ⟨32, true⟩ (if (Ref.slab rc lo hi tbest).1 then 1 else 0)), m')) ∧
      m' bOut = some (f32Block [(Ref.slab rc lo hi tbest).2.toNat]) ∧
      ∀ b, b ≠ bOut → m' b = m b := by
  obtain ⟨blk, hb, hbl⟩ := hout
  have hc : m bRc = some (f32Block (vecWords rc.org ++ vecWords rc.dir ++ vecWords rc.invd ++
      vecWords rc.oinv ++ [rc.tmin.toNat]) ++ encodeLE 4 rc.octant) := hrc
  have l0 : m (bs 0) = some (f32Block [(lo 0).toNat] ++ []) := by simpa using hlo 0
  have l1 : m (bs 1) = some (f32Block [(lo 1).toNat] ++ []) := by simpa using hlo 1
  have l2 : m (bs 2) = some (f32Block [(lo 2).toNat] ++ []) := by simpa using hlo 2
  have h3 : m (bs 3) = some (f32Block [(hi 0).toNat] ++ []) := by simpa using hhi 0
  have h4 : m (bs 4) = some (f32Block [(hi 1).toNat] ++ []) := by simpa using hhi 1
  have h5 : m (bs 5) = some (f32Block [(hi 2).toNat] ++ []) := by simpa using hhi 2
  have body : ∃ v s', ExS Gen.prog ⟨frameLocals Gen.tri_slab_scalar.params
      [.ptr (bs 0) 0, .ptr (bs 1) 0, .ptr (bs 2) 0, .ptr (bs 3) 0, .ptr (bs 4) 0, .ptr (bs 5) 0,
       .int ⟨32, true⟩ 0, .ptr bRc 0, .f32 tbest.toNat, .ptr bOut 0], m, false⟩
      Gen.tri_slab_scalar.body
      (.ret (some v)) s' ∧
      s'.mem = m.upd bOut (encodeLE 4 (Ref.slab rc lo hi tbest).2.toNat) ∧
      v = .int ⟨32, true⟩ (if (Ref.slab rc lo hi tbest).1 then 1 else 0) := by
    apply Exists.intro; apply Exists.intro; refine ⟨?h1, ?h2, ?h3⟩
    case h1 =>
      unfold Gen.tri_slab_scalar
      dsimp only
      repeat (first | (apply ExS.seq) | (apply ExS.set; ev))
      · apply ExS.store
        · ev
        · ev
        · rfl
        · simp only [store, writeBytes, hb, length_encodeLE, hbl, le_refl, ite_true, zero_add]
          rfl
      · apply ExS.ret; ev
    case h2 =>
      funext b'
      simp only [Mem.upd, List.take_zero, List.nil_append]
      split_ifs <;> simp [List.drop_eq_nil_of_le, hbl] <;> rfl
    case h3 => rfl
  obtain ⟨v, s', h, hm, hv⟩ := body
  refine ⟨s'.mem, ?_, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_slab_scalar) rfl rfl h
    exact ⟨K, fun n hn => by rw [hK n hn, hv]⟩
  · rw [hm]; simp [Mem.upd, f32Block]
  · intro b hb'; rw [hm]; simp [Mem.upd, hb']
end LightRT.C.Proofs
