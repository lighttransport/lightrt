import LightRT.C.Proofs.SlabRefines
import LightRT.C.GenRobust

/-!
Refinement for the **default** build's `tri_slab_scalar` (`LRT_TRI_SLAB_ROBUST`
on, `LRT_TRI_SLAB_INFLATE` on, translated into `GenRobust`): the C function
computes `Ref.slabRobust` (inflated far value).
`tri_ray_ctx` gains `sinv[3]` at byte 56; the theorem takes the stored `sinv`
as a parameter, and `tri_slab_scalar_robust_refines` instantiates it with the
value `tri_ray_setup` stores (`+∞` for `d = ±0`, else `invd`).
-/

namespace LightRT.C.Proofs
open LightRT.C

/-- `tri_ray_ctx` under `LRT_TRI_SLAB_ROBUST` (68 B): legacy fields + `sinv`. -/
def ctxBlockR (rc : Ref.RayCtx) (s : Fin 3 → Ref.F) : Block :=
  f32Block (vecWords rc.org ++ vecWords rc.dir ++ vecWords rc.invd ++ vecWords rc.oinv ++
    [rc.tmin.toNat, rc.octant] ++ vecWords s)

theorem EvE.callMinR {s a b} {x y : UInt32} (ha : EvE GenRobust.prog s a (.f32 x.toNat))
    (hb : EvE GenRobust.prog s b (.f32 y.toNat)) :
    EvE GenRobust.prog s (.call GenRobust.fid_tri_minf [a, b]) (.f32 (Ref.fmin x y).toNat) := by
  refine EvE.call (EvArgs.cons ha (EvArgs.cons hb EvArgs.nil)) rfl rfl (ExS.ret ?_)
  refine EvE.cond (EvE.f32lt (EvE.var rfl) (EvE.var rfl)) (truthy_boolVal _) ?_
  unfold Ref.fmin; cases FP.Binary32.ltBits x y <;> exact EvE.var rfl

theorem EvE.callMaxR {s a b} {x y : UInt32} (ha : EvE GenRobust.prog s a (.f32 x.toNat))
    (hb : EvE GenRobust.prog s b (.f32 y.toNat)) :
    EvE GenRobust.prog s (.call GenRobust.fid_tri_maxf [a, b]) (.f32 (Ref.fmax x y).toNat) := by
  refine EvE.call (EvArgs.cons ha (EvArgs.cons hb EvArgs.nil)) rfl rfl (ExS.ret ?_)
  refine EvE.cond (EvE.f32gt (EvE.var rfl) (EvE.var rfl)) (truthy_boolVal _) ?_
  unfold Ref.fmax; cases FP.Binary32.ltBits y x <;> exact EvE.var rfl

/-- `ev` for `GenRobust` (its own `tri_minf`/`tri_maxf` call lemmas). -/
syntax "evR" : tactic
macro_rules
  | `(tactic| evR) => `(tactic| first
      | (apply EvE.var; rfl)
      | (apply EvE.f32mul <;> evR) | (apply EvE.f32sub <;> evR)
      | (apply EvE.f32le <;> evR)
      | (apply EvE.callMinR <;> evR) | (apply EvE.callMaxR <;> evR)
      | (apply EvE.constF; norm_num)
      | (apply EvE.loadAt
         · evptr
         · assumption
         · (norm_num; done)
         · first | rfl | (simp [vecWords]; rfl)))

macro_rules
  | `(tactic| evside) => `(tactic|
      (simp only [ctxBlockR, List.length_append, length_f32Block, vecWords, List.length_cons,
        List.length_nil, ]; omega))

/-- The slab of `Ref.slabRobust` with the reciprocal read from `s`. -/
def slabS (rc : Ref.RayCtx) (s : Fin 3 → Ref.F) (lo hi : Fin 3 → Ref.F) (tbest : Ref.F) :
    Bool × Ref.F :=
  let t := fun (x : Ref.F) k => LightRT.FP.Binary32.mulBits (LightRT.FP.Binary32.subBits x (rc.org k)) (s k)
  let tn := fun k => Ref.fmin (t (hi k) k) (t (lo k) k)
  let tf := fun k => Ref.fmax (t (lo k) k) (t (hi k) k)
  let tnear := Ref.fmax (Ref.fmax (tn 0) (tn 1)) (Ref.fmax (tn 2) rc.tmin)
  let tfar := LightRT.FP.Binary32.mulBits (Ref.fmin (Ref.fmin (tf 0) (tf 1)) (Ref.fmin (tf 2) tbest))
    Ref.slabK
  (LightRT.FP.Binary32.leBits tnear tfar, tnear)

/-- What `tri_ray_setup` stores in `rc->sinv` under `LRT_TRI_SLAB_ROBUST`. -/
def sinvOf (rc : Ref.RayCtx) : Fin 3 → Ref.F :=
  fun k => if Ref.eqF (rc.dir k) Ref.zero then Ref.posInf else rc.invd k

theorem slabS_sinvOf (rc : Ref.RayCtx) (lo hi : Fin 3 → Ref.F) (tbest : Ref.F) :
    slabS rc (sinvOf rc) lo hi tbest = Ref.slabRobust rc lo hi tbest := rfl

theorem tri_slab_scalar_robust_refines' (rc : Ref.RayCtx) (s : Fin 3 → Ref.F) (lo hi : Fin 3 → Ref.F) (tbest : Ref.F)
    (m : Mem) (bRc : Nat) (bs : Fin 6 → Nat) (bOut : Nat)
    (hrc : m bRc = some (ctxBlockR rc s))
    (hlo : ∀ k : Fin 3, m (bs ⟨k, by omega⟩) = some (f32Block [(lo k).toNat]))
    (hhi : ∀ k : Fin 3, m (bs ⟨k + 3, by omega⟩) = some (f32Block [(hi k).toNat]))
    (hout : ∃ blk, m bOut = some blk ∧ blk.length = 4) :
    ∃ m', (∃ K, ∀ n, K ≤ n → callFunc GenRobust.prog n GenRobust.fid_tri_slab_scalar
        [.ptr (bs 0) 0, .ptr (bs 1) 0, .ptr (bs 2) 0, .ptr (bs 3) 0, .ptr (bs 4) 0, .ptr (bs 5) 0,
         .int ⟨32, true⟩ 0, .ptr bRc 0, .f32 tbest.toNat, .ptr bOut 0] m =
        .ok (some (.int ⟨32, true⟩ (if (slabS rc s lo hi tbest).1 then 1 else 0)), m')) ∧
      m' bOut = some (f32Block [(slabS rc s lo hi tbest).2.toNat]) ∧
      ∀ b, b ≠ bOut → m' b = m b := by
  obtain ⟨blk, hb, hbl⟩ := hout
  have hc : m bRc = some (f32Block (vecWords rc.org ++ vecWords rc.dir ++ vecWords rc.invd ++
      vecWords rc.oinv ++ [rc.tmin.toNat, rc.octant] ++ vecWords s) ++ []) := by
    simpa [ctxBlockR] using hrc
  have l0 : m (bs 0) = some (f32Block [(lo 0).toNat] ++ []) := by simpa using hlo 0
  have l1 : m (bs 1) = some (f32Block [(lo 1).toNat] ++ []) := by simpa using hlo 1
  have l2 : m (bs 2) = some (f32Block [(lo 2).toNat] ++ []) := by simpa using hlo 2
  have h3 : m (bs 3) = some (f32Block [(hi 0).toNat] ++ []) := by simpa using hhi 0
  have h4 : m (bs 4) = some (f32Block [(hi 1).toNat] ++ []) := by simpa using hhi 1
  have h5 : m (bs 5) = some (f32Block [(hi 2).toNat] ++ []) := by simpa using hhi 2
  have body : ∃ v s', ExS GenRobust.prog ⟨frameLocals GenRobust.tri_slab_scalar.params
      [.ptr (bs 0) 0, .ptr (bs 1) 0, .ptr (bs 2) 0, .ptr (bs 3) 0, .ptr (bs 4) 0, .ptr (bs 5) 0,
       .int ⟨32, true⟩ 0, .ptr bRc 0, .f32 tbest.toNat, .ptr bOut 0], m, false⟩
      GenRobust.tri_slab_scalar.body
      (.ret (some v)) s' ∧
      s'.mem = m.upd bOut (encodeLE 4 (slabS rc s lo hi tbest).2.toNat) ∧
      v = .int ⟨32, true⟩ (if (slabS rc s lo hi tbest).1 then 1 else 0) := by
    apply Exists.intro; apply Exists.intro; refine ⟨?h1, ?h2, ?h3⟩
    case h1 =>
      unfold GenRobust.tri_slab_scalar
      dsimp only
      repeat (first | (apply ExS.seq) | (apply ExS.set; evR))
      · apply ExS.store
        · evR
        · evR
        · rfl
        · simp only [store, writeBytes, hb, length_encodeLE, hbl, le_refl, ite_true, zero_add]
          rfl
      · apply ExS.ret; evR
    case h2 =>
      funext b'
      simp only [Mem.upd, List.take_zero, List.nil_append]
      split_ifs <;> simp [List.drop_eq_nil_of_le, hbl] <;> rfl
    case h3 => rfl
  obtain ⟨v, s', h, hm, hv⟩ := body
  refine ⟨s'.mem, ?_, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := callFunc_of_ExS (p := GenRobust.prog) (f := GenRobust.fid_tri_slab_scalar) rfl rfl h
    exact ⟨K, fun n hn => by rw [hK n hn, hv]⟩
  · rw [hm]; simp [Mem.upd, f32Block]
  · intro b hb'; rw [hm]; simp [Mem.upd, hb']
/-- **Default-build slab refinement**: with the context `tri_ray_setup` builds,
    the compiled `tri_slab_scalar` returns exactly `Ref.slabRobust`. -/
theorem tri_slab_scalar_robust_refines (rc : Ref.RayCtx) (lo hi : Fin 3 → Ref.F) (tbest : Ref.F)
    (m : Mem) (bRc : Nat) (bs : Fin 6 → Nat) (bOut : Nat)
    (hrc : m bRc = some (ctxBlockR rc (sinvOf rc)))
    (hlo : ∀ k : Fin 3, m (bs ⟨k, by omega⟩) = some (f32Block [(lo k).toNat]))
    (hhi : ∀ k : Fin 3, m (bs ⟨k + 3, by omega⟩) = some (f32Block [(hi k).toNat]))
    (hout : ∃ blk, m bOut = some blk ∧ blk.length = 4) :
    ∃ m', (∃ K, ∀ n, K ≤ n → callFunc GenRobust.prog n GenRobust.fid_tri_slab_scalar
        [.ptr (bs 0) 0, .ptr (bs 1) 0, .ptr (bs 2) 0, .ptr (bs 3) 0, .ptr (bs 4) 0, .ptr (bs 5) 0,
         .int ⟨32, true⟩ 0, .ptr bRc 0, .f32 tbest.toNat, .ptr bOut 0] m =
        .ok (some (.int ⟨32, true⟩ (if (Ref.slabRobust rc lo hi tbest).1 then 1 else 0)), m')) ∧
      m' bOut = some (f32Block [(Ref.slabRobust rc lo hi tbest).2.toNat]) ∧
      ∀ b, b ≠ bOut → m' b = m b :=
  tri_slab_scalar_robust_refines' rc (sinvOf rc) lo hi tbest m bRc bs bOut hrc hlo hhi hout

end LightRT.C.Proofs
