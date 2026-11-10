/-
  Stage 6: refinement of the real C (c2lean → MiniC) by the Lean reference
  kernels, and of the reference kernels by the abstract real-number algorithms.

      lightrt_c_tri.c ──c2lean──▶ Gen (MiniC) ══refines══▶ Ref (bits) ══▶ Robust/Geom (ℝ)
                                         ▲ cdiff: bit-identical with compiled C
-/
import LightRT.C.Gen
import LightRT.C.Ref
import LightRT.Robust.Slab
import LightRT.Geom.MTReal

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP

def f32Block (ws : List Nat) : Block := ws.flatMap (fun w => encodeLE 4 w)
def vecWords (v : Fin 3 → Ref.F) : List Nat := [(v 0).toNat, (v 1).toNat, (v 2).toNat]

/-- Bytes of a `tri_ray_ctx` (56 B, layout from the c2lean probe). -/
def ctxBlock (rc : Ref.RayCtx) : Block :=
  f32Block (vecWords rc.org ++ vecWords rc.dir ++ vecWords rc.invd ++ vecWords rc.oinv ++
    [rc.tmin.toNat]) ++ encodeLE 4 rc.octant

/-- `tri_ray_setup` writes exactly the reference context into `*rc`, for every
    input (including NaN/∞/subnormal), with no UB, and touches nothing else. -/
theorem tri_ray_setup_refines (org dir : Fin 3 → Ref.F) (tmin tmax : Ref.F) (m : Mem)
    (bRay bRc : Nat) (hne : bRay ≠ bRc)
    (hray : m bRay = some (f32Block (vecWords org ++ [tmin.toNat] ++ vecWords dir ++ [tmax.toNat])))
    (hrc : ∃ blk, m bRc = some blk ∧ blk.length = 56) :
    ∃ m', callFunc Gen.prog 10000 Gen.fid_tri_ray_setup [.ptr bRay 0, .ptr bRc 0] m = .ok (none, m') ∧
      m' bRc = some (ctxBlock (Ref.raySetup org dir tmin)) ∧ ∀ b, b ≠ bRc → m' b = m b := by
  sorry

/-- `tri_slab_scalar` returns the reference verdict and stores the reference `tnear`. -/
theorem tri_slab_scalar_refines (rc : Ref.RayCtx) (lo hi : Fin 3 → Ref.F) (tbest : Ref.F)
    (m : Mem) (bRc : Nat) (bs : Fin 6 → Nat) (bOut : Nat)
    (hrc : m bRc = some (ctxBlock rc))
    (hlo : ∀ k : Fin 3, m (bs ⟨k, by omega⟩) = some (f32Block [(lo k).toNat]))
    (hhi : ∀ k : Fin 3, m (bs ⟨k + 3, by omega⟩) = some (f32Block [(hi k).toNat]))
    (hout : ∃ blk, m bOut = some blk ∧ blk.length = 4)
    (hdis : bOut ≠ bRc ∧ ∀ k, bs k ≠ bOut) :
    ∃ m', callFunc Gen.prog 10000 Gen.fid_tri_slab_scalar
        [.ptr (bs 0) 0, .ptr (bs 1) 0, .ptr (bs 2) 0, .ptr (bs 3) 0, .ptr (bs 4) 0, .ptr (bs 5) 0,
         .int ⟨32, true⟩ 0, .ptr bRc 0, .f32 tbest.toNat, .ptr bOut 0] m =
        .ok (some (.int ⟨32, true⟩ (if (Ref.slab rc lo hi tbest).1 then 1 else 0)), m') ∧
      m' bOut = some (f32Block [(Ref.slab rc lo hi tbest).2.toNat]) ∧
      ∀ b, b ≠ bOut → m' b = m b := by
  sorry

/-- `tri_mt_one` returns the reference result (and writes `t,u,v` only on a hit). -/
theorem tri_mt_one_refines (o d v0 v1 v2 : Fin 3 → Ref.F) (tmin tbest : Ref.F) (m : Mem)
    (bv : Fin 5 → Nat) (bt bu bvv : Nat)
    (hv : ∀ k, m (bv k) = some (f32Block (vecWords ([o, d, v0, v1, v2].getD k.val o))))
    (hout : ∀ b ∈ [bt, bu, bvv], ∃ blk, m b = some blk ∧ blk.length = 4)
    (hdis : [bt, bu, bvv].Nodup ∧ ∀ k, bv k ∉ [bt, bu, bvv]) :
    ∃ m', callFunc Gen.prog 10000 Gen.fid_tri_mt_one
        [.ptr (bv 0) 0, .ptr (bv 1) 0, .ptr (bv 2) 0, .ptr (bv 3) 0, .ptr (bv 4) 0,
         .f32 tmin.toNat, .f32 tbest.toNat, .ptr bt 0, .ptr bu 0, .ptr bvv 0] m =
        .ok (some (.int ⟨32, true⟩ (if (Ref.mt o d v0 v1 v2 tmin tbest).isSome then 1 else 0)), m') ∧
      (match Ref.mt o d v0 v1 v2 tmin tbest with
       | some (t, u, v) => m' bt = some (f32Block [t.toNat]) ∧ m' bu = some (f32Block [u.toNat]) ∧
                           m' bvv = some (f32Block [v.toNat])
       | none => m' = m) := by
  sorry

/-- Value of a finite binary32 word as a real. -/
noncomputable def val (w : Ref.F) : ℝ := (((Binary32.decode w).toQ?).getD 0 : ℝ)

/-- Bridge to Stage 3: on finite inputs whose intermediates stay in the normal
    range, the bit-level slab verdict is the abstract `fpSlab` over
    `Binary32.model` with `K = 1` and `invd` unclamped (`|d| ≥ 1e-18`). -/
theorem slab_ref_eq_fpSlab (org dir : Fin 3 → Ref.F) (tmin tmax : Ref.F) (lo hi : Fin 3 → Ref.F)
    (hfin : ∀ w ∈ [org 0, org 1, org 2, dir 0, dir 1, dir 2, tmin, tmax, lo 0, lo 1, lo 2,
                    hi 0, hi 1, hi 2], ∃ s q, Binary32.decode w = .num s q)
    (hdir : ∀ k, (10 : ℝ) ^ (-18 : ℤ) ≤ |val (dir k)|)
    (hrange : Robust.SlabInRange Binary32.model
      ⟨fun k => val (org k), fun k => val (dir k), val tmin, val tmax⟩
      ⟨fun k => val (lo k), fun k => val (hi k)⟩ 1) :
    (Ref.slab (Ref.raySetup org dir tmin) lo hi tmax).1 = true ↔
      Robust.fpSlab Binary32.model
        ⟨fun k => val (org k), fun k => val (dir k), val tmin, val tmax⟩
        ⟨fun k => val (lo k), fun k => val (hi k)⟩ 1 := by
  sorry

end LightRT.C.Proofs
