/-
  Stage 6: refinement of the real C (c2lean → MiniC) by the Lean reference
  kernels, and of the reference kernels by the abstract real-number algorithms.

      lightrt_c_tri.c ──c2lean──▶ Gen (MiniC) ══refines══▶ Ref (bits) ══▶ Robust/Geom (ℝ)
                                         ▲ cdiff: bit-identical with compiled C
-/
import LightRT.C.Proofs.MTRefines
import LightRT.C.Proofs.RaySetupRefines
import LightRT.C.Proofs.SphereDistRefines
import LightRT.C.Proofs.SmallKernelsRefines
import LightRT.C.Proofs.SlabFP
import LightRT.Robust.Slab
import LightRT.Geom.MTReal

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP

/-- `tri_ray_setup` writes exactly the reference context into `*rc`, for every
    input (including NaN/∞/subnormal), with no UB, and touches nothing else
    (for all sufficiently large fuel; the 56-byte `*rc` may start with any contents).
    Proved in `RaySetupRefines.lean`. -/
theorem tri_ray_setup_refines (org dir : Fin 3 → Ref.F) (tmin tmax : Ref.F) (m : Mem)
    (bRay bRc : Nat) (hne : bRay ≠ bRc)
    (hray : m bRay = some (f32Block (vecWords org ++ [tmin.toNat] ++ vecWords dir ++ [tmax.toNat])))
    (hrc : ∃ blk, m bRc = some blk ∧ blk.length = 56) :
    ∃ m', (∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_ray_setup [.ptr bRay 0, .ptr bRc 0] m =
        .ok (none, m')) ∧
      m' bRc = some (ctxBlock (Ref.raySetup org dir tmin)) ∧ ∀ b, b ≠ bRc → m' b = m b :=
  tri_ray_setup_refines' org dir tmin tmax m bRay bRc hne hray hrc

/-- `tri_slab_scalar` returns the reference verdict and stores the reference `tnear`
    (for all sufficiently large fuel; no aliasing hypotheses are needed because every
    load precedes the single store). Proved in `SlabRefines.lean`. -/
theorem tri_slab_scalar_refines (rc : Ref.RayCtx) (lo hi : Fin 3 → Ref.F) (tbest : Ref.F)
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
      ∀ b, b ≠ bOut → m' b = m b :=
  tri_slab_scalar_refines' rc lo hi tbest m bRc bs bOut hrc hlo hhi hout

/-- `tri_mt_one` returns the reference result and writes `t,u,v` only on a hit
    (all inputs, incl. NaN/∞; loads precede stores, so input/output aliasing is
    irrelevant; the three outputs must be distinct). Proved in `MTRefines.lean`. -/
theorem tri_mt_one_refines (o d v0 v1 v2 : Fin 3 → Ref.F) (tmin tbest : Ref.F) (m : Mem)
    (bo bd b0 b1 b2 bt bu bvv : Nat)
    (ho : m bo = some (f32Block (vecWords o))) (hd : m bd = some (f32Block (vecWords d)))
    (h0 : m b0 = some (f32Block (vecWords v0))) (h1 : m b1 = some (f32Block (vecWords v1)))
    (h2 : m b2 = some (f32Block (vecWords v2)))
    (ht : ∃ blk, m bt = some blk ∧ blk.length = 4) (hu : ∃ blk, m bu = some blk ∧ blk.length = 4)
    (hvv : ∃ blk, m bvv = some blk ∧ blk.length = 4)
    (hne : bt ≠ bu ∧ bt ≠ bvv ∧ bu ≠ bvv) :
    ∃ m', (∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_mt_one
        [.ptr bo 0, .ptr bd 0, .ptr b0 0, .ptr b1 0, .ptr b2 0,
         .f32 tmin.toNat, .f32 tbest.toNat, .ptr bt 0, .ptr bu 0, .ptr bvv 0] m =
        .ok (some (.int ⟨32, true⟩ (if (Ref.mt o d v0 v1 v2 tmin tbest).isSome then 1 else 0)), m')) ∧
      (match Ref.mt o d v0 v1 v2 tmin tbest with
       | some (t, u, v) => m' bt = some (f32Block [t.toNat]) ∧ m' bu = some (f32Block [u.toNat]) ∧
                           m' bvv = some (f32Block [v.toNat]) ∧
                           ∀ b, b ≠ bt → b ≠ bu → b ≠ bvv → m' b = m b
       | none => m' = m) := by
  obtain ⟨s', hx, hp⟩ :=
    tri_mt_one_refines' o d v0 v1 v2 tmin tbest m bo bd b0 b1 b2 bt bu bvv ho hd h0 h1 h2 ht hu hvv hne
  exact ⟨s'.mem, callFunc_of_ExS (p := Gen.prog) rfl rfl hx, hp⟩

/-- Bridge to Stage 3: on finite inputs whose intermediates stay in the normal
    range, the bit-level slab verdict is the abstract `fpSlab` over
    `Binary32.model` with `K = 1` and `invd` unclamped (`|d| ≥ 1e-18`). Proved in `SlabFP.lean`. -/
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
        ⟨fun k => val (lo k), fun k => val (hi k)⟩ 1 :=
  slab_ref_eq_fpSlab' org dir tmin tmax lo hi hfin hdir hrange

end LightRT.C.Proofs
