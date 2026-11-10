/-
  A false miss of the default slab test outside the `|d| ≥ 1e-18` hypothesis of
  `slab_ref_eq_fpSlab` / `slab_no_false_miss`: a ray parallel to a box face and
  lying exactly ON it. `tri_ray_setup` clamps `1/±0` to `±1e18`, so the face
  plane at `org` contributes `(hi - org) * invd = 0 * 1e18 = 0` as the far slab
  bound and the interval collapses to `t ≤ 0`. Found by the BVH validator
  (`CheckBVH`) on C-built heightfield BVHs: vertical rays through the scene's
  boundary edge miss the whole scene although the triangle is hit (brute force).
  By `tri_slab_scalar_refines`, the C function returns the same verdict.
-/
import LightRT.C.Proofs.MTGap

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

def pO : Fin 3 → Ref.F := ![0x3f800000, 0x40000000, 0x3f000000]   -- (1, 2, 0.5)
def pD : Fin 3 → Ref.F := ![0, 0xbf800000, 0]                       -- (+0, -1, +0)
def pLo : Fin 3 → Ref.F := ![0, 0, 0]
def pHi : Fin 3 → Ref.F := ![0x3f800000, 0x3f800000, 0x3f800000]   -- unit box
def pTmax : Ref.F := 0x7149f2ca                                     -- 1e30

/-- The ray point at `t = 3/2` is `(1, 1/2, 1/2)`, inside the closed unit box. -/
theorem slab_parallel_inside :
    ∀ k : Fin 3, wq (pLo k) ≤ wq (pO k) + (3/2) * wq (pD k) ∧
      wq (pO k) + (3/2) * wq (pD k) ≤ wq (pHi k) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- …but the bit-level slab test (= `tri_slab_scalar`) rejects the box. -/
theorem slab_parallel_false_miss :
    (Ref.slab (Ref.raySetup pO pD 0) pLo pHi pTmax).1 = false := by
  decide +kernel

end LightRT.C.Proofs
