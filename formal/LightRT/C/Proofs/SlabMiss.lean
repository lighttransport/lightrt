/-
  A kernel-checked false miss of the *actual* `tri_slab_scalar` (as translated
  by c2lean and run under the binary32 MiniC semantics): the ray segment meets
  the box in exact rational arithmetic, yet the C function returns 0.
  Witness found by `tools/cdiff.py --search-miss` (seed 1); the compiled C
  (clang -O0 -ffp-contract=off, x86-64) returns 0 on it as well.
  Checked with `decide +kernel` (no `native_decide`).
-/
import LightRT.C.Gen

namespace LightRT.C.Proofs
open LightRT.C

/-- `lrt_ray` words: org[3] tmin dir[3] tmax; box: lo[3] hi[3]. -/
def missRay : List Nat :=
  [0x4214f160, 0x40ba8c35, 0xc02359b9, 0x00000000, 0x3a0c6eed, 0xbb3a8fe3, 0xc0c945fd, 0x7f800000]
def missBox : List Nat :=
  [0x4215a949, 0x409c01e8, 0xc503fec2, 0x42180434, 0x4133809d, 0xc503f416]

def blk (ws : List Nat) : Block := ws.flatMap (fun w => encodeLE 4 w)

def missMem : Mem := fun b =>
  ([blk missRay, List.replicate 56 0] ++ missBox.map (fun x => blk [x]) ++ [blk [0]])[b]?

/-- Result of `tri_ray_setup` followed by `tri_slab_scalar` (`t_best = +∞`). -/
def missRun : Option Nat :=
  match callFunc Gen.prog 10000 Gen.fid_tri_ray_setup [.ptr 0 0, .ptr 1 0] missMem with
  | .ok (_, m1) =>
    match callFunc Gen.prog 10000 Gen.fid_tri_slab_scalar
      [.ptr 2 0, .ptr 3 0, .ptr 4 0, .ptr 5 0, .ptr 6 0, .ptr 7 0, .int ⟨32, true⟩ 0, .ptr 1 0,
       .f32 0x7f800000, .ptr 8 0] m1 with
    | .ok (some (.int _ r), _) => some r
    | _ => none
  | _ => none

def q (w : Nat) : ℚ := ((FP.Binary32.decode w.toUInt32).toQ?).getD 0

/-- Exact rational ray/box test (all direction components nonzero here). -/
def exactHit (o d lo hi : Fin 3 → ℚ) (tmin : ℚ) : Bool :=
  let ts := fun i : Fin 3 =>
    let a := (lo i - o i) / d i
    let b := (hi i - o i) / d i
    (min a b, max a b)
  let near := max (max (ts 0).1 (ts 1).1) (max (ts 2).1 tmin)
  let far := min (min (ts 0).2 (ts 1).2) (ts 2).2
  decide (near ≤ far)

def missExact : Bool :=
  exactHit (fun i => q (missRay.getD i.val 0)) (fun i => q (missRay.getD (i.val + 4) 0))
    (fun i => q (missBox.getD i.val 0)) (fun i => q (missBox.getD (i.val + 3) 0))
    (q (missRay.getD 3 0))

set_option maxRecDepth 100000

/-- **The C slab test has a false miss** (kernel-checked, no `native_decide`):
    the exact ray segment `[0, ∞)` meets the box, but `tri_slab_scalar` returns 0.
    Lifting this to `Robust.tri_slab_scalar_false_miss_exists` needs the
    refinement `tri_slab_scalar_refines` (milestone M3). -/
theorem tri_slab_scalar_false_miss : missExact = true ∧ missRun = some 0 :=
  ⟨by decide +kernel, by decide +kernel⟩

end LightRT.C.Proofs
