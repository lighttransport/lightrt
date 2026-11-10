/-
  Stage 6: bit-level Lean reference implementations of the LightRT scalar
  kernels, written directly against the binary32 semantics (not via MiniC).
  `C/Proofs/Refines.lean` states that the c2lean translation of the real C
  equals these, and that, on finite in-range inputs, they are instances of the
  abstract algorithms of `Robust.Slab` / `Geom.MTReal` over `Binary32.model`.
  They also serve as the differential-testing oracle in `CDiff.lean`.
-/
import LightRT.FP.Binary32

namespace LightRT.C.Ref
open LightRT.FP.Binary32

abbrev F := UInt32

def one : F := 0x3f800000
def zero : F := 0
def invdMax : F := 0x5d5e0b6b   -- 1e18f  (TRI_INVD_MAX)
def oinvMax : F := 0x7cf0bdc2   -- 1e37f
def detEps : F := 0x2b8cbccc    -- 1e-12f

def neg (a : F) : F := a ^^^ 0x80000000
def copysign (a b : F) : F := (a &&& 0x7fffffff) ||| (b &&& 0x80000000)
def eqF (a b : F) : Bool := leBits a b && leBits b a
/-- `tri_minf(a, b) = a < b ? a : b` (NaN-asymmetric, as in C). -/
def fmin (a b : F) : F := if ltBits a b then a else b
/-- `tri_maxf(a, b) = a > b ? a : b`. -/
def fmax (a b : F) : F := if ltBits b a then a else b

structure RayCtx where
  org : Fin 3 → F
  dir : Fin 3 → F
  invd : Fin 3 → F
  oinv : Fin 3 → F
  tmin : F
  octant : Nat

/-- `tri_ray_setup`. -/
def raySetup (org dir : Fin 3 → F) (tmin : F) : RayCtx :=
  let invd := fun k =>
    let inv := divBits one (dir k)
    if !(leBits (neg invdMax) inv && leBits inv invdMax) then
      copysign invdMax (if eqF (dir k) zero then one else dir k)
    else inv
  let oinv := fun k =>
    let oi := mulBits (org k) (invd k)
    if !(leBits (neg oinvMax) oi && leBits oi oinvMax) then copysign oinvMax oi else oi
  let neg? := fun k => if ltBits (invd k) zero then 1 else 0
  { org, dir, invd, oinv, tmin, octant := neg? 0 ||| (neg? 1 * 2) ||| (neg? 2 * 4) }

/-- `tri_slab_scalar`: `(hit, tnear)`. -/
def slab (rc : RayCtx) (lo hi : Fin 3 → F) (tbest : F) : Bool × F :=
  let t := fun (x : F) k => mulBits (subBits x (rc.org k)) (rc.invd k)
  let tn := fun k => fmin (t (lo k) k) (t (hi k) k)
  let tf := fun k => fmax (t (lo k) k) (t (hi k) k)
  let tnear := fmax (fmax (tn 0) (tn 1)) (fmax (tn 2) rc.tmin)
  let tfar := fmin (fmin (tf 0) (tf 1)) (fmin (tf 2) tbest)
  (leBits tnear tfar, tnear)

/-- Proposed patch: Ize-style inflation, `tfar ← fl(tfar · K)` (Stage 3, `fpSlab … K`). -/
def slabInflated (rc : RayCtx) (lo hi : Fin 3 → F) (tbest K : F) : Bool :=
  let t := fun (x : F) k => mulBits (subBits x (rc.org k)) (rc.invd k)
  let tn := fun k => fmin (t (lo k) k) (t (hi k) k)
  let tf := fun k => fmax (t (lo k) k) (t (hi k) k)
  let tnear := fmax (fmax (tn 0) (tn 1)) (fmax (tn 2) rc.tmin)
  let tfar := mulBits (fmin (fmin (tf 0) (tf 1)) (fmin (tf 2) tbest)) K
  leBits tnear tfar

/-- `tri_mt_one`: `some (t, u, v)` on a hit. -/
def mt (o d v0 v1 v2 : Fin 3 → F) (tmin tbest : F) : Option (F × F × F) :=
  let sub := subBits; let mul := mulBits; let add := addBits
  let e1 := fun k => sub (v1 k) (v0 k)
  let e2 := fun k => sub (v2 k) (v0 k)
  let px := sub (mul (d 1) (e2 2)) (mul (d 2) (e2 1))
  let py := sub (mul (d 2) (e2 0)) (mul (d 0) (e2 2))
  let pz := sub (mul (d 0) (e2 1)) (mul (d 1) (e2 0))
  let det := add (add (mul (e1 0) px) (mul (e1 1) py)) (mul (e1 2) pz)
  if ltBits (neg detEps) det && ltBits det detEps then none else
  let inv := divBits one det
  let tvx := sub (o 0) (v0 0); let tvy := sub (o 1) (v0 1); let tvz := sub (o 2) (v0 2)
  let uu := mul (add (add (mul tvx px) (mul tvy py)) (mul tvz pz)) inv
  if ltBits uu zero || ltBits one uu then none else
  let qx := sub (mul tvy (e1 2)) (mul tvz (e1 1))
  let qy := sub (mul tvz (e1 0)) (mul tvx (e1 2))
  let qz := sub (mul tvx (e1 1)) (mul tvy (e1 0))
  let vv := mul (add (add (mul (d 0) qx) (mul (d 1) qy)) (mul (d 2) qz)) inv
  if ltBits vv zero || ltBits one (add uu vv) then none else
  let tt := mul (add (add (mul (e2 0) qx) (mul (e2 1) qy)) (mul (e2 2) qz)) inv
  if ltBits tt tmin || leBits tbest tt then none else some (tt, uu, vv)

end LightRT.C.Ref
