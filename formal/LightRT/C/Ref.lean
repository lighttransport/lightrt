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
/-- `lrt_sqrtf` / `sqrtf`: correctly-rounded IEEE binary32 square root. -/
def sqrt (a : F) : F := sqrtBits a
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

def posInf : F := 0x7f800000

/-- `TRI_SLAB_K = 1 + 10u` (binary32 `0x3f800005`), the far-value inflation
    factor of `LRT_TRI_SLAB_INFLATE` (Robust/Slab: `ize_constant_sufficient`). -/
def slabK : F := (1065353221 : Nat).toUInt32

/-- `tri_slab_scalar` in the default build (`-DLRT_TRI_SLAB_ROBUST` +
    `LRT_TRI_SLAB_INFLATE`): slab reciprocal `+∞` for `d = ±0` (`rc->sinv`) and
    the entry bound `min(th, tl)` (operands swapped), so the `0·∞ = NaN` of a
    parallel ray lying on a plane is dropped; the far value is scaled by
    `slabK`, which rules out false misses at box edges and corners. -/
def slabRobust (rc : RayCtx) (lo hi : Fin 3 → F) (tbest : F) : Bool × F :=
  let sinv := fun k => if eqF (rc.dir k) zero then posInf else rc.invd k
  let t := fun (x : F) k => mulBits (subBits x (rc.org k)) (sinv k)
  let tn := fun k => fmin (t (hi k) k) (t (lo k) k)
  let tf := fun k => fmax (t (lo k) k) (t (hi k) k)
  let tnear := fmax (fmax (tn 0) (tn 1)) (fmax (tn 2) rc.tmin)
  let tfar := mulBits (fmin (fmin (tf 0) (tf 1)) (fmin (tf 2) tbest)) slabK
  (leBits tnear tfar, tnear)

/-- Proposed patch: Ize-style inflation, `tfar ← fl(tfar · K)` (Stage 3, `fpSlab … K`). -/
def slabInflated (rc : RayCtx) (lo hi : Fin 3 → F) (tbest K : F) : Bool :=
  let t := fun (x : F) k => mulBits (subBits x (rc.org k)) (rc.invd k)
  let tn := fun k => fmin (t (lo k) k) (t (hi k) k)
  let tf := fun k => fmax (t (lo k) k) (t (hi k) k)
  let tnear := fmax (fmax (tn 0) (tn 1)) (fmax (tn 2) rc.tmin)
  let tfar := mulBits (fmin (fmin (tf 0) (tf 1)) (fmin (tf 2) tbest)) K
  leBits tnear tfar

/-- `tri_sphere_dist_f`: nearest ray/sphere hit distance (scalar fp32 core).
    Returns -1 when the discriminant is negative. -/
def sphereDistF (o d c : Fin 3 → F) (r : F) : F :=
  let ex := subBits (c 0) (o 0)
  let ey := subBits (c 1) (o 1)
  let ez := subBits (c 2) (o 2)
  let proj := addBits (addBits (mulBits ex (d 0)) (mulBits ey (d 1))) (mulBits ez (d 2))
  let l2 := addBits (addBits (mulBits ex ex) (mulBits ey ey)) (mulBits ez ez)
  let perp2 := subBits l2 (mulBits proj proj)
  let disc := subBits (mulBits r r) perp2
  if ltBits disc zero then neg one else subBits proj (sqrt disc)

/-- `tri_sph_quad_core`: the quadratic core of `tri_sph_isect_lane` -- the near
    ray/sphere root `(-b - sqrt(disc))/a`, in the C's fp32 evaluation order. -/
def sphQuadCore (org dir : Fin 3 → F) (cx cy cz r : F) : F :=
  let ocx := subBits (org 0) cx
  let ocy := subBits (org 1) cy
  let ocz := subBits (org 2) cz
  let a := addBits (addBits (mulBits (dir 0) (dir 0)) (mulBits (dir 1) (dir 1))) (mulBits (dir 2) (dir 2))
  let b := addBits (addBits (mulBits ocx (dir 0)) (mulBits ocy (dir 1))) (mulBits ocz (dir 2))
  let c := subBits (addBits (addBits (mulBits ocx ocx) (mulBits ocy ocy)) (mulBits ocz ocz)) (mulBits r r)
  let disc := subBits (mulBits b b) (mulBits a c)
  let sq := sqrt disc
  let inv_a := divBits one a
  mulBits (subBits (neg b) sq) inv_a

/-- `tri_point_oriented_core`: plane-hit parameter of the oriented-disc branch
    of `tri_point_isect_one`, `t = (c0 . n) / (d . n)`. -/
def pointOrientedCore (org dir : Fin 3 → F) (cx cy cz nx ny nz : F) : F :=
  let c0x := subBits cx (org 0)
  let c0y := subBits cy (org 1)
  let c0z := subBits cz (org 2)
  let divisor := addBits (addBits (mulBits (dir 0) nx) (mulBits (dir 1) ny)) (mulBits (dir 2) nz)
  divBits (addBits (addBits (mulBits c0x nx) (mulBits c0y ny)) (mulBits c0z nz)) divisor

/-- `tri_point_raydisc_core`: nearest-point parameter of the ray-facing-disc
    branch of `tri_point_isect_one`, `projC0 = (c0 . d) / |d|^2`. -/
def pointRayDiscCore (org dir : Fin 3 → F) (cx cy cz : F) : F :=
  let dx := dir 0
  let dy := dir 1
  let dz := dir 2
  let dOdO := addBits (addBits (mulBits dx dx) (mulBits dy dy)) (mulBits dz dz)
  let c0x := subBits cx (org 0)
  let c0y := subBits cy (org 1)
  let c0z := subBits cz (org 2)
  let rd2 := divBits one dOdO
  mulBits (addBits (addBits (mulBits c0x dx) (mulBits c0y dy)) (mulBits c0z dz)) rd2

/-! `tri_mt_one`, split into its intermediate values (same evaluation order as the C). -/
def mtE1 (v0 v1 : Fin 3 → F) (k : Fin 3) : F := subBits (v1 k) (v0 k)
def mtE2 (v0 v2 : Fin 3 → F) (k : Fin 3) : F := subBits (v2 k) (v0 k)
def mtPx (d v0 v2 : Fin 3 → F) : F :=
  subBits (mulBits (d 1) (mtE2 v0 v2 2)) (mulBits (d 2) (mtE2 v0 v2 1))
def mtPy (d v0 v2 : Fin 3 → F) : F :=
  subBits (mulBits (d 2) (mtE2 v0 v2 0)) (mulBits (d 0) (mtE2 v0 v2 2))
def mtPz (d v0 v2 : Fin 3 → F) : F :=
  subBits (mulBits (d 0) (mtE2 v0 v2 1)) (mulBits (d 1) (mtE2 v0 v2 0))
def mtDet (d v0 v1 v2 : Fin 3 → F) : F :=
  addBits (addBits (mulBits (mtE1 v0 v1 0) (mtPx d v0 v2)) (mulBits (mtE1 v0 v1 1) (mtPy d v0 v2)))
    (mulBits (mtE1 v0 v1 2) (mtPz d v0 v2))
def mtInv (d v0 v1 v2 : Fin 3 → F) : F := divBits one (mtDet d v0 v1 v2)
def mtTv (o v0 : Fin 3 → F) (k : Fin 3) : F := subBits (o k) (v0 k)
def mtU (o d v0 v1 v2 : Fin 3 → F) : F :=
  mulBits (addBits (addBits (mulBits (mtTv o v0 0) (mtPx d v0 v2)) (mulBits (mtTv o v0 1) (mtPy d v0 v2)))
    (mulBits (mtTv o v0 2) (mtPz d v0 v2))) (mtInv d v0 v1 v2)
def mtQx (o v0 v1 : Fin 3 → F) : F :=
  subBits (mulBits (mtTv o v0 1) (mtE1 v0 v1 2)) (mulBits (mtTv o v0 2) (mtE1 v0 v1 1))
def mtQy (o v0 v1 : Fin 3 → F) : F :=
  subBits (mulBits (mtTv o v0 2) (mtE1 v0 v1 0)) (mulBits (mtTv o v0 0) (mtE1 v0 v1 2))
def mtQz (o v0 v1 : Fin 3 → F) : F :=
  subBits (mulBits (mtTv o v0 0) (mtE1 v0 v1 1)) (mulBits (mtTv o v0 1) (mtE1 v0 v1 0))
def mtV (o d v0 v1 v2 : Fin 3 → F) : F :=
  mulBits (addBits (addBits (mulBits (d 0) (mtQx o v0 v1)) (mulBits (d 1) (mtQy o v0 v1)))
    (mulBits (d 2) (mtQz o v0 v1))) (mtInv d v0 v1 v2)
def mtT (o d v0 v1 v2 : Fin 3 → F) : F :=
  mulBits (addBits (addBits (mulBits (mtE2 v0 v2 0) (mtQx o v0 v1)) (mulBits (mtE2 v0 v2 1) (mtQy o v0 v1)))
    (mulBits (mtE2 v0 v2 2) (mtQz o v0 v1))) (mtInv d v0 v1 v2)

/-- The four rejection tests of `tri_mt_one`, in order. -/
/- The rejection tests are NaN-safe: `!(det <= -eps || det >= eps)`,
   `!(u >= 0 && u <= 1)`, `!(v >= 0 && u + v <= 1)`, `!(t >= tmin && t < tbest)`.
   For numbers they equal the plain `<` / `>` forms; a NaN anywhere rejects. -/
def mtRej1 (d v0 v1 v2 : Fin 3 → F) : Bool :=
  !(leBits (mtDet d v0 v1 v2) (neg detEps) || leBits detEps (mtDet d v0 v1 v2))
def mtRej2 (o d v0 v1 v2 : Fin 3 → F) : Bool :=
  !(leBits zero (mtU o d v0 v1 v2) && leBits (mtU o d v0 v1 v2) one)
def mtRej3 (o d v0 v1 v2 : Fin 3 → F) : Bool :=
  !(leBits zero (mtV o d v0 v1 v2) && leBits (addBits (mtU o d v0 v1 v2) (mtV o d v0 v1 v2)) one)
def mtRej4 (o d v0 v1 v2 : Fin 3 → F) (tmin tbest : F) : Bool :=
  !(leBits tmin (mtT o d v0 v1 v2) && ltBits (mtT o d v0 v1 v2) tbest)

/-- `tri_mt_one`: `some (t, u, v)` on a hit. -/
def mt (o d v0 v1 v2 : Fin 3 → F) (tmin tbest : F) : Option (F × F × F) :=
  if mtRej1 d v0 v1 v2 then none else
  if mtRej2 o d v0 v1 v2 then none else
  if mtRej3 o d v0 v1 v2 then none else
  if mtRej4 o d v0 v1 v2 tmin tbest then none else
  some (mtT o d v0 v1 v2, mtU o d v0 v1 v2, mtV o d v0 v1 v2)

/-! `tri_woop_one` (watertight, Woop–Benthin–Wald), split as in the C. -/

def fin3succ (k : Fin 3) : Fin 3 := if k = 2 then 0 else k + 1

/-- Dominant axis `kz` of `|d|` (first maximum, with NaN never winning a `>`). -/
def woopKz (d : Fin 3 → F) : Fin 3 :=
  let a := fun k => copysign (d k) one
  let k1 : Fin 3 := if ltBits (a 0) (a 1) then 1 else 0
  if ltBits (a 0) (a 2) && ltBits (a 1) (a 2) then 2 else k1

/-- `(kx, ky, kz)`, with `kx, ky` swapped when `d[kz] < 0` to keep the winding. -/
def woopAxes (d : Fin 3 → F) : Fin 3 × Fin 3 × Fin 3 :=
  let kz := woopKz d
  let kx := fin3succ kz
  let ky := fin3succ kx
  if ltBits (d kz) zero then (ky, kx, kz) else (kx, ky, kz)

abbrev Axes := Fin 3 × Fin 3 × Fin 3

def woopSx (k : Axes) (d : Fin 3 → F) : F := divBits (d k.1) (d k.2.2)
def woopSy (k : Axes) (d : Fin 3 → F) : F := divBits (d k.2.1) (d k.2.2)
def woopSz (k : Axes) (d : Fin 3 → F) : F := divBits one (d k.2.2)

/-- Sheared 2D image `(x, y)` and the translated `z` of a vertex, for axes `k`. -/
def woopVx (k : Axes) (o d v : Fin 3 → F) : F :=
  subBits (subBits (v k.1) (o k.1)) (mulBits (woopSx k d) (subBits (v k.2.2) (o k.2.2)))
def woopVy (k : Axes) (o d v : Fin 3 → F) : F :=
  subBits (subBits (v k.2.1) (o k.2.1)) (mulBits (woopSy k d) (subBits (v k.2.2) (o k.2.2)))
def woopVz (k : Axes) (o v : Fin 3 → F) : F := subBits (v k.2.2) (o k.2.2)

/-- 2D edge function `p.x q.y - p.y q.x`. -/
def woopEdge (px py qx qy : F) : F := subBits (mulBits px qy) (mulBits py qx)

def woopU (k : Axes) (o d v0 v1 v2 : Fin 3 → F) : F :=
  woopEdge (woopVx k o d v2) (woopVy k o d v2) (woopVx k o d v1) (woopVy k o d v1)
def woopV (k : Axes) (o d v0 v1 v2 : Fin 3 → F) : F :=
  woopEdge (woopVx k o d v0) (woopVy k o d v0) (woopVx k o d v2) (woopVy k o d v2)
def woopW (k : Axes) (o d v0 v1 v2 : Fin 3 → F) : F :=
  woopEdge (woopVx k o d v1) (woopVy k o d v1) (woopVx k o d v0) (woopVy k o d v0)

def woopRej1 (k : Axes) (o d v0 v1 v2 : Fin 3 → F) : Bool :=
  (ltBits (woopU k o d v0 v1 v2) zero || ltBits (woopV k o d v0 v1 v2) zero ||
      ltBits (woopW k o d v0 v1 v2) zero) &&
    (ltBits zero (woopU k o d v0 v1 v2) || ltBits zero (woopV k o d v0 v1 v2) ||
      ltBits zero (woopW k o d v0 v1 v2))
def woopDet (k : Axes) (o d v0 v1 v2 : Fin 3 → F) : F :=
  addBits (addBits (woopU k o d v0 v1 v2) (woopV k o d v0 v1 v2)) (woopW k o d v0 v1 v2)
def woopRej2 (k : Axes) (o d v0 v1 v2 : Fin 3 → F) : Bool := eqF (woopDet k o d v0 v1 v2) zero
def woopT (k : Axes) (o d v0 v1 v2 : Fin 3 → F) : F :=
  divBits (addBits (addBits (mulBits (woopU k o d v0 v1 v2) (mulBits (woopSz k d) (woopVz k o v0)))
      (mulBits (woopV k o d v0 v1 v2) (mulBits (woopSz k d) (woopVz k o v1))))
      (mulBits (woopW k o d v0 v1 v2) (mulBits (woopSz k d) (woopVz k o v2)))) (woopDet k o d v0 v1 v2)
def woopRej3 (k : Axes) (o d v0 v1 v2 : Fin 3 → F) (tmin tbest : F) : Bool :=
  !(leBits tmin (woopT k o d v0 v1 v2) && ltBits (woopT k o d v0 v1 v2) tbest)

/-- The body of `tri_woop_one` after the axis selection, for axes `k`. -/
def woopK (k : Axes) (o d v0 v1 v2 : Fin 3 → F) (tmin tbest : F) : Option (F × F × F) :=
  if woopRej1 k o d v0 v1 v2 then none else
  if woopRej2 k o d v0 v1 v2 then none else
  if woopRej3 k o d v0 v1 v2 tmin tbest then none else
  some (woopT k o d v0 v1 v2, divBits (woopV k o d v0 v1 v2) (woopDet k o d v0 v1 v2),
    divBits (woopW k o d v0 v1 v2) (woopDet k o d v0 v1 v2))

/-- `tri_woop_one`: `some (t, u, v)` on a hit (`u`, `v` weight `v1`, `v2` as in `tri_mt_one`). -/
def woop (o d v0 v1 v2 : Fin 3 → F) (tmin tbest : F) : Option (F × F × F) :=
  woopK (woopAxes d) o d v0 v1 v2 tmin tbest

end LightRT.C.Ref
