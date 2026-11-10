/-
  Stage 2/6: a concrete, *executable* IEEE-754 binary32 semantics
  (round-to-nearest-even, subnormals, ±0, ±∞, NaN), used by the MiniC
  interpreter so that `tools/cdiff.py` can compare it bit-for-bit with
  compiled C (`-ffp-contract=off`). `rne` is defined once, generically over an
  ordered field, so the computable `ℚ` instance and the real model `rneR`
  are the same definition; `model` packages `rneR` as a `RoundingModel`.
-/
import LightRT.FP.Model

namespace LightRT.FP.Binary32

def prec : ℕ := 24
def emin : ℤ := -126
def emax : ℤ := 127

section Generic
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- Round `m ≥ 0` to the nearest integer, ties to even. -/
def roundEven (m : K) : ℤ :=
  let f := ⌊m⌋
  let r := m - f
  if r < 1 / 2 then f else if 1 / 2 < r then f + 1 else if f % 2 = 0 then f else f + 1

/-- Quantum exponent of `|x|` (clamped at the subnormal threshold). -/
def qexp (x : K) : ℤ := max (Int.log 2 |x|) emin - (prec - 1 : ℕ)

/-- binary32 RNE without overflow (unbounded exponent range above). -/
def rne (x : K) : K :=
  if x = 0 then 0 else
    let q : K := (2 : K) ^ qexp x
    (if x < 0 then -1 else 1) * (roundEven (|x| / q) : K) * q

end Generic

/-- Largest finite binary32 value `(2 - 2⁻²³) · 2¹²⁷`. -/
def maxFinite : ℚ := (2 - (2 : ℚ) ^ (-23 : ℤ)) * (2 : ℚ) ^ (127 : ℤ)

/-! ### Values and bit patterns -/

/-- A binary32 datum: finite (`neg` is the sign, needed for `-0`), ±∞, NaN. -/
inductive V where
  | num (neg : Bool) (mag : ℚ)
  | inf (neg : Bool)
  | nan
  deriving Repr, DecidableEq, Inhabited

def V.toQ? : V → Option ℚ
  | .num n m => some (if n then -m else m)
  | _ => none

/-- Round an exact rational result; `zneg` is the sign to use if it is zero. -/
def roundQ (x : ℚ) (zneg : Bool) : V :=
  if x = 0 then .num zneg 0 else
    let r := rne x
    if |r| > maxFinite then .inf (x < 0) else .num (x < 0) |r|

def decode (b : UInt32) : V :=
  let s := (b >>> 31) == 1
  let e := ((b >>> 23) &&& 0xff).toNat
  let m := (b &&& 0x7fffff).toNat
  if e = 255 then (if m = 0 then .inf s else .nan)
  else if e = 0 then .num s ((m : ℚ) * (2 : ℚ) ^ (-149 : ℤ))
  else .num s (((2 ^ 23 + m : ℕ) : ℚ) * (2 : ℚ) ^ ((e : ℤ) - 150))

/-- Encode a representable value (no rounding performed). x86 default NaN. -/
def encode : V → UInt32
  | .nan => 0xffc00000
  | .inf n => if n then 0xff800000 else 0x7f800000
  | .num n m =>
    let sb : UInt32 := if n then 0x80000000 else 0
    if m = 0 then sb
    else if m < (2 : ℚ) ^ (-126 : ℤ) then
      sb ||| (m * (2 : ℚ) ^ (149 : ℤ)).floor.toNat.toUInt32
    else
      let e := Int.log 2 m
      let mant := (m * (2 : ℚ) ^ (23 - e) - 2 ^ 23).floor.toNat
      sb ||| ((e + 127).toNat.toUInt32 <<< 23) ||| mant.toUInt32

/-! ### IEEE operations on values -/

def V.negate : V → V
  | .num n m => .num (!n) m
  | .inf n => .inf (!n)
  | .nan => .nan

def V.add : V → V → V
  | .nan, _ | _, .nan => .nan
  | .inf a, .inf b => if a = b then .inf a else .nan
  | .inf a, _ => .inf a
  | _, .inf b => .inf b
  | x@(.num a _), y@(.num b _) =>
    roundQ ((x.toQ?.getD 0) + (y.toQ?.getD 0)) (a && b)

def V.sub (x y : V) : V := x.add y.negate

def V.mul : V → V → V
  | .nan, _ | _, .nan => .nan
  | .inf a, .num b m | .num b m, .inf a => if m = 0 then .nan else .inf (a != b)
  | .inf a, .inf b => .inf (a != b)
  | .num a x, .num b y => roundQ ((if a != b then -1 else 1) * (x * y)) (a != b)

def V.div : V → V → V
  | .nan, _ | _, .nan => .nan
  | .inf _, .inf _ => .nan
  | .inf a, .num b _ => .inf (a != b)
  | .num a _, .inf b => .num (a != b) 0
  | .num a x, .num b y =>
    if y = 0 then (if x = 0 then .nan else .inf (a != b))
    else roundQ ((if a != b then -1 else 1) * (x / y)) (a != b)

/-- Ordered comparison; every comparison with NaN is false. -/
def V.cmp (lt : Bool) : V → V → Bool
  | .nan, _ | _, .nan => false
  | x, y =>
    let key : V → ℚ × Int := fun
      | .inf n => (0, if n then -1 else 1)
      | v => (v.toQ?.getD 0, 0)
    let (qx, ix) := key x
    let (qy, iy) := key y
    if ix ≠ iy then (if lt then ix < iy else ix ≤ iy)
    else if ix ≠ 0 then !lt
    else if lt then qx < qy else qx ≤ qy

def isNaNBits (a : UInt32) : Bool := (a &&& 0x7f800000) == 0x7f800000 && (a &&& 0x7fffff) != 0

/-- NaN propagation as on x86 SSE/AVX (and the C semantics we compare against):
    if an operand is NaN, the result is the first NaN operand, quieted; an
    invalid operation on non-NaN operands yields the default NaN `0xffc00000`.
    IEEE 754 §6.2.3 leaves the payload/sign implementation-specific, and the
    sign is observable in LightRT through `copysignf(…, org * invd)`. -/
def propagate (a b : UInt32) (r : Unit → UInt32) : UInt32 :=
  if isNaNBits a then a ||| 0x400000 else if isNaNBits b then b ||| 0x400000 else r ()

def addBits (a b : UInt32) : UInt32 := propagate a b fun _ => encode ((decode a).add (decode b))
def subBits (a b : UInt32) : UInt32 := propagate a b fun _ => encode ((decode a).sub (decode b))
def mulBits (a b : UInt32) : UInt32 := propagate a b fun _ => encode ((decode a).mul (decode b))
def divBits (a b : UInt32) : UInt32 := propagate a b fun _ => encode ((decode a).div (decode b))
def ltBits (a b : UInt32) : Bool := (decode a).cmp true (decode b)
def leBits (a b : UInt32) : Bool := (decode a).cmp false (decode b)

/-! ### Sanity tests (kernel-checked by `decide`-free `rfl` on small values is too
slow; they run at build time via `#guard`). -/
#guard addBits 0x3f800000 0x3f800000 == 0x40000000          -- 1 + 1 = 2
#guard divBits 0x3f800000 0x40400000 == 0x3eaaaaab          -- 1/3
#guard mulBits 0x7f7fffff 0x40000000 == 0x7f800000          -- overflow → +∞
#guard divBits 0x3f800000 0x00000000 == 0x7f800000          -- 1/+0 = +∞
#guard divBits 0x3f800000 0x80000000 == 0xff800000          -- 1/-0 = -∞
#guard subBits 0x3f800000 0x3f800000 == 0x00000000          -- 1 - 1 = +0
#guard mulBits 0x00000001 0x3f000000 == 0x00000000          -- tie to even at subnormal
#guard addBits 0x4b800000 0x3f800000 == 0x4b800000          -- 2^24 + 1 → 2^24 (tie, even)
#guard ltBits 0x7fc00000 0x3f800000 == false                -- NaN < 1 is false
#guard mulBits 0x7fc00000 0x3f800000 == 0x7fc00000          -- NaN payload/sign propagates
#guard subBits 0x7f800000 0x7f800000 == 0xffc00000          -- ∞ - ∞ = default NaN

/-! ### The abstract model instance -/

noncomputable def rneR : ℝ → ℝ := rne

/-- Range where the standard model holds: zero or normal, no overflow. -/
def InRange (x : ℝ) : Prop :=
  x = 0 ∨ ((2 : ℝ) ^ (-126 : ℤ) ≤ |x| ∧ |x| ≤ (maxFinite : ℝ))

theorem rneR_rel (x : ℝ) (hx : InRange x) :
    ∃ δ, |δ| ≤ (2 : ℝ) ^ (-24 : ℤ) ∧ rneR x = x * (1 + δ) := by
  sorry

theorem rneR_mono : Monotone rneR := by
  sorry

theorem rneR_neg (x : ℝ) : rneR (-x) = -rneR x := by
  sorry

theorem rneR_idem (x : ℝ) : rneR (rneR x) = rneR x := by
  sorry

theorem rneR_zero : rneR 0 = 0 := by
  simp [rneR, rne]

/-- Bridge: the executable rational rounding agrees with the real model. -/
theorem rne_cast (q : ℚ) : rneR (q : ℝ) = ((rne q : ℚ) : ℝ) := by
  sorry

/-- Bridge: on non-overflowing finite results, `V.mul` is `rneR` of the exact product. -/
theorem mul_num_refines (a b : Bool) (x y : ℚ) (r : ℚ)
    (h : (V.num a x).mul (V.num b y) = .num (a != b) r ∨
         (V.num a x).mul (V.num b y) = .num (!(a != b)) r) :
    (((V.num a x).mul (V.num b y)).toQ?.getD 0 : ℝ) =
      rneR (((V.num a x).toQ?.getD 0 : ℝ) * ((V.num b y).toQ?.getD 0 : ℝ)) := by
  sorry

noncomputable def model : RoundingModel where
  fl := rneR
  u := (2 : ℝ) ^ (-24 : ℤ)
  InRange := InRange
  u_pos := by positivity
  u_lt_one := by
    rw [zpow_neg]; exact inv_lt_one_of_one_lt₀ (one_lt_zpow₀ (by norm_num) (by norm_num))
  rel := rneR_rel
  mono := rneR_mono
  neg := rneR_neg
  fl_zero := rneR_zero
  fl_idem := rneR_idem

end LightRT.FP.Binary32
