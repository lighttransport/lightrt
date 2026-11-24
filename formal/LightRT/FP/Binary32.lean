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

section GenericLemmas
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem roundEven_cases (m : K) :
    roundEven m = ⌊m⌋ ∨ roundEven m = ⌊m⌋ + 1 := by
  unfold roundEven; dsimp only; split_ifs <;> simp

theorem roundEven_err (m : K) : |(roundEven m : K) - m| ≤ 1 / 2 := by
  have h0 := Int.floor_le m
  have h1 := Int.lt_floor_add_one m
  unfold roundEven; dsimp only
  split_ifs with a b c <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

theorem roundEven_intCast (n : ℤ) : roundEven (n : K) = n := by
  unfold roundEven; simp

theorem roundEven_mono {m m' : K} (h : m ≤ m') : roundEven m ≤ roundEven m' := by
  have hf : ⌊m⌋ ≤ ⌊m'⌋ := Int.floor_mono h
  rcases hf.lt_or_eq with hlt | heq
  · rcases roundEven_cases m with e | e <;> rcases roundEven_cases m' with e' | e' <;> omega
  · have r := sub_le_sub_right h (⌊m⌋ : K)
    unfold roundEven
    simp only [heq] at r ⊢
    split_ifs <;> first | omega | (exfalso; linarith)
end GenericLemmas

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

/-- Correctly rounded binary32 square root (IEEE-754 RNE), bit-level. -/
def sqrtBits (a : UInt32) : UInt32 :=
  if isNaNBits a then a ||| 0x400000
  else
    let s := (a >>> 31) == 1
    let e := ((a >>> 23) &&& 0xff).toNat
    let frac := (a &&& 0x7fffff).toNat
    if e = 255 then
      if s then 0xffc00000 else 0x7f800000
    else
      let M : Nat := if e = 0 then frac else 2^23 + frac
      let E : Int := if e = 0 then -149 else (e : Int) - 150
      if M = 0 then (if s then 0x80000000 else 0)
      else if s then 0xffc00000
      else
        let L : Int := (Nat.log 2 M : Int) + E
        let j : Int := (if L % 2 = 0 then L else L - 1) / 2
        let k : Nat := (E + 46 - 2 * j).toNat
        let T : Nat := M * 2 ^ k
        let r : Nat := Nat.sqrt T
        let m0 : Nat := if T ≥ r*r + r + 1 then r+1 else r
        let m : Nat := if m0 = 2^24 then 2^23 else m0
        let j' : Int := if m0 = 2^24 then j + 1 else j
        let ex : Nat := (j' + 127).toNat
        (UInt32.shiftLeft ex.toUInt32 23) ||| (m - 2^23).toUInt32

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
#guard sqrtBits 0x3f800000 == 0x3f800000                    -- sqrt(1) = 1
#guard sqrtBits 0x40000000 == 0x3fb504f3                    -- sqrt(2) nearest-even
#guard sqrtBits 0x40490fdb == 0x3fe2dfc5                    -- sqrt(pi)
#guard sqrtBits 0x00000001 == 0x1a3504f3                    -- sqrt(min subnormal)
#guard sqrtBits 0x007fffff == 0x1fffffff                    -- sqrt(max subnormal)
#guard sqrtBits 0x00800000 == 0x20000000                    -- sqrt(min normal)
#guard sqrtBits 0x7f7fffff == 0x5f7fffff                    -- sqrt(max finite)
#guard sqrtBits 0x3f000000 == 0x3f3504f3                    -- sqrt(0.5)
#guard sqrtBits 0x00000000 == 0x00000000                    -- sqrt(+0) = +0
#guard sqrtBits 0x80000000 == 0x80000000                    -- sqrt(-0) = -0
#guard sqrtBits 0x7f800000 == 0x7f800000                    -- sqrt(+∞) = +∞
#guard sqrtBits 0xff800000 == 0xffc00000                    -- sqrt(-∞) = default NaN
#guard sqrtBits 0xbf800000 == 0xffc00000                    -- sqrt(-1) = default NaN
#guard sqrtBits 0x7fc00000 == 0x7fc00000                    -- QNaN passes through
#guard sqrtBits 0x7f800001 == 0x7fc00001                    -- SNaN quieted

/-! ### The abstract model instance -/

noncomputable def rneR : ℝ → ℝ := rne

/-- Range where the standard model holds: zero or normal, no overflow. -/
def InRange (x : ℝ) : Prop :=
  x = 0 ∨ ((2 : ℝ) ^ (-126 : ℤ) ≤ |x| ∧ |x| ≤ (maxFinite : ℝ))

/-! ### Proofs of the rounding lemmas -/
theorem two_zpow_log_le {x : ℝ} (hx : 0 < x) : (2 : ℝ) ^ Int.log 2 x ≤ x := by
  simpa using Int.zpow_log_le_self (b := 2) (by norm_num) hx
theorem lt_two_zpow_log (x : ℝ) : x < (2 : ℝ) ^ (Int.log 2 x + 1) := by
  simpa using Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
theorem qexp_eq (x : ℝ) : qexp x = max (Int.log 2 |x|) (-126) - 23 := by
  simp [qexp, prec, emin]



theorem roundEven_nonneg {m : ℝ} (h : 0 ≤ m) : 0 ≤ roundEven m := by
  have := roundEven_mono h; rwa [show (0:ℝ) = ((0:ℤ):ℝ) by simp, roundEven_intCast] at this

theorem roundEven_le_of_le {m : ℝ} {n : ℤ} (h : m ≤ n) : roundEven m ≤ n := by
  simpa [roundEven_intCast] using roundEven_mono h
theorem le_roundEven_of_le {m : ℝ} {n : ℤ} (h : (n : ℝ) ≤ m) : n ≤ roundEven m := by
  simpa [roundEven_intCast] using roundEven_mono h

theorem rne_pos {x : ℝ} (hx : 0 < x) :
    rne x = (roundEven (x / (2:ℝ) ^ qexp x) : ℝ) * (2:ℝ) ^ qexp x := by
  simp [rne, hx.ne', not_lt.2 hx.le, abs_of_pos hx]

theorem rne_neg' (x : ℝ) : rne (-x) = -rne x := by
  by_cases h0 : x = 0
  · simp [rne, h0]
  have hq : qexp (-x) = qexp x := by simp [qexp]
  simp only [rne, neg_eq_zero, h0, ite_false, abs_neg, hq]
  rcases lt_or_gt_of_ne h0 with h | h
  · simp [h, not_lt.2 h.le]
  · simp [h, not_lt.2 h.le]

theorem rne_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ rne x := by
  rcases hx.lt_or_eq with h | h
  · rw [rne_pos h]
    exact mul_nonneg (by exact_mod_cast roundEven_nonneg (div_nonneg h.le (by positivity))) (by positivity)
  · simp [rne, ← h]

private theorem z2 : (2:ℝ) ≠ 0 := by norm_num

/-- `k ≤ 2²⁴` always. -/
theorem rne_pos_le {x : ℝ} (hx : 0 < x) :
    rne x ≤ (2:ℝ) ^ (max (Int.log 2 x) (-126) + 1) := by
  rw [rne_pos hx]
  set q := (2:ℝ) ^ qexp x
  have hq : qexp x = max (Int.log 2 x) (-126) - 23 := by rw [qexp_eq, abs_of_pos hx]
  have qpos : 0 < q := by positivity
  have hm : x / q ≤ ((2 ^ 24 : ℤ) : ℝ) := by
    rw [div_le_iff₀ qpos]
    have h1 := lt_two_zpow_log x
    have h2 : (2:ℝ) ^ (Int.log 2 x + 1) ≤ 2 ^ (max (Int.log 2 x) (-126) + 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h3 : ((2 ^ 24 : ℤ) : ℝ) * q = 2 ^ (max (Int.log 2 x) (-126) + 1) := by
      simp only [q, hq]; push_cast
      rw [show (16777216:ℝ) = (2:ℝ) ^ (24:ℤ) by norm_num, ← zpow_add₀ z2]; ring_nf
    linarith
  have hk := roundEven_le_of_le hm
  have : (roundEven (x / q) : ℝ) ≤ ((2 ^ 24 : ℤ) : ℝ) := by exact_mod_cast hk
  calc (roundEven (x / q) : ℝ) * q ≤ ((2 ^ 24 : ℤ) : ℝ) * q := mul_le_mul_of_nonneg_right this qpos.le
    _ = _ := by
      simp only [q, hq]; push_cast
      rw [show (16777216:ℝ) = (2:ℝ) ^ (24:ℤ) by norm_num, ← zpow_add₀ z2]; ring_nf

/-- Normal range: `rne x ≥ 2^E`. -/
theorem rne_pos_ge {x : ℝ} (hx : 0 < x) (hE : (-126:ℤ) ≤ Int.log 2 x) :
    (2:ℝ) ^ Int.log 2 x ≤ rne x := by
  rw [rne_pos hx]
  have hq : qexp x = Int.log 2 x - 23 := by rw [qexp_eq, abs_of_pos hx, max_eq_left hE]
  rw [hq]
  have qpos : (0:ℝ) < 2 ^ (Int.log 2 x - 23) := by positivity
  have e : ((2 ^ 23 : ℤ) : ℝ) * 2 ^ (Int.log 2 x - 23) = 2 ^ Int.log 2 x := by
    push_cast; rw [show (8388608:ℝ) = (2:ℝ) ^ (23:ℤ) by norm_num, ← zpow_add₀ z2]; ring_nf
  have hm : ((2 ^ 23 : ℤ) : ℝ) ≤ x / 2 ^ (Int.log 2 x - 23) := by
    rw [le_div_iff₀ qpos, e]; exact two_zpow_log_le hx
  have : ((2 ^ 23 : ℤ) : ℝ) ≤ (roundEven (x / 2 ^ (Int.log 2 x - 23)) : ℝ) := by
    exact_mod_cast le_roundEven_of_le hm
  rw [← e]; exact mul_le_mul_of_nonneg_right this qpos.le

theorem rne_mono_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : rne x ≤ rne y := by
  have hy : 0 < y := hx.trans_le hxy
  have hl : Int.log 2 x ≤ Int.log 2 y := Int.log_mono_right hx hxy
  have hqx : qexp x = max (Int.log 2 x) (-126) - 23 := by rw [qexp_eq, abs_of_pos hx]
  have hqy : qexp y = max (Int.log 2 y) (-126) - 23 := by rw [qexp_eq, abs_of_pos hy]
  by_cases he : qexp x = qexp y
  · rw [rne_pos hx, rne_pos hy, he]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast roundEven_mono (div_le_div_of_nonneg_right hxy (by positivity))
  · have hlt : max (Int.log 2 x) (-126) < Int.log 2 y := by
      have : qexp x ≤ qexp y := by rw [hqx, hqy]; omega
      omega
    calc rne x ≤ (2:ℝ) ^ (max (Int.log 2 x) (-126) + 1) := rne_pos_le hx
      _ ≤ (2:ℝ) ^ Int.log 2 y := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ ≤ rne y := rne_pos_ge hy (by omega)

theorem rne_mono' : Monotone (rne : ℝ → ℝ) := by
  intro x y hxy
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rcases le_or_gt y 0 with hy | hy
    · rcases hy.lt_or_eq with hy | hy
      · have := rne_mono_pos (neg_pos.2 hy) (neg_le_neg hxy)
        rw [rne_neg', rne_neg'] at this; linarith
      · rw [hy]; have := rne_nonneg (neg_pos.2 hx).le; rw [rne_neg'] at this
        rw [show rne (0:ℝ) = 0 by simp [rne]]; linarith
    · have := rne_nonneg (neg_pos.2 hx).le; rw [rne_neg'] at this
      linarith [rne_nonneg hy.le]
  · subst hx; simpa [rne] using rne_nonneg hxy
  · exact rne_mono_pos hx hxy

/-- Values on the grid of their own quantum are fixed. -/
theorem rne_of_grid {y : ℝ} (hy : 0 < y) (n : ℤ) (s : ℤ) (hs : qexp y ≤ s)
    (e : y = n * (2:ℝ) ^ s) : rne y = y := by
  rw [rne_pos hy]
  generalize hq : qexp y = t at hs ⊢
  have : y / (2:ℝ) ^ t = ((n * 2 ^ (s - t).toNat : ℤ) : ℝ) := by
    rw [e]; push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_sub₀ z2]; field_simp
  rw [this, roundEven_intCast, ← this]; field_simp

theorem rne_idem_pos {x : ℝ} (hx : 0 < x) : rne (rne x) = rne x := by
  set M := max (Int.log 2 x) (-126)
  have hqx : qexp x = M - 23 := by rw [qexp_eq, abs_of_pos hx]
  set k := roundEven (x / (2:ℝ) ^ qexp x)
  have ey : rne x = k * (2:ℝ) ^ qexp x := rne_pos hx
  have k0 : 0 ≤ k := roundEven_nonneg (div_nonneg hx.le (by positivity))
  rcases k0.lt_or_eq with kpos | kz
  swap
  · rw [ey, ← kz]; simp [rne]
  have ypos : 0 < rne x := by rw [ey]; exact mul_pos (by exact_mod_cast kpos) (by positivity)
  have hle := rne_pos_le hx
  have hqy : qexp (rne x) = max (Int.log 2 (rne x)) (-126) - 23 := by
    rw [qexp_eq, abs_of_pos ypos]
  rcases hle.lt_or_eq with hlt | heq
  · apply rne_of_grid ypos k (qexp x) _ ey
    have : Int.log 2 (rne x) < M + 1 :=
      (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) ypos).1 (by simpa using hlt)
    rw [hqy, hqx]; omega
  · apply rne_of_grid ypos (2 ^ 23) (M - 22)
    · rw [hqy, heq, show (2:ℝ) ^ (M + 1) = ((2:ℕ):ℝ) ^ (M + 1) by norm_num,
        Int.log_zpow (by norm_num)]; omega
    · rw [heq]; push_cast
      rw [show (8388608:ℝ) = (2:ℝ) ^ (23:ℤ) by norm_num, ← zpow_add₀ z2]; simp only [M]; ring_nf

theorem rne_idem' (x : ℝ) : rne (rne x) = rne x := by
  rcases lt_trichotomy x 0 with h | h | h
  · have := rne_idem_pos (neg_pos.2 h); rw [rne_neg', rne_neg', neg_inj] at this; exact this
  · simp [rne, h]
  · exact rne_idem_pos h








theorem rne_ne (x : ℝ) (hx : x ≠ 0) :
    rne x = (if x < 0 then -1 else 1) * (roundEven (|x| / (2:ℝ) ^ qexp x) : ℝ) * (2:ℝ) ^ qexp x := by
  simp [rne, hx]

theorem rneR_rel' (x : ℝ) (hx : InRange x) :
    ∃ δ, |δ| ≤ (2 : ℝ) ^ (-24 : ℤ) ∧ rneR x = x * (1 + δ) := by
  rcases hx with h0 | ⟨hlo, -⟩
  · exact ⟨0, by simp, by simp [h0, rneR, rne]⟩
  have hx0 : x ≠ 0 := by rintro rfl; simp at hlo; linarith [show (0:ℝ) < 2 ^ (-126:ℤ) by positivity]
  have ha : 0 < |x| := abs_pos.2 hx0
  have hE : (-126 : ℤ) ≤ Int.log 2 |x| :=
    (Int.zpow_le_iff_le_log (b := 2) (by norm_num) ha).1 (by simpa using hlo)
  have hq : qexp x = Int.log 2 |x| - 23 := by rw [qexp_eq, max_eq_left hE]
  set q : ℝ := (2:ℝ) ^ qexp x with hqdef
  have qpos : 0 < q := by positivity
  have hsx : (if x < 0 then -1 else 1 : ℝ) * |x| = x := by
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (not_lt.1 h)]; ring
  have err : |rneR x - x| ≤ q / 2 := by
    have : rneR x - x = (if x < 0 then -1 else 1 : ℝ) * (q * ((roundEven (|x| / q) : ℝ) - |x| / q)) := by
      unfold rneR; rw [rne_ne x hx0]
      conv_rhs => rw [mul_sub, mul_div_cancel₀ _ qpos.ne', mul_sub, hsx]
      rw [← hqdef]; ring
    rw [this, abs_mul, abs_mul, abs_of_pos qpos]
    have hs : |(if x < 0 then -1 else 1 : ℝ)| = 1 := by split_ifs <;> simp
    rw [hs, one_mul]
    have := roundEven_err (|x| / q); nlinarith
  have hqx : q / 2 ≤ (2:ℝ) ^ (-24 : ℤ) * |x| := by
    have h2 := two_zpow_log_le ha
    have : q / 2 = (2:ℝ) ^ (-24 : ℤ) * (2:ℝ) ^ Int.log 2 |x| := by
      rw [hqdef, hq, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0),
        zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; norm_num; ring
    rw [this]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
  refine ⟨(rneR x - x) / x, ?_, by field_simp; ring⟩
  rw [abs_div, div_le_iff₀ ha]; exact err.trans hqx


theorem log_ratCast (q : ℚ) : Int.log 2 (q : ℝ) = Int.log 2 q := by
  rcases le_or_gt q 0 with h | h
  · rw [Int.log_of_right_le_zero _ h, Int.log_of_right_le_zero _ (by exact_mod_cast h)]
  · have hr : (0:ℝ) < q := by exact_mod_cast h
    refine le_antisymm ?_ ?_
    · rw [← Int.zpow_le_iff_le_log (b := 2) (by norm_num) h]
      have := Int.zpow_log_le_self (b := 2) (by norm_num) hr
      have h2 : (((2:ℚ) ^ Int.log 2 (q:ℝ) : ℚ) : ℝ) ≤ q := by push_cast; simpa using this
      exact_mod_cast h2
    · rw [← Int.zpow_le_iff_le_log (b := 2) (by norm_num) hr]
      have := Int.zpow_log_le_self (b := 2) (by norm_num) h
      have h2 : (((2:ℚ) ^ Int.log 2 q : ℚ) : ℝ) ≤ q := by exact_mod_cast (by simpa using this)
      push_cast at h2; exact h2

theorem roundEven_ratCast (m : ℚ) : roundEven (m : ℝ) = roundEven m := by
  unfold roundEven; dsimp only
  rw [Rat.floor_cast]
  have e : (m : ℝ) - (⌊m⌋ : ℝ) = ((m - ⌊m⌋ : ℚ) : ℝ) := by push_cast; ring
  rw [e]
  simp only [show ((1:ℝ) / 2) = ((1/2 : ℚ) : ℝ) by norm_num, Rat.cast_lt]

theorem rne_cast' (q : ℚ) : rneR (q : ℝ) = ((rne q : ℚ) : ℝ) := by
  unfold rneR rne
  by_cases h : q = 0
  · simp [h]
  have hr : (q : ℝ) ≠ 0 := by exact_mod_cast h
  have hq : qexp (q : ℝ) = qexp q := by
    simp only [qexp, ← Rat.cast_abs, log_ratCast]
  simp only [h, hr, ite_false, hq]
  rw [show |(q:ℝ)| / (2:ℝ) ^ qexp q = ((|q| / (2:ℚ) ^ qexp q : ℚ) : ℝ) by push_cast; rfl,
    roundEven_ratCast]
  push_cast
  by_cases hn : q < 0 <;> simp [hn]


theorem rneR_rel (x : ℝ) (hx : InRange x) :
    ∃ δ, |δ| ≤ (2 : ℝ) ^ (-24 : ℤ) ∧ rneR x = x * (1 + δ) := rneR_rel' x hx

theorem rneR_mono : Monotone rneR := rne_mono'

theorem rneR_neg (x : ℝ) : rneR (-x) = -rneR x := rne_neg' x

theorem rneR_idem (x : ℝ) : rneR (rneR x) = rneR x := rne_idem' x

theorem rneR_zero : rneR 0 = 0 := by
  simp [rneR, rne]

/-- Bridge: the executable rational rounding agrees with the real model. -/
theorem rne_cast (q : ℚ) : rneR (q : ℝ) = ((rne q : ℚ) : ℝ) := rne_cast' q

theorem rne_sign_q (p : ℚ) : (p < 0 → rne p ≤ 0) ∧ (0 ≤ p → 0 ≤ rne p) := by
  constructor
  · intro h
    have hp : (p:ℝ) < 0 := by exact_mod_cast h
    have h1 : (0:ℝ) ≤ rne (-(p : ℝ)) := rne_nonneg (by linarith)
    rw [rne_neg'] at h1
    have h2 : rne (p : ℝ) = ((rne p : ℚ) : ℝ) := rne_cast p
    rw [h2] at h1
    have : ((rne p : ℚ) : ℝ) ≤ 0 := by linarith
    exact_mod_cast this
  · intro h
    have : rneR ((p : ℚ) : ℝ) ≥ 0 := rne_nonneg (by exact_mod_cast h)
    rw [rne_cast] at this; exact_mod_cast this

/-- Bridge: on non-overflowing finite results, `V.mul` is `rneR` of the exact product. -/
theorem mul_num_refines (a b : Bool) (x y : ℚ)
    (hfin : ∃ n r, (V.num a x).mul (V.num b y) = .num n r) :
    (((V.num a x).mul (V.num b y)).toQ?.getD 0 : ℝ) =
      rneR (((V.num a x).toQ?.getD 0 : ℝ) * ((V.num b y).toQ?.getD 0 : ℝ)) := by
  have hp : ((V.num a x).toQ?.getD 0) * ((V.num b y).toQ?.getD 0) =
      (if a != b then -1 else 1) * (x * y) := by
    cases a <;> cases b <;> simp [V.toQ?]
  have cast : ((V.num a x).toQ?.getD 0 : ℝ) * ((V.num b y).toQ?.getD 0 : ℝ) =
      (((if a != b then -1 else 1) * (x * y) : ℚ) : ℝ) := by rw [← hp]; push_cast; rfl
  rw [cast, rne_cast]
  obtain ⟨n, r, hr⟩ := hfin
  revert hr
  simp only [V.mul, roundQ]
  generalize (if a != b then -1 else 1) * (x * y) = p
  split_ifs with h0 h1
  · intro _; simp [V.toQ?, h0, rne]
  · intro hr; cases hr
  · intro _
    simp only [V.toQ?, Option.getD_some]
    have hs := rne_sign_q p
    split_ifs with hn
    · rw [abs_of_nonpos (hs.1 hn)]; push_cast; ring
    · rw [abs_of_nonneg (hs.2 (not_lt.1 hn))]

theorem roundQ_toQ (p : ℚ) (z : Bool) (hfin : ∃ n r, roundQ p z = .num n r) :
    (((roundQ p z).toQ?.getD 0 : ℚ) : ℝ) = rneR (p : ℝ) := by
  rw [rne_cast]
  obtain ⟨n, r, hr⟩ := hfin
  revert hr
  simp only [roundQ]
  split_ifs with h0 h1
  · intro _; simp [V.toQ?, h0, rne]
  · intro hr; cases hr
  · intro _
    simp only [V.toQ?, Option.getD_some]
    have hs := rne_sign_q p
    split_ifs with hn
    · rw [abs_of_nonpos (hs.1 hn)]; push_cast; ring
    · rw [abs_of_nonneg (hs.2 (not_lt.1 hn))]

/-- Bridge: on finite results, `V.add` of two finite values is `rneR` of the exact sum. -/
theorem add_num_refines (a b : Bool) (x y : ℚ)
    (hfin : ∃ n r, (V.num a x).add (V.num b y) = .num n r) :
    (((V.num a x).add (V.num b y)).toQ?.getD 0 : ℝ) =
      rneR (((V.num a x).toQ?.getD 0 : ℝ) + ((V.num b y).toQ?.getD 0 : ℝ)) := by
  simp only [V.add] at hfin ⊢
  rw [roundQ_toQ _ _ hfin]; push_cast; rfl

/-- Bridge: `V.sub` (= add of the negation, as in IEEE) is `rneR` of the exact difference. -/
theorem sub_num_refines (a b : Bool) (x y : ℚ)
    (hfin : ∃ n r, (V.num a x).sub (V.num b y) = .num n r) :
    (((V.num a x).sub (V.num b y)).toQ?.getD 0 : ℝ) =
      rneR (((V.num a x).toQ?.getD 0 : ℝ) - ((V.num b y).toQ?.getD 0 : ℝ)) := by
  simp only [V.sub, V.negate] at hfin ⊢
  rw [add_num_refines a (!b) x y hfin, sub_eq_add_neg]
  congr 2; cases b <;> simp [V.toQ?]

/-- Bridge: `V.div` by a nonzero finite value is `rneR` of the exact quotient. -/
theorem div_num_refines (a b : Bool) (x y : ℚ) (hy : y ≠ 0)
    (hfin : ∃ n r, (V.num a x).div (V.num b y) = .num n r) :
    (((V.num a x).div (V.num b y)).toQ?.getD 0 : ℝ) =
      rneR (((V.num a x).toQ?.getD 0 : ℝ) / ((V.num b y).toQ?.getD 0 : ℝ)) := by
  simp only [V.div, hy, if_false] at hfin ⊢
  rw [roundQ_toQ _ _ hfin]
  congr 1
  cases a <;> cases b <;> simp [V.toQ?] <;> push_cast <;> ring

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

/-! ### Bit-level round trip: `decode ∘ encode = id` on representable values -/

theorem pack_toNat (s : Bool) (E M : ℕ) (hE : E < 256) (hM : M < 2^23) :
    ((if s then (0x80000000 : UInt32) else 0) ||| (E.toUInt32 <<< 23) ||| M.toUInt32).toNat =
      (if s then 2^31 else 0) + E * 2^23 + M := by
  have h1 : (E.toUInt32 <<< 23).toNat = E * 2^23 := by
    rw [UInt32.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  have h2 : (M.toUInt32).toNat = M := by simp; omega
  rw [UInt32.toNat_or, UInt32.toNat_or, h1, h2, Nat.or_assoc]
  have h3 : E * 2^23 ||| M = 2^23 * E + M := by
    rw [mul_comm]; exact (Nat.two_pow_add_eq_or_of_lt hM E).symm
  rw [h3]
  cases s
  · simp; ring
  · simp only [ite_true]
    have : (0x80000000 : UInt32).toNat = 2^31 * 1 := by decide
    rw [this, ← Nat.two_pow_add_eq_or_of_lt (by omega)]; ring

theorem decode_of_toNat (w : UInt32) (S E M : ℕ) (_hS : S ≤ 1) (hE : E < 256) (hM : M < 2^23)
    (hw : w.toNat = S * 2^31 + E * 2^23 + M) :
    decode w = if E = 255 then (if M = 0 then .inf (S = 1) else .nan)
      else if E = 0 then .num (S = 1) ((M : ℚ) * (2 : ℚ) ^ (-149 : ℤ))
      else .num (S = 1) (((2 ^ 23 + M : ℕ) : ℚ) * (2 : ℚ) ^ ((E : ℤ) - 150)) := by
  have hs : ((w >>> 31) == 1) = decide (S = 1) := by
    have : (w >>> 31).toNat = S := by
      rw [UInt32.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]; omega
    by_cases h : S = 1
    · simp [h]; apply UInt32.toNat_inj.mp; rw [this, h]; rfl
    · simp [h]; intro hc; apply h; rw [← this, hc]; rfl
  have he : ((w >>> 23) &&& 0xff).toNat = E := by
    rw [UInt32.toNat_and, UInt32.toNat_shiftRight]
    have : (0xff : UInt32).toNat = 2^8 - 1 := by decide
    rw [this, Nat.and_two_pow_sub_one_eq_mod]; simp [Nat.shiftRight_eq_div_pow]; omega
  have hm : (w &&& 0x7fffff).toNat = M := by
    rw [UInt32.toNat_and]
    have : (0x7fffff : UInt32).toNat = 2^23 - 1 := by decide
    rw [this, Nat.and_two_pow_sub_one_eq_mod]; omega
  unfold decode; simp only [hs, he, hm]

/-- `r ≥ 0` lies on the binary32 grid (unbounded above). -/
def Grid (r : ℚ) : Prop := ∃ (n : ℕ) (q : ℤ), -149 ≤ q ∧ n < 2^24 ∧ r = n * (2:ℚ) ^ q

theorem nat_of_grid (n : ℕ) (q k : ℤ) (h : 0 ≤ q + k) :
    (n : ℚ) * (2:ℚ) ^ q * (2:ℚ) ^ k = ((n * 2 ^ (q + k).toNat : ℕ) : ℚ) := by
  push_cast; rw [← zpow_natCast, Int.toNat_of_nonneg h, mul_assoc, ← zpow_add₀ (by norm_num)]

theorem sign_dec (s : Bool) : decide ((if s then 1 else 0 : ℕ) = 1) = s := by cases s <;> rfl

theorem decode_encode_num (s : Bool) (r : ℚ) (hg : Grid r) (hmax : r ≤ maxFinite) :
    decode (encode (.num s r)) = .num s r := by
  obtain ⟨n, q, hq, hn, rfl⟩ := hg
  have hsb : ∀ X : UInt32, (if s then (0x80000000 : UInt32) else 0) ||| X =
      (if s then (0x80000000 : UInt32) else 0) ||| ((0 : ℕ).toUInt32 <<< 23) ||| X := by
    intro X; simp
  have hS : (if s then 1 else 0 : ℕ) ≤ 1 := by cases s <;> simp
  have hsn : ∀ X : ℕ, (if s then 2^31 else 0 : ℕ) + X = (if s then 1 else 0 : ℕ) * 2^31 + X := by
    intro X; cases s <;> simp
  by_cases h0 : (n : ℚ) * 2 ^ q = 0
  · simp only [encode, h0, ite_true]
    rw [show (if s then (0x80000000 : UInt32) else 0) = (if s then (0x80000000 : UInt32) else 0)
      ||| ((0 : ℕ).toUInt32 <<< 23) ||| (0 : ℕ).toUInt32 by cases s <;> decide]
    rw [decode_of_toNat _ _ 0 0 hS (by norm_num) (by norm_num)]
    · simp [sign_dec]
    · rw [pack_toNat s 0 0 (by norm_num) (by norm_num), hsn]
  have hpos : 0 < (n : ℚ) * 2 ^ q := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at h0
    · positivity
  by_cases hsub : (n : ℚ) * 2 ^ q < (2 : ℚ) ^ (-126 : ℤ)
  · simp only [encode, h0, hsub, ite_true, ite_false]
    rw [nat_of_grid n q 149 (by omega), show ∀ x : ℚ, x.floor = ⌊x⌋ from fun _ => rfl,
      Int.floor_natCast]
    set N := n * 2 ^ (q + 149).toNat
    have hN : (N : ℚ) = (n : ℚ) * 2 ^ q * 2 ^ (149:ℤ) := (nat_of_grid n q 149 (by omega)).symm
    have hNlt : N < 2^23 := by
      have : (N : ℚ) < 2^23 := by
        rw [hN]; calc _ < (2:ℚ) ^ (-126 : ℤ) * 2 ^ (149:ℤ) := by gcongr
          _ = 2^23 := by norm_num
      exact_mod_cast this
    simp only [Int.toNat_natCast]
    rw [hsb, decode_of_toNat _ _ 0 N hS (by norm_num) hNlt]
    · rw [if_neg (by norm_num), if_pos rfl, sign_dec, hN, mul_assoc, ← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
      norm_num
    · rw [pack_toNat s 0 N (by norm_num) hNlt, hsn]
  · push_neg at hsub
    simp only [encode, h0, not_lt.2 hsub, ite_false]
    set r : ℚ := (n : ℚ) * 2 ^ q with hr
    set e := Int.log 2 r
    have he1 : (2:ℚ) ^ e ≤ r := by exact_mod_cast Int.zpow_log_le_self (b := 2) (by norm_num) hpos
    have he2 : r < (2:ℚ) ^ (e + 1) := by exact_mod_cast Int.lt_zpow_succ_log_self (b := 2) (by norm_num) r
    have hlo : -126 ≤ e := by
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℚ) < 2)).1 (lt_of_le_of_lt hsub he2); omega
    have hhi : e ≤ 127 := by
      have : (2:ℚ) ^ e < 2 ^ (128:ℤ) := lt_of_le_of_lt he1 (lt_of_le_of_lt hmax (by unfold maxFinite; norm_num))
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℚ) < 2)).1 this; omega
    have hqe : e ≤ q + 23 := by
      have : (2:ℚ) ^ e < 2 ^ (q + 24) := by
        calc (2:ℚ) ^ e ≤ r := he1
          _ < (2 ^ 24 : ℕ) * 2 ^ q := by rw [hr]; gcongr
          _ = _ := by rw [zpow_add₀ (by norm_num)]; push_cast; ring
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℚ) < 2)).1 this; omega
    set P := n * 2 ^ (q + (23 - e)).toNat
    have hP : (P : ℚ) = r * 2 ^ (23 - e) := (nat_of_grid n q (23 - e) (by omega)).symm
    have hP1 : (2:ℚ) ^ 23 ≤ P := by
      rw [hP]; calc (2:ℚ) ^ 23 = 2 ^ e * 2 ^ (23 - e) := by rw [← zpow_add₀ (by norm_num)]; norm_num
        _ ≤ _ := by gcongr
    have hP2 : (P : ℚ) < 2 ^ 24 := by
      rw [hP]; calc r * 2 ^ (23 - e) < 2 ^ (e + 1) * 2 ^ (23 - e) := by gcongr
        _ = 2 ^ 24 := by rw [← zpow_add₀ (by norm_num), show e + 1 + (23 - e) = (24:ℤ) by ring]; norm_num
    have hP1' : 2 ^ 23 ≤ P := by exact_mod_cast hP1
    have hP2' : P < 2 ^ 24 := by exact_mod_cast hP2
    have hm : (r * 2 ^ (23 - e) - 2 ^ 23 : ℚ) = ((P - 2 ^ 23 : ℕ) : ℚ) := by
      rw [← hP, Nat.cast_sub hP1']; norm_num
    rw [hm, show ∀ x : ℚ, x.floor = ⌊x⌋ from fun _ => rfl, Int.floor_natCast, Int.toNat_natCast]
    have hE : (e + 127).toNat < 256 := by omega
    have hM : P - 2 ^ 23 < 2 ^ 23 := by omega
    rw [decode_of_toNat _ _ _ _ hS hE hM]
    · rw [if_neg (show (e + 127).toNat ≠ 255 by omega), if_neg (show (e + 127).toNat ≠ 0 by omega),
        sign_dec]
      have h23 : 2 ^ 23 + (P - 2 ^ 23) = P := Nat.add_sub_cancel' hP1'
      rw [h23, hP, Int.toNat_of_nonneg (by omega), mul_assoc,
        ← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
      rw [show 23 - e + ((e + 127 : ℤ) - 150) = 0 by ring]; simp
    · rw [pack_toNat s _ _ hE hM, hsn]



theorem rne_maxFinite : rne maxFinite = maxFinite := by decide +kernel

theorem abs_rne_grid (p : ℚ) : Grid |rne p| := by
  by_cases h0 : p = 0
  · exact ⟨0, -149, le_refl _, by norm_num, by simp [h0, rne]⟩
  set Q := qexp p with hQ
  set N := roundEven (|p| / (2:ℚ) ^ Q)
  have hQ' : Q = max (Int.log 2 |p|) (-126) - 23 := by simp [hQ, qexp, prec, emin]
  have hpa : 0 < |p| := abs_pos.2 h0
  have hm0 : 0 ≤ |p| / (2:ℚ) ^ Q := by positivity
  have hm1 : |p| / (2:ℚ) ^ Q ≤ ((2 ^ 24 : ℤ) : ℚ) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : |p| < (2:ℚ) ^ (Int.log 2 |p| + 1) := by
      exact_mod_cast Int.lt_zpow_succ_log_self (b := 2) (by norm_num) |p|
    have h2 : (2:ℚ) ^ (Int.log 2 |p| + 1) ≤ 2 ^ (Q + 24) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [show (2:ℚ) ^ (Q + 24) = 2 ^ Q * 16777216 by rw [zpow_add₀ (by norm_num)]; norm_num] at h2
    push_cast; linarith
  have hN0 : 0 ≤ N := by
    show 0 ≤ roundEven _; rw [← roundEven_ratCast]; exact roundEven_nonneg (by exact_mod_cast hm0)
  have hN1 : N ≤ 2 ^ 24 := by
    show roundEven _ ≤ _; rw [← roundEven_ratCast]
    exact roundEven_le_of_le (by exact_mod_cast hm1)
  have hr : |rne p| = (N : ℚ) * 2 ^ Q := by
    unfold rne; rw [if_neg h0]; dsimp only
    rw [abs_mul, abs_mul]
    have : |(if p < 0 then (-1 : ℚ) else 1)| = 1 := by split_ifs <;> simp
    rw [this, one_mul, abs_of_nonneg (by exact_mod_cast hN0), abs_of_pos (zpow_pos (by norm_num : (0:ℚ) < 2) _)]
  have hQ149 : -149 ≤ Q := by omega
  rcases lt_or_eq_of_le hN1 with h | h
  · refine ⟨N.toNat, Q, hQ149, by omega, ?_⟩
    rw [hr]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hN0).symm
  · refine ⟨2 ^ 23, Q + 1, by omega, by norm_num, ?_⟩
    rw [hr, h, zpow_add₀ (by norm_num)]; push_cast; ring


theorem grid_fixed {r : ℚ} (hg : Grid r) : rne r = r := by
  obtain ⟨n, q, hq, hn, rfl⟩ := hg
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h, rne]
  have hc : ((rne ((n : ℚ) * 2 ^ q) : ℚ) : ℝ) = (((n : ℚ) * 2 ^ q : ℚ) : ℝ) := by
    rw [← rne_cast]; push_cast
    have hy : (0:ℝ) < n * 2 ^ q := by positivity
    apply rne_of_grid hy n q
    · rw [qexp_eq, abs_of_pos hy]
      have : Int.log 2 ((n:ℝ) * 2 ^ q) ≤ q + 23 := by
        have h1 := Int.zpow_log_le_self (b := 2) (by norm_num) hy
        have h2 : (n:ℝ) * 2 ^ q < (2:ℝ) ^ (q + 24) := by
          rw [zpow_add₀ (by norm_num), mul_comm]; gcongr; exact_mod_cast hn
        have := lt_of_le_of_lt h1 h2; push_cast at this
        have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).1 this; omega
      omega
    · push_cast; rfl
  exact_mod_cast hc

theorem rne_bound (p : ℚ) (h : |p| ≤ maxFinite) : |rne p| ≤ maxFinite := by
  have hm : rneR (maxFinite : ℝ) = maxFinite := by rw [rne_cast, rne_maxFinite]
  have h1 : rneR (p : ℝ) ≤ maxFinite := by
    rw [← hm]; exact rneR_mono (by exact_mod_cast (le_abs_self p).trans h)
  have h2 : -(maxFinite : ℝ) ≤ rneR (p : ℝ) := by
    rw [← hm, ← rneR_neg]; exact rneR_mono (by have := neg_abs_le p; push_cast; exact_mod_cast (by linarith))
  rw [rne_cast] at h1 h2
  have : |((rne p : ℚ) : ℝ)| ≤ maxFinite := abs_le.2 ⟨h2, h1⟩
  exact_mod_cast this

theorem roundQ_ok (p : ℚ) (z : Bool) (h : |p| ≤ maxFinite) :
    ∃ s r, roundQ p z = .num s r ∧ Grid r ∧ r ≤ maxFinite := by
  unfold roundQ
  by_cases h0 : p = 0
  · exact ⟨z, 0, by simp [h0], ⟨0, -149, le_refl _, by norm_num, by simp⟩, by unfold maxFinite; norm_num⟩
  have hb := rne_bound p h
  simp only [h0, ite_false, gt_iff_lt, not_lt.2 hb]
  exact ⟨_, _, rfl, abs_rne_grid p, hb⟩

theorem and_exp_mask (x : ℕ) : x &&& 0x7f800000 = (x / 2 ^ 23 % 256) * 2 ^ 23 := by
  have hm : (x &&& 0x7f800000) % 2 ^ 23 = 0 := by
    rw [Nat.and_mod_two_pow]; norm_num
  have hd : (x &&& 0x7f800000) / 2 ^ 23 = x / 2 ^ 23 % 256 := by
    rw [Nat.and_div_two_pow, show (0x7f800000 : ℕ) / 2 ^ 23 = 2 ^ 8 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.div_add_mod (x &&& 0x7f800000) (2 ^ 23)
  rw [hm, hd] at this; omega

theorem decode_fields (w : UInt32) :
    decode w = if w.toNat / 2^23 % 256 = 255 then
        (if w.toNat % 2^23 = 0 then .inf (w.toNat / 2^31 = 1) else .nan)
      else if w.toNat / 2^23 % 256 = 0 then
        .num (w.toNat / 2^31 = 1) (((w.toNat % 2^23 : ℕ) : ℚ) * (2 : ℚ) ^ (-149 : ℤ))
      else .num (w.toNat / 2^31 = 1)
        (((2 ^ 23 + w.toNat % 2^23 : ℕ) : ℚ) * (2 : ℚ) ^ (((w.toNat / 2^23 % 256 : ℕ) : ℤ) - 150)) := by
  have := w.toNat_lt
  exact decode_of_toNat w _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem isNaNBits_false {w : UInt32} {s : Bool} {q : ℚ} (h : decode w = .num s q) :
    isNaNBits w = false := by
  unfold isNaNBits
  rw [decode_fields] at h
  by_contra hc
  simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨h1, h2⟩ := hc
  have e1 := congrArg UInt32.toNat h1
  rw [UInt32.toNat_and, show (0x7f800000 : UInt32).toNat = 0x7f800000 by decide, and_exp_mask] at e1
  have e2 : (w &&& 0x7fffff).toNat ≠ 0 := fun hh => h2 (UInt32.toNat_inj.mp (by rw [hh]; rfl))
  rw [UInt32.toNat_and, show (0x7fffff : UInt32).toNat = 2^23 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod] at e2
  have : w.toNat / 2 ^ 23 % 256 = 255 := by omega
  rw [if_pos this, if_neg e2] at h; cases h

theorem decode_grid {w : UInt32} {s : Bool} {q : ℚ} (h : decode w = .num s q) :
    Grid q ∧ q ≤ maxFinite := by
  rw [decode_fields] at h
  have := w.toNat_lt
  split_ifs at h with h1 h2 <;> cases h
  · refine ⟨⟨_, -149, le_refl _, by omega, rfl⟩, ?_⟩
    calc _ ≤ ((2^23 : ℕ) : ℚ) * (2:ℚ) ^ (-149:ℤ) := by gcongr; omega
      _ ≤ maxFinite := by unfold maxFinite; norm_num
  · refine ⟨⟨_, _, by omega, by omega, rfl⟩, ?_⟩
    have hE : w.toNat / 2 ^ 23 % 256 ≤ 254 := by omega
    calc _ ≤ ((2^24 - 1 : ℕ) : ℚ) * (2:ℚ) ^ (((254 : ℕ) : ℤ) - 150) := by
          gcongr
          all_goals first | omega | norm_num | (push_cast; omega)
      _ = maxFinite := by unfold maxFinite; norm_num

end LightRT.FP.Binary32
