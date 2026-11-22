/-
  The ISA boundary of the SIMD watertight leaf, made explicit (resume-lean
  item 4 / PLAN.md M22 addendum 11).

  `SimdLanes.lean` proves the per-lane refinement `vWoopK_lane` (definitionally:
  the model fixes the scalar operation order) and the block-fold lemmas
  `blockBest_sound` / `blockBest_woop` (a reported change is a real scalar
  Woop hit in some lane). The *only* unproved link is that the vendor's
  packed intrinsics implement the model's lane-wise binary32 operations
  `mulBits/addBits/subBits/divBits/ltBits/leBits/eqF` (RNE, ordered compares,
  exact mask packing, no FMA). This module packages exactly those assumptions
  as the fields of `PackedOps`, re-runs the Woop kernel over abstract ops, and
  proves (with the audit equations as hypotheses) that the block result is
  still a genuine scalar hit.

  The `PackedOps` instance for real SSE4.1/AVX2/SVE intrinsics is NOT supplied
  here — that would require a vendor ISA semantics model; `wtcheck`'s leaf
  fuzz (every `make formal`) is the empirical evidence for it. The point of
  this file is that the exact remaining hypothesis is now a machine-checked
  structure, not prose.
-/
import LightRT.C.Proofs.SimdLanes

namespace LightRT.C.Ref
open LightRT.FP.Binary32

variable {w : ℕ}

/-- The audited semantics of the packed operations used by the Woop leaf.
    Defaults are the model ops; `*_model` fields are the audit equations
    (intrinsic ≡ per-lane `FP.Binary32` op). -/
structure PackedOps where
  mul : F → F → F := mulBits
  add : F → F → F := addBits
  sub : F → F → F := subBits
  div : F → F → F := divBits
  lt : F → F → Bool := ltBits
  le : F → F → Bool := leBits
  eq : F → F → Bool := eqF
  andB : Bool → Bool → Bool := (· && ·)
  orB : Bool → Bool → Bool := (· || ·)
  mul_model : ∀ x y, mul x y = mulBits x y := by intros; rfl
  add_model : ∀ x y, add x y = addBits x y := by intros; rfl
  sub_model : ∀ x y, sub x y = subBits x y := by intros; rfl
  div_model : ∀ x y, div x y = divBits x y := by intros; rfl
  lt_model : ∀ x y, lt x y = ltBits x y := by intros; rfl
  le_model : ∀ x y, le x y = leBits x y := by intros; rfl
  eq_model : ∀ x y, eq x y = eqF x y := by intros; rfl
  and_model : ∀ x y, andB x y = (x && y) := by intros; rfl
  or_model : ∀ x y, orB x y = (x || y) := by intros; rfl

/-- The kernel over abstract packed ops (same expression tree as
    `SimdLanes.vWoopK`). -/
def kVx (ops : PackedOps) (k : Axes) (o d : Fin 3 → F) (v : Fin w → Fin 3 → F) : Lane w :=
  fun i => ops.sub (ops.sub (v i k.1) (o k.1))
    (ops.mul (woopSx k d) (ops.sub (v i k.2.2) (o k.2.2)))
def kVy (ops : PackedOps) (k : Axes) (o d : Fin 3 → F) (v : Fin w → Fin 3 → F) : Lane w :=
  fun i => ops.sub (ops.sub (v i k.2.1) (o k.2.1))
    (ops.mul (woopSy k d) (ops.sub (v i k.2.2) (o k.2.2)))
def kVz (ops : PackedOps) (k : Axes) (o : Fin 3 → F) (v : Fin w → Fin 3 → F) : Lane w :=
  fun i => ops.sub (v i k.2.2) (o k.2.2)

def kEdge (ops : PackedOps) (px py qx qy : Lane w) : Lane w :=
  fun i => ops.sub (ops.mul (px i) (qy i)) (ops.mul (py i) (qx i))

def kU (ops : PackedOps) (k : Axes) (o d : Fin 3 → F)
    (_v0 v1 v2 : Fin w → Fin 3 → F) : Lane w :=
  kEdge ops (kVx ops k o d v2) (kVy ops k o d v2) (kVx ops k o d v1) (kVy ops k o d v1)
def kV (ops : PackedOps) (k : Axes) (o d : Fin 3 → F)
    (v0 _v1 v2 : Fin w → Fin 3 → F) : Lane w :=
  kEdge ops (kVx ops k o d v0) (kVy ops k o d v0) (kVx ops k o d v2) (kVy ops k o d v2)
def kW (ops : PackedOps) (k : Axes) (o d : Fin 3 → F)
    (v0 v1 _v2 : Fin w → Fin 3 → F) : Lane w :=
  kEdge ops (kVx ops k o d v1) (kVy ops k o d v1) (kVx ops k o d v0) (kVy ops k o d v0)
def kDet (ops : PackedOps) (k : Axes) (o d : Fin 3 → F)
    (v0 v1 v2 : Fin w → Fin 3 → F) : Lane w :=
  fun i => ops.add (ops.add (kU ops k o d v0 v1 v2 i) (kV ops k o d v0 v1 v2 i))
    (kW ops k o d v0 v1 v2 i)

def kT (ops : PackedOps) (k : Axes) (o d : Fin 3 → F)
    (v0 v1 v2 : Fin w → Fin 3 → F) : Lane w :=
  fun i => ops.div
    (ops.add (ops.add
        (ops.mul (kU ops k o d v0 v1 v2 i) (ops.mul (woopSz k d) (kVz ops k o v0 i)))
        (ops.mul (kV ops k o d v0 v1 v2 i) (ops.mul (woopSz k d) (kVz ops k o v1 i))))
      (ops.mul (kW ops k o d v0 v1 v2 i) (ops.mul (woopSz k d) (kVz ops k o v2 i))))
    (kDet ops k o d v0 v1 v2 i)

def kRej1 (ops : PackedOps) (k : Axes) (o d : Fin 3 → F)
    (v0 v1 v2 : Fin w → Fin 3 → F) : Mask w :=
  fun i => ops.andB
    (ops.orB (ops.orB (ops.lt (kU ops k o d v0 v1 v2 i) zero)
      (ops.lt (kV ops k o d v0 v1 v2 i) zero))
      (ops.lt (kW ops k o d v0 v1 v2 i) zero))
    (ops.orB (ops.orB (ops.lt zero (kU ops k o d v0 v1 v2 i))
      (ops.lt zero (kV ops k o d v0 v1 v2 i)))
      (ops.lt zero (kW ops k o d v0 v1 v2 i)))

def kRej2 (ops : PackedOps) (k : Axes) (o d : Fin 3 → F)
    (v0 v1 v2 : Fin w → Fin 3 → F) : Mask w :=
  fun i => ops.eq (kDet ops k o d v0 v1 v2 i) zero

def kRej3 (ops : PackedOps) (k : Axes) (o d : Fin 3 → F)
    (v0 v1 v2 : Fin w → Fin 3 → F) (tmin tbest : F) : Mask w :=
  fun i => !(ops.andB (ops.le tmin (kT ops k o d v0 v1 v2 i))
    (ops.lt (kT ops k o d v0 v1 v2 i) tbest))

def kWoopK (ops : PackedOps) (k : Axes) (o d : Fin 3 → F)
    (v0 v1 v2 : Fin w → Fin 3 → F) (tmin tbest : F) : Fin w → Option (F × F × F) :=
  fun i => if kRej1 ops k o d v0 v1 v2 i then none
    else if kRej2 ops k o d v0 v1 v2 i then none
    else if kRej3 ops k o d v0 v1 v2 tmin tbest i then none
    else some (kT ops k o d v0 v1 v2 i,
      ops.div (kV ops k o d v0 v1 v2 i) (kDet ops k o d v0 v1 v2 i),
      ops.div (kW ops k o d v0 v1 v2 i) (kDet ops k o d v0 v1 v2 i))

/-- With the audit equations, the abstract kernel IS the model kernel. -/
theorem kWoopK_eq_model (ops : PackedOps) (k : Axes) (o d : Fin 3 → F)
    (v0 v1 v2 : Fin w → Fin 3 → F) (tmin tbest : F) :
    kWoopK ops k o d v0 v1 v2 tmin tbest = vWoopK k o d v0 v1 v2 tmin tbest := by
  funext i
  simp only [kWoopK, kRej1, kRej2, kRej3, kT, kDet, kU, kV, kW, kEdge, kVx, kVy, kVz,
    vWoopK, vRej1, vRej2, vRej3, vWoopT, vWoopDet, vWoopU, vWoopV, vWoopW, vEdge,
    vWoopVx, vWoopVy, vWoopVz]
  simp only [ops.mul_model, ops.add_model, ops.sub_model, ops.div_model,
    ops.lt_model, ops.le_model, ops.eq_model, ops.and_model, ops.or_model,
    vmul, vadd, vsub, vdiv, vlt, vle, veq,
    vand, vor, vnot, vcomp, vbroadcast, vconst]
  rfl

/-- **The conditional SIMD leaf theorem**: if the packed intrinsics satisfy the
    audited per-lane equations (`PackedOps`), a block result that differs from
    the caller's best is a genuine scalar Woop hit in some lane — with the
    *same* `(t, u, v)` and lane id. The missing piece is the `PackedOps`
    instance for real SSE4.1/AVX2/SVE intrinsics (vendor semantics); this
    theorem isolates exactly that hypothesis. -/
theorem simd_leaf_eq_scalar_of_isa {α : Type} [DecidableEq α]
    (ops : PackedOps) (s0 : Best α) (ids : Fin w → α) (noHit : α)
    (blk : Fin w → Fin 3 → Fin 3 → F) (o d : Fin 3 → F) (tmin tbest : F)
    {t u v : F} {jid : α}
    (h : blockBest s0 ids noHit
      (kWoopK ops (woopAxes d) o d (fun i => blk i 0) (fun i => blk i 1)
        (fun i => blk i 2) tmin tbest) = (t, u, v, jid))
    (hne : jid ≠ s0.2.2.2) :
    ∃ i, ids i = jid ∧ woop o d (blk i 0) (blk i 1) (blk i 2) tmin tbest = some (t, u, v) := by
  rw [kWoopK_eq_model ops] at h
  exact blockBest_woop s0 ids noHit blk o d tmin tbest h hne

end LightRT.C.Ref
