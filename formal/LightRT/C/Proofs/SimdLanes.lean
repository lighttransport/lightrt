/-
  Per-lane model of the SIMD watertight leaf (resume-lean item 4).

  `tri_woop4_block` (SSE), `tri_woop8_block` (AVX2) and `tri_woop_sve_block`
  (SVE 8/16) run the scalar Woop test independently in every lane of a block
  and then select the smallest `t` (lowest lane on ties, `NO_HIT` padding
  skipped). This file models that structure:

  * `vmul`/`vadd`/`vsub`/`vdiv`/`vlt` are the lane-wise binary32 operations;
  * `vWoopK` mirrors `Ref.woopK` over those vector operations, with the same
    expression tree, association and `if`-based rejection (so no FMA and no
    reassociation);
  * `vWoopK_lane` proves that lane `i` of the vector kernel is exactly the
    scalar kernel on lane `i`'s vertices;
  * `blockBest` mirrors the C driver's fold (skip `NO_HIT`, keep strictly
    smaller `t`), and `blockBest_sound` shows that a block result different
    from the caller's best is a real lane hit with the reported `(t, u, v)`
    and lane id; `blockBest_all_skip` covers an all-padding block.

  **Assumption (the remaining gap).** The model *defines* the vector ops as
  the corresponding `FP.Binary32` lane operations (round-to-nearest-even, no
  FMA contraction, no reassociation). Showing that the ISA's packed
  `mulps/addps/subps/divps/cmpps` compute exactly this (and that the C's
  intrinsics compile to them) is what remains for a machine-checked SIMD
  refinement; `wtcheck`'s leaf fuzz checks it exhaustively for this kernel
  (400k blocks / 2.7M lanes bit-identical to `tri_woop_one`, including SVE
  8/16).
-/
import LightRT.C.Ref

namespace LightRT.C.Ref
open LightRT.FP.Binary32

variable {w : ℕ}

/-- One lane of a packed register. -/
abbrev Lane (w : ℕ) := Fin w → F

/-- Lane-wise boolean mask. -/
abbrev Mask (w : ℕ) := Fin w → Bool

/-- Packed binary32 operations (one IEEE operation per lane). -/
def vmul (x y : Lane w) : Lane w := fun i => mulBits (x i) (y i)
def vadd (x y : Lane w) : Lane w := fun i => addBits (x i) (y i)
def vsub (x y : Lane w) : Lane w := fun i => subBits (x i) (y i)
def vdiv (x y : Lane w) : Lane w := fun i => divBits (x i) (y i)
def vneg (x : Lane w) : Lane w := fun i => neg (x i)
def vconst (c : F) : Lane w := fun _ => c

def vlt (x y : Lane w) : Mask w := fun i => ltBits (x i) (y i)
def vle (x y : Lane w) : Mask w := fun i => leBits (x i) (y i)
def veq (x y : Lane w) : Mask w := fun i => eqF (x i) (y i)
def vand (p q : Mask w) : Mask w := fun i => p i && q i
def vor (p q : Mask w) : Mask w := fun i => p i || q i
def vnot (p : Mask w) : Mask w := fun i => !p i
def vall (p : Mask w) : Bool := (List.finRange w).all p
def vany (p : Mask w) : Bool := (List.finRange w).any p

/-- Broadcast a scalar coordinate, select a vertex component. -/
def vcomp (v : Fin w → Fin 3 → F) (k : Fin 3) : Lane w := fun i => v i k
def vbroadcast (c : F) : Lane w := fun _ => c

/-- The sheared 2D image of one vertex, lane-wise (the shape of
    `tri_woop8_lanes`). -/
def vWoopVx (k : Axes) (o d : Fin 3 → F) (v : Fin w → Fin 3 → F) : Lane w :=
  vsub (vsub (vcomp v k.1) (vbroadcast (o k.1)))
    (vmul (vbroadcast (woopSx k d))
      (vsub (vcomp v k.2.2) (vbroadcast (o k.2.2))))
def vWoopVy (k : Axes) (o d : Fin 3 → F) (v : Fin w → Fin 3 → F) : Lane w :=
  vsub (vsub (vcomp v k.2.1) (vbroadcast (o k.2.1)))
    (vmul (vbroadcast (woopSy k d))
      (vsub (vcomp v k.2.2) (vbroadcast (o k.2.2))))
def vWoopVz (k : Axes) (o : Fin 3 → F) (v : Fin w → Fin 3 → F) : Lane w :=
  vsub (vcomp v k.2.2) (vbroadcast (o k.2.2))

/-- Lane-wise 2D edge function. -/
def vEdge (px py qx qy : Lane w) : Lane w :=
  vsub (vmul px qy) (vmul py qx)

def vWoopU (k : Axes) (o d : Fin 3 → F) (v0 v1 v2 : Fin w → Fin 3 → F) : Lane w :=
  vEdge (vWoopVx k o d v2) (vWoopVy k o d v2) (vWoopVx k o d v1) (vWoopVy k o d v1)
def vWoopV (k : Axes) (o d : Fin 3 → F) (v0 v1 v2 : Fin w → Fin 3 → F) : Lane w :=
  vEdge (vWoopVx k o d v0) (vWoopVy k o d v0) (vWoopVx k o d v2) (vWoopVy k o d v2)
def vWoopW (k : Axes) (o d : Fin 3 → F) (v0 v1 v2 : Fin w → Fin 3 → F) : Lane w :=
  vEdge (vWoopVx k o d v1) (vWoopVy k o d v1) (vWoopVx k o d v0) (vWoopVy k o d v0)
def vWoopDet (k : Axes) (o d : Fin 3 → F) (v0 v1 v2 : Fin w → Fin 3 → F) : Lane w :=
  vadd (vadd (vWoopU k o d v0 v1 v2) (vWoopV k o d v0 v1 v2))
    (vWoopW k o d v0 v1 v2)

/-- The Woop `t` numerator/denominator, lane-wise (`woopT`'s order). -/
def vWoopT (k : Axes) (o d : Fin 3 → F) (v0 v1 v2 : Fin w → Fin 3 → F) : Lane w :=
  vdiv (vadd (vadd (vmul (vWoopU k o d v0 v1 v2)
        (vmul (vbroadcast (woopSz k d)) (vWoopVz k o v0)))
      (vmul (vWoopV k o d v0 v1 v2)
        (vmul (vbroadcast (woopSz k d)) (vWoopVz k o v1))))
      (vmul (vWoopW k o d v0 v1 v2)
        (vmul (vbroadcast (woopSz k d)) (vWoopVz k o v2))))
    (vWoopDet k o d v0 v1 v2)

/-- The three rejection masks of `woopK`, lane-wise. -/
def vRej1 (k : Axes) (o d : Fin 3 → F) (v0 v1 v2 : Fin w → Fin 3 → F) : Mask w :=
  vand (vor (vor (vlt (vWoopU k o d v0 v1 v2) (vconst zero))
              (vlt (vWoopV k o d v0 v1 v2) (vconst zero)))
          (vlt (vWoopW k o d v0 v1 v2) (vconst zero)))
    (vor (vor (vlt (vconst zero) (vWoopU k o d v0 v1 v2))
              (vlt (vconst zero) (vWoopV k o d v0 v1 v2)))
          (vlt (vconst zero) (vWoopW k o d v0 v1 v2)))
def vRej2 (k : Axes) (o d : Fin 3 → F) (v0 v1 v2 : Fin w → Fin 3 → F) : Mask w :=
  veq (vWoopDet k o d v0 v1 v2) (vconst zero)
def vRej3 (k : Axes) (o d : Fin 3 → F) (v0 v1 v2 : Fin w → Fin 3 → F)
    (tmin tbest : F) : Mask w :=
  vnot (vand (vle (vconst tmin) (vWoopT k o d v0 v1 v2))
    (vlt (vWoopT k o d v0 v1 v2) (vconst tbest)))

/-- The per-lane Woop test: exactly `Ref.woopK`, evaluated independently in
    each lane. -/
def vWoopK (k : Axes) (o d : Fin 3 → F) (v0 v1 v2 : Fin w → Fin 3 → F)
    (tmin tbest : F) : Fin w → Option (F × F × F) := fun i =>
  if vRej1 k o d v0 v1 v2 i then none
  else if vRej2 k o d v0 v1 v2 i then none
  else if vRej3 k o d v0 v1 v2 tmin tbest i then none
  else some (vWoopT k o d v0 v1 v2 i,
    vdiv (vWoopV k o d v0 v1 v2) (vWoopDet k o d v0 v1 v2) i,
    vdiv (vWoopW k o d v0 v1 v2) (vWoopDet k o d v0 v1 v2) i)

/-- **Per-lane refinement**: the vector kernel's lane `i` is the scalar
    reference kernel on lane `i`'s vertices. This is definitional: the model
    fixes the scalar operation order (no FMA, no reassociation), so this
    theorem is the statement that the SIMD leaf's arithmetic is the scalar
    arithmetic, not a numerical approximation to it. -/
theorem vWoopK_lane (k : Axes) (o d : Fin 3 → F) (v0 v1 v2 : Fin w → Fin 3 → F)
    (tmin tbest : F) (i : Fin w) :
    vWoopK k o d v0 v1 v2 tmin tbest i = woopK k o d (v0 i) (v1 i) (v2 i) tmin tbest :=
  rfl

/-- The block driver's state: `(t, u, v, prim)` of the current best. -/
abbrev Best (α : Type) := F × F × F × α

/-- One lane of the C driver: keep the lane's hit when its `t` is strictly
    smaller than the current best (`tri_woop8_block`'s `T[l] < bt`). -/
def bstep {α : Type} (s : Best α) (lane : Option (F × F × F)) (id : α) : Best α :=
  match lane with
  | none => s
  | some (t, u, v) => if ltBits t s.1 then (t, u, v, id) else s

/-- The C driver's fold over the block's lanes: `NO_HIT` slots are skipped. -/
def blockBest {α : Type} [DecidableEq α] (s0 : Best α) (ids : Fin w → α) (noHit : α)
    (lane : Fin w → Option (F × F × F)) : Best α :=
  (List.finRange w).foldl
    (fun s i => if ids i = noHit then s else bstep s (lane i) (ids i)) s0

/-- One driver step either leaves the state alone or installs the lane's
    reported `(t, u, v)` together with the lane's id. -/
theorem bstep_sound {α : Type} (s : Best α) (lane : Option (F × F × F)) (id : α) :
    bstep s lane id = s ∨
      (lane = some ((bstep s lane id).1, (bstep s lane id).2.1, (bstep s lane id).2.2.1) ∧
        (bstep s lane id).2.2.2 = id) := by
  unfold bstep
  cases lane with
  | none => exact Or.inl rfl
  | some x =>
    obtain ⟨t, u, v⟩ := x
    by_cases h : ltBits t s.1
    · exact Or.inr ⟨by simp [h], by simp [h]⟩
    · exact Or.inl (by simp [h])

/-- **Block-selection soundness**: the driver's fold either leaves the
    caller's best unchanged, or reports a real lane hit (a non-`NO_HIT` id
    with that lane's `(t, u, v)`). Combined with `vWoopK_lane` this says the
    block result is the scalar Woop test of one of the block's lanes. -/
theorem blockBest_sound {α : Type} [DecidableEq α] (s0 : Best α) (ids : Fin w → α)
    (noHit : α) (lane : Fin w → Option (F × F × F)) :
    let s := blockBest s0 ids noHit lane
    s = s0 ∨ ∃ i, ids i ≠ noHit ∧ lane i = some (s.1, s.2.1, s.2.2.1) ∧
      s.2.2.2 = ids i := by
  unfold blockBest
  suffices H : ∀ (l : List (Fin w)) (s : Best α),
      (l.foldl (fun s i => if ids i = noHit then s else bstep s (lane i) (ids i)) s = s) ∨
        ∃ i ∈ l, ids i ≠ noHit ∧
          lane i = some ((l.foldl (fun s i => if ids i = noHit then s else
            bstep s (lane i) (ids i)) s).1,
            (l.foldl (fun s i => if ids i = noHit then s else
              bstep s (lane i) (ids i)) s).2.1,
            (l.foldl (fun s i => if ids i = noHit then s else
              bstep s (lane i) (ids i)) s).2.2.1) ∧
          (l.foldl (fun s i => if ids i = noHit then s else
            bstep s (lane i) (ids i)) s).2.2.2 = ids i by
    simpa using H (List.finRange w) s0
  intro l
  induction l with
  | nil => intro s; exact Or.inl (by simp)
  | cons i is ih =>
    intro s
    simp only [List.foldl_cons]
    set s' := (if ids i = noHit then s else bstep s (lane i) (ids i)) with hs'
    have ih' := ih s'
    rcases ih' with h | ⟨j, hj, hlt⟩
    · -- the rest of the fold did not move
      rw [h]
      by_cases hni : ids i = noHit
      · exact Or.inl (by rw [hs', if_pos hni])
      · rw [hs', if_neg hni]
        rcases bstep_sound s (lane i) (ids i) with heq | ⟨hl, hid⟩
        · exact Or.inl heq
        · exact Or.inr ⟨i, List.mem_cons_self, hni, hl, hid⟩
    · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hlt⟩

/-- An all-padding block leaves the caller's best unchanged. -/
theorem blockBest_all_skip {α : Type} [DecidableEq α] (s0 : Best α) (ids : Fin w → α)
    (noHit : α) (lane : Fin w → Option (F × F × F)) (h : ∀ i, ids i = noHit) :
    blockBest s0 ids noHit lane = s0 := by
  unfold blockBest
  suffices H : ∀ (l : List (Fin w)) (s : Best α), (∀ i ∈ l, ids i = noHit) →
      l.foldl (fun s i => if ids i = noHit then s else bstep s (lane i) (ids i)) s = s by
    exact H _ _ (fun i _ => h i)
  intro l
  induction l with
  | nil => intro s _; simp
  | cons i is ih =>
    intro s hs
    simp only [List.foldl_cons, if_pos (hs i (List.mem_cons_self))]
    exact ih s (fun j hj => hs j (List.mem_cons_of_mem _ hj))


/-- **Block-level refinement**: if the block driver reports lane id `jid`
    (a change from the caller's best), then some lane with that id passes the
    scalar Woop test with exactly the reported `(t, u, v)`. This composes
    `blockBest_sound` with `vWoopK_lane`; it is the model-level statement that
    the SIMD block returns the scalar leaf's answer for one of its lanes. -/
theorem blockBest_woop {α : Type} [DecidableEq α] (s0 : Best α) (ids : Fin w → α)
    (noHit : α) (blk : Fin w → Fin 3 → Fin 3 → F) (o d : Fin 3 → F)
    (tmin tbest : F) {t u v : F} {jid : α}
    (h : blockBest s0 ids noHit
      (vWoopK (woopAxes d) o d (fun i => blk i 0) (fun i => blk i 1)
        (fun i => blk i 2) tmin tbest) = (t, u, v, jid))
    (hne : jid ≠ s0.2.2.2) :
    ∃ i, ids i = jid ∧ woop o d (blk i 0) (blk i 1) (blk i 2) tmin tbest = some (t, u, v) := by
  have hs := blockBest_sound s0 ids noHit
    (vWoopK (woopAxes d) o d (fun i => blk i 0) (fun i => blk i 1) (fun i => blk i 2) tmin tbest)
  rw [h] at hs
  rcases hs with heq | ⟨i, hni, hl, hidj⟩
  · exfalso
    exact hne (by simpa using congrArg (fun s : Best α => s.2.2.2) heq)
  · refine ⟨i, hidj.symm, ?_⟩
    have : vWoopK (woopAxes d) o d (fun i => blk i 0) (fun i => blk i 1)
        (fun i => blk i 2) tmin tbest i = some (t, u, v) := hl
    rwa [vWoopK_lane] at this
end LightRT.C.Ref
