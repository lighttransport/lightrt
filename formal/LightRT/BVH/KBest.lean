/-
  `lrt_tri_intersect_n`: the multi-hit traversal keeps an ascending buffer of up
  to `k` hits and prunes by the `k`-th best. This file starts its semantics:

  * `ins` / `kbest`: the sorted insertion buffer and the list-level k-best fold;
  * `runN` / `pruneOf`: the loop shape (buffer threaded through the stack,
    pruning by the k-th buffer value), with `runN` mirroring the C loop;
  * `runN_sound`: every hit the loop reports is a real primitive hit.

  Completeness (every hit strictly below the returned k-th is reported) and the
  k-best specification of `kbest` are the remaining pieces.
-/
import LightRT.BVH.Flat

namespace LightRT.BVH

variable {α ι : Type} {T : Type} [LinearOrder T]

namespace KBest

/-! ### Sorted insertion -/

/-- Insert `x` into a list sorted by `.2`. -/
def ins (x : α × T) : List (α × T) → List (α × T)
  | [] => [x]
  | y :: ys => if x.2 ≤ y.2 then x :: y :: ys else y :: ins x ys

theorem mem_ins_iff (x z : α × T) (l : List (α × T)) :
    z ∈ ins x l ↔ z = x ∨ z ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons y ys ih =>
    by_cases h : x.2 ≤ y.2
    · simp [ins, h, ih, or_assoc, or_left_comm, or_comm]
    · simp [ins, h, ih, or_assoc, or_left_comm, or_comm]

theorem ins_mem_self (x : α × T) (l : List (α × T)) : x ∈ ins x l :=
  (mem_ins_iff x x l).2 (Or.inl rfl)

theorem mem_ins_of_mem (x z : α × T) (l : List (α × T)) (hz : z ∈ l) : z ∈ ins x l :=
  (mem_ins_iff x z l).2 (Or.inr hz)

theorem ins_length (x : α × T) (l : List (α × T)) : (ins x l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons y ys ih => rw [ins]; by_cases h : x.2 ≤ y.2 <;> simp [h, ih]

theorem ins_sorted (x : α × T) :
    ∀ {l : List (α × T)}, l.Pairwise (fun a b => a.2 ≤ b.2) →
      (ins x l).Pairwise (fun a b => a.2 ≤ b.2)
  | [], _ => by simp [ins]
  | y :: ys, hs => by
    rw [ins]
    by_cases h : x.2 ≤ y.2
    · rw [if_pos h]
      refine List.Pairwise.cons ?_ hs
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz'
      · exact h
      · exact h.trans (List.rel_of_pairwise_cons hs hz')
    · rw [if_neg h]
      refine List.Pairwise.cons ?_ (ins_sorted x hs.tail)
      intro z hz
      rcases (mem_ins_iff x z ys).1 hz with rfl | hz'
      · exact le_of_not_ge h
      · exact List.rel_of_pairwise_cons hs hz'

/-! ### The k-best fold -/

/-- Fold a list into an ascending buffer of at most `k` entries. The C's
    duplicate-prim skip is omitted: the BVH stores each primitive once. -/
def kbest (k : ℕ) (l : List (α × T)) : List (α × T) :=
  l.foldl (fun b x => (ins x b).take k) []

theorem fold_sorted (k : ℕ) (l : List (α × T)) :
    ∀ b : List (α × T), b.Pairwise (fun a c => a.2 ≤ c.2) →
      (l.foldl (fun b x => (ins x b).take k) b).Pairwise (fun a c => a.2 ≤ c.2) := by
  induction l with
  | nil => intro b hb; exact hb
  | cons x xs ih =>
    intro b hb
    exact ih _ (List.Pairwise.take (i := k) (ins_sorted x hb))

theorem kbest_sorted (k : ℕ) (l : List (α × T)) :
    (kbest k l).Pairwise (fun a c => a.2 ≤ c.2) :=
  fold_sorted k l [] (by simp)

theorem fold_length_le (k : ℕ) (l : List (α × T)) :
    ∀ b : List (α × T), (l.foldl (fun b x => (ins x b).take k) b).length ≤ max b.length k := by
  induction l with
  | nil => intro b; simp
  | cons x xs ih =>
    intro b
    refine (ih ((ins x b).take k)).trans ?_
    have h1 : ((ins x b).take k).length ≤ k := List.length_take_le _ _
    have h2 : ((ins x b).take k).length ≤ b.length + 1 := by
      rw [List.length_take, ins_length]; omega
    omega

theorem kbest_length_le (k : ℕ) (l : List (α × T)) : (kbest k l).length ≤ k := by
  simpa [kbest] using fold_length_le k l []

theorem fold_mem (k : ℕ) (l : List (α × T)) :
    ∀ b : List (α × T), ∀ z ∈ l.foldl (fun b x => (ins x b).take k) b, z ∈ b ∨ z ∈ l := by
  induction l with
  | nil => intro b z hz; exact Or.inl hz
  | cons x xs ih =>
    intro b z hz
    rcases ih ((ins x b).take k) z hz with h | h
    · have h' : z ∈ ins x b := List.mem_of_mem_take h
      rcases (mem_ins_iff x z b).1 h' with rfl | h''
      · exact Or.inr (List.mem_cons_self)
      · exact Or.inl h''
    · exact Or.inr (List.mem_cons_of_mem x h)

theorem kbest_mem (k : ℕ) (l : List (α × T)) {z : α × T} (hz : z ∈ kbest k l) : z ∈ l :=
  (fold_mem k l [] z (by simpa [kbest] using hz)).resolve_left (by simp)

/-! ### The loop shape: pruning by the k-th buffer value -/

/-- The C's `prune_t`: the last (k-th) buffer value once the buffer is full,
    else `tmax`. -/
def pruneOf (k : ℕ) (buf : List (α × T)) (tmax : T) : T :=
  if buf.length = k then (buf.getLast?.map (·.2)).getD tmax else tmax

/-- One primitive inserted into the buffer. -/
def stepN (isect : α → Option T) (k : ℕ) (buf : List (α × T)) (p : α) : List (α × T) :=
  match isect p with
  | some t => (ins (p, t) buf).take k
  | none => buf

/-- The multi-hit traversal, mirroring `lrt_tri_intersect_n`'s loop (best-first
    stack, prune on `prune_t`, leaf fold). -/
def runN {B : Type} (F : Flat B α) (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (k : ℕ) :
    ℕ → List (CRef × T) → T → List (α × T) → List (α × T)
  | 0, _, _, buf => buf
  | _ + 1, [], _, buf => buf
  | f + 1, (r, tn) :: st, tmax, buf =>
    let prune := pruneOf k buf tmax
    if prune ≤ tn then runN F test isect order k f st tmax buf else
    match r with
    | .leaf blk n =>
      runN F test isect order k f st tmax ((F.leafPrims blk n).foldl (stepN isect k) buf)
    | .node i =>
      runN F test isect order k f
        (order ((F.children i).filterMap fun c => (test c.1 prune).map (c.2, ·)) ++ st) tmax buf

/-- The buffer only ever holds actual hits. -/
def BInv (isect : α → Option T) (buf : List (α × T)) : Prop :=
  ∀ x ∈ buf, isect x.1 = some x.2

theorem stepN_inv (isect : α → Option T) (k : ℕ) {buf : List (α × T)}
    (hb : BInv isect buf) (p : α) : BInv isect (stepN isect k buf p) := by
  unfold stepN
  cases hp : isect p with
  | none => simpa [hp] using hb
  | some t =>
    intro z hz
    have hz' : z ∈ ins (p, t) buf := List.mem_of_mem_take (by simpa [hp] using hz)
    rcases (mem_ins_iff (p, t) z buf).1 hz' with rfl | hz''
    · exact hp
    · exact hb z hz''

theorem foldBInv (isect : α → Option T) (k : ℕ) (ps : List α) :
    ∀ buf : List (α × T), BInv isect buf → BInv isect (ps.foldl (stepN isect k) buf) := by
  induction ps with
  | nil => intro buf hb; exact hb
  | cons p ps ih => intro buf hb; exact ih _ (stepN_inv isect k hb p)

/-- **Soundness of the multi-hit loop**: every reported hit is a real hit of the
    reported primitive (`isect p = some t`). -/
theorem runN_sound {B : Type} (F : Flat B α) (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (k : ℕ) :
    ∀ (f : ℕ) (st : List (CRef × T)) (tmax : T) (buf : List (α × T)),
      BInv isect buf → BInv isect (runN F test isect order k f st tmax buf) := by
  intro f
  induction f with
  | zero => intro st tmax buf hb; exact hb
  | succ f ih =>
    intro st tmax buf hb
    match st with
    | [] => exact hb
    | (r, tn) :: st =>
      simp only [runN]
      split_ifs
      · exact ih st tmax buf hb
      · cases r with
        | leaf blk n => exact ih st tmax _ (foldBInv isect k (F.leafPrims blk n) buf hb)
        | node i => exact ih _ tmax buf hb

end KBest
end LightRT.BVH
