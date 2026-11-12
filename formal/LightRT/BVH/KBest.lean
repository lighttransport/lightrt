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

/-! ### The k-th value and the k-smallest specification -/

/-- The value order on primitives paired with their hit parameter. -/
abbrev R (a b : α × T) : Prop := a.2 ≤ b.2

theorem pairwise_mono {l : List (α × T)} (hs : l.Pairwise R) :
    ∀ {i j : ℕ} (hi : i < l.length) (hj : j < l.length), i ≤ j → l[i].2 ≤ l[j].2 := by
  intro i j hi hj hij
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · exact (List.pairwise_iff_getElem.1 hs i j hi hj h)
  · exact le_rfl

/-- An element present in a sorted list but not in its `k`-prefix is at least
    the `k`-th element (the prefix holds the `k` smallest). -/
theorem le_of_mem_not_mem_take {l : List (α × T)} (hs : l.Pairwise R) {z : α × T}
    (hz : z ∈ l) {k : ℕ} (h0 : 0 < k) (hkl : k ≤ l.length) (hnt : z ∉ l.take k) :
    (l[k-1]'(by omega)).2 ≤ z.2 := by
  obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.1 hz
  have hjk : ¬ j < k := by
    intro hjk
    have hjl : j < (l.take k).length := by rw [List.length_take]; omega
    apply hnt
    refine List.mem_iff_getElem.2 ⟨j, hjl, ?_⟩
    rw [List.getElem_take, hjeq]
  have hkj : k ≤ j := by omega
  have hm := pairwise_mono hs (i := k-1) (j := j) (by omega) hj (by omega)
  rwa [hjeq] at hm

/-- Inserting one element into a sorted list cannot raise the value at any
    position: the inserted element shifts the rest right. -/
theorem ins_getElem?_le (x : α × T) {buf : List (α × T)} (hs : buf.Pairwise R) :
    ∀ (tmax : T) (i : ℕ), i < buf.length →
      (((ins x buf)[i]?).map (·.2)).getD tmax ≤ ((buf[i]?).map (·.2)).getD tmax := by
  induction buf with
  | nil => intro tmax i hi; simp at hi
  | cons y ys ih =>
    intro tmax i hi
    simp only [ins]
    by_cases h : x.2 ≤ y.2
    · simp only [if_pos h]
      cases i with
      | zero => simpa using h
      | succ j =>
        have hj1 : j + 1 < (y :: ys).length := by simpa using hi
        have hjlen : j < (y :: ys).length := by omega
        have hjys : j < ys.length := by simpa using hj1
        have hm : (y :: ys)[j].2 ≤ ys[j].2 := by
          simpa using pairwise_mono hs hjlen hj1 (by omega)
        simp only [List.getElem?_cons_succ]
        rw [List.getElem?_eq_getElem hjlen, List.getElem?_eq_getElem hjys]
        simpa using hm
    · simp only [if_neg h]
      cases i with
      | zero => simp
      | succ j =>
        have hj : j < ys.length := by simpa using hi
        simpa using ih hs.tail tmax j hj

/-- **The k-th value only decreases under insertion** (the prefix keeps the
    smallest `k`, so the full buffer may drop its maximum). -/
theorem prune_take_ins_le (buf : List (α × T)) (x : α × T) (hs : buf.Pairwise R)
    (k : ℕ) (hk : buf.length = k) (h0 : 0 < k) (tmax : T) :
    pruneOf k ((ins x buf).take k) tmax ≤ pruneOf k buf tmax := by
  have hlen : ((ins x buf).take k).length = k := by
    rw [List.length_take, ins_length, hk]; omega
  simp only [pruneOf]
  rw [if_pos hlen, if_pos hk, List.getLast?_eq_getElem?, List.getLast?_eq_getElem?]
  simp only [hlen, hk]
  rw [List.getElem?_take]
  have hk1 : k - 1 < k := by omega
  simp only [hk1, if_true]
  exact ins_getElem?_le x hs tmax (k - 1) (by omega)

/-- The `k`-th value of a `k`-prefix is the `k`-th entry of the source. -/
theorem prune_take_eq (l : List (α × T)) (k : ℕ) (h0 : 0 < k)
    (hk : (l.take k).length = k) (tmax : T) :
    pruneOf k (l.take k) tmax = (l[k-1]'(by
      have := hk; rw [List.length_take] at this; omega)).2 := by
  have hk1 : k - 1 < k := by omega
  have hkl : k - 1 < l.length := by
    have := hk; rw [List.length_take] at this; omega
  simp only [pruneOf]
  rw [if_pos hk, List.getLast?_eq_getElem?]
  simp only [hk]
  rw [List.getElem?_take]
  simp only [hk1, if_true]
  rw [List.getElem?_eq_getElem hkl]
  rfl

theorem mem_not_take_bound {k : ℕ} {l : List (α × T)} {z : α × T} (h0 : 0 < k) (hs : l.Pairwise R)
    (hz : z ∈ l) (hB : (l.take k).length = k) (hnt : z ∉ l.take k) (tmax : T) :
    pruneOf k (l.take k) tmax ≤ z.2 := by
  rw [prune_take_eq l k h0 hB tmax]
  exact le_of_mem_not_mem_take hs hz h0 (by rw [List.length_take] at hB; omega) hnt

/-- Fold invariant of the k-best buffer: sorted, at most `k` entries, and every
    processed element not kept is at least the `k`-th value. -/
def KInv (k : ℕ) (tmax : T) (seen buf : List (α × T)) : Prop :=
  buf.Pairwise R ∧ buf.length ≤ k ∧
    ∀ z ∈ seen, z ∉ buf → buf.length = k ∧ pruneOf k buf tmax ≤ z.2

theorem kInv_nil (k : ℕ) (tmax : T) :
    KInv (α := α) k tmax ([] : List (α × T)) ([] : List (α × T)) := by
  refine ⟨by simp, by simp, ?_⟩
  intro z hz; simp at hz

theorem kInv_step {k : ℕ} (h0 : 0 < k) (tmax : T) (seen buf : List (α × T)) (x : α × T)
    (h : KInv k tmax seen buf) :
    KInv k tmax (x :: seen) ((ins x buf).take k) := by
  obtain ⟨hs, hlen, hcomp⟩ := h
  have hBs : ((ins x buf).take k).Pairwise R :=
    List.Pairwise.take (i := k) (ins_sorted x hs)
  have hBl : ((ins x buf).take k).length ≤ k := List.length_take_le k _
  have htake_k : ∀ z : α × T, z ∈ ins x buf → z ∉ (ins x buf).take k →
      ((ins x buf).take k).length = k := by
    intro z hzL hzB
    by_contra hne
    have hlt : ((ins x buf).take k).length < k := by omega
    have hLk : (ins x buf).length ≤ k := by rw [List.length_take] at hlt; omega
    have htake : (ins x buf).take k = ins x buf := List.take_of_length_le hLk
    rw [htake] at hzB
    exact hzB hzL
  refine ⟨hBs, hBl, ?_⟩
  intro z hz hzB
  rcases List.mem_cons.1 hz with hzeq | hzseen
  · subst z
    exact ⟨htake_k x (ins_mem_self x buf) hzB,
      mem_not_take_bound h0 (ins_sorted x hs) (ins_mem_self x buf)
        (htake_k x (ins_mem_self x buf) hzB) hzB tmax⟩
  · by_cases hzbuf : z ∈ buf
    · have hzL : z ∈ ins x buf := mem_ins_of_mem x z buf hzbuf
      exact ⟨htake_k z hzL hzB,
        mem_not_take_bound h0 (ins_sorted x hs) hzL (htake_k z hzL hzB) hzB tmax⟩
    · obtain ⟨hbk, hbp⟩ := hcomp z hzseen hzbuf
      have hBk : ((ins x buf).take k).length = k := by
        rw [List.length_take, ins_length, hbk]; omega
      have hpr : pruneOf k ((ins x buf).take k) tmax ≤ pruneOf k buf tmax :=
        prune_take_ins_le buf x hs k hbk h0 tmax
      exact ⟨hBk, hpr.trans hbp⟩

theorem KInv_perm {k : ℕ} {tmax : T} {a b buf : List (α × T)}
    (h : KInv k tmax a buf) (hp : a.Perm b) : KInv k tmax b buf := by
  obtain ⟨hs, hl, hc⟩ := h
  exact ⟨hs, hl, fun z hz => hc z (hp.mem_iff.2 hz)⟩

theorem foldKInv {k : ℕ} (h0 : 0 < k) (tmax : T) (l : List (α × T)) :
    ∀ (seen buf : List (α × T)), KInv k tmax seen buf →
      KInv k tmax (l ++ seen) (l.foldl (fun b x => (ins x b).take k) buf) := by
  induction l with
  | nil => intro seen buf h; simpa using h
  | cons x xs ih =>
    intro seen buf h
    have h1 : KInv k tmax (x :: seen) ((ins x buf).take k) := kInv_step h0 tmax seen buf x h
    have h2 := ih (x :: seen) ((ins x buf).take k) h1
    have hp : (xs ++ (x :: seen)).Perm ((x :: xs) ++ seen) := by
      rw [List.cons_append]
      exact List.perm_middle
    exact KInv_perm h2 hp

theorem kbest_KInv {k : ℕ} (h0 : 0 < k) (tmax : T) (l : List (α × T)) :
    KInv k tmax l (kbest k l) := by
  have := foldKInv (α := α) (k := k) h0 tmax l
    ([] : List (α × T)) ([] : List (α × T)) (kInv_nil (α := α) k tmax)
  simpa [kbest] using this

/-- **The k-best specification**: an element omitted from `kbest k l` is at
    least the `k`-th kept value (and the buffer is full). -/
theorem kbest_omitted {k : ℕ} (h0 : 0 < k) (tmax : T) {l : List (α × T)} {z : α × T}
    (hz : z ∈ l) (hnot : z ∉ kbest k l) :
    (kbest k l).length = k ∧ pruneOf k (kbest k l) tmax ≤ z.2 :=
  (kbest_KInv h0 tmax l).2.2 z hz hnot


/-- One primitive inserted into the buffer (the C leaf test rejects
    `t >= prune_t`, so an accepted hit is strictly below the current prune). -/
def stepN (isect : α → Option T) (k : ℕ) (tmax : T) (buf : List (α × T)) (p : α) :
    List (α × T) :=
  match isect p with
  | some t => if t < pruneOf k buf tmax then (ins (p, t) buf).take k else buf
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
      runN F test isect order k f st tmax
        ((F.leafPrims blk n).foldl (stepN isect k tmax) buf)
    | .node i =>
      runN F test isect order k f
        (order ((F.children i).filterMap fun c => (test c.1 prune).map (c.2, ·)) ++ st) tmax buf

theorem mem_of_getLast? {l : List (α × T)} {z : α × T} (h : l.getLast? = some z) : z ∈ l := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 h
  exact List.mem_append_right _ (List.mem_singleton_self z)

theorem pruneOf_zero (buf : List (α × T)) (tmax : T) : pruneOf 0 buf tmax = tmax := by
  unfold pruneOf
  by_cases h : buf.length = 0
  · rw [if_pos h]
    have hb : buf = [] := List.eq_nil_of_length_eq_zero h
    subst hb; rfl
  · rw [if_neg h]

theorem pruneOf_le_tmax {k : ℕ} {buf : List (α × T)} {tmax : T}
    (h : ∀ z ∈ buf, z.2 ≤ tmax) : pruneOf k buf tmax ≤ tmax := by
  unfold pruneOf
  split_ifs with hk
  · cases hg : buf.getLast? with
    | none => simp
    | some z => simpa [hg] using h z (mem_of_getLast? hg)
  · exact le_rfl

theorem stepN_sorted (isect : α → Option T) (k : ℕ) (tmax : T) {buf : List (α × T)}
    (hs : buf.Pairwise R) (p : α) : (stepN isect k tmax buf p).Pairwise R := by
  unfold stepN
  cases hp : isect p with
  | none => simpa [hp] using hs
  | some t =>
    simp only [hp]
    by_cases hlt : t < pruneOf k buf tmax
    · rw [if_pos hlt]; exact List.Pairwise.take (i := k) (ins_sorted (p,t) hs)
    · rw [if_neg hlt]; exact hs

theorem stepN_length_le (isect : α → Option T) (k : ℕ) (tmax : T) {buf : List (α × T)}
    (hl : buf.length ≤ k) (p : α) : (stepN isect k tmax buf p).length ≤ k := by
  unfold stepN
  cases hp : isect p with
  | none => simpa [hp] using hl
  | some t =>
    simp only [hp]
    by_cases hlt : t < pruneOf k buf tmax
    · rw [if_pos hlt]; exact List.length_take_le _ _
    · rw [if_neg hlt]; exact hl

theorem stepN_values_lt (isect : α → Option T) (k : ℕ) (tmax : T) {buf : List (α × T)}
    (hv : ∀ z ∈ buf, z.2 < tmax) (hits : ∀ p t, isect p = some t → t < tmax) (p : α) :
    ∀ z ∈ stepN isect k tmax buf p, z.2 < tmax := by
  unfold stepN
  cases hp : isect p with
  | none => simpa [hp] using hv
  | some t =>
    simp only [hp]
    by_cases hlt : t < pruneOf k buf tmax
    · rw [if_pos hlt]
      intro z hz
      have hz' : z ∈ ins (p,t) buf := List.mem_of_mem_take hz
      rcases (mem_ins_iff (p,t) z buf).1 hz' with rfl | hz''
      · exact hits p t hp
      · exact hv z hz''
    · rw [if_neg hlt]; exact hv

theorem stepN_prune_le (isect : α → Option T) (k : ℕ) (tmax : T) {buf : List (α × T)}
    (hs : buf.Pairwise R) (hl : buf.length ≤ k) (hv : ∀ z ∈ buf, z.2 < tmax)
    (hits : ∀ p t, isect p = some t → t < tmax) (p : α) :
    pruneOf k (stepN isect k tmax buf p) tmax ≤ pruneOf k buf tmax := by
  rcases k with _ | k'
  · rw [pruneOf_zero, pruneOf_zero]
  · unfold stepN
    cases hp : isect p with
    | none => simp [hp]
    | some t =>
      simp only [hp]
      by_cases hlt : t < pruneOf (k'+1) buf tmax
      · rw [if_pos hlt]
        by_cases hk : buf.length = k' + 1
        · exact prune_take_ins_le buf (p,t) hs (k'+1) hk (by omega) tmax
        · have hpru : pruneOf (k'+1) buf tmax = tmax := by
            unfold pruneOf; rw [if_neg hk]
          rw [hpru]
          apply pruneOf_le_tmax
          intro z hz
          have hz' : z ∈ ins (p,t) buf := List.mem_of_mem_take hz
          rcases (mem_ins_iff (p,t) z buf).1 hz' with rfl | hz''
          · exact le_of_lt (hits p t hp)
          · exact le_of_lt (hv z hz'')
      · rw [if_neg hlt]

/-- The prune never increases along a leaf fold. -/
theorem fold_prune_le (isect : α → Option T) (k : ℕ) (tmax : T) (ps : List α) :
    ∀ buf : List (α × T), buf.Pairwise R → buf.length ≤ k → (∀ z ∈ buf, z.2 < tmax) →
      (∀ p t, isect p = some t → t < tmax) →
      pruneOf k (ps.foldl (stepN isect k tmax) buf) tmax ≤ pruneOf k buf tmax := by
  induction ps with
  | nil => intro buf _ _ _ _; simp
  | cons p ps ih =>
    intro buf hs hl hv hits
    exact (ih _ (stepN_sorted isect k tmax hs p) (stepN_length_le isect k tmax hl p)
      (stepN_values_lt isect k tmax hv hits p) hits).trans
      (stepN_prune_le isect k tmax hs hl hv hits p)

theorem fold_sortedN (isect : α → Option T) (k : ℕ) (tmax : T) (ps : List α) :
    ∀ buf, buf.Pairwise R → (ps.foldl (stepN isect k tmax) buf).Pairwise R := by
  induction ps with
  | nil => intro buf h; exact h
  | cons p ps ih => intro buf h; exact ih _ (stepN_sorted isect k tmax h p)

theorem fold_lengthN (isect : α → Option T) (k : ℕ) (tmax : T) (ps : List α) :
    ∀ buf, buf.length ≤ k → (ps.foldl (stepN isect k tmax) buf).length ≤ k := by
  induction ps with
  | nil => intro buf h; exact h
  | cons p ps ih => intro buf h; exact ih _ (stepN_length_le isect k tmax h p)

theorem fold_valuesN (isect : α → Option T) (k : ℕ) (tmax : T) (ps : List α)
    (hits : ∀ p t, isect p = some t → t < tmax) :
    ∀ buf, (∀ z ∈ buf, z.2 < tmax) → ∀ z ∈ ps.foldl (stepN isect k tmax) buf, z.2 < tmax := by
  induction ps with
  | nil =>
    intro buf h z hz
    exact h z hz
  | cons p ps ih =>
    intro buf h z hz
    exact ih (stepN isect k tmax buf p) (stepN_values_lt isect k tmax h hits p) z hz



theorem stepN_KInv {k : ℕ} (h0 : 0 < k) (isect : α → Option T) (tmax : T)
    {seen buf : List (α × T)} (hK : KInv k tmax seen buf)
    (hits : ∀ p t, isect p = some t → t < tmax) (p : α) :
    KInv k tmax (match isect p with | some t => (p, t) :: seen | none => seen)
      (stepN isect k tmax buf p) := by
  unfold stepN
  cases hp : isect p with
  | none => simpa [hp] using hK
  | some t =>
    simp only [hp]
    by_cases hlt : t < pruneOf k buf tmax
    · rw [if_pos hlt]
      exact kInv_step h0 tmax seen buf (p, t) hK
    · rw [if_neg hlt]
      obtain ⟨hs, hl, hc⟩ := hK
      refine ⟨hs, hl, ?_⟩
      intro z hz hzb
      rcases List.mem_cons.1 hz with hzeq | hzseen
      · subst z
        have hbk : buf.length = k := by
          rcases lt_or_eq_of_le hl with hlt' | heq
          · exfalso
            have hpru : pruneOf k buf tmax = tmax := by unfold pruneOf; rw [if_neg (by omega)]
            rw [hpru] at hlt
            exact (not_lt.2 (le_of_not_gt hlt)) (hits p t hp)
          · exact heq
        exact ⟨hbk, le_of_not_gt hlt⟩
      · exact hc z hzseen hzb

/-- The hit pairs of a primitive list (the order the leaf fold encounters them). -/
def hitList (isect : α → Option T) : List α → List (α × T)
  | [] => []
  | p :: ps =>
    match isect p with
    | some t => (p, t) :: hitList isect ps
    | none => hitList isect ps

theorem hitList_append (isect : α → Option T) (l1 l2 : List α) :
    hitList isect (l1 ++ l2) = hitList isect l1 ++ hitList isect l2 := by
  induction l1 with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.cons_append, hitList]
    cases hp : isect p <;> simp [hp, ih]

theorem foldN_KInv {k : ℕ} (h0 : 0 < k) (isect : α → Option T) (tmax : T) (ps : List α)
    (hits : ∀ p t, isect p = some t → t < tmax) :
    ∀ seen buf, KInv k tmax seen buf →
      KInv k tmax (hitList isect ps ++ seen) (ps.foldl (stepN isect k tmax) buf) := by
  induction ps with
  | nil => intro seen buf hK; simpa [hitList] using hK
  | cons p ps ih =>
    intro seen buf hK
    have hK1 := stepN_KInv h0 isect tmax hK hits p
    have h2 := ih _ _ hK1
    cases hp : isect p with
    | none => simpa [hitList, hp] using h2
    | some t =>
      have hp' : hitList isect (p :: ps) = (p, t) :: hitList isect ps := by simp [hitList, hp]
      simp only [hp] at h2
      rw [hp']
      refine KInv_perm h2 ?_
      simpa [List.cons_append] using
        (List.perm_middle (l₁ := hitList isect ps) (a := (p, t)) (l₂ := seen))



theorem runN_prune_le {B : Type} (F : Flat B α) (test : B → T → Option T)
    (isect : α → Option T) (order : List (CRef × T) → List (CRef × T)) (k : ℕ)
    (tmax : T) (hits : ∀ p t, isect p = some t → t < tmax) :
    ∀ (f : ℕ) (st : List (CRef × T)) (buf : List (α × T)),
      buf.Pairwise R → buf.length ≤ k → (∀ z ∈ buf, z.2 < tmax) →
      pruneOf k (runN F test isect order k f st tmax buf) tmax ≤ pruneOf k buf tmax := by
  intro f
  induction f with
  | zero => intro st buf _ _ _; rfl
  | succ f ih =>
    intro st buf hs hl hv
    match st with
    | [] => rfl
    | (r, tn) :: st =>
      simp only [runN]
      split_ifs with hskip
      · exact ih st buf hs hl hv
      · cases r with
        | leaf blk n =>
          have hs' := fold_sortedN isect k tmax (F.leafPrims blk n) buf hs
          have hl' := fold_lengthN isect k tmax (F.leafPrims blk n) buf hl
          have hv' := fold_valuesN isect k tmax (F.leafPrims blk n) hits buf hv
          exact (ih st _ hs' hl' hv').trans
            (fold_prune_le isect k tmax (F.leafPrims blk n) buf hs hl hv hits)
        | node i => exact ih _ buf hs hl hv

/-- The buffer only ever holds actual hits. -/
def BInv (isect : α → Option T) (buf : List (α × T)) : Prop :=
  ∀ x ∈ buf, isect x.1 = some x.2

theorem stepN_inv (isect : α → Option T) (k : ℕ) (tmax : T) {buf : List (α × T)}
    (hb : BInv isect buf) (p : α) : BInv isect (stepN isect k tmax buf p) := by
  unfold stepN
  cases hp : isect p with
  | none => simpa [hp] using hb
  | some t =>
    simp only [hp]
    by_cases hlt : t < pruneOf k buf tmax
    · rw [if_pos hlt]
      intro z hz
      have hz' : z ∈ ins (p, t) buf := List.mem_of_mem_take hz
      rcases (mem_ins_iff (p, t) z buf).1 hz' with rfl | hz''
      · exact hp
      · exact hb z hz''
    · rw [if_neg hlt]; exact hb

theorem foldBInv (isect : α → Option T) (k : ℕ) (tmax : T) (ps : List α) :
    ∀ buf : List (α × T), BInv isect buf → BInv isect (ps.foldl (stepN isect k tmax) buf) := by
  induction ps with
  | nil => intro buf hb; exact hb
  | cons p ps ih => intro buf hb; exact ih _ (stepN_inv isect k tmax hb p)

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
        | leaf blk n => exact ih st tmax _ (foldBInv isect k tmax (F.leafPrims blk n) buf hb)
        | node i => exact ih _ tmax buf hb

end KBest
end LightRT.BVH
