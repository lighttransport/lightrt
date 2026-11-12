/-
  `lrt_tri_intersect_n`: the multi-hit traversal keeps an ascending buffer of up
  to `k` hits and prunes by the `k`-th best. This file starts its semantics:

  * `ins` / `kbest`: the sorted insertion buffer and the list-level k-best fold;
  * `runN` / `pruneOf`: the loop shape (buffer threaded through the stack,
    pruning by the k-th buffer value), with `runN` mirroring the C loop;
  * `runN_sound`: every hit the loop reports is a real primitive hit;
  * `kbest_omitted` / `KInv`: the k-best-by-value specification (the k-th
    buffer value is nonincreasing under insertion; an omitted element is at
    least the k-th kept value);
  * `runN_complete`: every hit of the root's primitives strictly below the
    returned k-th value is reported (no false misses), under the same C1/C2
    and `WF` hypotheses as `Flat.run_root`.
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

theorem KInv_add_ge {k : ℕ} {tmax : T} {seen buf extra : List (α × T)}
    (hK : KInv k tmax seen buf)
    (h : ∀ z ∈ extra, z ∉ buf → buf.length = k ∧ pruneOf k buf tmax ≤ z.2) :
    KInv k tmax (extra ++ seen) buf := by
  obtain ⟨hs, hl, hc⟩ := hK
  refine ⟨hs, hl, ?_⟩
  intro z hz hzb
  rcases List.mem_append.1 hz with hz | hz
  · exact h z hz hzb
  · exact hc z hz hzb

theorem mem_hitList {isect : α → Option T} {ps : List α} {x : α × T} :
    x ∈ hitList isect ps ↔ x.1 ∈ ps ∧ isect x.1 = some x.2 := by
  induction ps with
  | nil => simp [hitList]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := x
    cases hp : isect p with
    | none =>
      simp only [hitList, hp]
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨List.mem_cons_of_mem p h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases List.mem_cons.1 h1 with rfl | h1
        · rw [hp] at h2; cases h2
        · exact ⟨h1, h2⟩
    | some t =>
      simp only [hitList, hp]
      constructor
      · intro hx
        rcases List.mem_cons.1 hx with hx | hx
        · cases hx; exact ⟨List.mem_cons_self, hp⟩
        · obtain ⟨h1, h2⟩ := ih.1 hx
          exact ⟨List.mem_cons_of_mem p h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases List.mem_cons.1 h1 with rfl | h1
        · rw [hp] at h2; cases h2; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih.2 ⟨h1, h2⟩)


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

theorem hitList_filterMap (isect : α → Option T) (ps : List α) :
    hitList isect ps = ps.filterMap (fun p => (isect p).map (p, ·)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [hitList, List.filterMap_cons]
    cases hp : isect p <;> simp [hp, ih]

theorem hitList_perm {isect : α → Option T} {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (hitList isect l₁).Perm (hitList isect l₂) := by
  rw [hitList_filterMap, hitList_filterMap]
  exact List.Perm.filterMap _ h

theorem runN_KInv {B : Type} (F : Flat B α) (test : B → T → Option T)
    (isect : α → Option T) (order : List (CRef × T) → List (CRef × T))
    (k : ℕ) (h0 : 0 < k) (tmax : T) (hits : ∀ p t, isect p = some t → t < tmax)
    {inside : α → B → Prop} {sub : B → B → Prop} (hw : F.WF inside sub)
    (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (C1 : ∀ p b t best, inside p b → isect p = some t → t < best → (test b best).isSome)
    (C2 : ∀ p b t best tn, test b best = some tn → inside p b → isect p = some t → t < best → tn ≤ t)
    (hord : ∀ l, (order l).Perm l) :
    ∀ (f : ℕ) (st : List (CRef × T)) (buf seen : List (α × T)),
      KInv k tmax seen buf → (∀ z ∈ buf, z.2 < tmax) →
      (∀ e ∈ st, (∀ j, e.1 = .node j → j < F.nodes.length) ∧
        ∀ p ∈ F.denRef e.1, ∀ t, isect p = some t → t < pruneOf k buf tmax → e.2 ≤ t) →
      (st.map (F.visitsRef ∘ Prod.fst)).sum < f →
      KInv k tmax (hitList isect (st.flatMap (F.denRef ∘ Prod.fst)) ++ seen)
        (runN F test isect order k f st tmax buf) := by
  intro f
  induction f with
  | zero => intro st buf seen _ _ _ hf; omega
  | succ f ih =>
    intro st buf seen hK hv hvi hf
    match st with
    | [] => simpa [runN, hitList] using hK
    | (r, tn) :: st =>
      have hr := hvi (r, tn) (by simp)
      have hvi_st : ∀ e ∈ st, (∀ j, e.1 = .node j → j < F.nodes.length) ∧
          ∀ p ∈ F.denRef e.1, ∀ t, isect p = some t → t < pruneOf k buf tmax → e.2 ≤ t :=
        fun e he => hvi e (by simp [he])
      simp only [runN]
      split_ifs with hskip
      · rw [List.flatMap_cons, hitList_append, List.append_assoc]
        -- skipped entry: its hits are all >= prune
        have hge : ∀ z ∈ hitList isect (F.denRef r), pruneOf k buf tmax ≤ z.2 := by
          intro z hz
          obtain ⟨h1, h2⟩ := mem_hitList.1 hz
          by_contra hlt
          have hlt' : z.2 < pruneOf k buf tmax := lt_of_not_ge hlt
          exact absurd (hr.2 z.1 h1 z.2 h2 hlt') (not_le.2 (lt_of_lt_of_le hlt' hskip))
        have hs := hK.1; have hl := hK.2.1
        have hpr := runN_prune_le F test isect order k tmax hits f st buf hs hl hv
        have ih' := ih st buf seen hK hv hvi_st (by
          have := F.visitsRef_pos r
          simp only [List.map_cons, List.sum_cons, Function.comp] at hf ⊢; omega)
        refine KInv_perm ?_ (List.Perm.refl _)
        refine KInv_add_ge ih' ?_
        intro z hz hzb
        obtain ⟨h1, h2⟩ := mem_hitList.1 hz
        have hzlt : z.2 < tmax := hits z.1 z.2 h2
        have hfull : (runN F test isect order k f st tmax buf).length = k := by
          by_contra hne
          have hlt : (runN F test isect order k f st tmax buf).length < k := by
            have := ih'.2.1; omega
          have hpru : pruneOf k (runN F test isect order k f st tmax buf) tmax = tmax := by
            unfold pruneOf; rw [if_neg (by omega)]
          rw [hpru] at hpr
          have hgz := hge z hz
          exact absurd (le_trans hpr hgz) (not_le.2 hzlt)
        exact ⟨hfull, le_trans hpr (hge z hz)⟩
      · cases r with
        | leaf blk n =>
          have hK' : KInv k tmax (hitList isect (F.leafPrims blk n) ++ seen)
              ((F.leafPrims blk n).foldl (stepN isect k tmax) buf) :=
            foldN_KInv h0 isect tmax (F.leafPrims blk n) hits seen buf hK
          have hv' := fold_valuesN isect k tmax (F.leafPrims blk n) hits buf hv
          have hpr := fold_prune_le isect k tmax (F.leafPrims blk n) buf hK.1 hK.2.1 hv hits
          have ih' := ih st _ (hitList isect (F.leafPrims blk n) ++ seen) hK' hv'
            (fun e he => ⟨(hvi_st e he).1, fun p hp t ht hlt =>
              (hvi_st e he).2 p hp t ht (lt_of_lt_of_le hlt hpr)⟩)
            (by simp only [List.map_cons, List.sum_cons, Function.comp, Flat.visitsRef] at hf ⊢; omega)
          rw [List.flatMap_cons, hitList_append, List.append_assoc]
          refine KInv_perm ih' ?_
          show (hitList isect (st.flatMap (F.denRef ∘ Prod.fst)) ++
                  (hitList isect (F.leafPrims blk n) ++ seen)).Perm
                (hitList isect (F.leafPrims blk n) ++
                  (hitList isect (st.flatMap (F.denRef ∘ Prod.fst)) ++ seen))
          exact (List.Perm.of_eq (List.append_assoc _ _ _).symm).trans
            ((List.perm_append_comm.append_right seen).trans
              (List.Perm.of_eq (List.append_assoc _ _ _)))
        | node i =>
          have hi : i < F.nodes.length := hr.1 i rfl
          dsimp only
          set prune := pruneOf k buf tmax with hprune
          set X := (F.children i).filterMap
            (fun c => (test c.1 prune).map (c.2, ·)) with hX
          obtain ⟨hX1, hX2⟩ := Flat.filterMap_facts F test prune (F.children i)
          rw [← hX] at hX1 hX2
          set P : B × CRef → Bool := fun c => (test c.1 prune).isSome with hP
          have hviX : ∀ e ∈ order X ++ st,
              (∀ j, e.1 = .node j → j < F.nodes.length) ∧
                ∀ p ∈ F.denRef e.1, ∀ t, isect p = some t →
                  t < pruneOf k buf tmax → e.2 ≤ t := by
            intro e he
            rcases List.mem_append.1 he with he | he
            · have he' := (hord X).mem_iff.1 he
              rw [hX, List.mem_filterMap] at he'
              obtain ⟨c, hc, hce⟩ := he'
              cases htc : test c.1 prune with
              | none => simp [htc] at hce
              | some tn' =>
                simp only [htc, Option.map_some, Option.some.injEq] at hce
                subst hce
                refine ⟨fun j hj => ?_, fun p hp t ht hlt =>
                  C2 p c.1 t prune tn' htc (Flat.den_inside hw mono i hi c hc p hp) ht
                    (by simpa [hprune] using hlt)⟩
                have hw2 := hw.2 i hi c hc
                rcases c with ⟨b, r⟩; simp only at hj; subst hj
                exact hw2.2.1
            · exact hvi_st e he
          have hdrop : ∀ z ∈ hitList isect
                (((F.children i).filter fun c => !P c).flatMap
                  (F.denRef ∘ Prod.snd)), prune ≤ z.2 := by
            intro z hz
            obtain ⟨h1, h2⟩ := mem_hitList.1 hz
            rw [List.mem_flatMap] at h1
            obtain ⟨c, hc, hcc⟩ := h1
            rw [List.mem_filter] at hc
            by_contra hlt
            have hlt' : z.2 < prune := lt_of_not_ge hlt
            have hc1 := C1 z.1 c.1 z.2 prune
              (Flat.den_inside hw mono i hi c hc.1 z.1 hcc) h2 (by simpa [hprune] using hlt')
            simp [hP, hc1] at hc
          have hdropSeen : KInv k tmax
              (hitList isect (((F.children i).filter fun c => !P c).flatMap
                (F.denRef ∘ Prod.snd)) ++ seen) buf := by
            refine KInv_add_ge hK ?_
            intro z hz hzb
            obtain ⟨h1, h2⟩ := mem_hitList.1 hz
            have hzlt : z.2 < tmax := hits z.1 z.2 h2
            have hge := hdrop z hz
            have hfull : buf.length = k := by
              by_contra hne
              have hlt : buf.length < k := by have := hK.2.1; omega
              have hpru : pruneOf k buf tmax = tmax := by
                unfold pruneOf; rw [if_neg (by omega)]
              have hpru' : prune = tmax := by rw [hprune]; exact hpru
              rw [hpru'] at hge
              exact absurd hge (not_le.2 hzlt)
            exact ⟨hfull, hge⟩
          have ih' := ih (order X ++ st) buf
            (hitList isect (((F.children i).filter fun c => !P c).flatMap
              (F.denRef ∘ Prod.snd)) ++ seen) hdropSeen hv hviX (by
              have hvi : F.visitsRef (.node i) =
                  1 + ((F.children i).map (F.visitsRef ∘ Prod.snd)).sum := by
                show F.visits i = _
                rw [Flat.visits_wf hw hi]
                rfl
              simp only [Function.comp_apply, List.map_cons, List.sum_cons] at hf hX2 ⊢
              rw [hvi] at hf
              rw [List.map_append, List.sum_append, ((hord X).map _).sum_eq]
              omega)
          rw [List.flatMap_cons, hitList_append, List.append_assoc]
          rw [Function.comp_apply]
          dsimp only
          rw [show F.denRef (.node i) = (F.children i).flatMap (F.denRef ∘ Prod.snd) from by
            rw [show F.denRef (.node i) = F.den i from rfl, Flat.den_wf hw hi]; rfl]
          set A := hitList isect (((F.children i).filter P).flatMap (F.denRef ∘ Prod.snd)) with hA
          set B := hitList isect
            (((F.children i).filter fun c => !P c).flatMap (F.denRef ∘ Prod.snd)) with hB
          set C := hitList isect (st.flatMap (F.denRef ∘ Prod.fst)) with hC
          set D := seen with hD
          set O := hitList isect (order X |>.flatMap (F.denRef ∘ Prod.fst)) with hO
          rw [List.flatMap_append, hitList_append] at ih'
          change KInv k tmax ((O ++ C) ++ (B ++ D))
            (runN F test isect order k f (order X ++ st) tmax buf) at ih'
          have hordX : O.Perm A := by
            have h := hitList_perm (α := α) (T := T) (isect := isect) ((hord X).flatMap_right (F.denRef ∘ Prod.fst))
            rw [hX1] at h
            exact h
          have hsplitHits : (hitList isect ((F.children i).flatMap (F.denRef ∘ Prod.snd))).Perm (A ++ B) := by
            have h := hitList_perm (α := α) (T := T) (isect := isect) ((List.filter_append_perm P (F.children i)).symm.flatMap_right
              (F.denRef ∘ Prod.snd))
            rw [List.flatMap_append, hitList_append] at h
            exact h
          have hswap : (C ++ (B ++ D)).Perm (B ++ (C ++ D)) :=
            (List.Perm.of_eq (List.append_assoc C B D).symm).trans
              ((List.perm_append_comm.append_right D).trans
                (List.Perm.of_eq (List.append_assoc B C D)))
          have ihP : ((O ++ C) ++ (B ++ D)).Perm (((A ++ B) ++ C) ++ D) := by
            have h1 : ((O ++ C) ++ (B ++ D)).Perm ((A ++ C) ++ (B ++ D)) :=
              (hordX.append_right C).append_right (B ++ D)
            have h2 : ((A ++ C) ++ (B ++ D)).Perm (((A ++ B) ++ C) ++ D) := by
              simpa [List.append_assoc] using (List.Perm.append_left A hswap)
            exact h1.trans h2
          have goalP : ((hitList isect ((F.children i).flatMap (F.denRef ∘ Prod.snd)) ++ C) ++ D).Perm
              (((A ++ B) ++ C) ++ D) :=
            (hsplitHits.append_right C).append_right D
          refine KInv_perm ih' ?_
          simpa only [List.append_assoc] using ihP.trans goalP.symm

theorem runN_complete {B : Type} (F : Flat B α) (test : B → T → Option T)
    (isect : α → Option T) (order : List (CRef × T) → List (CRef × T))
    (k : ℕ) (h0 : 0 < k) (tmax : T) (hits : ∀ p t, isect p = some t → t < tmax)
    {inside : α → B → Prop} {sub : B → B → Prop} (hw : F.WF inside sub)
    (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (C1 : ∀ p b t best, inside p b → isect p = some t → t < best → (test b best).isSome)
    (C2 : ∀ p b t best tn, test b best = some tn → inside p b → isect p = some t → t < best → tn ≤ t)
    (hord : ∀ l, (order l).Perm l)
    (tmin : T) (htmin : ∀ p ∈ F.denRef F.root, ∀ t, isect p = some t → tmin ≤ t) :
    ∀ p ∈ F.denRef F.root, ∀ t, isect p = some t → t < pruneOf k
        (runN F test isect order k (F.visitsRef F.root + 1) [(F.root, tmin)] tmax []) tmax →
      (p, t) ∈ runN F test isect order k (F.visitsRef F.root + 1) [(F.root, tmin)] tmax [] := by
  intro p hp t ht hpr
  have h := runN_KInv F test isect order k h0 tmax hits hw mono C1 C2 hord
    (F.visitsRef F.root + 1) [(F.root, tmin)] [] [] (kInv_nil (α := α) k tmax) (by simp)
    (fun e he => by
      rw [List.mem_singleton] at he; subst he
      refine ⟨fun j hj => ?_, fun q hq u hu _ => htmin q hq u hu⟩
      exact hw.1 j (by simpa using hj))
    (by simp)
  have hm : (p, t) ∈ hitList isect (F.denRef F.root) :=
    (mem_hitList (isect := isect)).2 ⟨hp, ht⟩
  by_contra hnot
  have hc := h.2.2 (p, t) (by simpa using hm) hnot
  exact absurd hc.2 (not_le.2 hpr)

end KBest
end LightRT.BVH
