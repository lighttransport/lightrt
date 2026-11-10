/-
  Stage 5b: the flat wide BVH of `lightrt_c_tri.c` and its stack traversal.

  `tri_intersect_scalar` walks an array of wide nodes. Each node lists children
  `(box, ref)`; a ref is an inner node index or a leaf range of primitive blocks.
  The loop pops `(ref, tnear)`, skips it if `tnear ≥ best`, intersects a leaf's
  primitives (keeping `t` only if `t < best`), or slab-tests every child of an
  inner node and pushes the hits (sorted, nearest on top).

  This file models that loop generically (box type `B`, primitive type `α`,
  parameter type `T`, any child ordering) and proves it returns exactly the
  brute-force nearest hit over all primitives reachable from the root, given
  * a LOCAL well-formedness condition `WF`, decidable for concrete data
    (child node indices increase — hence acyclic — and every child box contains
    its children's boxes / its leaf primitives), and
  * the two halves of box-test conservativity (`TestOK`).
  The fuel needed is the number of reachable entries (`visits`), so it also
  terminates.
-/
import Mathlib

namespace LightRT.BVH

/-- Child reference: an inner node index or a leaf (first block, block count). -/
inductive CRef where
  | node (i : ℕ)
  | leaf (blk n : ℕ)
  deriving DecidableEq, Repr

structure Flat (B α : Type) where
  nodes : List (List (B × CRef))
  block : ℕ → List α
  root : CRef

variable {B α T : Type}

namespace Flat

def children (F : Flat B α) (i : ℕ) : List (B × CRef) := F.nodes.getD i []

def leafPrims (F : Flat B α) (blk n : ℕ) : List α :=
  (List.range n).flatMap fun b => F.block (blk + b)

/-- Primitives reachable from node `i` (children that would break the index
    order are ignored; `WF` rules them out). -/
def den (F : Flat B α) (i : ℕ) : List α :=
  (F.children i).attach.flatMap fun ⟨c, _⟩ =>
    match c.2 with
    | .leaf blk n => F.leafPrims blk n
    | .node j => if h : i < j ∧ j < F.nodes.length then F.den j else []
termination_by F.nodes.length - i

def denRef (F : Flat B α) : CRef → List α
  | .leaf blk n => F.leafPrims blk n
  | .node j => F.den j

/-- Number of stack entries the traversal can pop below node `i` (itself included). -/
def visits (F : Flat B α) (i : ℕ) : ℕ :=
  1 + ((F.children i).attach.map fun ⟨c, _⟩ =>
    match c.2 with
    | .leaf _ _ => 1
    | .node j => if h : i < j ∧ j < F.nodes.length then F.visits j else 0).sum
termination_by F.nodes.length - i

def visitsRef (F : Flat B α) : CRef → ℕ
  | .leaf _ _ => 1
  | .node j => F.visits j

/-- Local well-formedness. `inside p b`: primitive `p` lies in box `b`;
    `sub b' b`: box `b'` is inside `b`. -/
def WF (F : Flat B α) (inside : α → B → Prop) (sub : B → B → Prop) : Prop :=
  (∀ j, F.root = .node j → j < F.nodes.length) ∧
  ∀ i < F.nodes.length, ∀ c ∈ F.children i,
    match c.2 with
    | .leaf blk n => ∀ p ∈ F.leafPrims blk n, inside p c.1
    | .node j => i < j ∧ j < F.nodes.length ∧ ∀ c' ∈ F.children j, sub c'.1 c.1

theorem den_eq (F : Flat B α) (i : ℕ) : F.den i =
    (F.children i).flatMap fun c =>
      match c.2 with
      | .leaf blk n => F.leafPrims blk n
      | .node j => if i < j ∧ j < F.nodes.length then F.den j else [] := by
  rw [den]
  conv_rhs => rw [← List.attach_map_subtype_val (F.children i), List.flatMap_map]
  congr 1

theorem visits_eq (F : Flat B α) (i : ℕ) : F.visits i =
    1 + ((F.children i).map fun c =>
      match c.2 with
      | .leaf _ _ => 1
      | .node j => if i < j ∧ j < F.nodes.length then F.visits j else 0).sum := by
  rw [visits]
  conv_rhs => rw [← List.attach_map_subtype_val (F.children i), List.map_map]
  congr 3

/-- Under `WF`, the guard is always true: `den i` is the union over children. -/
theorem den_wf {inside : α → B → Prop} {sub : B → B → Prop} {F : Flat B α}
    (hw : F.WF inside sub) {i : ℕ} (hi : i < F.nodes.length) :
    F.den i = (F.children i).flatMap fun c => F.denRef c.2 := by
  rw [den_eq]
  apply List.flatMap_congr
  intro c hc
  have := hw.2 i hi c hc
  rcases c with ⟨b, r⟩; cases r with
  | leaf blk n => rfl
  | node j => simp only at this; simp [denRef, this.1, this.2.1]

theorem visits_wf {inside : α → B → Prop} {sub : B → B → Prop} {F : Flat B α}
    (hw : F.WF inside sub) {i : ℕ} (hi : i < F.nodes.length) :
    F.visits i = 1 + ((F.children i).map fun c => F.visitsRef c.2).sum := by
  rw [visits_eq]
  congr 2
  apply List.map_congr_left
  intro c hc
  have := hw.2 i hi c hc
  rcases c with ⟨b, r⟩; cases r with
  | leaf blk n => rfl
  | node j => simp only at this; simp [visitsRef, this.1, this.2.1]

theorem visitsRef_pos (F : Flat B α) (r : CRef) : 1 ≤ F.visitsRef r := by
  cases r with
  | leaf => exact le_rfl
  | node j => simp only [visitsRef]; rw [visits_eq]; omega

/-- Global containment from the local checks. -/
theorem den_inside {inside : α → B → Prop} {sub : B → B → Prop} {F : Flat B α}
    (hw : F.WF inside sub) (mono : ∀ p b b', inside p b' → sub b' b → inside p b) :
    ∀ i, i < F.nodes.length → ∀ c ∈ F.children i, ∀ p ∈ F.denRef c.2, inside p c.1 := by
  suffices H : ∀ k i, F.nodes.length - i = k → i < F.nodes.length →
      ∀ c ∈ F.children i, ∀ p ∈ F.denRef c.2, inside p c.1 from fun i => H _ i rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hk hi c hc p hp
    have hwc := hw.2 i hi c hc
    rcases c with ⟨b, r⟩
    cases r with
    | leaf blk n => exact hwc p hp
    | node j =>
      obtain ⟨hij, hj, hsub⟩ := hwc
      simp only [denRef] at hp
      rw [den_wf hw hj, List.mem_flatMap] at hp
      obtain ⟨c', hc', hp'⟩ := hp
      exact mono p b c'.1 (ih _ (by omega) j rfl hj c' hc' p hp') (hsub c' hc')

/-! ### Executable well-formedness check -/

/-- Boolean version of `WF`, run on BVHs dumped from the C builder. -/
def checkWF (F : Flat B α) (insideB : α → B → Bool) (subB : B → B → Bool) : Bool :=
  (match F.root with
   | .node j => decide (j < F.nodes.length)
   | .leaf _ _ => true) &&
  (List.range F.nodes.length).all fun i => (F.children i).all fun c =>
    match c.2 with
    | .leaf blk n => (F.leafPrims blk n).all fun p => insideB p c.1
    | .node j => decide (i < j) && decide (j < F.nodes.length) &&
        (F.children j).all fun c' => subB c'.1 c.1

theorem checkWF_sound (F : Flat B α) (insideB : α → B → Bool) (subB : B → B → Bool)
    (h : F.checkWF insideB subB = true) :
    F.WF (fun p b => insideB p b = true) (fun a b => subB a b = true) := by
  unfold checkWF at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hr, hn⟩ := h
  refine ⟨fun j hj => ?_, fun i hi c hc => ?_⟩
  · rw [hj] at hr; simpa using hr
  · rw [List.all_eq_true] at hn
    have := hn i (List.mem_range.2 hi)
    rw [List.all_eq_true] at this
    have := this c hc
    rcases c with ⟨b, r⟩
    cases r with
    | leaf blk n => simpa [List.all_eq_true] using this
    | node j => simp [List.all_eq_true] at this; exact ⟨this.1.1, this.1.2, fun c' hc' => this.2 _ _ hc'⟩


section Traverse
variable [LinearOrder T]

/-- Leaf update of `best` (C: `if (t < best_t) best_t = t`). -/
def step (isect : α → Option T) (b : T) (p : α) : T :=
  match isect p with
  | some t => min b t
  | none => b

/-- `tri_intersect_scalar`'s loop: pop, cull on `tnear ≥ best`, leaf or push hits. -/
def run (F : Flat B α) (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) : ℕ → List (CRef × T) → T → Option T
  | 0, _, _ => none
  | _ + 1, [], best => some best
  | f + 1, (r, tn) :: st, best =>
    if best ≤ tn then run F test isect order f st best else
    match r with
    | .leaf blk n => run F test isect order f st ((F.leafPrims blk n).foldl (step isect) best)
    | .node i => run F test isect order f
        (order ((F.children i).filterMap fun c => (test c.1 best).map (c.2, ·)) ++ st) best

theorem step_comm (isect : α → Option T) (b : T) (p q : α) :
    step isect (step isect b p) q = step isect (step isect b q) p := by
  unfold step; cases hp : isect p <;> cases hq : isect q <;> simp only [min_right_comm]

theorem foldl_perm (isect : α → Option T) {l₁ l₂ : List α} (h : l₁.Perm l₂) (b : T) :
    l₁.foldl (step isect) b = l₂.foldl (step isect) b :=
  h.foldl_eq' (fun _ _ _ _ z => step_comm isect z _ _) b

theorem foldl_le (isect : α → Option T) : ∀ (ps : List α) (b : T), ps.foldl (step isect) b ≤ b
  | [], _ => le_rfl
  | p :: ps, b => by
    simp only [List.foldl_cons]
    refine (foldl_le isect ps _).trans ?_
    unfold step; cases isect p <;> simp

theorem foldl_nohit (isect : α → Option T) : ∀ (ps : List α) (b : T),
    (∀ p ∈ ps, ∀ t, isect p = some t → ¬ t < b) → ps.foldl (step isect) b = b
  | [], _, _ => rfl
  | p :: ps, b, h => by
    simp only [List.foldl_cons]
    have : step isect b p = b := by
      unfold step; cases hp : isect p with
      | none => rfl
      | some t => simpa using not_lt.1 (h p (by simp) t hp)
    rw [this]; exact foldl_nohit isect ps b (fun q hq => h q (by simp [hq]))

theorem filterMap_facts (F : Flat B α) (test : B → T → Option T) (best : T) :
    ∀ l : List (B × CRef),
      (l.filterMap fun c => (test c.1 best).map (c.2, ·)).flatMap (F.denRef ∘ Prod.fst) =
        (l.filter fun c => (test c.1 best).isSome).flatMap (F.denRef ∘ Prod.snd) ∧
      ((l.filterMap fun c => (test c.1 best).map (c.2, ·)).map (F.visitsRef ∘ Prod.fst)).sum ≤
        (l.map (F.visitsRef ∘ Prod.snd)).sum
  | [] => by simp
  | c :: l => by
    obtain ⟨h1, h2⟩ := filterMap_facts F test best l
    cases ht : test c.1 best with
    | none =>
      rw [List.filterMap_cons, ht, Option.map_none, List.filter_cons, ht]
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons]
      exact ⟨h1, by omega⟩
    | some tn =>
      rw [List.filterMap_cons, ht, Option.map_some, List.filter_cons, ht]
      simp only [Option.isSome_some, ite_true, List.flatMap_cons, List.map_cons, List.sum_cons]
      exact ⟨by rw [h1]; rfl, by simp only [Function.comp] at h2 ⊢; omega⟩

/-- **Flat BVH traversal = brute force** (with termination): with fuel above the
    number of reachable entries, the stack loop returns `best` folded over every
    primitive reachable from the stack. -/
theorem run_spec {inside : α → B → Prop} {sub : B → B → Prop} (F : Flat B α)
    (hw : F.WF inside sub) (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l)
    (C1 : ∀ p b t best, inside p b → isect p = some t → t < best → (test b best).isSome)
    (C2 : ∀ p b t best tn, test b best = some tn → inside p b → isect p = some t → t < best → tn ≤ t) :
    ∀ f (st : List (CRef × T)) best,
      (∀ e ∈ st, (∀ j, e.1 = .node j → j < F.nodes.length) ∧
        ∀ p ∈ F.denRef e.1, ∀ t, isect p = some t → t < best → e.2 ≤ t) →
      (st.map (F.visitsRef ∘ Prod.fst)).sum < f →
      run F test isect order f st best = some ((st.flatMap (F.denRef ∘ Prod.fst)).foldl (step isect) best) := by
  intro f
  induction f with
  | zero => intro st best _ hf; omega
  | succ f ih =>
    intro st best hv hf
    match st with
    | [] => simp [run]
    | (r, tn) :: st =>
      have hvst : ∀ b' ≤ best, ∀ e ∈ st, (∀ j, e.1 = .node j → j < F.nodes.length) ∧
          ∀ p ∈ F.denRef e.1, ∀ t, isect p = some t → t < b' → e.2 ≤ t := fun b' hb' e he =>
        ⟨(hv e (by simp [he])).1, fun p hp t ht hlt =>
          (hv e (by simp [he])).2 p hp t ht (lt_of_lt_of_le hlt hb')⟩
      have hr := hv (r, tn) (by simp)
      simp only [List.map_cons, List.sum_cons, Function.comp] at hf
      simp only [run, List.flatMap_cons, List.foldl_append, Function.comp]
      split_ifs with hskip
      · rw [foldl_nohit isect _ best (fun p hp t ht hlt => absurd (hr.2 p hp t ht hlt)
          (not_le.2 (lt_of_lt_of_le hlt hskip)))]
        exact ih st best (hvst best le_rfl) (by have := F.visitsRef_pos r; omega)
      · cases r with
        | leaf blk n =>
          exact ih st _ (hvst _ (foldl_le isect _ _)) (by have := F.visitsRef_pos (.leaf blk n); omega)
        | node i =>
          have hi := hr.1 i rfl
          dsimp only
          set X := (F.children i).filterMap fun c => (test c.1 best).map (c.2, ·) with hX
          obtain ⟨hX1, hX2⟩ := filterMap_facts F test best (F.children i)
          rw [← hX] at hX1 hX2
          have hvX : ∀ e ∈ order X ++ st, (∀ j, e.1 = .node j → j < F.nodes.length) ∧
              ∀ p ∈ F.denRef e.1, ∀ t, isect p = some t → t < best → e.2 ≤ t := by
            intro e he
            rcases List.mem_append.1 he with he | he
            · have he' := (hord X).mem_iff.1 he
              rw [hX, List.mem_filterMap] at he'
              obtain ⟨c, hc, hce⟩ := he'
              cases htc : test c.1 best with
              | none => simp [htc] at hce
              | some tn' =>
                simp only [htc, Option.map_some, Option.some.injEq] at hce
                subst hce
                refine ⟨fun j hj => ?_, fun p hp t ht hlt =>
                  C2 p c.1 t best tn' htc (den_inside hw mono i hi c hc p hp) ht hlt⟩
                have := hw.2 i hi c hc
                rcases c with ⟨b, r⟩; simp only at hj; subst hj; exact this.2.1
            · exact hvst best le_rfl e he
          set P : B × CRef → Bool := fun c => (test c.1 best).isSome with hP
          have hsplit : (F.denRef (.node i)).Perm
              (((F.children i).filter P).flatMap (F.denRef ∘ Prod.snd) ++
                ((F.children i).filter (fun c => !P c)).flatMap (F.denRef ∘ Prod.snd)) := by
            rw [← List.flatMap_append, show F.denRef (.node i) = F.den i from rfl, den_wf hw hi]
            exact (List.filter_append_perm P (F.children i)).symm.flatMap_right _
          have hmiss : ∀ p ∈ ((F.children i).filter (fun c => !P c)).flatMap (F.denRef ∘ Prod.snd),
              ∀ t, isect p = some t → ¬ t < best := by
            intro p hp t ht hlt
            rw [List.mem_flatMap] at hp
            obtain ⟨c, hc, hp⟩ := hp
            rw [List.mem_filter] at hc
            have := C1 p c.1 t best (den_inside hw mono i hi c hc.1 p hp) ht hlt
            simp [hP, this] at hc
          have E : ((order X ++ st).flatMap (F.denRef ∘ Prod.fst)).foldl (step isect) best =
              (F.denRef (.node i) ++ st.flatMap (F.denRef ∘ Prod.fst)).foldl (step isect) best := by
            rw [List.flatMap_append, foldl_perm isect (((hord X).flatMap_right _).append_right _), hX1,
              foldl_perm isect (hsplit.append_right _), List.foldl_append, List.foldl_append,
              List.foldl_append,
              foldl_nohit isect _ _ (fun p hp t ht hlt => hmiss p hp t ht
                (lt_of_lt_of_le hlt (foldl_le isect _ _)))]
          rw [ih _ best hvX (by
            rw [List.map_append, List.sum_append, ((hord X).map _).sum_eq]
            rw [show F.visitsRef (.node i) = F.visits i from rfl, visits_wf hw hi] at hf
            simp only [Function.comp_def] at hX2 hf ⊢; omega), E, List.foldl_append]

/-- **Root form.** Starting `tri_intersect_scalar`'s loop from `(root, tmin)` with
    `best = tmax`, fuel `visitsRef root + 1` suffices, and the result is the
    brute-force fold over every primitive reachable from the root. -/
theorem run_root {inside : α → B → Prop} {sub : B → B → Prop} (F : Flat B α)
    (hw : F.WF inside sub) (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l)
    (C1 : ∀ p b t best, inside p b → isect p = some t → t < best → (test b best).isSome)
    (C2 : ∀ p b t best tn, test b best = some tn → inside p b → isect p = some t → t < best → tn ≤ t)
    (tmin tmax : T) (htmin : ∀ p ∈ F.denRef F.root, ∀ t, isect p = some t → tmin ≤ t) :
    run F test isect order (F.visitsRef F.root + 1) [(F.root, tmin)] tmax =
      some ((F.denRef F.root).foldl (step isect) tmax) := by
  have := run_spec F hw mono test isect order hord C1 C2 (F.visitsRef F.root + 1)
    [(F.root, tmin)] tmax (by
      intro e he; simp only [List.mem_singleton] at he; subst he
      exact ⟨hw.1, fun p hp t ht _ => htmin p hp t ht⟩) (by simp)
  simpa using this

/-- **Exact-nearest mode** (`-DLRT_TRI_EXACT_NEAREST`): the box test ignores the
    current best (`test0` against `tmax`) and children are pushed with
    `tnear = tmin`. Then C2 holds trivially and the loop returns EXACTLY the
    brute-force nearest hit, needing only containment (`WF`) and conservativity
    of `test0` for hits below `tmax`. -/
theorem run_exact {inside : α → B → Prop} {sub : B → B → Prop} (F : Flat B α)
    (hw : F.WF inside sub) (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (test0 : B → Bool) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l)
    (tmin tmax : T)
    (hrange : ∀ p t, isect p = some t → tmin ≤ t ∧ t < tmax)
    (C1 : ∀ p b t, inside p b → isect p = some t → test0 b = true) :
    run F (fun b _ => if test0 b then some tmin else none) isect order
        (F.visitsRef F.root + 1) [(F.root, tmin)] tmax =
      some ((F.denRef F.root).foldl (step isect) tmax) := by
  refine run_root F hw mono _ isect order hord ?_ ?_ tmin tmax
    (fun p _ t ht => (hrange p t ht).1)
  · intro p b t best hin ht _
    simp [C1 p b t hin ht]
  · intro p b t best tn htn hin ht _
    have := C1 p b t hin ht
    simp only [this, ite_true, Option.some.injEq] at htn
    exact htn ▸ (hrange p t ht).1

/-! ### Approximate culling: `tnear` may exceed the hit `t` by a slack `g` -/

theorem le_foldl_iff (isect : α → Option T) (x : T) : ∀ (l : List α) (b : T),
    x ≤ l.foldl (step isect) b ↔ x ≤ b ∧ ∀ p ∈ l, ∀ t, isect p = some t → x ≤ t
  | [], b => by simp
  | p :: l, b => by
    rw [List.foldl_cons, le_foldl_iff isect x l]
    unfold step
    cases hp : isect p with
    | none => simp [hp]
    | some t => simp [hp, le_min_iff, and_assoc]

theorem foldl_le_hit (isect : α → Option T) (l : List α) (b : T) {p : α} (hp : p ∈ l) {t : T}
    (ht : isect p = some t) : l.foldl (step isect) b ≤ t :=
  ((le_foldl_iff isect _ l b).1 le_rfl).2 p hp t ht

/-- **Approximately nearest.** If the box test is conservative (`C1`) and its
    `tnear` exceeds any enclosed hit `t` by at most the slack `g t` (`C2g`), the
    traversal returns `r` with `brute ≤ r ≤ best` and `r ≤ g t` for every hit
    `t < best`: the hit returned is at most `g` farther than the nearest one. -/
theorem run_approx {inside : α → B → Prop} {sub : B → B → Prop} (F : Flat B α)
    (hw : F.WF inside sub) (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l)
    (g : T → T) (hg : ∀ t, t ≤ g t)
    (C1 : ∀ p b t best, inside p b → isect p = some t → t < best → (test b best).isSome)
    (C2g : ∀ p b t best tn, test b best = some tn → inside p b → isect p = some t → t < best →
      tn ≤ g t) :
    ∀ f (st : List (CRef × T)) best,
      (∀ e ∈ st, (∀ j, e.1 = .node j → j < F.nodes.length) ∧
        ∀ p ∈ F.denRef e.1, ∀ t, isect p = some t → t < best → e.2 ≤ g t) →
      (st.map (F.visitsRef ∘ Prod.fst)).sum < f →
      ∃ r, run F test isect order f st best = some r ∧
        (st.flatMap (F.denRef ∘ Prod.fst)).foldl (step isect) best ≤ r ∧ r ≤ best ∧
        ∀ p ∈ st.flatMap (F.denRef ∘ Prod.fst), ∀ t, isect p = some t → t < best → r ≤ g t := by
  intro f
  induction f with
  | zero => intro st best _ hf; omega
  | succ f ih =>
    intro st best hv hf
    match st with
    | [] => exact ⟨best, by simp [run], by simp, le_rfl, by simp⟩
    | (r0, tn) :: st =>
      have hvst : ∀ b' ≤ best, ∀ e ∈ st, (∀ j, e.1 = .node j → j < F.nodes.length) ∧
          ∀ p ∈ F.denRef e.1, ∀ t, isect p = some t → t < b' → e.2 ≤ g t := fun b' hb' e he =>
        ⟨(hv e (by simp [he])).1, fun p hp t ht hlt =>
          (hv e (by simp [he])).2 p hp t ht (lt_of_lt_of_le hlt hb')⟩
      have hr := hv (r0, tn) (by simp)
      simp only [List.map_cons, List.sum_cons, Function.comp] at hf
      simp only [run, List.flatMap_cons, List.mem_append]
      split_ifs with hskip
      · obtain ⟨r, hrun, ha, hb, hc⟩ := ih st best (hvst best le_rfl)
          (by have := F.visitsRef_pos r0; omega)
        refine ⟨r, hrun, ?_, hb, ?_⟩
        · rw [List.foldl_append]
          exact le_trans ((le_foldl_iff isect _ _ _).2 ⟨(foldl_le isect _ _).trans (foldl_le isect _ _),
            fun p hp t ht => foldl_le_hit isect _ _ hp ht⟩) ha
        · rintro p (hp | hp) t ht hlt
          · exact hb.trans (hskip.trans (hr.2 p hp t ht hlt))
          · exact hc p hp t ht hlt
      · cases r0 with
        | leaf blk n =>
          set b' := (F.leafPrims blk n).foldl (step isect) best
          have hb' : b' ≤ best := foldl_le isect _ _
          obtain ⟨r, hrun, ha, hb, hc⟩ := ih st b' (hvst _ hb')
            (by have := F.visitsRef_pos (.leaf blk n); omega)
          refine ⟨r, hrun, by rw [List.foldl_append]; exact ha, hb.trans hb', ?_⟩
          rintro p (hp | hp) t ht hlt
          · exact hb.trans ((foldl_le_hit isect _ _ hp ht).trans (hg t))
          · by_cases h : t < b'
            · exact hc p hp t ht h
            · exact hb.trans ((not_lt.1 h).trans (hg t))
        | node i =>
          have hi := hr.1 i rfl
          dsimp only
          set X := (F.children i).filterMap fun c => (test c.1 best).map (c.2, ·) with hX
          obtain ⟨hX1, hX2⟩ := filterMap_facts F test best (F.children i)
          rw [← hX] at hX1 hX2
          have hvX : ∀ e ∈ order X ++ st, (∀ j, e.1 = .node j → j < F.nodes.length) ∧
              ∀ p ∈ F.denRef e.1, ∀ t, isect p = some t → t < best → e.2 ≤ g t := by
            intro e he
            rcases List.mem_append.1 he with he | he
            · have he' := (hord X).mem_iff.1 he
              rw [hX, List.mem_filterMap] at he'
              obtain ⟨c, hc, hce⟩ := he'
              cases htc : test c.1 best with
              | none => simp [htc] at hce
              | some tn' =>
                simp only [htc, Option.map_some, Option.some.injEq] at hce
                subst hce
                refine ⟨fun j hj => ?_, fun p hp t ht hlt =>
                  C2g p c.1 t best tn' htc (den_inside hw mono i hi c hc p hp) ht hlt⟩
                have := hw.2 i hi c hc
                rcases c with ⟨b, r⟩; simp only at hj; subst hj; exact this.2.1
            · exact hvst best le_rfl e he
          obtain ⟨r, hrun, ha, hb, hc⟩ := ih _ best hvX (by
            rw [List.map_append, List.sum_append, ((hord X).map _).sum_eq]
            rw [show F.visitsRef (.node i) = F.visits i from rfl, visits_wf hw hi] at hf
            simp only [Function.comp_def] at hX2 hf ⊢; omega)
          -- prims of pushed entries are prims of node `i`
          have hpush : ∀ p, p ∈ (order X ++ st).flatMap (F.denRef ∘ Prod.fst) →
              p ∈ F.denRef (.node i) ∨ p ∈ st.flatMap (F.denRef ∘ Prod.fst) := by
            intro p hp
            rw [List.flatMap_append, List.mem_append] at hp
            rcases hp with hp | hp
            · left
              rw [((hord X).flatMap_right _).mem_iff, hX1, List.mem_flatMap] at hp
              obtain ⟨c, hc, hp⟩ := hp
              rw [show F.denRef (.node i) = F.den i from rfl, den_wf hw hi, List.mem_flatMap]
              exact ⟨c, (List.mem_filter.1 hc).1, hp⟩
            · exact Or.inr hp
          refine ⟨r, hrun, ?_, hb, ?_⟩
          · refine le_trans ?_ ha
            rw [le_foldl_iff]
            have h0 := (le_foldl_iff isect
              ((F.denRef (.node i) ++ st.flatMap (F.denRef ∘ Prod.fst)).foldl (step isect) best)
              (F.denRef (.node i) ++ st.flatMap (F.denRef ∘ Prod.fst)) best).1 le_rfl
            rw [List.foldl_append] at h0 ⊢
            refine ⟨h0.1, fun p hp t ht => h0.2 p ?_ t ht⟩
            exact List.mem_append.2 (hpush p hp)
          · rintro p (hp | hp) t ht hlt
            · -- `p` lies under some child `c`; `C1` forces `c` to be pushed
              change p ∈ F.denRef (.node i) at hp
              rw [show F.denRef (.node i) = F.den i from rfl, den_wf hw hi, List.mem_flatMap] at hp
              obtain ⟨c, hcm, hp⟩ := hp
              have hs := C1 p c.1 t best (den_inside hw mono i hi c hcm p hp) ht hlt
              obtain ⟨tn', htn⟩ := Option.isSome_iff_exists.1 hs
              apply hc p _ t ht hlt
              rw [List.flatMap_append, List.mem_append]; left
              rw [((hord X).flatMap_right _).mem_iff, hX1, List.mem_flatMap]
              exact ⟨c, List.mem_filter.2 ⟨hcm, by simp [htn]⟩, hp⟩
            · exact hc p (by rw [List.flatMap_append]; exact List.mem_append_right _ hp) t ht hlt

end Traverse

/-! ### Spatial-split BVHs (SBVH): coverage instead of containment

An SBVH leaf box is CLIPPED: it may cover only part of a triangle referenced in
it, so `WF`'s containment fails by design. What the traversal needs instead,
for the ray at hand, is COVERAGE: every primitive hit by the ray has at least
one reference whose whole box path contains the hit point (`hitIn p b`). -/

/-- Only the index part of `WF` (child node indices increase, are in range). -/
def WFidx (F : Flat B α) : Prop :=
  (∀ j, F.root = .node j → j < F.nodes.length) ∧
  ∀ i < F.nodes.length, ∀ c ∈ F.children i, ∀ j, c.2 = .node j → i < j ∧ j < F.nodes.length

theorem WF.idx {inside : α → B → Prop} {sub : B → B → Prop} {F : Flat B α}
    (hw : F.WF inside sub) : F.WFidx := by
  refine ⟨hw.1, fun i hi c hc j hj => ?_⟩
  have := hw.2 i hi c hc
  rcases c with ⟨b, r⟩; simp only at hj; subst hj; exact ⟨this.1, this.2.1⟩

theorem den_wfi {F : Flat B α} (hw : F.WFidx) {i : ℕ} (hi : i < F.nodes.length) :
    F.den i = (F.children i).flatMap fun c => F.denRef c.2 := by
  rw [den_eq]
  apply List.flatMap_congr
  intro c hc
  rcases c with ⟨b, r⟩; cases r with
  | leaf blk n => rfl
  | node j => have := hw.2 i hi _ hc j rfl; simp [denRef, this.1, this.2]

theorem visits_wfi {F : Flat B α} (hw : F.WFidx) {i : ℕ} (hi : i < F.nodes.length) :
    F.visits i = 1 + ((F.children i).map fun c => F.visitsRef c.2).sum := by
  rw [visits_eq]
  congr 2
  apply List.map_congr_left
  intro c hc
  rcases c with ⟨b, r⟩; cases r with
  | leaf blk n => rfl
  | node j => have := hw.2 i hi _ hc j rfl; simp [visitsRef, this.1, this.2]

/-- `p` has a reference below node `i` whose box path contains its hit point. -/
def goodN (F : Flat B α) (hitIn : α → B → Prop) (p : α) (i : ℕ) : Prop :=
  ∃ c ∈ (F.children i).attach, hitIn p c.1.1 ∧
    match c.1.2 with
    | .leaf blk n => p ∈ F.leafPrims blk n
    | .node j => if h : i < j ∧ j < F.nodes.length then F.goodN hitIn p j else False
termination_by F.nodes.length - i

def goodRef (F : Flat B α) (hitIn : α → B → Prop) (p : α) : CRef → Prop
  | .leaf blk n => p ∈ F.leafPrims blk n
  | .node j => F.goodN hitIn p j

theorem goodN_iff {F : Flat B α} (hw : F.WFidx) (hitIn : α → B → Prop) (p : α) {i : ℕ}
    (hi : i < F.nodes.length) :
    F.goodN hitIn p i ↔ ∃ c ∈ F.children i, hitIn p c.1 ∧ F.goodRef hitIn p c.2 := by
  rw [goodN]
  constructor
  · rintro ⟨⟨c, hc⟩, -, h1, h2⟩
    refine ⟨c, hc, h1, ?_⟩
    rcases c with ⟨b, r⟩; cases r with
    | leaf blk n => exact h2
    | node j =>
      have := hw.2 i hi _ hc j rfl
      simp only [this.1, this.2, and_self, dite_true] at h2; exact h2
  · rintro ⟨c, hc, h1, h2⟩
    refine ⟨⟨c, hc⟩, List.mem_attach _ _, h1, ?_⟩
    rcases c with ⟨b, r⟩; cases r with
    | leaf blk n => exact h2
    | node j =>
      have := hw.2 i hi _ hc j rfl
      simp only [this.1, this.2, and_self, dite_true]; exact h2

section Cover
variable [LinearOrder T]

/-- **SBVH traversal (coverage form).** With box tests conservative for hit
    POINTS (`C1`: a box containing the hit point of a hit `t < best` passes;
    `C2g`: its `tnear ≤ g t`), the loop terminates with `r` such that
    `brute ≤ r ≤ best`, and `r ≤ g t` for every hit `t < best` of a primitive
    that has a good reference on the stack. -/
theorem run_cover (F : Flat B α) (hw : F.WFidx) (hitIn : α → B → Prop)
    (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l)
    (g : T → T) (hg : ∀ t, t ≤ g t)
    (C1 : ∀ p b t best, hitIn p b → isect p = some t → t < best → (test b best).isSome)
    (C2g : ∀ p b t best tn, test b best = some tn → hitIn p b → isect p = some t → t < best →
      tn ≤ g t) :
    ∀ f (st : List (CRef × T)) best,
      (∀ e ∈ st, ∀ j, e.1 = .node j → j < F.nodes.length) →
      (st.map (F.visitsRef ∘ Prod.fst)).sum < f →
      ∃ r, run F test isect order f st best = some r ∧
        (st.flatMap (F.denRef ∘ Prod.fst)).foldl (step isect) best ≤ r ∧ r ≤ best ∧
        ∀ p t, isect p = some t → t < best →
          (∃ e ∈ st, F.goodRef hitIn p e.1 ∧ e.2 ≤ g t) → r ≤ g t := by
  intro f
  induction f with
  | zero => intro st best _ hf; omega
  | succ f ih =>
    intro st best hv hf
    match st with
    | [] => exact ⟨best, by simp [run], by simp, le_rfl, by simp⟩
    | (r0, tn) :: st =>
      have hvst : ∀ e ∈ st, ∀ j, e.1 = .node j → j < F.nodes.length :=
        fun e he => hv e (by simp [he])
      have hr := hv (r0, tn) (by simp)
      simp only [List.map_cons, List.sum_cons, Function.comp] at hf
      simp only [run, List.flatMap_cons]
      split_ifs with hskip
      · obtain ⟨r, hrun, ha, hb, hc⟩ := ih st best hvst (by have := F.visitsRef_pos r0; omega)
        refine ⟨r, hrun, ?_, hb, ?_⟩
        · rw [List.foldl_append]
          exact le_trans ((le_foldl_iff isect _ _ _).2 ⟨(foldl_le isect _ _).trans (foldl_le isect _ _),
            fun p hp t ht => foldl_le_hit isect _ _ hp ht⟩) ha
        · rintro p t ht hlt ⟨e, he, hg1, hg2⟩
          rcases List.mem_cons.1 he with rfl | he
          · exact hb.trans (hskip.trans hg2)
          · exact hc p t ht hlt ⟨e, he, hg1, hg2⟩
      · cases r0 with
        | leaf blk n =>
          set b' := (F.leafPrims blk n).foldl (step isect) best
          have hb' : b' ≤ best := foldl_le isect _ _
          obtain ⟨r, hrun, ha, hb, hc⟩ := ih st b' hvst
            (by have := F.visitsRef_pos (.leaf blk n); omega)
          refine ⟨r, hrun, by rw [List.foldl_append]; exact ha, hb.trans hb', ?_⟩
          rintro p t ht hlt ⟨e, he, hg1, hg2⟩
          rcases List.mem_cons.1 he with rfl | he
          · exact hb.trans ((foldl_le_hit isect _ _ (show p ∈ F.leafPrims blk n from hg1) ht).trans (hg t))
          · by_cases h : t < b'
            · exact hc p t ht h ⟨e, he, hg1, hg2⟩
            · exact hb.trans ((not_lt.1 h).trans (hg t))
        | node i =>
          have hi := hr i rfl
          dsimp only
          set X := (F.children i).filterMap fun c => (test c.1 best).map (c.2, ·) with hX
          obtain ⟨hX1, hX2⟩ := filterMap_facts F test best (F.children i)
          rw [← hX] at hX1 hX2
          have hmemX : ∀ e ∈ X, ∃ c ∈ F.children i, test c.1 best = some e.2 ∧ e.1 = c.2 := by
            intro e he
            rw [hX, List.mem_filterMap] at he
            obtain ⟨c, hc, hce⟩ := he
            cases htc : test c.1 best with
            | none => simp [htc] at hce
            | some tn' =>
              simp only [htc, Option.map_some, Option.some.injEq] at hce
              exact ⟨c, hc, by rw [← hce]; exact htc, by rw [← hce]⟩
          have hvX : ∀ e ∈ order X ++ st, ∀ j, e.1 = .node j → j < F.nodes.length := by
            intro e he j hj
            rcases List.mem_append.1 he with he | he
            · obtain ⟨c, hc, -, hce⟩ := hmemX e ((hord X).mem_iff.1 he)
              exact (hw.2 i hi c hc j (hce ▸ hj)).2
            · exact hvst e he j hj
          obtain ⟨r, hrun, ha, hb, hc⟩ := ih _ best hvX (by
            rw [List.map_append, List.sum_append, ((hord X).map _).sum_eq]
            rw [show F.visitsRef (.node i) = F.visits i from rfl, visits_wfi hw hi] at hf
            simp only [Function.comp_def] at hX2 hf ⊢; omega)
          have hpush : ∀ p, p ∈ (order X ++ st).flatMap (F.denRef ∘ Prod.fst) →
              p ∈ F.denRef (.node i) ∨ p ∈ st.flatMap (F.denRef ∘ Prod.fst) := by
            intro p hp
            rw [List.flatMap_append, List.mem_append] at hp
            rcases hp with hp | hp
            · left
              rw [((hord X).flatMap_right _).mem_iff, hX1, List.mem_flatMap] at hp
              obtain ⟨c, hc, hp⟩ := hp
              rw [show F.denRef (.node i) = F.den i from rfl, den_wfi hw hi, List.mem_flatMap]
              exact ⟨c, (List.mem_filter.1 hc).1, hp⟩
            · exact Or.inr hp
          refine ⟨r, hrun, ?_, hb, ?_⟩
          · refine le_trans ?_ ha
            rw [le_foldl_iff]
            have h0 := (le_foldl_iff isect
              ((F.denRef (.node i) ++ st.flatMap (F.denRef ∘ Prod.fst)).foldl (step isect) best)
              (F.denRef (.node i) ++ st.flatMap (F.denRef ∘ Prod.fst)) best).1 le_rfl
            rw [List.foldl_append] at h0 ⊢
            exact ⟨h0.1, fun p hp t ht => h0.2 p (List.mem_append.2 (hpush p hp)) t ht⟩
          · rintro p t ht hlt ⟨e, he, hg1, hg2⟩
            rcases List.mem_cons.1 he with rfl | he
            · -- the good path continues through some child `c` that the box test passes
              obtain ⟨c, hcm, hin, hgc⟩ := (goodN_iff hw hitIn p hi).1 hg1
              obtain ⟨tn', htn⟩ := Option.isSome_iff_exists.1 (C1 p c.1 t best hin ht hlt)
              apply hc p t ht hlt
              refine ⟨(c.2, tn'), List.mem_append_left _ ((hord X).mem_iff.2 ?_), hgc,
                C2g p c.1 t best tn' htn hin ht hlt⟩
              rw [hX, List.mem_filterMap]
              exact ⟨c, hcm, by simp [htn]⟩
            · exact hc p t ht hlt ⟨e, List.mem_append_right _ he, hg1, hg2⟩

/-- **SBVH root form.** If every primitive the ray hits below `tmax` has a good
    reference (coverage) and `tmin ≤ g t`, the result is within `g` of the
    brute-force nearest hit: `brute ≤ r` and `r ≤ g t` for every hit `t < tmax`.
    With `g = id` it is exactly the brute-force nearest hit. -/
theorem run_cover_root (F : Flat B α) (hw : F.WFidx) (hitIn : α → B → Prop)
    (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l)
    (g : T → T) (hg : ∀ t, t ≤ g t)
    (C1 : ∀ p b t best, hitIn p b → isect p = some t → t < best → (test b best).isSome)
    (C2g : ∀ p b t best tn, test b best = some tn → hitIn p b → isect p = some t → t < best →
      tn ≤ g t)
    (tmin tmax : T)
    (hcov : ∀ p t, isect p = some t → t < tmax → F.goodRef hitIn p F.root ∧ tmin ≤ g t) :
    ∃ r, run F test isect order (F.visitsRef F.root + 1) [(F.root, tmin)] tmax = some r ∧
      (F.denRef F.root).foldl (step isect) tmax ≤ r ∧ r ≤ tmax ∧
      ∀ p t, isect p = some t → t < tmax → r ≤ g t := by
  obtain ⟨r, h1, h2, h3, h4⟩ := run_cover F hw hitIn test isect order hord g hg C1 C2g
    (F.visitsRef F.root + 1) [(F.root, tmin)] tmax
    (by intro e he; simp only [List.mem_singleton] at he; subst he; exact hw.1) (by simp)
  refine ⟨r, h1, by simpa using h2, h3, fun p t ht hlt => h4 p t ht hlt ?_⟩
  exact ⟨(F.root, tmin), by simp, (hcov p t ht hlt).1, (hcov p t ht hlt).2⟩

end Cover

end Flat
end LightRT.BVH
