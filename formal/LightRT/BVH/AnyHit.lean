/-
  Any-hit (shadow-ray) traversal of the flat wide BVH: `lrt_tri_occluded1`.
  The node test is against the fixed segment `[tmin, tmax]` (no best-hit
  update), and the loop stops at the first leaf that contains a hit. The
  theorem: with a conservative box test, the loop answers exactly "does any
  primitive reachable from the stack hit?", for any child push order.
  SBVH form (`runAny_cover`): only per-hit coverage is needed (`goodRef`), not
  containment.
-/
import LightRT.BVH.Flat

namespace LightRT.BVH
variable {B α : Type}

namespace Flat

/-- `tri_occluded_scalar`'s loop. `test0 b`: box `b` passes the slab test
    against `[tmin, tmax]`; `hit p`: primitive `p` hits in `[tmin, tmax]`. -/
def runAny (F : Flat B α) (test0 : B → Bool) (hit : α → Bool)
    (order : List CRef → List CRef) : ℕ → List CRef → Option Bool
  | 0, _ => none
  | _ + 1, [] => some false
  | f + 1, r :: st =>
    match r with
    | .leaf blk n => if (F.leafPrims blk n).any hit then some true
        else runAny F test0 hit order f st
    | .node i => runAny F test0 hit order f
        (order (((F.children i).filter fun c => test0 c.1).map Prod.snd) ++ st)

theorem any_congr_hits {hit : α → Bool} {L₁ L₂ : List α}
    (h : ∀ p, hit p = true → (p ∈ L₁ ↔ p ∈ L₂)) : L₁.any hit = L₂.any hit := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  exact ⟨fun ⟨p, hp, hh⟩ => ⟨p, (h p hh).1 hp, hh⟩, fun ⟨p, hp, hh⟩ => ⟨p, (h p hh).2 hp, hh⟩⟩

theorem sum_filter_map_le (l : List (B × CRef)) (P : B × CRef → Bool) (g : CRef → ℕ) :
    ((l.filter P).map (g ∘ Prod.snd)).sum ≤ (l.map (g ∘ Prod.snd)).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.filter_cons]
    split_ifs <;> simp only [List.map_cons, List.sum_cons] <;> omega

/-- Generic any-hit loop correctness, parameterized by the per-node fact the
    filtered-out children satisfy (`skip`): a child the box test rejects has no
    hitting primitive below it. -/
theorem runAny_gen (F : Flat B α) (hw : F.WFidx) (test0 : B → Bool) (hit : α → Bool)
    (order : List CRef → List CRef) (hord : ∀ l, (order l).Perm l)
    (skip : ∀ i < F.nodes.length, ∀ c ∈ F.children i, test0 c.1 = false →
      ∀ p ∈ F.denRef c.2, hit p = false) :
    ∀ f (st : List CRef), (∀ r ∈ st, ∀ j, r = .node j → j < F.nodes.length) →
      (st.map F.visitsRef).sum < f →
      runAny F test0 hit order f st = some ((st.flatMap F.denRef).any hit) := by
  intro f
  induction f with
  | zero => intro st _ hf; omega
  | succ f ih =>
    intro st hv hf
    match st with
    | [] => simp [runAny]
    | r :: st =>
      have hvst : ∀ e ∈ st, ∀ j, e = .node j → j < F.nodes.length :=
        fun e he => hv e (by simp [he])
      simp only [List.map_cons, List.sum_cons] at hf
      cases r with
      | leaf blk n =>
        simp only [runAny, List.flatMap_cons, List.any_append]
        by_cases hl : (F.leafPrims blk n).any hit = true
        · simp [hl, denRef]
        · simp only [Bool.not_eq_true] at hl
          simp only [hl, Bool.false_eq_true, ite_false, denRef, Bool.false_or]
          exact ih st hvst (by have := F.visitsRef_pos (.leaf blk n); omega)
      | node i =>
        have hi := hv (.node i) (by simp) i rfl
        simp only [runAny]
        set Y := ((F.children i).filter fun c => test0 c.1).map Prod.snd with hY
        have hvY : ∀ e ∈ order Y ++ st, ∀ j, e = .node j → j < F.nodes.length := by
          intro e he j hj
          rcases List.mem_append.1 he with he | he
          · have he' := (hord Y).mem_iff.1 he
            rw [hY, List.mem_map] at he'
            obtain ⟨c, hc, hce⟩ := he'
            exact (hw.2 i hi c (List.mem_filter.1 hc).1 j (hce.trans hj)).2
          · exact hvst e he j hj
        have hden : F.denRef (.node i) = (F.children i).flatMap fun c => F.denRef c.2 := by
          show F.den i = _
          rw [den_eq]
          apply List.flatMap_congr
          intro c hc
          have := hw.2 i hi c hc
          rcases c with ⟨b, r⟩; cases r with
          | leaf blk n => rfl
          | node j => obtain ⟨h1, h2⟩ := this j rfl; simp [denRef, h1, h2]
        rw [ih _ hvY (by
          rw [List.map_append, List.sum_append, ((hord Y).map _).sum_eq]
          have hvi : F.visitsRef (.node i) = 1 + ((F.children i).map (F.visitsRef ∘ Prod.snd)).sum := by
            show F.visits i = _
            rw [visits_eq]
            congr 2
            apply List.map_congr_left
            intro c hc
            have := hw.2 i hi c hc
            rcases c with ⟨b, r⟩; cases r with
            | leaf blk n => rfl
            | node j => obtain ⟨h1, h2⟩ := this j rfl; simp [visitsRef, h1, h2]
          have := sum_filter_map_le (F.children i) (fun c => test0 c.1) F.visitsRef
          rw [hY, List.map_map]
          omega)]
        rw [List.flatMap_cons, List.flatMap_append, List.any_append, List.any_append]
        refine congrArg (fun x => some (x || (List.flatMap F.denRef st).any hit)) ?_
        apply any_congr_hits
        intro p hp
        rw [((hord Y).flatMap_right _).mem_iff, hY, hden, List.flatMap_map, List.mem_flatMap,
          List.mem_flatMap]
        constructor
        · rintro ⟨c, hc, hpc⟩; exact ⟨c, (List.mem_filter.1 hc).1, hpc⟩
        · rintro ⟨c, hc, hpc⟩
          refine ⟨c, List.mem_filter.2 ⟨hc, ?_⟩, hpc⟩
          by_contra h0
          simp only [Bool.not_eq_true] at h0
          simp [skip i hi c hc h0 p hpc] at hp

/-- **Any-hit = brute force** (containment form, non-SBVH): with `WF` and a
    box test that accepts every box containing a hitting primitive, the loop
    from the root returns whether ANY reachable primitive hits. -/
theorem runAny_root {inside : α → B → Prop} {sub : B → B → Prop} (F : Flat B α)
    (hw : F.WF inside sub) (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (test0 : B → Bool) (hit : α → Bool)
    (order : List CRef → List CRef) (hord : ∀ l, (order l).Perm l)
    (C1 : ∀ p b, inside p b → hit p = true → test0 b = true) :
    runAny F test0 hit order (F.visitsRef F.root + 1) [F.root] =
      some ((F.denRef F.root).any hit) := by
  have := runAny_gen F hw.idx test0 hit order hord (by
      intro i hi c hc h0 p hp
      cases hh : hit p
      · rfl
      · have := C1 p c.1 (den_inside hw mono i hi c hc p hp) hh
        simp [this] at h0)
    (F.visitsRef F.root + 1) [F.root]
    (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hw.1) (by simp)
  simpa using this

/-- **SBVH any-hit** (coverage form): containment is not needed, only that
    every hitting primitive has a reference whose box path passes the test,
    expressed per node as `skip`. `goodRef`-style coverage implies it. -/
theorem runAny_cover_root (F : Flat B α) (hw : F.WFidx) (test0 : B → Bool) (hit : α → Bool)
    (order : List CRef → List CRef) (hord : ∀ l, (order l).Perm l)
    (skip : ∀ i < F.nodes.length, ∀ c ∈ F.children i, test0 c.1 = false →
      ∀ p ∈ F.denRef c.2, hit p = false) :
    runAny F test0 hit order (F.visitsRef F.root + 1) [F.root] =
      some ((F.denRef F.root).any hit) := by
  have := runAny_gen F hw test0 hit order hord skip (F.visitsRef F.root + 1) [F.root]
    (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hw.1) (by simp)
  simpa using this

/-! ### Bounded stack (`TRI_STACK_SIZE`)

`tri_occluded_scalar` returns 0 ("not occluded") when the remaining stack plus
the popped node's children would exceed `TRI_STACK_SIZE`
(`if (sp + nchildren > TRI_STACK_SIZE) return 0`). `runAnyB` models that. It is proved
never to fire, so the answer is `runAny`'s, whenever the tree's
stack requirement `need root` fits. `need` is computable (the validator
checks it against `TRI_STACK_SIZE` on real trees) and order-independent:
`need i = (#children - 1) + max(1, max over children of need)`. The same
bound covers `tri_intersect_scalar`'s check, which uses the (smaller) number
of children that pass the box test. -/

/-- `tri_occluded_scalar` with the capacity check. -/
def runAnyB (F : Flat B α) (cap : ℕ) (test0 : B → Bool) (hit : α → Bool)
    (order : List CRef → List CRef) : ℕ → List CRef → Option Bool
  | 0, _ => none
  | _ + 1, [] => some false
  | f + 1, r :: st =>
    match r with
    | .leaf blk n => if (F.leafPrims blk n).any hit then some true
        else runAnyB F cap test0 hit order f st
    | .node i =>
      if cap < st.length + (F.children i).length then some false else
      runAnyB F cap test0 hit order f
        (order (((F.children i).filter fun c => test0 c.1).map Prod.snd) ++ st)

/-- Stack entries needed below node `i` (itself included). -/
def need (F : Flat B α) (i : ℕ) : ℕ :=
  ((F.children i).length - 1) + max 1 (((F.children i).attach.map fun ⟨c, _⟩ =>
    match c.2 with
    | .leaf _ _ => 1
    | .node j => if h : i < j ∧ j < F.nodes.length then F.need j else 1).foldr max 0)
termination_by F.nodes.length - i

def needRef (F : Flat B α) : CRef → ℕ
  | .leaf _ _ => 1
  | .node j => F.need j

theorem need_eq (F : Flat B α) (i : ℕ) : F.need i =
    ((F.children i).length - 1) + max 1 (((F.children i).map fun c =>
      match c.2 with
      | .leaf _ _ => 1
      | .node j => if i < j ∧ j < F.nodes.length then F.need j else 1).foldr max 0) := by
  rw [need]
  congr 3
  conv_rhs => rw [← List.attach_map_subtype_val (F.children i), List.map_map]
  rfl

theorem le_foldr_max {x : ℕ} : ∀ {l : List ℕ}, x ∈ l → x ≤ l.foldr max 0
  | _ :: _, List.Mem.head _ => le_max_left _ _
  | _ :: _, List.Mem.tail _ h => (le_foldr_max h).trans (le_max_right _ _)

/-- A child's requirement, plus the siblings that may sit above it, fits in its
    parent's requirement. -/
theorem need_child (F : Flat B α) (hw : F.WFidx) {i : ℕ} (hi : i < F.nodes.length)
    {c : B × CRef} (hc : c ∈ F.children i) :
    ((F.children i).length - 1) + F.needRef c.2 ≤ F.need i := by
  rw [need_eq]
  have hv : F.needRef c.2 ∈ (F.children i).map fun c =>
      match c.2 with
      | .leaf _ _ => 1
      | .node j => if i < j ∧ j < F.nodes.length then F.need j else 1 := by
    refine List.mem_map.2 ⟨c, hc, ?_⟩
    rcases c with ⟨b, r⟩; cases r with
    | leaf => rfl
    | node j => obtain ⟨h1, h2⟩ := hw.2 i hi _ hc j rfl; simp [needRef, h1, h2]
  have := le_foldr_max hv
  omega

theorem children_le_need (F : Flat B α) (i : ℕ) : (F.children i).length ≤ F.need i := by
  rw [need_eq]; omega

/-- Stack invariant: each entry's requirement plus the entries below it fits. -/
def Good (F : Flat B α) (cap : ℕ) : List CRef → Prop
  | [] => True
  | r :: st => st.length + F.needRef r ≤ cap ∧ Good F cap st

theorem good_append (F : Flat B α) (cap : ℕ) (st : List CRef) (hst : F.Good cap st) :
    ∀ (L : List CRef), (∀ x ∈ L, (L.length - 1) + st.length + F.needRef x ≤ cap) →
      F.Good cap (L ++ st)
  | [], _ => hst
  | x :: L, h => by
    refine ⟨?_, good_append F cap st hst L fun y hy => ?_⟩
    · have := h x (by simp)
      simp only [List.append_eq, List.length_append, List.length_cons] at this ⊢; omega
    · have := h y (by simp [hy]); simp only [List.length_cons] at this; omega

/-- **The capacity check never fires** under the invariant (in particular from
    `[root]` when `needRef root ≤ cap`): the bounded loop equals `runAny`. -/
theorem runAnyB_eq (F : Flat B α) (hw : F.WFidx) (cap : ℕ) (test0 : B → Bool) (hit : α → Bool)
    (order : List CRef → List CRef) (hord : ∀ l, (order l).Perm l) :
    ∀ f (st : List CRef), (∀ r ∈ st, ∀ j, r = .node j → j < F.nodes.length) → F.Good cap st →
      runAnyB F cap test0 hit order f st = runAny F test0 hit order f st := by
  intro f
  induction f with
  | zero => intros; rfl
  | succ f ih =>
    intro st hv hg
    match st with
    | [] => rfl
    | r :: st =>
      have hvst : ∀ e ∈ st, ∀ j, e = .node j → j < F.nodes.length :=
        fun e he => hv e (by simp [he])
      cases r with
      | leaf blk n =>
        simp only [runAnyB, runAny]
        split_ifs
        · rfl
        · exact ih st hvst hg.2
      | node i =>
        have hi := hv (.node i) (by simp) i rfl
        have hcap : ¬ cap < st.length + (F.children i).length := by
          have := children_le_need F i; have := hg.1; simp only [needRef] at this; omega
        simp only [runAnyB, runAny, hcap, ite_false]
        set Y := ((F.children i).filter fun c => test0 c.1).map Prod.snd with hY
        apply ih
        · intro e he j hj
          rcases List.mem_append.1 he with he | he
          · have he' := (hord Y).mem_iff.1 he
            rw [hY, List.mem_map] at he'
            obtain ⟨c, hc, hce⟩ := he'
            exact (hw.2 i hi c (List.mem_filter.1 hc).1 j (hce.trans hj)).2
          · exact hvst e he j hj
        · refine good_append F cap st hg.2 _ fun x hx => ?_
          have hx' := (hord Y).mem_iff.1 hx
          rw [hY, List.mem_map] at hx'
          obtain ⟨c, hc, rfl⟩ := hx'
          have hc' := (List.mem_filter.1 hc).1
          have h1 := need_child F hw hi hc'
          have h2 : (order Y).length ≤ (F.children i).length := by
            rw [(hord Y).length_eq, hY, List.length_map]; exact List.length_filter_le _ _
          have h3 := hg.1
          simp only [needRef] at h3
          omega

/-- **Root form**: if the tree's stack requirement fits in `TRI_STACK_SIZE`, the
    C any-hit loop (with its overflow `return 0`) answers exactly brute force. -/
theorem runAnyB_root {inside : α → B → Prop} {sub : B → B → Prop} (F : Flat B α)
    (hw : F.WF inside sub) (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (cap : ℕ) (hcap : F.needRef F.root ≤ cap)
    (test0 : B → Bool) (hit : α → Bool)
    (order : List CRef → List CRef) (hord : ∀ l, (order l).Perm l)
    (C1 : ∀ p b, inside p b → hit p = true → test0 b = true) :
    runAnyB F cap test0 hit order (F.visitsRef F.root + 1) [F.root] =
      some ((F.denRef F.root).any hit) := by
  rw [runAnyB_eq F hw.idx cap test0 hit order hord _ _
    (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hw.1)
    (by simp only [Good, List.length_nil, zero_add]; exact ⟨hcap, trivial⟩)]
  exact runAny_root F hw mono test0 hit order hord C1

/-! ### Bounded stack, closest hit

`tri_intersect_scalar` returns "no hit" when the remaining stack plus the
children that passed the box test would exceed `TRI_STACK_SIZE`
(`if (sp + nhit > TRI_STACK_SIZE) return 0`). `runB` models the overflow as
`none`. Under the same `need` bound as any-hit the check never fires, so the
bounded loop equals `run`, and with `run_root` / `run_exact` / `run_cover_root`
its answer is theirs. -/

/-- `tri_intersect_scalar` with the capacity check. -/
def runB {T : Type} [LinearOrder T] (F : Flat B α) (cap : ℕ) (test : B → T → Option T)
    (isect : α → Option T) (order : List (CRef × T) → List (CRef × T)) :
    ℕ → List (CRef × T) → T → Option T
  | 0, _, _ => none
  | _ + 1, [], best => some best
  | f + 1, (r, tn) :: st, best =>
    if best ≤ tn then runB F cap test isect order f st best else
    match r with
    | .leaf blk n => runB F cap test isect order f st ((F.leafPrims blk n).foldl (step isect) best)
    | .node i =>
      let Y := (F.children i).filterMap fun c => (test c.1 best).map (c.2, ·)
      if cap < st.length + Y.length then none else
      runB F cap test isect order f (order Y ++ st) best

theorem length_filterMap_le' {β γ : Type} (g : β → Option γ) (l : List β) :
    (l.filterMap g).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.filterMap_cons]; split <;> simp <;> omega

/-- **The closest-hit capacity check never fires** under the stack invariant:
    the bounded loop equals `run`. -/
theorem runB_eq {T : Type} [LinearOrder T] (F : Flat B α) (hw : F.WFidx) (cap : ℕ)
    (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l) :
    ∀ f (st : List (CRef × T)) best, (∀ e ∈ st, ∀ j, e.1 = .node j → j < F.nodes.length) →
      F.Good cap (st.map Prod.fst) →
      runB F cap test isect order f st best = run F test isect order f st best := by
  intro f
  induction f with
  | zero => intros; rfl
  | succ f ih =>
    intro st best hv hg
    match st with
    | [] => rfl
    | (r, tn) :: st =>
      have hvst : ∀ e ∈ st, ∀ j, e.1 = .node j → j < F.nodes.length :=
        fun e he => hv e (by simp [he])
      have hg2 : F.Good cap (st.map Prod.fst) := hg.2
      simp only [runB, run]
      split_ifs with hb
      · exact ih st best hvst hg2
      · cases r with
        | leaf blk n => exact ih st _ hvst hg2
        | node i =>
          have hi := hv (.node i, tn) (by simp) i rfl
          set Y := (F.children i).filterMap fun c => (test c.1 best).map (c.2, ·) with hY
          have hYmem : ∀ x ∈ Y, ∃ c ∈ F.children i, x.1 = c.2 := by
            intro x hx
            rw [hY, List.mem_filterMap] at hx
            obtain ⟨c, hc, hce⟩ := hx
            cases h : test c.1 best with
            | none => simp [h] at hce
            | some t => simp [h] at hce; exact ⟨c, hc, by rw [← hce]⟩
          have hYlen : Y.length ≤ (F.children i).length := length_filterMap_le' _ _
          have h3 := hg.1
          simp only [List.length_map, needRef] at h3
          have hcap : ¬ cap < st.length + Y.length := by
            have := children_le_need F i; omega
          show (if cap < st.length + Y.length then none else
            runB F cap test isect order f (order Y ++ st) best) = _
          rw [if_neg hcap]
          apply ih
          · intro e he j hj
            rcases List.mem_append.1 he with he | he
            · obtain ⟨c, hc, hce⟩ := hYmem e ((hord Y).mem_iff.1 he)
              exact (hw.2 i hi c hc j (hce.symm.trans hj)).2
            · exact hvst e he j hj
          · rw [List.map_append]
            refine good_append F cap _ hg2 _ fun x hx => ?_
            rw [List.mem_map] at hx
            obtain ⟨e, he, rfl⟩ := hx
            obtain ⟨c, hc, hce⟩ := hYmem e ((hord Y).mem_iff.1 he)
            have h1 := need_child F hw hi hc
            have h2 : ((order Y).map Prod.fst).length ≤ (F.children i).length := by
              rw [List.length_map, (hord Y).length_eq]; exact hYlen
            rw [hce]; simp only [List.length_map] at h2 ⊢; omega

/-- **Root form**: if the tree's stack requirement fits in `TRI_STACK_SIZE`, the
    C closest-hit loop (with its overflow `return 0`) returns `run_root`'s answer,
    the brute-force fold. -/
theorem runB_root {T : Type} [LinearOrder T] {inside : α → B → Prop} {sub : B → B → Prop}
    (F : Flat B α)
    (hw : F.WF inside sub) (mono : ∀ p b b', inside p b' → sub b' b → inside p b)
    (cap : ℕ) (hcap : F.needRef F.root ≤ cap)
    (test : B → T → Option T) (isect : α → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l)
    (C1 : ∀ p b t best, inside p b → isect p = some t → t < best → (test b best).isSome)
    (C2 : ∀ p b t best tn, test b best = some tn → inside p b → isect p = some t → t < best → tn ≤ t)
    (tmin tmax : T) (htmin : ∀ p ∈ F.denRef F.root, ∀ t, isect p = some t → tmin ≤ t) :
    runB F cap test isect order (F.visitsRef F.root + 1) [(F.root, tmin)] tmax =
      some ((F.denRef F.root).foldl (step isect) tmax) := by
  rw [runB_eq F hw.idx cap test isect order hord _ _ _
    (by intro e he; simp only [List.mem_singleton] at he; subst he; exact hw.1)
    (by simp only [List.map_cons, List.map_nil, Good, List.length_nil, zero_add]; exact ⟨hcap, trivial⟩)]
  exact run_root F hw mono test isect order hord C1 C2 tmin tmax htmin

end Flat
end LightRT.BVH
