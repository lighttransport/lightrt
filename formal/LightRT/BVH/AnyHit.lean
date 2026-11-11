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

end Flat
end LightRT.BVH
