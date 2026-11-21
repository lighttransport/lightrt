/-
  BVH region-query traversal: the stack loop of `tri_query_region` over a
  `Flat` tree, proved equal to the brute-force filter over `Flat.denRef`.
  Soundness and completeness follow from that equality. The key hypothesis is
  `WF` containment plus `boxMayOverlap_mono`: a child box that fails the region
  test cannot contain a primitive whose bound overlaps the region.
-/
import LightRT.BVH.Flat
import LightRT.Geom.Region

namespace LightRT.BVH
open LightRT.Geom Flat
noncomputable section

/-- Bool form of the region test (classical decidability). -/
def boxMayOverlapDec (R : Region) (b : Box) : Bool := by
  classical exact decide (boxMayOverlap R b)

theorem boxMayOverlapDec_eq (R : Region) (b : Box) :
    boxMayOverlapDec R b = true ↔ boxMayOverlap R b := by
  by_cases h : boxMayOverlap R b <;> simp [boxMayOverlapDec, h]

variable {α : Type}

namespace RegionQuery

/-- Stack entry: a ref together with the child box that admitted it. -/
abbrev Entry := CRef × Box

/-- The C `tri_query_region` loop. -/
def runRegion (F : Flat Box α) (bound : α → Box) (R : Region) :
    ℕ → List Entry → List α → List α
  | 0, _, out => out
  | _ + 1, [], out => out
  | f + 1, (r, _) :: st, out =>
    match r with
    | .leaf blk n =>
        runRegion F bound R f st
          (out ++ (F.leafPrims blk n).filter (fun p => boxMayOverlapDec R (bound p)))
    | .node i =>
        runRegion F bound R f
          (((F.children i).filter (fun c => boxMayOverlapDec R c.1)).map (fun c => (c.2, c.1)) ++ st)
          out

/-- Containment of reachable primitives, from `Flat.den_inside`. -/
theorem WF.den_subset {bound : α → Box} {F : Flat Box α}
    (hw : F.WF (fun p b => (bound p).Subset b) Box.Subset) :
    ∀ i (hi : i < F.nodes.length), ∀ c ∈ F.children i,
      ∀ p ∈ F.denRef c.2, (bound p).Subset c.1 :=
  Flat.den_inside hw (fun _ _ _ h1 h2 => h1.trans h2)

/-- If a child box fails the region test, none of its reachable primitives has
    an overlapping bound (by conservativity). -/
theorem not_overlap_den {bound : α → Box} {F : Flat Box α} {R : Region}
    (hw : F.WF (fun p b => (bound p).Subset b) Box.Subset) :
    ∀ i (hi : i < F.nodes.length), ∀ c ∈ F.children i,
      ¬ boxMayOverlap R c.1 → ∀ p ∈ F.denRef c.2, ¬ boxMayOverlap R (bound p) := by
  intro i hi c hc hno p hp hov
  exact hno (boxMayOverlap_mono (WF.den_subset hw i hi c hc p hp) hov)

/-- Filtering the admitted children's refs is the same as filtering all
    children's refs: rejected children contribute no overlapping primitive. -/
theorem filter_admitted {bound : α → Box} {F : Flat Box α} {R : Region}
    (hw : F.WF (fun p b => (bound p).Subset b) Box.Subset) :
    ∀ (l : List (Box × CRef)),
      (∀ c ∈ l, ∀ j, c.2 = .node j → j < F.nodes.length) →
      (∀ c ∈ l, (∀ j, c.2 = .node j → j < F.nodes.length) →
        ¬ boxMayOverlap R c.1 → ∀ p ∈ F.denRef c.2, ¬ boxMayOverlap R (bound p)) →
      ((l.filter (fun c => boxMayOverlapDec R c.1)).flatMap (fun c => F.denRef c.2)).filter
          (fun p => boxMayOverlapDec R (bound p)) =
        (l.flatMap (fun c => F.denRef c.2)).filter (fun p => boxMayOverlapDec R (bound p)) := by
  intro l
  induction l with
  | nil => simp
  | cons c l ih =>
    intro hidx hno
    have hidx_c : ∀ j, c.2 = .node j → j < F.nodes.length := hidx c (by simp)
    have hno_c : ¬ boxMayOverlap R c.1 → ∀ p ∈ F.denRef c.2, ¬ boxMayOverlap R (bound p) :=
      hno c (by simp) hidx_c
    have hidx_l : ∀ c' ∈ l, ∀ j, c'.2 = .node j → j < F.nodes.length := by
      intro c' hc' j hj; exact hidx c' (by simp [hc']) j hj
    have hno_l : ∀ c' ∈ l, (∀ j, c'.2 = .node j → j < F.nodes.length) →
        ¬ boxMayOverlap R c'.1 → ∀ p ∈ F.denRef c'.2, ¬ boxMayOverlap R (bound p) := by
      intro c' hc' hj; exact hno c' (by simp [hc']) hj
    by_cases hov : boxMayOverlapDec R c.1 = true
    · simp [hov, ih hidx_l hno_l]
    · have hnov : ¬ boxMayOverlap R c.1 := by
        intro h; exact hov ((boxMayOverlapDec_eq R c.1).2 h)
      have hzero : (F.denRef c.2).filter (fun p => boxMayOverlapDec R (bound p)) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro p hp
        have hp' := List.mem_filter.1 hp
        exact (hno_c hnov p hp'.1) ((boxMayOverlapDec_eq R (bound p)).1 hp'.2)
      simp [hov, hzero, ih hidx_l hno_l]

/-- `flatMap` over a mapped list. -/
theorem flatMap_map' {β γ δ : Type} (f : γ → List δ) (g : β → γ) :
    ∀ l : List β, List.flatMap f (l.map g) = l.flatMap (fun c => f (g c))
  | [] => rfl
  | c :: l => by simp [flatMap_map' f g l]

/-- The loop equals the brute-force filtered denotation. -/
theorem runRegion_spec {bound : α → Box} {F : Flat Box α} {R : Region}
    (hw : F.WF (fun p b => (bound p).Subset b) Box.Subset) :
    ∀ f (st : List Entry) out,
      (∀ e ∈ st, ∀ j, e.1 = .node j → j < F.nodes.length) →
      (st.map (fun e => F.visitsRef e.1)).sum < f →
      runRegion F bound R f st out =
        out ++ (st.flatMap (fun e => F.denRef e.1)).filter (fun p => boxMayOverlapDec R (bound p)) := by
  intro f
  induction f with
  | zero => intro st out _ hf; omega
  | succ f ih =>
    intro st out hst hf
    match st with
    | [] => simp [runRegion]
    | (r, b) :: st =>
      have hst' : ∀ e ∈ st, ∀ j, e.1 = .node j → j < F.nodes.length := by
        intro e he j hj; exact hst e (by simp [he]) j hj
      cases r with
      | leaf blk n =>
        have hfuel : (st.map (fun e => F.visitsRef e.1)).sum < f := by
          change (1 + (st.map (fun e => F.visitsRef e.1)).sum) < f + 1 at hf
          omega
        simp only [runRegion]
        rw [ih st (out ++ (F.leafPrims blk n).filter (fun p => boxMayOverlapDec R (bound p))) hst' hfuel]
        simpa [List.filter_append, List.append_assoc, Flat.denRef]
      | node i =>
        have hi : i < F.nodes.length := hst (.node i, b) (by simp) i rfl
        let newst : List Entry :=
          ((F.children i).filter (fun c => boxMayOverlapDec R c.1)).map (fun c => (c.2, c.1)) ++ st
        have hnewst : ∀ e ∈ newst, ∀ j, e.1 = .node j → j < F.nodes.length := by
          intro e he j hj
          change e ∈ (((F.children i).filter (fun c => boxMayOverlapDec R c.1)).map
              (fun c => (c.2, c.1)) ++ st) at he
          rcases List.mem_append.1 he with he | he
          · rcases List.mem_map.1 he with ⟨c, hc, rfl⟩
            have hc' := (List.mem_filter.1 hc).1
            rcases c with ⟨bb, rr⟩
            have hwc := hw.2 i hi (bb, rr) hc'
            cases rr with
            | leaf _ _ => cases hj
            | node j0 =>
                injection hj with h
                subst j
                exact hwc.2.1
          · exact hst' e he j hj
        have hno : ∀ c ∈ F.children i,
            (∀ j, c.2 = .node j → j < F.nodes.length) →
            ¬ boxMayOverlap R c.1 → ∀ p ∈ F.denRef c.2, ¬ boxMayOverlap R (bound p) := by
          intro c hc hj hno
          exact not_overlap_den hw i hi c hc hno
        have hv := Flat.visits_wfi (Flat.WF.idx hw) hi
        have hfuel : (newst.map (fun e => F.visitsRef e.1)).sum < f := by
          have hsum : (((F.children i).filter (fun c => boxMayOverlapDec R c.1)).map
                (fun c => F.visitsRef c.2)).sum ≤
              ((F.children i).map fun c => F.visitsRef c.2).sum := by
            induction F.children i with
            | nil => simp
            | cons c l ih =>
                by_cases h : boxMayOverlapDec R c.1 = true
                · simpa [h] using ih
                · simpa [h] using ih.trans (Nat.le_add_left _ (F.visitsRef c.2))
          have hle : (newst.map (fun e => F.visitsRef e.1)).sum ≤
              ((F.children i).map fun c => F.visitsRef c.2).sum +
                (st.map (fun e => F.visitsRef e.1)).sum := by
            dsimp [newst]
            simp only [List.map_append, List.map_map, Function.comp_apply, List.sum_append]
            exact Nat.add_le_add_right hsum _
          change F.visits i + (st.map (fun e => F.visitsRef e.1)).sum < f + 1 at hf
          rw [hv] at hf
          change (1 + ((F.children i).map fun c => F.visitsRef c.2).sum +
            (st.map (fun e => F.visitsRef e.1)).sum) < f + 1 at hf
          omega
        simp only [runRegion]
        rw [ih newst out hnewst hfuel]
        congr 1
        have hnm : newst.flatMap (fun e => F.denRef e.1) =
            ((F.children i).filter (fun c => boxMayOverlapDec R c.1)).flatMap
                (fun c => F.denRef c.2) ++ st.flatMap (fun e => F.denRef e.1) := by
          dsimp [newst]
          rw [List.flatMap_append]
          congr 1
          exact flatMap_map' (fun e : Entry => F.denRef e.1) (fun c : Box × CRef => (c.2, c.1))
            ((F.children i).filter (fun c => boxMayOverlapDec R c.1))
        rw [hnm]
        rw [List.filter_append]
        have hfilt := filter_admitted hw (F.children i)
          (by intro c hc j hj; rcases c with ⟨bb,rr⟩; simp only at hj;
              have hwc := hw.2 i hi (bb,rr) hc
              cases rr with
              | leaf _ _ => cases hj
              | node j0 =>
                  injection hj with h
                  subst j
                  exact hwc.2.1)
          (by intro c hc hj; exact hno c hc hj)
        rw [hfilt]
        simp only [List.flatMap_cons]
        rw [show F.denRef (CRef.node i) = F.den i from rfl]
        rw [Flat.den_wfi (Flat.WF.idx hw) hi]
        rw [List.filter_append]

/-- Soundness: every reported primitive's bound overlaps the region. -/
theorem runRegion_sound {bound : α → Box} {F : Flat Box α} {R : Region}
    (hw : F.WF (fun p b => (bound p).Subset b) Box.Subset) :
    ∀ f st out, (∀ e ∈ st, ∀ j, e.1 = .node j → j < F.nodes.length) →
      (st.map (fun e => F.visitsRef e.1)).sum < f →
      ∀ p ∈ runRegion F bound R f st out,
        p ∈ out ∨ (∃ e ∈ st, p ∈ F.denRef e.1) ∧ boxMayOverlap R (bound p) := by
  intro f st out hst hf p hp
  rw [runRegion_spec hw f st out hst hf] at hp
  rcases List.mem_append.1 hp with hp | hp
  · exact Or.inl hp
  · have hp' := List.mem_filter.1 hp
    right
    constructor
    · rcases List.mem_flatMap.1 hp'.1 with ⟨e, he, hpden⟩
      exact ⟨e, he, hpden⟩
    · exact (boxMayOverlapDec_eq R (bound p)).1 hp'.2

/-- Completeness: every reachable overlapping primitive is reported. -/
theorem runRegion_complete {bound : α → Box} {F : Flat Box α} {R : Region}
    (hw : F.WF (fun p b => (bound p).Subset b) Box.Subset) :
    ∀ f st out, (∀ e ∈ st, ∀ j, e.1 = .node j → j < F.nodes.length) →
      (st.map (fun e => F.visitsRef e.1)).sum < f →
      ∀ p ∈ st.flatMap (fun e => F.denRef e.1), boxMayOverlap R (bound p) →
        p ∈ runRegion F bound R f st out := by
  intro f st out hst hf p hp hpov
  rw [runRegion_spec hw f st out hst hf]
  apply List.mem_append_right
  apply List.mem_filter.2
  exact ⟨hp, (boxMayOverlapDec_eq R (bound p)).2 hpov⟩

end RegionQuery
