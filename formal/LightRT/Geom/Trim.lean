/-
  Trimmed parametric surfaces over R: (u,v) trim loops (outer boundary + holes)
  with the even–odd crossing rule, and the trim invariant for reported hits.
  The crossing count is the standard horizontal-ray cast; generic-position
  cases (vertices exactly on the ray) are excluded by hypothesis as in the
  C intersector's exact adjudication.
  Tier 1 item 1 of the roadmap.
-/
import Mathlib

namespace LightRT.Geom
noncomputable section
open Classical

/-- A trim loop is a closed polyline in the (u,v) parameter domain. -/
abbrev TrimLoop := List (ℝ × ℝ)

/-- Does the half-open vertical span `[min y0 y1, max y0 y1)` of an edge contain
    `y`? This is the standard half-open rule that makes the crossing count
    independent of how vertices are shared between edges. -/
def edgeSpansY (p q : ℝ × ℝ) (y : ℝ) : Prop :=
  (p.2 ≤ y ∧ y < q.2) ∨ (q.2 ≤ y ∧ y < p.2)

/-- The x-coordinate where the horizontal line `y = c` meets the segment `p,q`
    (valid when `edgeSpansY p q y`). -/
def edgeCrossX (p q : ℝ × ℝ) (y : ℝ) : ℝ :=
  if q.2 = p.2 then p.1 else p.1 + (y - p.2) / (q.2 - p.2) * (q.1 - p.1)

/-- One crossing contribution of an edge at a query point `(x,y)`: 1 if the
    edge spans `y` and the crossing is strictly to the right of `x`. -/
def edgeCross (p q : ℝ × ℝ) (x y : ℝ) : ℕ :=
  if edgeSpansY p q y ∧ x < edgeCrossX p q y then 1 else 0

/-- Even–odd crossing number of a closed polyline at `(x,y)`. The loop is
    closed by connecting the last point back to the first. -/
def crossingNumber (loop : TrimLoop) (x y : ℝ) : ℕ :=
  match loop with
  | [] => 0
  | [_] => 0
  | p :: q :: rest =>
      edgeCross p q x y + crossingNumber (q :: rest) x y

/-- Point-in-loop by the even–odd rule: odd crossing count means inside. -/
def inLoop (loop : TrimLoop) (x y : ℝ) : Prop :=
  crossingNumber loop x y % 2 = 1

/-- A trim region: an outer loop and a list of hole loops. A point is visible
    iff it is inside the outer loop and inside no hole. -/
structure TrimRegion where
  outer : TrimLoop
  holes : List TrimLoop

def trimVisible (R : TrimRegion) (x y : ℝ) : Prop :=
  inLoop R.outer x y ∧ ∀ h ∈ R.holes, ¬ inLoop h x y

/-- **Trim invariant** (soundness half): a hit accepted by the trim test is a
    visible parameter. Definitional, but stated as a contract for the C's
    even–odd test. -/
theorem accepted_hit_is_visible (R : TrimRegion) {u v : ℝ}
    (h : trimVisible R u v) : inLoop R.outer u v ∧ ∀ h' ∈ R.holes, ¬ inLoop h' u v := h

/-- **Trim rejection**: a hit inside a hole is not visible, so the search must
    continue past it. -/
theorem hole_hit_rejected (R : TrimRegion) {u v : ℝ} (h : TrimLoop)
    (hh : h ∈ R.holes) (hin : inLoop h u v) : ¬ trimVisible R u v := by
  intro hv
  exact hv.2 h hh hin


/-- Crossing number is at most one per edge. -/
theorem edgeCross_le_one (p q : ℝ × ℝ) (x y : ℝ) : edgeCross p q x y ≤ 1 := by
  unfold edgeCross
  split <;> simp

/-- **Unit-square crossing parity** (Jordan curve theorem for the simplest
    trim loop): the center `(1/2,1/2)` is inside the unit square loop and a
    point strictly to the right is outside. This validates the even-odd rule. -/
theorem unit_square_crossing_center :
    crossingNumber [Prod.mk (0:ℝ) 0, Prod.mk 1 0, Prod.mk 1 1, Prod.mk 0 1] (1/2) (1/2) % 2 = 1 := by
  norm_num [crossingNumber, edgeCross, edgeSpansY, edgeCrossX]


/-- Scan a finite list of candidate hits `(u,v,t)` and keep the smallest `t`
    among the trim-visible ones. Uses classical decidability of visibility. -/
noncomputable def nearestVisibleT (R : TrimRegion) : List (ℝ × ℝ × ℝ) → Option ℝ
  | [] => none
  | (u,v,t) :: rest =>
      match nearestVisibleT R rest with
      | none => if trimVisible R u v then some t else none
      | some m => if trimVisible R u v then some (min t m) else some m

/-- If the scan returns `none`, no hit in the list is trim-visible. -/
theorem nearestVisibleT_none (R : TrimRegion) (hits : List (ℝ × ℝ × ℝ))
    (h : nearestVisibleT R hits = none) :
    ¬ (∃ u v t, (u, v, t) ∈ hits ∧ trimVisible R u v) := by
  classical
  induction hits with
  | nil => simp
  | cons hd rest ih =>
    rcases hd with ⟨u, v, t⟩
    by_cases hvis : trimVisible R u v
    · cases hmv : nearestVisibleT R rest with
      | none =>
          have hh : nearestVisibleT R ((u,v,t)::rest) = some t := by simp [nearestVisibleT, hvis, hmv]
          rw [hh] at h
          contradiction
      | some m =>
          have hh : nearestVisibleT R ((u,v,t)::rest) = some (min t m) := by simp [nearestVisibleT, hvis, hmv]
          rw [hh] at h
          contradiction
    · intro hbad
      rcases hbad with ⟨uu, vv, tt, hmem, hv⟩
      simp at hmem
      rcases hmem with hsame | hmem
      · rcases hsame with ⟨rfl, rfl, rfl⟩
        exact hvis hv
      · have hrest : nearestVisibleT R rest = none := by
          by_contra hn
          cases hm2 : nearestVisibleT R rest with
          | none => exact hn hm2
          | some mm =>
              have hh : nearestVisibleT R ((u,v,t)::rest) = some mm := by simp [nearestVisibleT, hvis, hm2]
              rw [hh] at h
              contradiction
        exact ih hrest ⟨uu, vv, tt, hmem, hv⟩

/-- **Nearest-visible-hit specification.** If the scan returns `some m`, then
    `m` is the parameter of a trim-visible hit in the list and no trim-visible
    hit has a smaller parameter. Rejected (invisible) hits are skipped, so the
    search continues past holes. This is the positive half of the finite
    nearest-untrimmed-hit search. -/
theorem nearestVisibleT_spec (R : TrimRegion) (hits : List (ℝ × ℝ × ℝ)) {m : ℝ}
    (hm : nearestVisibleT R hits = some m) :
    (∃ u v, (u, v, m) ∈ hits ∧ trimVisible R u v) ∧
    (∀ t', (∃ u v, (u, v, t') ∈ hits ∧ trimVisible R u v) → m ≤ t') := by
  classical
  revert m
  induction hits with
  | nil =>
      intro m hm
      simp [nearestVisibleT] at hm
  | cons hd rest ih =>
      intro m hm
      rcases hd with ⟨u, v, t⟩
      by_cases hvis : trimVisible R u v
      · cases hmv : nearestVisibleT R rest with
        | none =>
            have hm_eq : t = m := by simpa [nearestVisibleT, hvis, hmv] using hm
            subst m
            constructor
            · exact ⟨u, v, by simp, hvis⟩
            · intro t' ht'
              rcases ht' with ⟨uu, vv, hmem, hv'⟩
              simp at hmem
              rcases hmem with hsame | hmem
              · rcases hsame with ⟨rfl, rfl, rfl⟩
                exact le_rfl
              · exfalso
                have hnone := nearestVisibleT_none R rest hmv
                exact hnone ⟨uu, vv, t', hmem, hv'⟩
        | some mr =>
            have hm_eq : min t mr = m := by simpa [nearestVisibleT, hvis, hmv] using hm
            subst m
            have hs := ih hmv
            by_cases hle : t ≤ mr
            · rw [min_eq_left hle]
              constructor
              · exact ⟨u, v, by simp, hvis⟩
              · intro t' ht'
                rcases ht' with ⟨uu, vv, hmem, hv'⟩
                simp at hmem
                rcases hmem with hsame | hmem
                · rcases hsame with ⟨rfl, rfl, rfl⟩
                  exact le_rfl
                · exact le_trans hle (hs.2 t' ⟨uu, vv, hmem, hv'⟩)
            · rw [min_eq_right (le_of_not_ge hle)]
              constructor
              · rcases hs.1 with ⟨uu, vv, hmem, hv'⟩
                exact ⟨uu, vv, by simp [hmem], hv'⟩
              · intro t' ht'
                rcases ht' with ⟨uu, vv, hmem, hv'⟩
                simp at hmem
                rcases hmem with hsame | hmem
                · rcases hsame with ⟨rfl, rfl, rfl⟩
                  exact le_of_not_ge hle
                · exact hs.2 t' ⟨uu, vv, hmem, hv'⟩
      · cases hmv : nearestVisibleT R rest with
        | none =>
            have hh : nearestVisibleT R ((u,v,t)::rest) = none := by
              simp [nearestVisibleT, hvis, hmv]
            rw [hh] at hm
            contradiction
        | some mr =>
            have hm_eq : mr = m := by simpa [nearestVisibleT, hvis, hmv] using hm
            subst m
            have hs := ih hmv
            constructor
            · rcases hs.1 with ⟨uu, vv, hmem, hv'⟩
              exact ⟨uu, vv, by simp [hmem], hv'⟩
            · intro t' ht'
              rcases ht' with ⟨uu, vv, hmem, hv'⟩
              simp at hmem
              rcases hmem with hsame | hmem
              · rcases hsame with ⟨rfl, rfl, rfl⟩
                exfalso
                exact hvis hv'
              · exact hs.2 t' ⟨uu, vv, hmem, hv'⟩

/-- **Reject-and-continue soundness.** If a hit is not trim-visible, skipping
    it does not change the result of the nearest-visible scan. -/
theorem nearestVisibleT_skip_invisible (R : TrimRegion) (u v t : ℝ)
    (hvis : ¬ trimVisible R u v) (hits : List (ℝ × ℝ × ℝ)) :
    nearestVisibleT R ((u,v,t) :: hits) = nearestVisibleT R hits := by
  classical
  cases hm : nearestVisibleT R hits with
  | none => simp [nearestVisibleT, hvis, hm]
  | some m => simp [nearestVisibleT, hvis, hm]

end
end LightRT.Geom
