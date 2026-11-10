/-
  Concrete instance of `Flat` for the BVH4/BVH8 triangle scenes of
  `lightrt_c_tri.c`, as dumped by `tools/bvhdump.c`:
  * a box is the 6 binary32 words `lo0 lo1 lo2 hi0 hi1 hi2` of a node child slot;
  * a primitive is a leaf slot `block*W + lane`, holding `v0, e1, e2` words.
  `insideQ` asks, in exact rational arithmetic, that the triangle the
  intersector actually tests (`v0 + u e1 + v e2`, `u,v ≥ 0`, `u+v ≤ 1`: its
  corners `v0`, `v0+e1`, `v0+e2`) lies in the box; `subQ` is box inclusion.
  `checkWF` (executable, run by `CheckBVH`) then certifies the hypothesis `WF`
  of `Flat.run_root` for the C-built tree.
-/
import LightRT.BVH.Flat
import LightRT.FP.Binary32

namespace LightRT.BVH.Check
open LightRT.FP.Binary32

abbrev Box6 := Array UInt32

def q (w : UInt32) : Option ℚ := (decode w).toQ?

/-- `x ∈ [lo, hi]` with all three finite. -/
def inQ (lo x hi : Option ℚ) : Bool :=
  match lo, x, hi with
  | some a, some b, some c => decide (a ≤ b) && decide (b ≤ c)
  | _, _, _ => false

def addQ : Option ℚ → Option ℚ → Option ℚ
  | some a, some b => some (a + b)
  | _, _ => none

/-- Slot data: 9 words `v0 e1 e2` (xyz each), from the leaf block. -/
def insideQ (tri : ℕ → Array UInt32) (p : ℕ) (b : Box6) : Bool :=
  let t := tri p
  (List.range 3).all fun k =>
    let v0 := q t[k]!
    let lo := q b[k]!
    let hi := q b[k + 3]!
    inQ lo v0 hi && inQ lo (addQ v0 (q t[3 + k]!)) hi && inQ lo (addQ v0 (q t[6 + k]!)) hi

def subQ (a b : Box6) : Bool :=
  (List.range 3).all fun k =>
    inQ (q b[k]!) (q a[k]!) (q b[k + 3]!) && inQ (q b[k]!) (q a[k + 3]!) (q b[k + 3]!)

theorem inQ_trans {a b c a' c' : Option ℚ} (h1 : inQ a b c = true) (h2 : inQ a' a c' = true)
    (h3 : inQ a' c c' = true) : inQ a' b c' = true := by
  rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;> simp [inQ] at h1
  rcases a' with _ | a' <;> rcases c' with _ | c' <;> simp [inQ] at h2 h3 ⊢
  exact ⟨h2.1.trans h1.1, h1.2.trans h3.2⟩

/-- Containment is monotone under box inclusion (hypothesis `mono` of `run_root`). -/
theorem insideQ_mono (tri : ℕ → Array UInt32) (p : ℕ) (b b' : Box6)
    (h : insideQ tri p b' = true) (hs : subQ b' b = true) : insideQ tri p b = true := by
  unfold insideQ at *; unfold subQ at hs
  simp only [List.all_eq_true, Bool.and_eq_true] at *
  intro k hk
  obtain ⟨⟨h1, h2⟩, h3⟩ := h k hk
  obtain ⟨s1, s2⟩ := hs k hk
  exact ⟨⟨inQ_trans h1 s1 s2, inQ_trans h2 s1 s2⟩, inQ_trans h3 s1 s2⟩

/-- **C-built BVH traversal is brute force**, for every tree accepted by the
    executable checker, given box-test conservativity (`C1`, `C2`). -/
theorem checked_run_root {T : Type} [LinearOrder T] (F : Flat Box6 ℕ) (tri : ℕ → Array UInt32)
    (hc : F.checkWF (insideQ tri) subQ = true)
    (test : Box6 → T → Option T) (isect : ℕ → Option T)
    (order : List (CRef × T) → List (CRef × T)) (hord : ∀ l, (order l).Perm l)
    (C1 : ∀ p b t best, insideQ tri p b = true → isect p = some t → t < best → (test b best).isSome)
    (C2 : ∀ p b t best tn, test b best = some tn → insideQ tri p b = true → isect p = some t →
      t < best → tn ≤ t)
    (tmin tmax : T) (htmin : ∀ p ∈ F.denRef F.root, ∀ t, isect p = some t → tmin ≤ t) :
    Flat.run F test isect order (F.visitsRef F.root + 1) [(F.root, tmin)] tmax =
      some ((F.denRef F.root).foldl (Flat.step isect) tmax) :=
  Flat.run_root F (F.checkWF_sound _ _ hc) (fun p b b' h hs => insideQ_mono tri p b b' h hs)
    test isect order hord C1 C2 tmin tmax htmin

end LightRT.BVH.Check
