/-
  Stage 5: BVH containment invariant and traversal = brute force.

  The tree is generic in the primitive type `α`, a bounding function
  `bound : α → Box`, a box test, and a primitive intersector returning the hit
  parameter. Correctness of traversal needs only that the box test is
  *conservative* for every box enclosing a hit primitive's bound — exactly what
  Stage 3 (`slab_no_false_miss`) provides for the floating-point slab test.
-/
import LightRT.Geom.Basic

namespace LightRT.BVH
open LightRT.Geom
noncomputable section

variable {α : Type}

inductive Tree (α : Type) where
  | leaf (b : Box) (ps : List α)
  | node (b : Box) (l r : Tree α)

namespace Tree

def box : Tree α → Box
  | leaf b _ => b
  | node b _ _ => b

def prims : Tree α → List α
  | leaf _ ps => ps
  | node _ l r => l.prims ++ r.prims

/-- Containment invariant: every node's box encloses its children / primitives. -/
def Contains (bound : α → Box) : Tree α → Prop
  | leaf b ps => ∀ p ∈ ps, (bound p).Subset b
  | node b l r => l.box.Subset b ∧ r.box.Subset b ∧ Contains bound l ∧ Contains bound r

/-- Helper: the invariant implies every primitive's bound is inside the root box. -/
theorem Contains.prim_subset {bound : α → Box} :
    ∀ {T : Tree α}, Contains bound T → ∀ p ∈ T.prims, (bound p).Subset T.box
  | leaf b ps, h, p, hp => h p hp
  | node b l r, ⟨hl, hr, cl, cr⟩, p, hp => by
    rcases List.mem_append.1 hp with hp | hp
    · exact Box.Subset.trans (cl.prim_subset p hp) hl
    · exact Box.Subset.trans (cr.prim_subset p hp) hr

/-! ### Build -/

/-- Bounding box of a primitive list (`[]` gets an arbitrary box; it bounds nothing). -/
def boxOf (bound : α → Box) : List α → Box
  | [] => ⟨0, 0⟩
  | [p] => bound p
  | p :: q :: rest => (bound p).union (boxOf bound (q :: rest))

def mkLeaf (bound : α → Box) (ps : List α) : Tree α := leaf (boxOf bound ps) ps
def mkNode (l r : Tree α) : Tree α := node (l.box.union r.box) l r

/-- Generic top-down build: `split` is the (SAH, LBVH, …) partition strategy,
    `fuel` bounds the depth. Any split strategy is allowed. -/
def build (bound : α → Box) (split : List α → List α × List α) (leafSize : ℕ) :
    ℕ → List α → Tree α
  | 0, ps => mkLeaf bound ps
  | n + 1, ps =>
    if ps.length ≤ leafSize then mkLeaf bound ps
    else mkNode (build bound split leafSize n (split ps).1)
                (build bound split leafSize n (split ps).2)

/-- Helper: `boxOf` encloses every member. -/
theorem boxOf_subset (bound : α → Box) : ∀ (ps : List α), ∀ p ∈ ps, (bound p).Subset (boxOf bound ps)
  | [], _, h => absurd h (List.not_mem_nil)
  | [q], p, h => by
    rw [List.mem_singleton.1 h]; exact fun _ => ⟨le_rfl, le_rfl⟩
  | q :: r :: rest, p, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Box.subset_union_left _ _
    · exact Box.Subset.trans (boxOf_subset bound (r :: rest) p h) (Box.subset_union_right _ _)

/-- **Containment invariant of the build** (for every split strategy). -/
theorem build_contains (bound : α → Box) (split : List α → List α × List α) (leafSize : ℕ) :
    ∀ (n : ℕ) (ps : List α), Contains bound (build bound split leafSize n ps)
  | 0, ps => boxOf_subset bound ps
  | n + 1, ps => by
    unfold build
    split_ifs
    · exact boxOf_subset bound ps
    · exact ⟨Box.subset_union_left _ _, Box.subset_union_right _ _,
        build_contains bound split leafSize n _, build_contains bound split leafSize n _⟩

/-- The build neither loses nor duplicates primitives, if `split` partitions. -/
theorem build_prims_perm (bound : α → Box) (split : List α → List α × List α) (leafSize : ℕ)
    (hsplit : ∀ ps, ((split ps).1 ++ (split ps).2).Perm ps) :
    ∀ (n : ℕ) (ps : List α), (build bound split leafSize n ps).prims.Perm ps := by
  sorry

/-! ### Traversal -/

def minOpt : Option ℝ → Option ℝ → Option ℝ
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

/-- Brute force: nearest hit parameter over a list. -/
def brute (isect : α → Option ℝ) (ps : List α) : Option ℝ :=
  ps.foldr (fun p acc => minOpt (isect p) acc) none

/-- Recursive traversal (order-free; the ordered/early-cull variant is `traverseOrdered`). -/
def traverse (boxTest : Box → Bool) (isect : α → Option ℝ) : Tree α → Option ℝ
  | leaf b ps => if boxTest b then brute isect ps else none
  | node b l r => if boxTest b then minOpt (traverse boxTest isect l) (traverse boxTest isect r)
                  else none

/-- The box test never rejects a box that encloses the bound of a primitive the
    intersector hits. -/
def Conservative (bound : α → Box) (boxTest : Box → Bool) (isect : α → Option ℝ) : Prop :=
  ∀ B p t, (bound p).Subset B → isect p = some t → boxTest B = true

/-- **Stage 5 main theorem**: traversal returns the brute-force nearest hit. -/
theorem traverse_eq_brute (bound : α → Box) (boxTest : Box → Bool) (isect : α → Option ℝ)
    (hcons : Conservative bound boxTest isect) :
    ∀ T : Tree α, Contains bound T → traverse boxTest isect T = brute isect T.prims := by
  sorry

/-- Ordered traversal with `t_best` culling (LightRT's actual loop shape): the box
    test also receives the current best hit, and nearer child first. -/
def traverseOrdered (boxTest : Box → Option ℝ → Bool) (isect : α → Option ℝ)
    (nearFirst : Box → Box → Bool) : Option ℝ → Tree α → Option ℝ
  | best, leaf b ps => if boxTest b best then minOpt best (brute isect ps) else best
  | best, node b l r =>
    if boxTest b best then
      if nearFirst l.box r.box then
        traverseOrdered boxTest isect nearFirst (traverseOrdered boxTest isect nearFirst best l) r
      else
        traverseOrdered boxTest isect nearFirst (traverseOrdered boxTest isect nearFirst best r) l
    else best

/-- Culling is only allowed to drop boxes that cannot contain a strictly nearer hit. -/
def ConservativeBest (bound : α → Box) (boxTest : Box → Option ℝ → Bool) (isect : α → Option ℝ) :
    Prop :=
  ∀ B p t best, (bound p).Subset B → isect p = some t →
    (∀ b, best = some b → t < b) → boxTest B best = true

theorem traverseOrdered_eq_brute (bound : α → Box) (boxTest : Box → Option ℝ → Bool)
    (isect : α → Option ℝ) (nearFirst : Box → Box → Bool)
    (hcons : ConservativeBest bound boxTest isect) :
    ∀ T : Tree α, Contains bound T →
      traverseOrdered boxTest isect nearFirst none T = brute isect T.prims := by
  sorry

end Tree
end
end LightRT.BVH
