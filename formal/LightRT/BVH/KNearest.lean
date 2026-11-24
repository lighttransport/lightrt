/-
  k-nearest-neighbour contracts for `lrt_tri_knn` / `lrt_tri_closest_point`,
  instantiated from the generic `KBest.runN` multi-hit traversal. The distance
  order is `WithTop ℝ` (so the caller's `tmax` is `⊤`); the box test is the
  box-point distance, which is a lower bound on the triangle distance by
  `Geom/PointTriReal.lean`. The nearest-single query is the k=1 case.
-/
import LightRT.BVH.KBest
import LightRT.Geom.PointTriReal

namespace LightRT.BVH
open LightRT.Geom KBest
noncomputable section

abbrev Tri3 := Vec3 × Vec3 × Vec3

namespace KNearest

/-- The exact (fp-free) squared distance from `p` to primitive `a`. -/
def primDist {α : Type} (triOf : α → Tri3) (p : Vec3) (a : α) : ℝ :=
  pointTriDistSq p (triOf a).1 (triOf a).2.1 (triOf a).2.2

/-- `isect` for the kNN fold: always succeeds with the exact distance. -/
def knnIsect {α : Type} (triOf : α → Tri3) (p : Vec3) (a : α) : Option (WithTop ℝ) :=
  some (primDist triOf p a : WithTop ℝ)

/-- `test` for the kNN fold: a box is admitted iff its point distance does not
    exceed the current k-th best distance. -/
def knnTest (p : Vec3) (b : Box) (best : WithTop ℝ) : Option (WithTop ℝ) :=
  if (boxPointDistSq b p : WithTop ℝ) ≤ best then some (boxPointDistSq b p : WithTop ℝ) else none

/-- The k-nearest traversal (a `KBest.runN` with `tmax = ⊤`, ordered stack). -/
def runKNN {α : Type} (triOf : α → Tri3) (p : Vec3) (F : Flat Box α) (k : ℕ) :
    List (α × WithTop ℝ) :=
  KBest.runN F (knnTest p) (knnIsect triOf p) id k
    (F.visitsRef F.root + 1) [(F.root, 0)] ⊤ []

/-- Soundness: every reported pair has the exact primitive distance. -/
theorem runKNN_sound {α : Type} (triOf : α → Tri3) (p : Vec3) (F : Flat Box α) (k : ℕ)
    (z : α × WithTop ℝ) (hz : z ∈ runKNN triOf p F k) :
    knnIsect triOf p z.1 = some z.2 := by
  have hB : KBest.BInv (knnIsect triOf p) (runKNN triOf p F k) := by
    unfold runKNN
    apply KBest.runN_sound
    intro x hx
    simp at hx
  exact hB z hz

/-- The box point distance is a lower bound on a contained primitive's exact
    triangle distance (the pruning key). -/
theorem box_le_prim {α : Type} (bound : α → Box) (triOf : α → Tri3) (p : Vec3)
    {a : α} {b : Box} (ha : (bound a).Subset b)
    (htri : ∀ q, InTriangle (triOf a).1 (triOf a).2.1 (triOf a).2.2 q → (bound a).Mem q) :
    boxPointDistSq b p ≤ primDist triOf p a := by
  apply boxPointDistSq_le_pointTriDistSq p (triOf a).1 (triOf a).2.1 (triOf a).2.2 b
  intro q hq
  exact ha.mem (htri q hq)

/-- Completeness: every reachable primitive whose distance is strictly below
    the returned k-th value is reported. -/
theorem runKNN_complete {α : Type} (bound : α → Box) (triOf : α → Tri3) (p : Vec3)
    (F : Flat Box α) (k : ℕ) (hk : 0 < k)
    (hw : F.WF (fun a b => (bound a).Subset b) Box.Subset)
    (htri : ∀ a, ∀ q, InTriangle (triOf a).1 (triOf a).2.1 (triOf a).2.2 q → (bound a).Mem q) :
    ∀ a ∈ F.denRef F.root, ∀ d, knnIsect triOf p a = some d →
      d < KBest.pruneOf k (runKNN triOf p F k) ⊤ →
        (a, d) ∈ runKNN triOf p F k := by
  apply KBest.runN_complete F (knnTest p) (knnIsect triOf p) id k hk
  · intro a t ht
    simp [knnIsect] at ht
    subst t
    exact WithTop.coe_lt_top _
  · exact hw
  · intro a b b' hab hbb
    exact hab.trans hbb
  · intro a b t best ha ht hlt
    simp [knnTest]
    have hreal : boxPointDistSq b p ≤ primDist triOf p a := box_le_prim bound triOf p ha (htri a)
    have hcoe : (boxPointDistSq b p : WithTop ℝ) ≤ (primDist triOf p a : WithTop ℝ) :=
      WithTop.coe_le_coe.2 hreal
    have ht' : (primDist triOf p a : WithTop ℝ) = t := by simpa [knnIsect] using ht
    rw [← ht'] at hlt
    exact (hcoe.trans_lt hlt).le
  · intro a b t best tn ht ha htint hlt
    simp [knnTest] at ht
    rw [← ht.2]
    have hreal : boxPointDistSq b p ≤ primDist triOf p a := box_le_prim bound triOf p ha (htri a)
    have ht' : (primDist triOf p a : WithTop ℝ) = t := by simpa [knnIsect] using htint
    rw [← ht']
    exact WithTop.coe_le_coe.2 hreal
  · intro l; rfl
  · intro a ha t ht
    simp [knnIsect] at ht
    subst t
    exact WithTop.coe_le_coe.2 (pointTriDistSq_nonneg p (triOf a).1 (triOf a).2.1 (triOf a).2.2)

end KNearest
