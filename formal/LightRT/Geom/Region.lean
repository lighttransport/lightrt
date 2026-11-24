/-
  Real-number region predicates for the spatial queries of `lightrt_c_tri.c`
  (`query_aabb` / `query_sphere` / `query_frustum`). `boxMayOverlap R b` is the
  conservative box test: it holds exactly when a point of `b` may lie in `R`.
  It is monotone under box inclusion, which is the hypothesis the BVH region
  traversal needs to be conservative.
-/
import Mathlib
import LightRT.Geom.Basic
import LightRT.Geom.PrimReal

namespace LightRT.Geom
noncomputable section
open Matrix

/-- A frustum plane `(n, d)`: inside is `n·p + d ≥ 0`. -/
abbrev Plane4 := Vec3 × ℝ

/-- Squared distance from `c` to the interval `[lo, hi]`. This is the distance
    to the *nearest* point, written without a min/clamp: `dist(c,[lo,hi]) =
    max(0, lo-c, c-hi)`. -/
def distToIntervalSq (c lo hi : ℝ) : ℝ :=
  (max 0 (max (lo - c) (c - hi))) ^ 2

theorem distToIntervalSq_nonneg (c lo hi : ℝ) : 0 ≤ distToIntervalSq c lo hi := sq_nonneg _

/-- Shrinking an interval cannot decrease the squared distance from a point. -/
theorem distToIntervalSq_mono {c alo ahi blo bhi : ℝ}
    (hsublo : blo ≤ alo) (hsubhi : ahi ≤ bhi) :
    distToIntervalSq c blo bhi ≤ distToIntervalSq c alo ahi := by
  unfold distToIntervalSq
  have hle : max 0 (max (blo - c) (c - bhi)) ≤ max 0 (max (alo - c) (c - ahi)) := by
    apply max_le
    · exact le_max_left _ _
    · apply max_le
      · exact (sub_le_sub_right hsublo c).trans
          (le_trans (le_max_left _ _) (le_max_right _ _))
      · have h : c - bhi ≤ c - ahi := sub_le_sub_left hsubhi c
        exact h.trans (le_trans (le_max_right _ _) (le_max_right _ _))
  have h0a : 0 ≤ max 0 (max (alo - c) (c - ahi)) := le_max_left _ _
  have h0b : 0 ≤ max 0 (max (blo - c) (c - bhi)) := le_max_left _ _
  nlinarith

/-- If `q ∈ [lo, hi]` then the interval distance is at most `|q - c|`. -/
theorem distToIntervalSq_le (c lo hi q : ℝ) (hlo : lo ≤ q) (hhi : q ≤ hi) :
    distToIntervalSq c lo hi ≤ (q - c) ^ 2 := by
  unfold distToIntervalSq
  have hM : max 0 (max (lo - c) (c - hi)) ≤ |q - c| := by
    rw [le_abs]
    by_cases hqc : 0 ≤ q - c
    · left
      apply max_le
      · exact hqc
      · apply max_le
        · linarith
        · linarith
    · right
      have hcq : 0 ≤ c - q := by linarith
      rw [show -(q - c) = c - q by ring]
      apply max_le
      · exact hcq
      · apply max_le
        · linarith
        · linarith
  have hsq : (max 0 (max (lo - c) (c - hi))) ^ 2 ≤ |q - c| ^ 2 := by
    have hM0 : 0 ≤ max 0 (max (lo - c) (c - hi)) := le_max_left _ _
    have hA0 : 0 ≤ |q - c| := abs_nonneg _
    nlinarith [sq_nonneg (|q - c| - max 0 (max (lo - c) (c - hi)))]
  nlinarith [hsq, sq_abs (q - c)]

/-- Squared distance from a point to a box (sum of per-axis interval distances). -/
def boxPointDistSq (b : Box) (p : Vec3) : ℝ :=
  ∑ i : Fin 3, distToIntervalSq (p i) (b.lo i) (b.hi i)

theorem boxPointDistSq_mono {a b : Box} (hsub : a.Subset b) (c : Vec3) :
    boxPointDistSq b c ≤ boxPointDistSq a c := by
  unfold boxPointDistSq
  apply Finset.sum_le_sum
  intro i hi
  exact distToIntervalSq_mono (hsub i).1 (hsub i).2

/-- If `q` lies in the box, the box-point distance is at most `distSq q c`. -/
theorem boxPointDistSq_le_of_mem {b : Box} {q c : Vec3} (hq : b.Mem q) :
    boxPointDistSq b c ≤ distSq q c := by
  unfold boxPointDistSq distSq
  simp only [dotProduct, Fin.sum_univ_three, Pi.sub_apply]
  have h0 := distToIntervalSq_le (c 0) (b.lo 0) (b.hi 0) (q 0) (hq 0).1 (hq 0).2
  have h1 := distToIntervalSq_le (c 1) (b.lo 1) (b.hi 1) (q 1) (hq 1).1 (hq 1).2
  have h2 := distToIntervalSq_le (c 2) (b.lo 2) (b.hi 2) (q 2) (hq 2).1 (hq 2).2
  nlinarith

/-! ### Region definition -/

inductive Region where
  | aabb (lo hi : Vec3)
  | sphere (c : Vec3) (r : ℝ)
  | frustum (planes : Fin 6 → Plane4)

/-- For a plane normal `n`, the box corner maximising `n·p`. -/
def pVertex (b : Box) (n : Vec3) : Vec3 :=
  fun i => if 0 ≤ n i then b.hi i else b.lo i

theorem pVertex_coord_le {a b : Box} (hsub : a.Subset b) (n : Vec3) (i : Fin 3) :
    n i * pVertex a n i ≤ n i * pVertex b n i := by
  unfold pVertex
  by_cases h : 0 ≤ n i
  · simp [h]; exact mul_le_mul_of_nonneg_left (hsub i).2 h
  · simp [h]; exact mul_le_mul_of_nonpos_left (hsub i).1 (le_of_not_ge h)

theorem pVertex_mono {a b : Box} (hsub : a.Subset b) (n : Vec3) :
    n ⬝ᵥ pVertex a n ≤ n ⬝ᵥ pVertex b n := by
  simp only [dotProduct, Fin.sum_univ_three]
  exact add_le_add (add_le_add (pVertex_coord_le hsub n 0) (pVertex_coord_le hsub n 1))
    (pVertex_coord_le hsub n 2)

/-- Conservative box-vs-region test (mirrors C `tri_region_test_box`). -/
def boxMayOverlap : Region → Box → Prop
  | .aabb lo hi, b => ∀ i, b.lo i ≤ hi i ∧ lo i ≤ b.hi i
  | .sphere c r, b => boxPointDistSq b c ≤ r ^ 2
  | .frustum planes, b =>
      ∀ k, 0 ≤ (planes k).1 ⬝ᵥ pVertex b (planes k).1 + (planes k).2

/-- **Conservativity**: a region-overlapping box stays overlapping when enlarged. -/
theorem boxMayOverlap_mono {R : Region} {a b : Box} (hsub : a.Subset b) :
    boxMayOverlap R a → boxMayOverlap R b := by
  cases R with
  | aabb lo hi =>
      intro h i
      exact ⟨(hsub i).1.trans (h i).1, (h i).2.trans (hsub i).2⟩
  | sphere c r =>
      intro h
      exact (boxPointDistSq_mono hsub c).trans h
  | frustum planes =>
      intro h k
      linarith [pVertex_mono hsub (planes k).1, h k]

/-- A point of the box that is in an AABB region makes the box test pass. -/
theorem mem_aabb_of_mem_region {q : Vec3} {lo hi : Vec3} {b : Box}
    (hq : b.Mem q) (hr : ∀ i, lo i ≤ q i ∧ q i ≤ hi i) :
    boxMayOverlap (.aabb lo hi) b := by
  intro i
  exact ⟨(hq i).1.trans (hr i).2, (hr i).1.trans (hq i).2⟩

/-- A point of the box inside a sphere makes the box test pass. -/
theorem mem_sphere_of_mem_region {q c : Vec3} {r : ℝ} {b : Box}
    (hq : b.Mem q) (hr : distSq q c ≤ r ^ 2) :
    boxMayOverlap (.sphere c r) b :=
  (boxPointDistSq_le_of_mem hq).trans hr

/-- A point of the box inside every frustum plane makes the box test pass. -/
theorem mem_frustum_of_mem_region {q : Vec3} {planes : Fin 6 → Plane4} {b : Box}
    (hq : b.Mem q) (hr : ∀ k, 0 ≤ (planes k).1 ⬝ᵥ q + (planes k).2) :
    boxMayOverlap (.frustum planes) b := by
  intro k
  have hv : (planes k).1 ⬝ᵥ q ≤ (planes k).1 ⬝ᵥ pVertex b (planes k).1 := by
    let n := (planes k).1
    have h0 : n 0 * q 0 ≤ n 0 * pVertex b n 0 := by
      by_cases h : 0 ≤ n 0
      · simp [pVertex, h]; exact mul_le_mul_of_nonneg_left (hq 0).2 h
      · simp [pVertex, h]; exact mul_le_mul_of_nonpos_left (hq 0).1 (le_of_not_ge h)
    have h1 : n 1 * q 1 ≤ n 1 * pVertex b n 1 := by
      by_cases h : 0 ≤ n 1
      · simp [pVertex, h]; exact mul_le_mul_of_nonneg_left (hq 1).2 h
      · simp [pVertex, h]; exact mul_le_mul_of_nonpos_left (hq 1).1 (le_of_not_ge h)
    have h2 : n 2 * q 2 ≤ n 2 * pVertex b n 2 := by
      by_cases h : 0 ≤ n 2
      · simp [pVertex, h]; exact mul_le_mul_of_nonneg_left (hq 2).2 h
      · simp [pVertex, h]; exact mul_le_mul_of_nonpos_left (hq 2).1 (le_of_not_ge h)
    simp only [dotProduct, Fin.sum_univ_three]
    linarith
  linarith [hr k]

end
end LightRT.Geom
