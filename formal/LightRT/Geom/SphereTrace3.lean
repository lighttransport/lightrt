/-
  Three-dimensional no-overshoot for sphere tracing, built on `Metric.infDist`.

  The Bézier leaf (`lightrt_c_tri.c`, `tri_bez_leaf_dist` / `tri_bez_newton`)
  sphere-traces a ray against the tube of a round Bézier curve: at parameter
  `t` it steps by (a sample-based lower bound of) the distance from the
  current point to the tube. Distance functions are 1-Lipschitz, so a step
  can never pass a point where the distance is ≤ 0 — this file proves that
  atom in `Metric.infDist` form, for the exact distance to an arbitrary set:

      `|infDist x S − infDist y S| ≤ dist x y`      (`infDist_lipschitz`)

  composed along a ray `x₀ + t • v` with `‖v‖ ≤ 1` (the C's ray direction
  may be normalized upstream; the restriction of the distance function to the
  ray has Lipschitz constant `‖v‖`):

      `|infDist (x₀ + t • v) S − infDist (x₀ + u • v) S| ≤ |t − u|`

  and the no-overshoot trace theorem `stTrace3_le_root` (via the 1D argument
  `stTrace_le_root` of `Geom.SphereTrace`): starting at `t ≤ root`, the
  iterate never passes `root`, whenever `infDist (x₀ + root • v) S ≤ 0`
  (a point of `S`, or of its closure — the tube's interior). Also included
  is `stTrace3_tube_le_root`, the `r`-tube variant for the round Bézier
  curve (`g = infDist · S − r ≤ 0` inside the tube).

  `AbsLipschitz` generalizes the 1D `Lipschitz1` to a metric space; the two
  atoms behind the *sampled* distance the leaf actually evaluates
  (`tri_bez_leaf_dist` minimizes point distances over sample sites) are
  `lipschitz1_dist_of_mem` (distance to a point is 1-Lipschitz) and
  `lipschitz1_min` (min of two 1-Lipschitz functions is 1-Lipschitz);
  repeated `min` application closes the sample fold.

  Not modeled: the leaf's distance is only a *sample-based* estimate, not
  the exact `infDist` (the golden-section/Newton foot refinement is analyzed
  in `SphereTrace.lean`'s `newton_step_quadratic`); the trace here is the
  ideal-distance model of the sphere trace. The C's behavior under the
  sampled rule is covered by `primhitcheck` empirically.
-/
import Mathlib
import LightRT.Geom.SphereTrace

namespace LightRT.Geom

/-- 1-Lipschitz real function on a metric space (the 3D counterpart of
    `Lipschitz1` on `ℝ`). -/
def AbsLipschitz {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ dist x y

/-- Distance to a set is 1-Lipschitz in the point. -/
theorem infDist_lipschitz {X : Type*} [NormedAddCommGroup X] (S : Set X) (x y : X) :
    |Metric.infDist x S - Metric.infDist y S| ≤ dist x y := by
  have h1 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := S)
  have h2 := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := S)
  rw [dist_comm y x] at h2
  rw [abs_le]
  constructor <;> linarith

/-- The distance-to-set function is `AbsLipschitz`. -/
theorem absLipschitz_infDist {X : Type*} [NormedAddCommGroup X] (S : Set X) :
    AbsLipschitz (fun x => Metric.infDist x S) :=
  infDist_lipschitz S

/-- The distance-to-set function restricted to a ray with `‖v‖ ≤ 1` is
    1-Lipschitz in the parameter. -/
theorem infDist_line_lipschitz {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {x₀ v : X} (hv : ‖v‖ ≤ 1) (t u : ℝ) :
    |Metric.infDist (x₀ + t • v) S - Metric.infDist (x₀ + u • v) S| ≤ |t - u| := by
  have hd : ∀ t u, dist (x₀ + t • v) (x₀ + u • v) = |t - u| * ‖v‖ := fun t u => by
    rw [dist_eq_norm_sub, show x₀ + t • v - (x₀ + u • v) = (t - u) • v by module,
      norm_smul, Real.norm_eq_abs]
  have h1 := Metric.infDist_le_infDist_add_dist (x := x₀ + t • v) (y := x₀ + u • v) (s := S)
  have h2 := Metric.infDist_le_infDist_add_dist (x := x₀ + u • v) (y := x₀ + t • v) (s := S)
  rw [hd t u] at h1
  rw [hd u t] at h2
  have hnn : 0 ≤ |t - u| := abs_nonneg _
  have h3 : |t - u| * ‖v‖ ≤ |t - u| := by
    simpa using mul_le_mul_of_nonneg_left hv hnn
  rw [abs_sub_comm u t] at h2
  have h1' : Metric.infDist (x₀ + t • v) S - Metric.infDist (x₀ + u • v) S ≤ |t - u| * ‖v‖ := by linarith
  have h2' : Metric.infDist (x₀ + u • v) S - Metric.infDist (x₀ + t • v) S ≤ |t - u| * ‖v‖ := by linarith
  rw [abs_le]
  constructor <;> nlinarith [h1', h2', h3]

/-- The ray-restricted distance-to-set function is `Lipschitz1` (1D). -/
theorem lipschitz1_infDist_line {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {x₀ v : X} (hv : ‖v‖ ≤ 1) :
    Lipschitz1 fun s => Metric.infDist (x₀ + s • v) S :=
  fun t u => infDist_line_lipschitz S hv t u

/-- **No overshoot, 3D form**: for a ray with `‖v‖ ≤ 1` and a set `S` with
    `infDist (x₀ + root • v) S ≤ 0` (a point of `S`, or of its closure),
    the distance-driven trace started at `t ≤ root` never passes `root`. -/
theorem stTrace3_le_root {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {x₀ v : X} (hv : ‖v‖ ≤ 1) {root : ℝ}
    (hroot : Metric.infDist (x₀ + root • v) S ≤ 0) {t : ℝ}
    (ht : t ≤ root) (n : ℕ) :
    stTrace (fun s => Metric.infDist (x₀ + s • v) S) t n ≤ root :=
  stTrace_le_root (lipschitz1_infDist_line S hv) hroot ht n

/-- The `r`-tube variant, matching the round Bézier curve of `tri_bez_newton`
    (`S` = the curve's point set, `infDist · S − r` the signed distance to the
    tube). Starting outside, no step passes a `g ≤ 0` point. -/
theorem stTrace3_tube_le_root {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {x₀ v : X} (hv : ‖v‖ ≤ 1) {r root : ℝ}
    (hroot : Metric.infDist (x₀ + root • v) S ≤ r) {t : ℝ}
    (ht : t ≤ root) (n : ℕ) :
    stTrace (fun s => Metric.infDist (x₀ + s • v) S - r) t n ≤ root := by
  have hg : Lipschitz1 fun s => Metric.infDist (x₀ + s • v) S - r := by
    intro x y
    have h := infDist_line_lipschitz S (x₀ := x₀) (v := v) hv x y
    have e : |(Metric.infDist (x₀ + x • v) S - r) - (Metric.infDist (x₀ + y • v) S - r)| =
        |Metric.infDist (x₀ + x • v) S - Metric.infDist (x₀ + y • v) S| := by
      congr 1; ring
    rw [e]; exact h
  exact stTrace_le_root hg (by simpa using sub_nonpos.mpr hroot) ht n

/-- The `min` atom behind the sampled distance objective of `tri_bez_leaf_dist`
    (min over sample sites of point distances): min of two 1-Lipschitz
    functions is 1-Lipschitz. -/
theorem lipschitz1_min {X : Type*} [PseudoMetricSpace X] {f g : X → ℝ}
    (hf : AbsLipschitz f) (hg : AbsLipschitz g) :
    AbsLipschitz fun x => min (f x) (g x) := by
  have hf' : LipschitzWith 1 f := LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    exact hf x y
  have hg' : LipschitzWith 1 g := LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    exact hg x y
  have h := hf'.min hg'
  rw [max_self] at h
  intro x y
  have h2 := (LipschitzWith.dist_le_mul h) x y
  rwa [NNReal.coe_one, one_mul, Real.dist_eq] at h2

/-- Distance to a fixed point is 1-Lipschitz (the reverse triangle
    inequality); one fold of the sample min. -/
theorem lipschitz1_dist_of_mem {X : Type*} [PseudoMetricSpace X] (p : X) :
    AbsLipschitz fun x => dist x p :=
  fun x y => abs_dist_sub_le x y p

end LightRT.Geom
