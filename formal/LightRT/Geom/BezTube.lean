/-
  The signed-distance model of the round Bézier tube (PLAN M14): the
  function the Bézier-curve intersector's sphere trace descends on.

  For a round cubic Bézier curve `C(u)` in `ℝ³` with radius `r(u)` (the
  fourth control-point lane of the 16-value `cp` array), a point `x` is at
  signed distance `φ(u) = |x − C(u)| − r(u)` from the tube at parameter
  `u`. The tube is the union of balls `B(C(u), r(u))`; on the closed
  interval the `inf` of `φ` is attained (continuity on a compact set).

  This file proves the model facts in the order the C relies on them:

  * `BezSys.curvePt` — the curve as a point of `EuclideanSpace ℝ (Fin 3)`;
  * `bezPhi` / `bezQ` — the signed distance `φ(u) = |x − C(u)| − r(u)`
    and its square `|x − C(u)|²`;
  * `bezQ_eq_dist_sq`, `bezPhi_eq_dist` — bridges to Mathlib's `dist`;
  * `hasDerivAt_bezQ` / `hasDerivAt_bezPhi` / `deriv_bezPhi`,
    `continuous_bezPhi` — `φ` is differentiable off the curve;
  * `phi_min_attained` — `∃ u ∈ Icc a b, ∀ v ∈ Icc a b, φ x u ≤ φ x v`;
  * `bezPhiMin` — the attained minimum value; `bezPhiMin_eq`;
  * `bezTubeSet` — the union of closed balls over `Icc a b`;
  * `infDist_bezTubeSet` — the minimal distance from `x` to the tube,

      `infDist x (bezTubeSet S a b) = max 0 (bezPhiMin S x a b)`,

    the identity the sphere trace rests on: the C's ray-stepping descends
    on exactly this distance function.
-/
import Mathlib
import LightRT.Geom.Basic
import LightRT.Geom.SphereTrace3
import LightRT.Geom.BezNewton

namespace LightRT.Geom

open Real

noncomputable section

/-- The curve point as a point of `EuclideanSpace ℝ (Fin 3)`. -/
def curvePt (S : BezSys) (u : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[S.gx u, S.gy u, S.gz u]

@[simp] theorem curvePt_zero (S : BezSys) (u : ℝ) : curvePt S u 0 = S.gx u := by
  simp [curvePt]
@[simp] theorem curvePt_one (S : BezSys) (u : ℝ) : curvePt S u 1 = S.gy u := by
  simp [curvePt]
@[simp] theorem curvePt_two (S : BezSys) (u : ℝ) : curvePt S u 2 = S.gz u := by
  simp [curvePt]

/-- The squared distance from `x` to `C(u)`. -/
def bezQ (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) (u : ℝ) : ℝ :=
  (x 0 - S.gx u) ^ 2 + (x 1 - S.gy u) ^ 2 + (x 2 - S.gz u) ^ 2

theorem bezQ_eq_dist_sq (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) (u : ℝ) :
    bezQ S x u = dist x (curvePt S u) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [bezQ, Fin.sum_univ_three, Real.dist_eq, sq_abs]

/-- The signed distance from `x` to the tube at parameter `u`. -/
def bezPhi (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) (u : ℝ) : ℝ :=
  Real.sqrt (bezQ S x u) - S.rad u

theorem bezPhi_eq_dist (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) (u : ℝ) :
    bezPhi S x u = dist x (curvePt S u) - S.rad u := by
  rw [bezPhi, bezQ_eq_dist_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]

theorem hasDerivAt_bezQ (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) (u : ℝ) :
    HasDerivAt (fun u => bezQ S x u)
      (2 * (x 0 - S.gx u) * (-S.px u) +
        (2 * (x 1 - S.gy u) * (-S.py u) + 2 * (x 2 - S.gz u) * (-S.pz u))) u := by
  have h1 : HasDerivAt (fun s => (x 0 - S.gx s) ^ 2) (2 * (x 0 - S.gx u) * -S.px u) u := by
    have h := (S.hγx u).const_sub (x 0)
    exact h.pow 2 |>.congr_deriv (by ring)
  have h2 : HasDerivAt (fun s => (x 1 - S.gy s) ^ 2) (2 * (x 1 - S.gy u) * -S.py u) u := by
    have h := (S.hγy u).const_sub (x 1)
    exact h.pow 2 |>.congr_deriv (by ring)
  have h3 : HasDerivAt (fun s => (x 2 - S.gz s) ^ 2) (2 * (x 2 - S.gz u) * -S.pz u) u := by
    have h := (S.hγz u).const_sub (x 2)
    exact h.pow 2 |>.congr_deriv (by ring)
  have h := (h1.add h2).add h3
  unfold bezQ
  convert h using 1 <;> simp
  ring

/-- **`φ` is differentiable off the curve.** -/
theorem hasDerivAt_bezPhi (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) (u : ℝ)
    (hne : bezQ S x u ≠ 0) :
    HasDerivAt (fun u => bezPhi S x u)
      ((2 * (x 0 - S.gx u) * (-S.px u) +
        (2 * (x 1 - S.gy u) * (-S.py u) + 2 * (x 2 - S.gz u) * (-S.pz u))) /
          (2 * Real.sqrt (bezQ S x u)) - S.dr u) u := by
  have hq := hasDerivAt_bezQ S x u
  have hlen := hq.sqrt hne
  have hg := hlen.sub (S.hρ u)
  unfold bezPhi
  exact hg

theorem deriv_bezPhi (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) (u : ℝ)
    (hne : bezQ S x u ≠ 0) :
    deriv (fun u => bezPhi S x u) u =
      ((2 * (x 0 - S.gx u) * (-S.px u) +
        (2 * (x 1 - S.gy u) * (-S.py u) + 2 * (x 2 - S.gz u) * (-S.pz u))) /
          (2 * Real.sqrt (bezQ S x u)) - S.dr u) :=
  (hasDerivAt_bezPhi S x u hne).deriv

/-- `φ` is continuous everywhere (no nonzero-norm side condition). -/
theorem continuous_bezPhi (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) :
    Continuous fun u => bezPhi S x u := by
  have hq : Differentiable ℝ fun u => bezQ S x u := fun u => (hasDerivAt_bezQ S x u).differentiableAt
  have hr : Differentiable ℝ S.rad := fun u => (S.hρ u).differentiableAt
  exact (Real.continuous_sqrt.comp hq.continuous).sub hr.continuous

/-- The closed interval `[a, b]` is compact, so `φ` attains its min. -/
theorem phi_min_attained (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) {a b : ℝ} (hab : a ≤ b) :
    ∃ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, bezPhi S x u ≤ bezPhi S x v := by
  have hcont : Continuous (fun u => bezPhi S x u) := continuous_bezPhi S x
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab) hcont.continuousOn
  exact ⟨u, hu, hmin⟩

/-- The minimum value of `φ` on `[a, b]`. -/
def bezPhiMin (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) (a b : ℝ) : ℝ :=
  sInf (bezPhi S x '' Set.Icc a b)

theorem bezPhiMin_eq (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) {a b : ℝ} (hab : a ≤ b) :
    ∃ u ∈ Set.Icc a b, bezPhiMin S x a b = bezPhi S x u := by
  obtain ⟨u, hu, hbest⟩ := phi_min_attained S x hab
  have hbdd : BddBelow (bezPhi S x '' Set.Icc a b) := by
    refine ⟨bezPhi S x u, ?_⟩
    rintro b ⟨w, hw, rfl⟩
    exact hbest w hw
  have hle : bezPhiMin S x a b ≤ bezPhi S x u :=
    csInf_le hbdd (Set.mem_image_of_mem _ hu)
  refine ⟨u, hu, le_antisymm hle ?_⟩
  apply le_csInf
  · exact ⟨bezPhi S x u, Set.mem_image_of_mem _ hu⟩
  · rintro w ⟨v, hv, rfl⟩
    exact hbest v hv

/-- The tube as the union of closed balls over `[a, b]`. -/
def bezTubeSet (S : BezSys) (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ u ∈ Set.Icc a b, Metric.closedBall (curvePt S u) (S.rad u)

theorem mem_bezTubeSet_iff (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) {a b : ℝ}
    (_hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u) :
    x ∈ bezTubeSet S a b ↔ ∃ u ∈ Set.Icc a b, bezPhi S x u ≤ 0 := by
  unfold bezTubeSet
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨u, hu, hball⟩
    refine ⟨u, hu, ?_⟩
    have hle : dist x (curvePt S u) ≤ S.rad u := Metric.mem_closedBall.mp hball
    have h := bezPhi_eq_dist S x u
    rw [h]
    linarith [hle]
  · rintro ⟨u, hu, hphi⟩
    refine ⟨u, hu, ?_⟩
    have hphi' := hphi
    rw [bezPhi_eq_dist] at hphi'
    exact Metric.mem_closedBall.mpr (by linarith)

theorem mem_bezTubeSet_of_bezPhi_le (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) {a b : ℝ}
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u) {u : ℝ} (hu : u ∈ Set.Icc a b)
    (hphi : bezPhi S x u ≤ 0) : x ∈ bezTubeSet S a b := by
  rw [mem_bezTubeSet_iff S x hrad]
  exact ⟨u, hu, hphi⟩

/-- The image curve point lies in the tube's ball. -/
theorem bezTubeSet_nonempty (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u) : (bezTubeSet S a b).Nonempty := by
  refine ⟨curvePt S a, ?_⟩
  unfold bezTubeSet
  simp only [Set.mem_iUnion]
  exact ⟨a, ⟨le_refl a, hab⟩, Metric.mem_closedBall.mpr (by simp [hrad a ⟨le_refl a, hab⟩])⟩

theorem bezPhiMin_le (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) {a b : ℝ} (hab : a ≤ b)
    {u : ℝ} (hu : u ∈ Set.Icc a b) : bezPhiMin S x a b ≤ bezPhi S x u := by
  obtain ⟨u₀, hu₀, hbest⟩ := phi_min_attained S x hab
  have hbdd : BddBelow (bezPhi S x '' Set.Icc a b) := by
    refine ⟨bezPhi S x u₀, ?_⟩
    rintro b ⟨w, hw, rfl⟩
    exact hbest w hw
  exact csInf_le hbdd (Set.mem_image_of_mem _ hu)

/-- **The minimal distance from `x` to the tube** is `max 0 (min_u φ)`:
if some parameter gives nonpositive φ, `x` is in the tube (distance 0);
otherwise every tube point is at distance ≥ `min φ` and the perpendicular
foot at the minimizing parameter sits at exactly that distance. -/
theorem infDist_bezTubeSet (S : BezSys) (x : EuclideanSpace ℝ (Fin 3))
    {a b : ℝ} (hab : a ≤ b) (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u) :
    Metric.infDist x (bezTubeSet S a b) = max 0 (bezPhiMin S x a b) := by
  have hne : (bezTubeSet S a b).Nonempty := bezTubeSet_nonempty S hab hrad
  by_cases hle0 : bezPhiMin S x a b ≤ 0
  · obtain ⟨u, hu, hφm⟩ := bezPhiMin_eq S x hab
    have hφle : bezPhi S x u ≤ 0 := by linarith [hφm, hle0]
    have hx : x ∈ bezTubeSet S a b := mem_bezTubeSet_of_bezPhi_le S x hrad hu hφle
    rw [Metric.infDist_zero_of_mem hx, max_eq_left hle0]
  · have hmin : 0 < bezPhiMin S x a b := lt_of_not_ge hle0
    apply le_antisymm
    · obtain ⟨u₀, hu₀, hφm⟩ := bezPhiMin_eq S x hab
      have hhrad := hrad u₀ hu₀
      have hφ : 0 < bezPhi S x u₀ := by linarith [hmin, hφm]
      have hd : 0 < dist x (curvePt S u₀) := by
        have h1 := bezPhi_eq_dist S x u₀
        linarith [hφ, hhrad]
      set C := curvePt S u₀ with hC
      set d := dist x C with hd'
      set r := S.rad u₀ with hr'
      set y := C + (r / d) • (x - C) with hy
      have hy_def : y = C + (r / d) • (x - C) := hy
      have hydist : dist y C = r := by
        rw [hy_def, dist_eq_norm_sub]
        have e : C + (r / d) • (x - C) - C = (r / d) • (x - C) := by module
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hhrad hd.le)]
        have hxd : ‖x - C‖ = d := dist_eq_norm_sub x C
        have hxn : ‖x - C‖ ≠ 0 := by
          rw [← hxd] at hd
          exact hd.ne'
        rw [← hxd]
        field_simp [hxn]
      have hytube : y ∈ bezTubeSet S a b := by
        apply mem_bezTubeSet_of_bezPhi_le S y hrad hu₀
        have e := bezPhi_eq_dist S y u₀
        have hyC : dist y (curvePt S u₀) = S.rad u₀ := hydist
        nlinarith [e, hyC, hhrad]
      have hrle : r ≤ d := by
        have h1 := bezPhi_eq_dist S x u₀
        nlinarith [hφ, h1, hd']
      have hxy : dist x y = d - r := by
        rw [hy_def, dist_eq_norm_sub]
        have e : x - (C + (r / d) • (x - C)) = (1 - r / d) • (x - C) := by module
        rw [e, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by
            have h1 : (1:ℝ) ≥ r / d := (div_le_one hd).mpr hrle
            linarith [h1])]
        have hxd : ‖x - C‖ = d := dist_eq_norm_sub x C
        have hxn : ‖x - C‖ ≠ 0 := by
          rw [← hxd] at hd
          exact hd.ne'
        have hxd' : d = ‖x - C‖ := hxd.symm
        rw [hxd']
        field_simp [hxn]
      have hφdist : bezPhi S x u₀ = d - r := by
        have h1 := bezPhi_eq_dist S x u₀
        rw [dist_eq_norm_sub] at h1
        exact h1
      calc Metric.infDist x (bezTubeSet S a b) ≤ dist x y :=
            Metric.infDist_le_dist_of_mem hytube
        _ = d - r := hxy
        _ = bezPhi S x u₀ := hφdist.symm
        _ = bezPhiMin S x a b := hφm.symm
        _ ≤ max 0 (bezPhiMin S x a b) := le_max_right 0 _
    · rw [Metric.le_infDist hne, max_eq_right hmin.le]
      intro y hy
      rw [mem_bezTubeSet_iff S y hrad] at hy
      obtain ⟨u, hu, hφy⟩ := hy
      have hyC : dist y (curvePt S u) ≤ S.rad u := by
        have e := bezPhi_eq_dist S y u
        linarith [hφy, e]
      have hbd : bezPhiMin S x a b ≤ bezPhi S x u := bezPhiMin_le S x hab hu
      have htri : dist x (curvePt S u) ≤ dist x y + dist y (curvePt S u) :=
        dist_triangle x y (curvePt S u)
      have e := bezPhi_eq_dist S x u
      have hdyC : dist y (curvePt S u) = dist y (curvePt S u) := rfl
      linarith [hbd, e, htri, hyC, dist_comm y (curvePt S u)]

/-- **Sphere trace on the round Bézier tube, exact-distance version**: for a
    ray with `‖v‖ ≤ 1`, if the tube's `bezPhiMin` at the root is nonpositive
    (the root lies in the tube, or touches it), the distance-driven trace
    started at `t ≤ root` never passes `root`. This is the no-overshoot
    guarantee the C's `tri_bez_leaf` stepping rests on (with the *sampled*
    distance rule in place of `Metric.infDist`; sampled-mins 1-Lipschitz by
    `lipschitz1_min`, and the sampled fold overshoots nowhere that the true
    distance doesn't, cf. `primhitcheck`). -/
theorem stTrace3_bezTube_le_root (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u)
    {x₀ v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ ≤ 1) {root : ℝ}
    (hroot : bezPhiMin S (x₀ + root • v) a b ≤ 0) {t : ℝ} (ht : t ≤ root) (n : ℕ) :
    stTrace (fun s => Metric.infDist (x₀ + s • v) (bezTubeSet S a b)) t n ≤ root := by
  have hroot' : Metric.infDist (x₀ + root • v) (bezTubeSet S a b) ≤ 0 := by
    rw [infDist_bezTubeSet S (x₀ + root • v) hab hrad]
    exact max_le_iff.mpr ⟨le_refl 0, hroot⟩
  exact stTrace3_le_root (bezTubeSet S a b) hv hroot' ht n

/-! ### The interior nearest point is a critical point of `φ`

The `tri_bez_newton` contact solve, the soundness direction: if the
minimum of `φ` on `[a, b]` is attained at an interior point and `x` is
off the curve, the derivative vanishes there — the foot-point (envelope)
equation `⟨x − C, C′⟩ / |x − C| = −r′` that the C's Newton iterations
converge on (up to sign conventions). The completeness direction is
`phi_min_attained`. -/
theorem interior_min_bezPhi_deriv (S : BezSys) (x : EuclideanSpace ℝ (Fin 3))
    {a b u₀ : ℝ} (_hab : a ≤ b) (hu : u₀ ∈ Set.Ioo a b)
    (hmin : ∀ v ∈ Set.Icc a b, bezPhi S x u₀ ≤ bezPhi S x v) :
    deriv (fun u => bezPhi S x u) u₀ = 0 := by
  have hnhds : Set.Icc a b ∈ nhds u₀ :=
    Filter.mem_of_superset (Ioo_mem_nhds hu.1 hu.2) Set.Ioo_subset_Icc_self
  exact (IsMinOn.isLocalMin (show IsMinOn (fun u => bezPhi S x u) (Set.Icc a b) u₀ from hmin)
    hnhds).deriv_eq_zero

theorem interior_min_bezPhi_envelope (S : BezSys) (x : EuclideanSpace ℝ (Fin 3))
    {a b u₀ : ℝ} (hab : a ≤ b) (hu : u₀ ∈ Set.Ioo a b)
    (hmin : ∀ v ∈ Set.Icc a b, bezPhi S x u₀ ≤ bezPhi S x v) (hne : bezQ S x u₀ ≠ 0) :
    (2 * (x 0 - S.gx u₀) * (-S.px u₀) +
        (2 * (x 1 - S.gy u₀) * (-S.py u₀) + 2 * (x 2 - S.gz u₀) * (-S.pz u₀))) /
          (2 * Real.sqrt (bezQ S x u₀)) - S.dr u₀ = 0 := by
  have h := interior_min_bezPhi_deriv S x hab hu hmin
  rwa [deriv_bezPhi S x u₀ hne] at h

/-- **Nearest-point classification over `[a, b]`**: the minimum of `φ` on
    the interval is attained at either an endpoint of `[a, b]`, a point
    off the curve where `φ′` vanishes (the C's foot-point condition), or a
    point on the curve itself (`bezQ = 0`, the degenerate case). -/
theorem bezPhi_min_critical (S : BezSys) (x : EuclideanSpace ℝ (Fin 3))
    {a b : ℝ} (hab : a ≤ b) :
    ∃ u ∈ Set.Icc a b,
      u = a ∨ u = b ∨ deriv (fun u => bezPhi S x u) u = 0 ∨ bezQ S x u = 0 := by
  obtain ⟨u, hu, hbest⟩ := phi_min_attained S x hab
  refine ⟨u, hu, ?_⟩
  by_cases hne : bezQ S x u = 0
  · exact Or.inr (Or.inr (Or.inr hne))
  · by_cases hio : u ∈ Set.Ioo a b
    · exact Or.inr (Or.inr (Or.inl (interior_min_bezPhi_deriv S x hab hio hbest)))
    · have h1 := hu.1
      have h2 := hu.2
      have hio' : ¬ (a < u ∧ u < b) := by
        simpa [Set.mem_Ioo] using hio
      by_cases h : u = a
      · exact Or.inl h
      · have hb : u = b := by
          by_contra hb'
          exact absurd ⟨lt_of_le_of_ne h1 (Ne.symm h), lt_of_le_of_ne h2 hb'⟩ hio' 
        exact Or.inr (Or.inl hb)

/-! ### The sampled distance rule (the C's `tri_bez_leaf_dist` fold) -/

/-- The sampled distance from `x` to the tube over `sites`: the min over
    the sample sites of `dist x (C u) − r(u)` — exactly what
    `tri_bez_leaf_dist` accumulates. The empty site list is degenerate and
    maps to `0`. -/
def samDist (S : BezSys) (sites : List ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  match sites with
  | [] => 0
  | u :: us =>
    List.foldr (fun v acc => min (dist x (curvePt S v) - S.rad v) acc)
      (dist x (curvePt S u) - S.rad u) us

theorem absLipschitz_bezContact (S : BezSys) (u : ℝ) :
    AbsLipschitz (fun x : EuclideanSpace ℝ (Fin 3) => dist x (curvePt S u) - S.rad u) := by
  intro x y
  have h := lipschitz1_dist_of_mem (X := EuclideanSpace ℝ (Fin 3)) (curvePt S u) x y
  have e : |(dist x (curvePt S u) - S.rad u) - (dist y (curvePt S u) - S.rad u)| =
      |dist x (curvePt S u) - dist y (curvePt S u)| := by congr 1; ring
  rw [e]; exact h

theorem absLipschitz_samDist_foldr (S : BezSys) (us : List ℝ) (u : ℝ) :
    AbsLipschitz (fun x : EuclideanSpace ℝ (Fin 3) =>
      List.foldr (fun v acc => min (dist x (curvePt S v) - S.rad v) acc)
        (dist x (curvePt S u) - S.rad u) us) := by
  induction us generalizing u with
  | nil => exact absLipschitz_bezContact S u
  | cons v us ih => exact lipschitz1_min (absLipschitz_bezContact S v) (ih u)

theorem absLipschitz_samDist (S : BezSys) (sites : List ℝ) :
    AbsLipschitz (fun x : EuclideanSpace ℝ (Fin 3) => samDist S sites x) := by
  intro x y
  cases sites with
  | nil =>
    show |samDist S [] x - samDist S [] y| ≤ dist x y
    have e : samDist S [] x = 0 := rfl
    have e2 : samDist S [] y = 0 := rfl
    rw [e, e2, sub_self, abs_zero]
    exact dist_nonneg
  | cons u us => exact absLipschitz_samDist_foldr S us u x y

/-- The sampled distance along a unit ray is 1-Lipschitz. -/
theorem lipschitz1_samDist_line (S : BezSys) (sites : List ℝ)
    {x₀ v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ ≤ 1) :
    Lipschitz1 fun t => samDist S sites (x₀ + t • v) := by
  have hg := absLipschitz_samDist S sites
  intro a b
  have h := hg (x₀ + a • v) (x₀ + b • v)
  have d : dist (x₀ + a • v) (x₀ + b • v) = |a - b| * ‖v‖ := by
    rw [dist_eq_norm_sub, show x₀ + a • v - (x₀ + b • v) = (a - b) • v from by module,
      norm_smul, Real.norm_eq_abs]
  rw [d] at h
  have h4 : |a - b| * ‖v‖ ≤ |a - b| := by nlinarith [hv, abs_nonneg (a - b)]
  linarith [h, h4]

/-- **No overshoot for the sampled stepping rule**: the trace driven by the
    `tri_bez_leaf_dist` fold never passes a root where the sampled min is
    ≤ 0 (some sample site's ball covers the root). This is the honest
    analogue of the exact-distance guarantee for the C's actual stepping
    function; whether the sampled fold's roots lie inside the true tube is
    a sampling-density question, not covered here. -/
theorem stTrace3_samDist_le_root (S : BezSys) (sites : List ℝ)
    {x₀ v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ ≤ 1) {root : ℝ}
    (hroot : samDist S sites (x₀ + root • v) ≤ 0) {t : ℝ} (ht : t ≤ root) (n : ℕ) :
    stTrace (fun s => samDist S sites (x₀ + s • v)) t n ≤ root :=
  stTrace_le_root (lipschitz1_samDist_line S sites hv) hroot ht n

end
end LightRT.Geom
