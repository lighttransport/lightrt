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

/-- **Boundary existence along the ray**: if the trace starts outside the
    tube (`infDist > 0`) and a `root` ahead is in/touching it, some `s`
    between them has the distance exactly zero — a first boundary point of
    the tube along the segment. (IVT; no tube params needed.) -/
theorem exists_bezTube_boundary_point (S : BezSys) {a b : ℝ}
    {x₀ v : EuclideanSpace ℝ (Fin 3)} {t₀ root : ℝ} (ht : t₀ < root)
    (h0 : 0 < Metric.infDist (x₀ + t₀ • v) (bezTubeSet S a b))
    (hroot : Metric.infDist (x₀ + root • v) (bezTubeSet S a b) ≤ 0) :
    ∃ s ∈ Set.Icc t₀ root, Metric.infDist (x₀ + s • v) (bezTubeSet S a b) = 0 := by
  have hgc : Continuous fun s : ℝ => Metric.infDist (x₀ + s • v) (bezTubeSet S a b) := by
    fun_prop
  have hcont : ContinuousOn (fun s : ℝ => Metric.infDist (x₀ + s • v) (bezTubeSet S a b))
      (Set.Icc t₀ root) := hgc.continuousOn
  have hsub := intermediate_value_Icc' ht.le hcont
  have hmem : (0:ℝ) ∈ Set.Icc
      ((fun s : ℝ => Metric.infDist (x₀ + s • v) (bezTubeSet S a b)) root)
      ((fun s : ℝ => Metric.infDist (x₀ + s • v) (bezTubeSet S a b)) t₀) :=
    ⟨hroot, h0.le⟩
  obtain ⟨s, hs, hfs⟩ := hsub hmem
  exact ⟨s, hs, hfs⟩

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

/-- The continuous min is a lower bound on the sampled fold: for nonempty
    site lists lying in `[a, b]`, `bezPhiMin` bounds every sample term from
    below, hence the min. (The honest direction for the sampled fold: it is
    an *over*-estimate of the true distance-to-tube, which is why the C
    can step by it without leaving the search — whether one step suffices
    for no-overshoot is exactly the density question.) -/
theorem bezPhiMin_le_foldr (S : BezSys) (x : EuclideanSpace ℝ (Fin 3))
    {a b : ℝ} (hab : a ≤ b) (us : List ℝ) (u : ℝ)
    (hu : u ∈ Set.Icc a b) (hsites : ∀ w ∈ us, w ∈ Set.Icc a b) :
    bezPhiMin S x a b ≤
      List.foldr (fun v acc => min (dist x (curvePt S v) - S.rad v) acc)
        (dist x (curvePt S u) - S.rad u) us := by
  induction us generalizing u hu with
  | nil =>
    have h := bezPhiMin_le S x hab hu
    rwa [bezPhi_eq_dist] at h
  | cons v us ih =>
    have hv : v ∈ Set.Icc a b := hsites v (by simp)
    have hrest : ∀ w ∈ us, w ∈ Set.Icc a b := fun w hw => hsites w (by simp [hw])
    have h1 : bezPhiMin S x a b ≤ dist x (curvePt S v) - S.rad v := by
      have h := bezPhiMin_le S x hab hv
      rwa [bezPhi_eq_dist] at h
    have h2 : bezPhiMin S x a b ≤
        List.foldr (fun w acc => min (dist x (curvePt S w) - S.rad w) acc)
          (dist x (curvePt S u) - S.rad u) us :=
      ih u hu hrest
    exact le_min h1 h2

theorem bezPhiMin_le_samDist (S : BezSys) (x : EuclideanSpace ℝ (Fin 3))
    {a b : ℝ} (hab : a ≤ b) (sites : List ℝ)
    (hsites : ∀ u ∈ sites, u ∈ Set.Icc a b) (hne : sites ≠ []) :
    bezPhiMin S x a b ≤ samDist S sites x := by
  cases sites with
  | nil => exact absurd rfl hne
  | cons u us =>
    have hu : u ∈ Set.Icc a b := hsites u (by simp)
    have hrest : ∀ w ∈ us, w ∈ Set.Icc a b := fun w hw => hsites w (by simp [hw])
    exact bezPhiMin_le_foldr S x hab us u hu hrest

/-! ### Quantitative sampled-vs-exact distance bound -/

/-- Lagrange's mean value theorem, collected form: a real function whose
    derivative is bounded by `M` on `[min u v, max u v]` varies by at most
    `M · |u − v|` between `u` and `v` inside `[a, b]`. -/
theorem abs_sub_le_of_deriv_bound {a b : ℝ} {M : ℝ} {g p : ℝ → ℝ}
    (hd : ∀ w : ℝ, HasDerivAt g (p w) w)
    (hb : ∀ w ∈ Set.Icc a b, |p w| ≤ M)
    {u v : ℝ} (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) :
    |g u - g v| ≤ M * |u - v| := by
  rcases le_total u v with hle | hle
  · by_cases hune : u = v
    · simp [hune]
    · have hlo : u < v := lt_of_le_of_ne hle hune
      have hcon : ContinuousOn g (Set.Icc u v) :=
        fun w _ => (hd w).differentiableAt.continuousAt.continuousWithinAt
      have hdist : DifferentiableOn ℝ g (Set.Ioo u v) :=
        fun w _ => (hd w).differentiableAt.differentiableWithinAt
      obtain ⟨ξ, hξ, hMVT⟩ := exists_deriv_eq_slope g hlo hcon hdist
      have hξu : ξ ∈ Set.Icc u v := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
      have hξa : ξ ∈ Set.Icc a b := ⟨le_trans hu.1 hξu.1, le_trans hξu.2 hv.2⟩
      have h1 : |p ξ| ≤ M := hb ξ hξa
      have hdξ : deriv g ξ = p ξ := (hd ξ).deriv
      have h3 : g v - g u = p ξ * (v - u) := by
        rw [hMVT] at hdξ
        exact (div_eq_iff (sub_ne_zero.2 hlo.ne')).mp hdξ
      have h2 : |g v - g u| ≤ M * |v - u| := by
        rw [h3, abs_mul]
        exact mul_le_mul h1 (le_refl _) (abs_nonneg _)
          (le_trans (abs_nonneg _) h1)
      rw [abs_sub_comm (g u) (g v), abs_sub_comm u v]
      exact h2
  · by_cases hune : u = v
    · simp [hune]
    · have hlo : v < u := lt_of_le_of_ne hle (Ne.symm hune)
      have hcon : ContinuousOn g (Set.Icc v u) :=
        fun w _ => (hd w).differentiableAt.continuousAt.continuousWithinAt
      have hdist : DifferentiableOn ℝ g (Set.Ioo v u) :=
        fun w _ => (hd w).differentiableAt.differentiableWithinAt
      obtain ⟨ξ, hξ, hMVT⟩ := exists_deriv_eq_slope g hlo hcon hdist
      have hξu : ξ ∈ Set.Icc v u := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
      have hξa : ξ ∈ Set.Icc a b := ⟨le_trans hv.1 hξu.1, le_trans hξu.2 hu.2⟩
      have h1 : |p ξ| ≤ M := hb ξ hξa
      have hdξ : deriv g ξ = p ξ := (hd ξ).deriv
      have h3 : g u - g v = p ξ * (u - v) := by
        rw [hMVT] at hdξ
        exact (div_eq_iff (sub_ne_zero.2 hlo.ne')).mp hdξ
      rw [h3, abs_mul]
      exact mul_le_mul h1 (le_refl _) (abs_nonneg _)
        (le_trans (abs_nonneg _) h1)

/-- The curve is `√3·M`-Lipschitz on the parameter interval when each
    component derivative is bounded by `M` there. -/
theorem curve_dist_le (S : BezSys) {a b : ℝ} {Mx : ℝ} (hM : 0 ≤ Mx)
    (h : ∀ u ∈ Set.Icc a b, |S.px u| ≤ Mx ∧ |S.py u| ≤ Mx ∧ |S.pz u| ≤ Mx)
    {u v : ℝ} (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) :
    dist (curvePt S u) (curvePt S v) ≤ Real.sqrt 3 * Mx * |u - v| := by
  have hx := abs_sub_le_of_deriv_bound (hd := S.hγx) (hb := fun w hw => (h w hw).1) hu hv
  have hy := abs_sub_le_of_deriv_bound (hd := S.hγy) (hb := fun w hw => (h w hw).2.1) hu hv
  have hz := abs_sub_le_of_deriv_bound (hd := S.hγz) (hb := fun w hw => (h w hw).2.2) hu hv
  have d2 : dist (curvePt S u) (curvePt S v) ^ 2 =
      (S.gx u - S.gx v) ^ 2 + (S.gy u - S.gy v) ^ 2 + (S.gz u - S.gz v) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp [Fin.sum_univ_three, Real.dist_eq, sq_abs]
  have s1 : (S.gx u - S.gx v) ^ 2 ≤ (Mx * |u - v|) ^ 2 := by
    rw [← sq_abs (S.gx u - S.gx v)]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have s2 : (S.gy u - S.gy v) ^ 2 ≤ (Mx * |u - v|) ^ 2 := by
    rw [← sq_abs (S.gy u - S.gy v)]
    exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  have s3 : (S.gz u - S.gz v) ^ 2 ≤ (Mx * |u - v|) ^ 2 := by
    rw [← sq_abs (S.gz u - S.gz v)]
    exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  have hsq : dist (curvePt S u) (curvePt S v) ^ 2 ≤ 3 * Mx ^ 2 * (u - v) ^ 2 := by
    rw [d2]
    have e : (Mx * |u - v|) ^ 2 = Mx ^ 2 * (u - v) ^ 2 := by rw [mul_pow, sq_abs]
    nlinarith [s1, s2, s3, e]
  calc dist (curvePt S u) (curvePt S v) =
        Real.sqrt (dist (curvePt S u) (curvePt S v) ^ 2) := (Real.sqrt_sq dist_nonneg).symm
    _ ≤ Real.sqrt (3 * Mx ^ 2 * (u - v) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 3 * Mx * |u - v| := by
        have e : (3:ℝ) * Mx ^ 2 * (u - v) ^ 2 = (Real.sqrt 3 * Mx * |u - v|) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), sq_abs]
        have h1 : (0:ℝ) ≤ Real.sqrt 3 * Mx * |u - v| :=
          mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM) (abs_nonneg _)
        rw [e, Real.sqrt_sq h1]

theorem rad_dist_le (S : BezSys) {a b : ℝ} {Mr : ℝ}
    (h : ∀ u ∈ Set.Icc a b, |S.dr u| ≤ Mr) {u v : ℝ} (hu : u ∈ Set.Icc a b)
    (hv : v ∈ Set.Icc a b) :
    |S.rad u - S.rad v| ≤ Mr * |u - v| :=
  abs_sub_le_of_deriv_bound (hd := S.hρ) (hb := h) hu hv

theorem foldr_min_le_base {f : ℝ → ℝ} : ∀ (l : List ℝ) (b : ℝ),
    List.foldr (fun v acc => min (f v) acc) b l ≤ b := by
  intro l
  induction l with
  | nil => intro b; exact le_refl _
  | cons v us ih =>
    intro b
    simp only [List.foldr]
    exact le_trans (min_le_right _ _) (ih b)

/-- The `foldr` of `min (f v)` is bounded by any member `f i`. -/
theorem foldr_min_le_mem {f : ℝ → ℝ} {l : List ℝ} {i : ℝ} {b : ℝ} (hi : i ∈ l) :
    List.foldr (fun v acc => min (f v) acc) b l ≤ f i := by
  induction l with
  | nil => simp at hi
  | cons v us ih =>
    by_cases h' : i = v
    · subst h'
      simp only [List.foldr]
      exact min_le_left _ _
    · have hi' : i ∈ us := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h h'
        · exact h
      simp only [List.foldr]
      exact le_trans (min_le_right _ _) (ih hi')

theorem samDist_le_mem (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) (sites : List ℝ)
    {i : ℝ} (hmem : i ∈ sites) :
    samDist S sites x ≤ dist x (curvePt S i) - S.rad i := by
  match sites, hmem with
  | [], hi => exact absurd hi (by simp)
  | u :: us, hi =>
    show List.foldr (fun v acc => min (dist x (curvePt S v) - S.rad v) acc)
        (dist x (curvePt S u) - S.rad u) us ≤ _
    rcases List.mem_cons.mp hi with h | h
    · subst h
      exact foldr_min_le_base us _
    · exact foldr_min_le_mem h

/-- **Quantitative sampled-vs-exact bound**: over sites with covering
    radius `R` on `[a, b]`, the sampled fold is at most
    `bezPhiMin + (√3·Mx + Mr)·R` — one Bézier-length bound plus one radius
    slope bound, times how far the site list can be from every point of
    the interval. -/
theorem samDist_le_bezPhiMin_add (S : BezSys) (x : EuclideanSpace ℝ (Fin 3))
    {a b : ℝ} (hab : a ≤ b) (Mx Mr R : ℝ) (hM : 0 ≤ Mx)
    (hMx : ∀ u ∈ Set.Icc a b,
      |S.px u| ≤ Mx ∧ |S.py u| ≤ Mx ∧ |S.pz u| ≤ Mx ∧ |S.dr u| ≤ Mr)
    (sites : List ℝ) (hsites : ∀ u ∈ sites, u ∈ Set.Icc a b) (_hne : sites ≠ [])
    (hR : ∀ u ∈ Set.Icc a b, ∃ i ∈ sites, |u - i| ≤ R) :
    samDist S sites x ≤ bezPhiMin S x a b + (Real.sqrt 3 * Mx + Mr) * R := by
  have Mr_nonneg : 0 ≤ Mr :=
    le_trans (abs_nonneg _) (hMx a ⟨le_refl a, hab⟩).2.2.2
  obtain ⟨u₀, hu₀, hφ0⟩ := bezPhiMin_eq S x hab
  obtain ⟨i, hi, hRi⟩ := hR u₀ hu₀
  have hsam : samDist S sites x ≤ dist x (curvePt S i) - S.rad i :=
    samDist_le_mem S x sites hi
  have hC : dist (curvePt S u₀) (curvePt S i) ≤ Real.sqrt 3 * Mx * |u₀ - i| :=
    curve_dist_le S hM (fun w hw => ⟨(hMx w hw).1, (hMx w hw).2.1, (hMx w hw).2.2.1⟩) hu₀ (hsites i hi)
  have hdist_xi : dist x (curvePt S i) ≤ dist x (curvePt S u₀) + Real.sqrt 3 * Mx * |u₀ - i| := by
    have h := dist_triangle x (curvePt S u₀) (curvePt S i)
    linarith [h, hC]
  have hr_rad : S.rad u₀ - S.rad i ≤ Mr * |u₀ - i| := by
    have h := rad_dist_le S (fun w hw => (hMx w hw).2.2.2) hu₀ (hsites i hi)
    have h1 := (abs_le.mp h).2
    linarith
  have hr_step : (Real.sqrt 3 * Mx + Mr) * |u₀ - i| ≤ (Real.sqrt 3 * Mx + Mr) * R := by
    apply mul_le_mul_of_nonneg_left hRi
    have h1 : (0:ℝ) ≤ Real.sqrt 3 * Mx := mul_nonneg (Real.sqrt_nonneg _) hM
    exact add_nonneg h1 Mr_nonneg
  have hφ : bezPhi S x u₀ = dist x (curvePt S u₀) - S.rad u₀ := bezPhi_eq_dist S x u₀
  calc samDist S sites x ≤ dist x (curvePt S i) - S.rad i := hsam
    _ ≤ (dist x (curvePt S u₀) + Real.sqrt 3 * Mx * |u₀ - i|) -
          (S.rad u₀ - Mr * |u₀ - i|) := by linarith [hdist_xi, hr_rad]
    _ = (dist x (curvePt S u₀) - S.rad u₀) + (Real.sqrt 3 * Mx + Mr) * |u₀ - i| := by ring
    _ ≤ bezPhiMin S x a b + (Real.sqrt 3 * Mx + Mr) * R := by
        rw [← hφ, hφ0]
        linarith [hr_step]

end
end LightRT.Geom
