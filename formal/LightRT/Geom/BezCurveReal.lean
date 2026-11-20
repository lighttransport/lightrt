/-
  Cubic-Bezier curve ray-hit API over R: soundness, completeness and nearest
  hit, composing the existing M14 BezTube / SphereTrace / BezFirstContact
  chain. Tier 1 item 1 of the roadmap.
-/
import Mathlib
import LightRT.Geom.BezFirstContact

namespace LightRT.Geom
noncomputable section
open Filter Topology

/-- A ray hit on a cubic-Bezier tube within the parameter window. -/
def HitsBezCurveRay (S : BezSys) (a b tmin tbest : ℝ)
    (x₀ v : EuclideanSpace ℝ (Fin 3)) (t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ x₀ + t • v ∈ bezTubeSet S a b

/-- **Soundness**: a sampled-accepted contact is a genuine Bezier-tube hit. -/
theorem bezCurve_hit_of_sampled_accept (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u) (sites : List ℝ)
    (hsites : ∀ u ∈ sites, u ∈ Set.Icc a b) (hne : sites ≠ [])
    {x₀ v : EuclideanSpace ℝ (Fin 3)} {tmin tbest t : ℝ}
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hsam : samDist S sites (x₀ + t • v) ≤ 0) :
    HitsBezCurveRay S a b tmin tbest x₀ v t := by
  refine ⟨htmin, htbest, ?_⟩
  exact samDist_nonpos_mem_tube S (x₀ + t • v) hab hrad sites hsites hne hsam

/-- **Completeness**: if the ray is outside the tube at `t₀` and inside at a
    later `root`, some parameter in between touches the tube boundary. -/
theorem bezCurve_complete (S : BezSys) {a b : ℝ} (hab : a ≤ b)
    (hrad : ∀ u ∈ Set.Icc a b, 0 ≤ S.rad u)
    {x₀ v : EuclideanSpace ℝ (Fin 3)} {t₀ root : ℝ} (ht : t₀ < root)
    (hout : 0 < Metric.infDist (x₀ + t₀ • v) (bezTubeSet S a b))
    (hin : Metric.infDist (x₀ + root • v) (bezTubeSet S a b) ≤ 0) :
    ∃ s ∈ Set.Icc t₀ root, x₀ + s • v ∈ bezTubeSet S a b :=
  bez_first_contact_boundary S hab hrad ht hout hin

lemma continuous_curvePt (S : BezSys) : Continuous (curvePt S) := by
  let f : ℝ → (Fin 3 → ℝ) := fun u => ![S.gx u, S.gy u, S.gz u]
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa [f] using (continuous_iff_continuousAt.2 fun u => (S.hγx u).continuousAt)
    · simpa [f] using (continuous_iff_continuousAt.2 fun u => (S.hγy u).continuousAt)
    · simpa [f] using (continuous_iff_continuousAt.2 fun u => (S.hγz u).continuousAt)
  have hc : Continuous (fun u => WithLp.toLp 2 (V := ∀ _ : Fin 3, ℝ) (f u)) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp hf
  change Continuous (fun u => !₂[S.gx u, S.gy u, S.gz u])
  exact hc

lemma continuous_rad (S : BezSys) : Continuous S.rad := by
  exact continuous_iff_continuousAt.2 (fun u => (S.hρ u).continuousAt)

theorem isClosed_bezTubeSet (S : BezSys) (a b : ℝ) : IsClosed (bezTubeSet S a b) := by
  let A : Set (EuclideanSpace ℝ (Fin 3) × ℝ) :=
    {p | p.2 ∈ Set.Icc a b ∧ dist p.1 (curvePt S p.2) ≤ S.rad p.2}
  have hpair : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × ℝ => (p.1, curvePt S p.2)) := by
    exact continuous_fst.prodMk ((continuous_curvePt S).comp continuous_snd)
  have hdist_cont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × ℝ => dist p.1 (curvePt S p.2)) := by
    exact continuous_dist.comp hpair
  have hrad_cont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × ℝ => S.rad p.2) :=
    (continuous_rad S).comp continuous_snd
  have hAclosed : IsClosed A := by
    dsimp [A]
    exact (isClosed_Icc.preimage continuous_snd).inter (isClosed_le hdist_cont hrad_cont)
  -- boundedness
  have hcp : IsCompact (curvePt S '' Set.Icc a b) :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).image (continuous_curvePt S)
  have hrad : IsCompact (S.rad '' Set.Icc a b) :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).image (continuous_rad S)
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 3))).1 hcp.isBounded
  obtain ⟨D, hD⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hrad.isBounded
  have hAbdd : Bornology.IsBounded A := by
    rw [Metric.isBounded_iff_subset_closedBall ((0 : EuclideanSpace ℝ (Fin 3)), (0 : ℝ))]
    refine ⟨|C| + |D| + |a| + |b| + 1, ?_⟩
    intro p hp
    rcases hp with ⟨hu, hdist⟩
    have hpc : curvePt S p.2 ∈ curvePt S '' Set.Icc a b := ⟨p.2, hu, rfl⟩
    have hpr : S.rad p.2 ∈ S.rad '' Set.Icc a b := ⟨p.2, hu, rfl⟩
    have hCp := hC hpc
    have hDr := hD hpr
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]
    simp only [Prod.fst_zero, Prod.snd_zero]
    constructor
    · rw [dist_zero_right]
      calc ‖p.1‖ = ‖curvePt S p.2 + (p.1 - curvePt S p.2)‖ := by congr 1; abel
        _ ≤ ‖curvePt S p.2‖ + dist p.1 (curvePt S p.2) := by
              rw [dist_eq_norm]; exact norm_add_le _ _
        _ ≤ |C| + |D| := by
          have hc0 : ‖curvePt S p.2‖ ≤ C := by simpa [Metric.mem_closedBall, dist_zero_right] using hCp
          have hd0 : S.rad p.2 ≤ D := by
            have := hDr; rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
            exact le_trans (le_abs_self _) this
          exact add_le_add (le_trans hc0 (le_abs_self C)) (le_trans (hdist.trans hd0) (le_abs_self D))
        _ ≤ |C| + |D| + |a| + |b| + 1 := by nlinarith [abs_nonneg a, abs_nonneg b]
    · rw [Real.dist_eq, sub_zero]
      have hd0 : S.rad p.2 ≤ D := by
        have := hDr; rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
        exact le_trans (le_abs_self _) this
      have hp2abs : |p.2| ≤ |a| + |b| := by
        apply abs_le.mpr
        constructor
        · have ha' : -(|a| + |b|) ≤ a := by nlinarith [neg_le_abs a, abs_nonneg b]
          exact le_trans ha' hu.1
        · have hb' : b ≤ |a| + |b| := by nlinarith [le_abs_self b, abs_nonneg a]
          exact le_trans hu.2 hb'
      nlinarith [abs_nonneg C, abs_nonneg D, abs_nonneg a, abs_nonneg b]
  have hAcompact : IsCompact A := (Metric.isCompact_iff_isClosed_bounded).2 ⟨hAclosed, hAbdd⟩
  have himage : Prod.fst '' A = bezTubeSet S a b := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      unfold bezTubeSet
      simp only [Set.mem_iUnion]
      exact ⟨p.2, hp.1, Metric.mem_closedBall.mpr hp.2⟩
    · intro hx
      unfold bezTubeSet at hx
      simp only [Set.mem_iUnion] at hx
      rcases hx with ⟨u, hu, hball⟩
      exact ⟨(x, u), ⟨hu, Metric.mem_closedBall.mp hball⟩, rfl⟩
  rw [← himage]
  exact (hAcompact.image continuous_fst).isClosed

theorem bezCurve_exists_nearest_hit (S : BezSys) (a b tmin tbest : ℝ)
    (x₀ v : EuclideanSpace ℝ (Fin 3))
    (hhit : ∃ t, HitsBezCurveRay S a b tmin tbest x₀ v t) :
    ∃ tstar, HitsBezCurveRay S a b tmin tbest x₀ v tstar ∧
      ∀ t, HitsBezCurveRay S a b tmin tbest x₀ v t → tstar ≤ t := by
  let H : Set ℝ := {t | tmin ≤ t ∧ t ≤ tbest ∧ x₀ + t • v ∈ bezTubeSet S a b}
  have hray : Continuous (fun t : ℝ => x₀ + t • v) := by fun_prop
  have hH_eq : H = Set.Icc tmin tbest ∩ (fun t : ℝ => x₀ + t • v) ⁻¹' bezTubeSet S a b := by
    ext t; simp [H, and_assoc]
  have hHclosed : IsClosed H := by
    rw [hH_eq]
    exact (isClosed_Icc : IsClosed (Set.Icc tmin tbest)).inter ((isClosed_bezTubeSet S a b).preimage hray)
  have hHsub : H ⊆ Set.Icc tmin tbest := by intro t ht; exact ⟨ht.1, ht.2.1⟩
  have hHcompact : IsCompact H := (isCompact_Icc : IsCompact (Set.Icc tmin tbest)).of_isClosed_subset hHclosed hHsub
  rcases hhit with ⟨t0, ht0min, ht0best, ht0on⟩
  have ht0H : t0 ∈ H := ⟨ht0min, le_of_lt ht0best, ht0on⟩
  obtain ⟨tstar, htstarH, hmin⟩ := hHcompact.exists_isMinOn ⟨t0, ht0H⟩ continuous_id.continuousOn
  have htstar_best : tstar < tbest := lt_of_le_of_lt (hmin ht0H) ht0best
  refine ⟨tstar, ⟨htstarH.1, htstar_best, htstarH.2.2⟩, ?_⟩
  intro t ht
  exact hmin ⟨ht.1, le_of_lt ht.2.1, ht.2.2⟩

end
end LightRT.Geom
