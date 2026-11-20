/-
  Round-linear curve intersector over R: the swept-ball tube of a strand
  segment (tapered cone + end spheres, Embree round-linear curves), with
  hit soundness and control-box containment. Tier 1 item 1 of the roadmap;
  builds on Geom/Hull.lean's `Hull.linear_tube_in_box`.
-/
import Mathlib
import LightRT.Geom.Hull
import LightRT.Geom.Basic

namespace LightRT.Geom
open LightRT.Geom.Hull
noncomputable section

/-- Centerline of a linear strand at parameter `s`. -/
def roundLinearCenter (p0 p1 : Vec3) (s : ℝ) : Vec3 := (1 - s) • p0 + s • p1

/-- Interpolated radius of a round-linear segment. -/
def roundLinearRadius (r0 r1 : ℝ) (s : ℝ) : ℝ := (1 - s) * r0 + s * r1

/-- The swept-ball tube: points within the interpolated radius of some
    centerline point. This is exactly the Embree round-linear curve. -/
def OnRoundLinear (p0 p1 : Vec3) (r0 r1 : ℝ) (x : Vec3) : Prop :=
  ∃ s ∈ Set.Icc (0:ℝ) 1, dist x (roundLinearCenter p0 p1 s) ≤ roundLinearRadius r0 r1 s

/-- A ray hit on a round-linear tube within the parameter window. -/
def HitsRoundLinear (o d p0 p1 : Vec3) (r0 r1 tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnRoundLinear p0 p1 r0 r1 (o + t • d)

/-- **Sampled acceptance is sound**: a ray point inside the swept tube at a
    parameter in range is a genuine round-linear hit (definitionally). -/
theorem hitsRoundLinear_of_sample (o d p0 p1 : Vec3) (r0 r1 tmin tbest t : ℝ)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hmem : OnRoundLinear p0 p1 r0 r1 (o + t • d)) :
    HitsRoundLinear o d p0 p1 r0 r1 tmin tbest t := ⟨htmin, htbest, hmem⟩


/-- A flat (ribbon) linear curve: for a ray direction `dir`, the width axis is
    `b = normalize(cross(p1-p0, dir))` (the ray-facing ribbon of width `2r(s)`).
    A point is on the ribbon if it is `C(s) + w·b` with `|w| ≤ r(s)`. -/
def OnFlatLinear (p0 p1 : Vec3) (r0 r1 : ℝ) (dir b : Vec3) (x : Vec3) : Prop :=
  ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ w : ℝ, |w| ≤ roundLinearRadius r0 r1 s ∧
    x = roundLinearCenter p0 p1 s + w • b

def HitsFlatLinear (o d p0 p1 : Vec3) (r0 r1 : ℝ) (b : Vec3)
    (tmin tbest t : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ OnFlatLinear p0 p1 r0 r1 d b (o + t • d)

/-- Flat-curve sampled acceptance is sound (definitionally). -/
theorem hitsFlatLinear_of_sample (o d p0 p1 : Vec3) (r0 r1 : ℝ) (b : Vec3)
    (tmin tbest t : ℝ) (htmin : tmin ≤ t) (htbest : t < tbest)
    (hmem : OnFlatLinear p0 p1 r0 r1 d b (o + t • d)) :
    HitsFlatLinear o d p0 p1 r0 r1 b tmin tbest t := ⟨htmin, htbest, hmem⟩


lemma norm_roundLinearCenter_le (p0 p1 : Vec3) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖roundLinearCenter p0 p1 s‖ ≤ ‖p0‖ + ‖p1‖ := by
  unfold roundLinearCenter
  calc
    ‖(1 - s) • p0 + s • p1‖ ≤ ‖(1 - s) • p0‖ + ‖s • p1‖ := norm_add_le _ _
    _ = |1 - s| * ‖p0‖ + |s| * ‖p1‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖p0‖ + ‖p1‖ := by
      have h1 : |1 - s| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hs1)]; linarith
      have h2 : |s| ≤ 1 := by rw [abs_of_nonneg hs0]; exact hs1
      nlinarith [norm_nonneg p0, norm_nonneg p1]

lemma roundLinearRadius_le_abs (r0 r1 : ℝ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    roundLinearRadius r0 r1 s ≤ |r0| + |r1| := by
  unfold roundLinearRadius
  have h1s : 0 ≤ 1 - s := by linarith
  calc
    (1 - s) * r0 + s * r1 ≤ (1 - s) * |r0| + s * |r1| := by
      gcongr <;> exact le_abs_self _
    _ ≤ |r0| + |r1| := by nlinarith [abs_nonneg r0, abs_nonneg r1]

theorem isClosed_roundLinearTube (p0 p1 : Vec3) (r0 r1 : ℝ) :
    IsClosed {x : Vec3 | OnRoundLinear p0 p1 r0 r1 x} := by
  let A : Set (Vec3 × ℝ) := {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    dist p.1 (roundLinearCenter p0 p1 p.2) ≤ roundLinearRadius r0 r1 p.2}
  have hdist_cont : Continuous (fun p : Vec3 × ℝ => dist p.1 (roundLinearCenter p0 p1 p.2)) := by
    unfold roundLinearCenter
    fun_prop
  have hrad_cont : Continuous (fun p : Vec3 × ℝ => roundLinearRadius r0 r1 p.2) := by
    unfold roundLinearRadius
    fun_prop
  have hAclosed : IsClosed A := by
    dsimp [A]
    exact (isClosed_Icc.preimage continuous_snd).inter (isClosed_le hdist_cont hrad_cont)
  have hAbdd : Bornology.IsBounded A := by
    let R : ℝ := ‖p0‖ + ‖p1‖ + |r0| + |r1| + 1
    rw [Metric.isBounded_iff_subset_closedBall (0 : Vec3 × ℝ)]
    refine ⟨R, ?_⟩
    intro p hp
    rcases hp with ⟨hs, hdist⟩
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]
    simp only [Prod.fst_zero, Prod.snd_zero]
    constructor
    · rw [dist_zero_right]
      have hc := norm_roundLinearCenter_le p0 p1 p.2 hs.1 hs.2
      have hr := roundLinearRadius_le_abs r0 r1 p.2 hs.1 hs.2
      calc ‖p.1‖ = ‖roundLinearCenter p0 p1 p.2 + (p.1 - roundLinearCenter p0 p1 p.2)‖ := by
              congr 1; abel
        _ ≤ ‖roundLinearCenter p0 p1 p.2‖ + ‖p.1 - roundLinearCenter p0 p1 p.2‖ := norm_add_le _ _
        _ = ‖roundLinearCenter p0 p1 p.2‖ + dist p.1 (roundLinearCenter p0 p1 p.2) := by rw [dist_eq_norm]
        _ ≤ (‖p0‖ + ‖p1‖) + (|r0| + |r1|) := add_le_add hc (hdist.trans hr)
        _ ≤ R := by dsimp [R]; linarith
    · rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      dsimp [R]
      nlinarith [hs.2, norm_nonneg p0, norm_nonneg p1, abs_nonneg r0, abs_nonneg r1]
  have hAcompact : IsCompact A := (Metric.isCompact_iff_isClosed_bounded).2 ⟨hAclosed, hAbdd⟩
  have himage : Prod.fst '' A = {x : Vec3 | OnRoundLinear p0 p1 r0 r1 x} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, hp.1, hp.2⟩
    · rintro ⟨s, hs, hdist⟩
      exact ⟨(x, s), ⟨hs, hdist⟩, rfl⟩
  rw [← himage]
  exact (hAcompact.image continuous_fst).isClosed

theorem isClosed_flatLinearTube (p0 p1 b : Vec3) (r0 r1 : ℝ) :
    IsClosed {x : Vec3 | OnFlatLinear p0 p1 r0 r1 p0 b x} := by
  -- OnFlatLinear ignores its `dir` argument except through b, so any dir works
  let B : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ |p.2| ≤ roundLinearRadius r0 r1 p.1}
  have hBclosed : IsClosed B := by
    dsimp [B]
    have hc : Continuous (fun p : ℝ × ℝ => roundLinearRadius r0 r1 p.1) := by
      unfold roundLinearRadius; fun_prop
    exact isClosed_Icc.preimage continuous_fst |>.inter (isClosed_le (continuous_abs.comp continuous_snd) hc)
  have hBbdd : Bornology.IsBounded B := by
    let R : ℝ := |r0| + |r1| + 1
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)]
    refine ⟨R, ?_⟩
    intro p hp
    rcases hp with ⟨hs, hw⟩
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]
    simp only [Prod.fst_zero, Prod.snd_zero]
    constructor
    · rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      dsimp [R]; nlinarith [hs.2, abs_nonneg r0, abs_nonneg r1]
    · rw [Real.dist_eq, sub_zero]
      have hr := roundLinearRadius_le_abs r0 r1 p.1 hs.1 hs.2
      dsimp [R]; nlinarith [hw, hr]
  have hBcompact : IsCompact B := (Metric.isCompact_iff_isClosed_bounded).2 ⟨hBclosed, hBbdd⟩
  let g : ℝ × ℝ → Vec3 := fun p => roundLinearCenter p0 p1 p.1 + p.2 • b
  have hgcont : Continuous g := by
    dsimp [g]; unfold roundLinearCenter; fun_prop
  have himage : g '' B = {x : Vec3 | OnFlatLinear p0 p1 r0 r1 p0 b x} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
    · rintro ⟨s, hs, w, hw, hx⟩
      refine ⟨(s, w), ⟨hs, hw⟩, ?_⟩
      simpa [g] using hx.symm
  rw [← himage]
  exact (hBcompact.image hgcont).isClosed

theorem roundLinear_exists_nearest_hit (o d p0 p1 : Vec3) (r0 r1 tmin tbest : ℝ)
    (hhit : ∃ t, HitsRoundLinear o d p0 p1 r0 r1 tmin tbest t) :
    ∃ tstar, HitsRoundLinear o d p0 p1 r0 r1 tmin tbest tstar ∧
      ∀ t, HitsRoundLinear o d p0 p1 r0 r1 tmin tbest t → tstar ≤ t := by
  let H : Set ℝ := {t | tmin ≤ t ∧ t ≤ tbest ∧ OnRoundLinear p0 p1 r0 r1 (o + t • d)}
  have hray : Continuous (fun t : ℝ => o + t • d) := by fun_prop
  have hH_eq : H = Set.Icc tmin tbest ∩ (fun t : ℝ => o + t • d) ⁻¹' {x : Vec3 | OnRoundLinear p0 p1 r0 r1 x} := by
    ext t
    simp [H, and_assoc]
  have hHclosed : IsClosed H := by
    rw [hH_eq]
    exact (isClosed_Icc : IsClosed (Set.Icc tmin tbest)).inter ((isClosed_roundLinearTube p0 p1 r0 r1).preimage hray)
  have hHsub : H ⊆ Set.Icc tmin tbest := by intro t ht; exact ⟨ht.1, ht.2.1⟩
  have hHcompact : IsCompact H := (isCompact_Icc : IsCompact (Set.Icc tmin tbest)).of_isClosed_subset hHclosed hHsub
  rcases hhit with ⟨t0, ht0min, ht0best, ht0on⟩
  have ht0H : t0 ∈ H := ⟨ht0min, le_of_lt ht0best, ht0on⟩
  obtain ⟨tstar, htstarH, hmin⟩ := hHcompact.exists_isMinOn ⟨t0, ht0H⟩ continuous_id.continuousOn
  have htstar_best : tstar < tbest := lt_of_le_of_lt (hmin ht0H) ht0best
  refine ⟨tstar, ⟨htstarH.1, htstar_best, htstarH.2.2⟩, ?_⟩
  intro t ht
  exact hmin ⟨ht.1, le_of_lt ht.2.1, ht.2.2⟩


/-- **Nearest flat-ribbon hit exists** (no closedness hypothesis). -/
theorem flatLinear_exists_nearest_hit (o d p0 p1 b : Vec3) (r0 r1 tmin tbest : ℝ)
    (hhit : ∃ t, HitsFlatLinear o d p0 p1 r0 r1 b tmin tbest t) :
    ∃ tstar, HitsFlatLinear o d p0 p1 r0 r1 b tmin tbest tstar ∧
      ∀ t, HitsFlatLinear o d p0 p1 r0 r1 b tmin tbest t → tstar ≤ t := by
  -- OnFlatLinear's `dir` argument is unused; instantiate it with p0.
  let H : Set ℝ := {t | tmin ≤ t ∧ t ≤ tbest ∧ OnFlatLinear p0 p1 r0 r1 p0 b (o + t • d)}
  have hray : Continuous (fun t : ℝ => o + t • d) := by fun_prop
  have hH_eq : H = Set.Icc tmin tbest ∩
      (fun t : ℝ => o + t • d) ⁻¹' {x : Vec3 | OnFlatLinear p0 p1 r0 r1 p0 b x} := by
    ext t; simp [H, and_assoc]
  have hHclosed : IsClosed H := by
    rw [hH_eq]
    exact (isClosed_Icc : IsClosed (Set.Icc tmin tbest)).inter
      ((isClosed_flatLinearTube p0 p1 b r0 r1).preimage hray)
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
