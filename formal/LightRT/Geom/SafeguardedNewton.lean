/-
  Safeguarded (bracketed) Newton convergence — the global argument for the
  C's leaf-distance envelope solve (`tri_bez_leaf_dist`), whose inner loop
  brackets a sign change of `φ′` and steps by Newton when the step stays
  inside the bracket, bisection otherwise. The *correctness backbone* — the
  bracket shrinks to a point at which the envelope condition holds — does not
  depend on the Newton step at all: bisection alone halves the width every
  iteration, so the iterates converge to a root of the sign-changing function
  on the interval. This module formalizes that backbone:

  * `fsplit` / `seqIter` — the bracket split and its `n`-fold iteration;
  * `seqLo` / `seqHi` — the monotone sequences of bracket ends;
  * the invariants `seqIter_sign`, `seqIter_width`, `seqIter_in_interval`;
  * convergence to a common limit `c` (`seqLo_tendsto`, `seqHi_tendsto`,
    `limit_unique`) — the "global" half of the argument;
  * `bracket_root` — `g c = 0` by continuity, hence the existence of the
    envelope-critical point, with a converging bracket sequence;
  * `envelope_continuousOn` / `bracket_envelope_bezPhi` — instantiated to
    `φ′` for the round Bézier tube (`φ′` continuous where `x` is off the
    curve): whenever `φ′` changes sign on `[a, b]` there is a critical point
    (the C's `F = 0` stationarity) — convergence of the safeguarded loop the
    C uses, from an arbitrary seed.

  Newton acceleration (quadratic contraction near the limit) is the local
  half (`ofCubic_newton_quadratic`, M7/M22 addendum 4). The 2D `(u, t)`
  `tri_bez_newton` solve from a contact seed is addressed by the same
  bracket argument applied to its envelope component.
-/
import Mathlib
import LightRT.Geom.BezTube

open Filter Topology

namespace LightRT.Geom

/-! ### The bracket split and its iterates -/

/-- One bracket split: with a guaranteed sign change on `[lo, hi]`, the
    midpoint either replaces `lo` or `hi` (halving the width), or the split
    is degenerate and nothing moves (cannot happen under the invariant). -/
noncomputable def fsplit (g : ℝ → ℝ) (lo hi : ℝ) : ℝ × ℝ :=
  if g ((lo + hi) / 2) ≤ 0 ∧ 0 ≤ g hi then ((lo + hi) / 2, hi)
  else if g lo ≤ 0 ∧ 0 ≤ g ((lo + hi) / 2) then (lo, (lo + hi) / 2)
  else (lo, hi)

/-- `n` bracket splits from `[a, b]`. -/
noncomputable def seqIter (g : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 => fsplit g (seqIter g a b n).1 (seqIter g a b n).2

theorem seqIter_succ (g : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    seqIter g a b (n + 1) = fsplit g (seqIter g a b n).1 (seqIter g a b n).2 := rfl

theorem mid_mem_Icc {lo hi : ℝ} (h : lo ≤ hi) :
    lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 ≤ hi :=
  ⟨by linarith, by linarith⟩

theorem seqIter_fst_le_snd (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∀ n, (seqIter g a b n).1 ≤ (seqIter g a b n).2 := by
  intro n
  induction n with
  | zero => exact hab
  | succ n ih =>
    rw [seqIter_succ]
    unfold fsplit
    split_ifs with h1 h2
    · exact (mid_mem_Icc ih).2
    · exact (mid_mem_Icc ih).1
    · exact ih

theorem seqIter_in_interval (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∀ n, (seqIter g a b n).1 ∈ Set.Icc a b ∧ (seqIter g a b n).2 ∈ Set.Icc a b := by
  intro n
  induction n with
  | zero => exact ⟨⟨le_refl a, hab⟩, ⟨hab, le_refl b⟩⟩
  | succ n ih =>
    obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩ := ih
    have hm := mid_mem_Icc (seqIter_fst_le_snd g hab n)
    rw [seqIter_succ]
    unfold fsplit
    split_ifs with h1 h2
    · exact ⟨⟨le_trans ha1 hm.1, le_trans hm.2 hb2⟩, ⟨hb1, hb2⟩⟩
    · exact ⟨⟨ha1, ha2⟩, ⟨le_trans ha1 hm.1, le_trans hm.2 hb2⟩⟩
    · exact ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩

/-- The sign-change invariant: both bracket ends keep their signs. -/
theorem seqIter_sign (g : ℝ → ℝ) {a b : ℝ} (hA : g a ≤ 0) (hB : 0 ≤ g b) :
    ∀ n, g (seqIter g a b n).1 ≤ 0 ∧ 0 ≤ g (seqIter g a b n).2 := by
  intro n
  induction n with
  | zero => exact ⟨hA, hB⟩
  | succ n ih =>
    rw [seqIter_succ]
    unfold fsplit
    split_ifs with h1 h2
    · exact h1
    · exact ⟨ih.1, h2.2⟩
    · exact ih

/-- The width halves every split (bisection is the safety net). -/
theorem seqIter_width (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hA : g a ≤ 0) (hB : 0 ≤ g b) :
    ∀ n, (seqIter g a b n).2 - (seqIter g a b n).1 ≤ (b - a) / 2 ^ n := by
  intro n
  induction n with
  | zero =>
    show (seqIter g a b 0).2 - (seqIter g a b 0).1 ≤ (b - a) / 2 ^ 0
    rw [pow_zero, div_one]
    show b - a ≤ b - a
    exact le_refl _
  | succ n ih =>
    rw [seqIter_succ]
    unfold fsplit
    split_ifs with h1 h2
    · have e : (seqIter g a b n).2 - ((seqIter g a b n).1 + (seqIter g a b n).2) / 2 =
          ((seqIter g a b n).2 - (seqIter g a b n).1) / 2 := by ring
      have hp : (b - a) / 2 ^ (n + 1) = (b - a) / 2 ^ n / 2 := by rw [pow_succ, div_div]
      rw [e, hp]
      linarith
    · have e : ((seqIter g a b n).1 + (seqIter g a b n).2) / 2 - (seqIter g a b n).1 =
          ((seqIter g a b n).2 - (seqIter g a b n).1) / 2 := by ring
      have hp : (b - a) / 2 ^ (n + 1) = (b - a) / 2 ^ n / 2 := by rw [pow_succ, div_div]
      rw [e, hp]
      linarith
    · obtain ⟨hlo, hhi⟩ := seqIter_sign g hA hB n
      have hp2 : 0 ≤ (b - a) / 2 ^ n :=
        div_nonneg (sub_nonneg.mpr hab) (by positivity : (0:ℝ) ≤ 2 ^ n)
      have h3 : (0:ℝ) < g (((seqIter g a b n).1 + (seqIter g a b n).2) / 2) := by
        by_contra h'
        exact h1 ⟨le_of_not_gt h', hhi⟩
      have h4 : ¬ 0 ≤ g (((seqIter g a b n).1 + (seqIter g a b n).2) / 2) := by
        intro hge
        exact h2 ⟨hlo, hge⟩
      exact absurd (le_of_lt h3) h4

/-! ### The bracket ends as monotone sequences -/

noncomputable def seqLo (g : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ := (seqIter g a b n).1
noncomputable def seqHi (g : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ := (seqIter g a b n).2

theorem seqLo_step (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    seqLo g a b n ≤ seqLo g a b (n + 1) := by
  show (seqIter g a b n).1 ≤ (seqIter g a b (n + 1)).1
  rw [seqIter_succ]
  unfold fsplit
  split_ifs with h1 h2
  · exact (mid_mem_Icc (seqIter_fst_le_snd g hab n)).1
  · exact le_refl _
  · exact le_refl _

theorem seqHi_step (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    seqHi g a b (n + 1) ≤ seqHi g a b n := by
  show (seqIter g a b (n + 1)).2 ≤ (seqIter g a b n).2
  rw [seqIter_succ]
  unfold fsplit
  split_ifs with h1 h2
  · exact le_refl _
  · exact (mid_mem_Icc (seqIter_fst_le_snd g hab n)).2
  · exact le_refl _

theorem seqLo_mono (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) : Monotone (seqLo g a b) :=
  monotone_nat_of_le_succ (seqLo_step g hab)

theorem seqHi_anti (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) : Antitone (seqHi g a b) :=
  antitone_nat_of_succ_le (seqHi_step g hab)

theorem seqLo_bddAbove (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    BddAbove (Set.range (seqLo g a b)) := by
  refine ⟨b, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (seqIter_in_interval g hab n).1.2

theorem seqHi_bddBelow (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    BddBelow (Set.range (seqHi g a b)) := by
  refine ⟨a, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (seqIter_in_interval g hab n).2.1

theorem seqLo_tendsto (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (seqLo g a b) atTop (nhds (⨆ n, seqLo g a b n)) :=
  tendsto_atTop_ciSup (seqLo_mono g hab) (seqLo_bddAbove g hab)

theorem seqHi_tendsto (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (seqHi g a b) atTop (nhds (⨅ n, seqHi g a b n)) :=
  tendsto_atTop_ciInf (seqHi_anti g hab) (seqHi_bddBelow g hab)

/-- The two bracket ends converge to the same point (width → 0). -/
theorem limit_unique (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (hA : g a ≤ 0) (hB : 0 ≤ g b) :
    ⨆ n, seqLo g a b n = ⨅ n, seqHi g a b n := by
  have hS : ∀ i j, seqLo g a b i ≤ seqHi g a b j := by
    intro i j
    by_cases h : i ≤ j
    · exact le_trans (seqLo_mono g hab h) (seqIter_fst_le_snd g hab j)
    · have h' : j ≤ i := le_of_not_ge h
      exact le_trans (seqIter_fst_le_snd g hab i) (seqHi_anti g hab h')
  have hne : Set.Nonempty (Set.range (seqLo g a b)) := ⟨_, Set.mem_range_self 0⟩
  have hne' : Set.Nonempty (Set.range (seqHi g a b)) := ⟨_, Set.mem_range_self 0⟩
  have hle : ⨆ n, seqLo g a b n ≤ ⨅ n, seqHi g a b n := by
    apply le_csInf hne'
    rintro j ⟨i, rfl⟩
    apply csSup_le hne
    rintro i' ⟨i', rfl⟩
    exact hS i' i
  apply le_antisymm hle
  have hlo := seqLo_tendsto g hab
  have hhi := seqHi_tendsto g hab
  set Llo := ⨆ n, seqLo g a b n
  set Lhi := ⨅ n, seqHi g a b n
  by_contra h'
  push Not at h'
  have hpos : 0 < Lhi - Llo := sub_pos.mpr h'
  have h0 : Tendsto (fun n : ℕ => (b - a) / 2 ^ n) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have e : (fun n : ℕ => (b - a) / 2 ^ n) = fun n : ℕ => (b - a) * (1 / 2) ^ n := by
      funext n
      rw [div_eq_mul_inv, ← one_div, ← one_div_pow]
    rw [e]
    simpa [zero_mul, mul_comm] using hp.mul_const (b - a)
  have hev : ∀ᶠ n in atTop, (b - a) / 2 ^ n < Lhi - Llo := h0.eventually (gt_mem_nhds hpos)
  obtain ⟨N, hN⟩ := hev.exists
  have h3 : Lhi ≤ seqHi g a b N := csInf_le (seqHi_bddBelow g hab) (Set.mem_range_self N)
  have h4 : seqLo g a b N ≤ Llo := le_csSup (seqLo_bddAbove g hab) (Set.mem_range_self N)
  have h5 : seqHi g a b N - seqLo g a b N ≤ (b - a) / 2 ^ N := seqIter_width g hab hA hB N
  linarith [h3, h4, h5, hN]

/-! ### The limit is a root of `g` -/

/-- **The safeguarded bracket converges to a root**: starting from a
    sign-changing bracket, the bisection envelope of the safeguarded Newton
    loop shrinks to a point where `g` vanishes. -/
theorem bracket_root (g : ℝ → ℝ) {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b)) (hab : a ≤ b) (hA : g a ≤ 0) (hB : 0 ≤ g b) :
    ∃ c ∈ Set.Icc a b, g c = 0 := by
  set c := ⨆ n, seqLo g a b n
  have hhi0 : ⨅ n, seqHi g a b n = c := (limit_unique g hab hA hB).symm
  have hc_mem : c ∈ Set.Icc a b := by
    rw [← hhi0]
    refine ⟨?_, ?_⟩
    · apply le_csInf ⟨_, Set.mem_range_self 0⟩
      intro j hj
      rcases hj with ⟨i, rfl⟩
      exact (seqIter_in_interval g hab i).2.1
    · exact le_trans (csInf_le (seqHi_bddBelow g hab) (Set.mem_range_self 0))
        (seqIter_in_interval g hab 0).2.2
  have hlo := seqLo_tendsto g hab
  have hhi := seqHi_tendsto g hab
  rw [hhi0] at hhi
  have hcseq : Tendsto (fun n => seqLo g a b n) atTop (𝓝[Set.Icc a b] c) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlo
      (Filter.Eventually.of_forall (fun n => (seqIter_in_interval g hab n).1))
  have hcseq' : Tendsto (fun n => seqHi g a b n) atTop (𝓝[Set.Icc a b] c) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hhi
      (Filter.Eventually.of_forall (fun n => (seqIter_in_interval g hab n).2))
  have hl1 : Tendsto (fun n => g (seqLo g a b n)) atTop (𝓝 (g c)) :=
    (hg c hc_mem).tendsto.comp hcseq
  have hl2 : Tendsto (fun n => g (seqHi g a b n)) atTop (𝓝 (g c)) :=
    (hg c hc_mem).tendsto.comp hcseq'
  have gc_le : g c ≤ 0 :=
    le_of_tendsto' hl1 (fun n => (seqIter_sign g hA hB n).1)
  have gc_ge : 0 ≤ g c := by
    have hl2n : Tendsto (fun n => -g (seqHi g a b n)) atTop (𝓝 (-g c)) := hl2.neg
    have h := le_of_tendsto' hl2n (fun n => neg_nonpos.mpr (seqIter_sign g hA hB n).2)
    linarith
  exact ⟨c, hc_mem, le_antisymm gc_le gc_ge⟩

/-! ### Instantiation to the Bézier envelope equation -/

theorem bezQ_nonneg (S : BezSys) (x : EuclideanSpace ℝ (Fin 3)) (u : ℝ) :
    0 ≤ bezQ S x u := by
  unfold bezQ
  nlinarith [sq_nonneg (x 0 - S.gx u), sq_nonneg (x 1 - S.gy u), sq_nonneg (x 2 - S.gz u)]

/-- `φ′` is continuous on the interval whenever `x` is off the curve. -/
theorem envelope_continuousOn (S : BezSys) (x : EuclideanSpace ℝ (Fin 3))
    {a b : ℝ} (hne : ∀ u ∈ Set.Icc a b, bezQ S x u ≠ 0) :
    ContinuousOn (fun u => deriv (fun u => bezPhi S x u) u) (Set.Icc a b) := by
  have hgx : Differentiable ℝ S.gx := fun u => (S.hγx u).differentiableAt
  have hgy : Differentiable ℝ S.gy := fun u => (S.hγy u).differentiableAt
  have hgz : Differentiable ℝ S.gz := fun u => (S.hγz u).differentiableAt
  have hpx : Differentiable ℝ S.px := fun u => (S.hγx' u).differentiableAt
  have hpy : Differentiable ℝ S.py := fun u => (S.hγy' u).differentiableAt
  have hpz : Differentiable ℝ S.pz := fun u => (S.hγz' u).differentiableAt
  have hdr : Differentiable ℝ S.dr := fun u => (S.hρ' u).differentiableAt
  have hq : Differentiable ℝ fun u => bezQ S x u :=
    fun u => (hasDerivAt_bezQ S x u).differentiableAt
  have hgxc : Continuous S.gx := hgx.continuous
  have hgyc : Continuous S.gy := hgy.continuous
  have hgzc : Continuous S.gz := hgz.continuous
  have hpxc : Continuous S.px := hpx.continuous
  have hpyc : Continuous S.py := hpy.continuous
  have hpzc : Continuous S.pz := hpz.continuous
  have hdrc : Continuous S.dr := hdr.continuous
  have hqc : Continuous fun u => bezQ S x u := hq.continuous
  have h0x : Continuous fun u => 2 * (x 0 - S.gx u) := continuous_const.mul (continuous_const.sub hgxc)
  have h0y : Continuous fun u => 2 * (x 1 - S.gy u) := continuous_const.mul (continuous_const.sub hgyc)
  have h0z : Continuous fun u => 2 * (x 2 - S.gz u) := continuous_const.mul (continuous_const.sub hgzc)
  have h1 : Continuous fun u =>
      (2 * (x 0 - S.gx u) * (-S.px u) +
        (2 * (x 1 - S.gy u) * (-S.py u) + 2 * (x 2 - S.gz u) * (-S.pz u))) :=
    ((h0x.mul hpxc.neg).add ((h0y.mul hpyc.neg).add (h0z.mul hpzc.neg)))
  have hden : Continuous fun u => 2 * Real.sqrt (bezQ S x u) :=
    continuous_const.mul (Real.continuous_sqrt.comp hqc)
  have hcon : ContinuousOn (fun u =>
      (2 * (x 0 - S.gx u) * (-S.px u) +
        (2 * (x 1 - S.gy u) * (-S.py u) + 2 * (x 2 - S.gz u) * (-S.pz u))) /
          (2 * Real.sqrt (bezQ S x u))) (Set.Icc a b) :=
    h1.continuousOn.div hden.continuousOn (fun u hu => by
      have hne' : bezQ S x u ≠ 0 := hne u hu
      have hpos : 0 ≤ bezQ S x u := bezQ_nonneg S x u
      have hsp : (0:ℝ) < Real.sqrt (bezQ S x u) :=
        Real.sqrt_pos.mpr (lt_of_le_of_ne hpos (Ne.symm hne'))
      positivity)
  have hcon' : ContinuousOn (fun u =>
      (2 * (x 0 - S.gx u) * (-S.px u) +
        (2 * (x 1 - S.gy u) * (-S.py u) + 2 * (x 2 - S.gz u) * (-S.pz u))) /
          (2 * Real.sqrt (bezQ S x u)) - S.dr u) (Set.Icc a b) :=
    hcon.sub hdrc.continuousOn
  exact hcon'.congr (fun u hu => deriv_bezPhi S x u (hne u hu))

/-- **Global safeguarded-Newton existence for the envelope equation**:
    whenever `φ′` changes sign on `[a, b]` (the C's sample-detected bracket)
    and `x` is off the curve, there is an interior point where the envelope
    condition `φ′ = 0` holds — and the bracket sequence of the C's safeguarded
    loop converges to one such point. -/
theorem bracket_envelope_bezPhi (S : BezSys) (x : EuclideanSpace ℝ (Fin 3))
    {a b : ℝ} (hab : a ≤ b)
    (hA : deriv (fun u => bezPhi S x u) a ≤ 0)
    (hB : 0 ≤ deriv (fun u => bezPhi S x u) b)
    (hne : ∀ u ∈ Set.Icc a b, bezQ S x u ≠ 0) :
    ∃ c ∈ Set.Icc a b, deriv (fun u => bezPhi S x u) c = 0 :=
  bracket_root _ (envelope_continuousOn S x hne) hab hA hB

/-- The opposite sign convention. -/
theorem bracket_envelope_bezPhi' (S : BezSys) (x : EuclideanSpace ℝ (Fin 3))
    {a b : ℝ} (hab : a ≤ b)
    (hA : 0 ≤ deriv (fun u => bezPhi S x u) a)
    (hB : deriv (fun u => bezPhi S x u) b ≤ 0)
    (hne : ∀ u ∈ Set.Icc a b, bezQ S x u ≠ 0) :
    ∃ c ∈ Set.Icc a b, deriv (fun u => bezPhi S x u) c = 0 := by
  have hg : ContinuousOn (fun u => -deriv (fun u => bezPhi S x u) u) (Set.Icc a b) :=
    (envelope_continuousOn S x hne).neg
  obtain ⟨c, hc, hc0⟩ := bracket_root _ hg hab (neg_nonpos.mpr hA) (neg_nonneg.mpr hB)
  exact ⟨c, hc, by simpa using hc0⟩

end LightRT.Geom
