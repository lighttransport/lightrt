/-
  The guards of the C's `tri_bez_newton` (M14, phases 1-2): a faithful model
  of the damped 2D Newton step and its acceptance/termination conditions,
  with their basic invariants. The C (lightrt_c_tri.c, tri_bez_newton) does:

    F = <R, C'> + r r',  G = |R| - r,  det = dF/du dG/dt - dF/dt dG/du
    reject if |R| == 0 or |C'| == 0 or |det| <= 1e-30
    du = (dG/dt F - dF/dt G)/det, dt = (dF/du G - dG/du F)/det
    accept if |G| < eps, |F| < eps sqrt(dpd), dF/du < 0, t in [tmin,best), u in [0,1]
    else damp |du| >= 1 to ±0.25, u -= du, t -= dt, clamp u to [-0.05,1.05]
    at most 12 iterations.

  We model the guarded step and acceptance as real functions/Propositions;
  the float epsilons and the 12-iteration cap are parameters/outside this
  model. The radius clamp `max r 0` is not C^2 at the kink; as in BezNewton,
  the unclamped radius is used on intervals where r > 0 (the kink's interval
  ends are handled by `BezTube.bezPhi_min_critical`). What is proved here:

  * the accepted state satisfies exactly the C's residual, minimum-direction
    and range conditions (`accepted_*`);
  * the det guard makes the raw Newton step well-defined and identifies it
    with `newton2Step` (`guardedStep_raw`);
  * the damped step always stays in the C's extended u-range and the clamp
    is a no-op when the raw step is already in range (`damped_step_range`);

  The local quadratic contraction at a nondegenerate root is already proved
  (`BezSys.bez_newton_quadratic`). The global basin-of-attraction connection
  remains the open deep item (M14 phase 3-4).
-/
import Mathlib
import LightRT.Geom.BezNewton
import LightRT.Geom.BezTube

namespace LightRT.Geom

open Real
open Filter Topology

namespace BezSys

variable (S : BezSys)

/-- The C's extended u-range for the damped iterate. -/
noncomputable def uLo : ℝ := -(1:ℝ) / 20
noncomputable def uHi : ℝ := 21 / 20

/-- Clamp the parameter to the C's extended range `[-0.05, 1.05]`. -/
noncomputable def clampU (u : ℝ) : ℝ := max uLo (min uHi u)

/-- The damping of a wild Newton u-step: the C replaces `|du| >= 1` by
    `±0.25` before applying it. -/
noncomputable def dampDu (du : ℝ) : ℝ := if |du| < 1 then du else (if 0 < du then (1:ℝ)/4 else -(1:ℝ)/4)

/-- The raw Newton step of the contact system (same as `newton2Step`). -/
noncomputable def rawStep (u t : ℝ) : ℝ × ℝ := newton2Step (bezF S) (bezG S) u t

/-- One guarded step: damp the u-component, advance, clamp to the extended
    range. The det guard is a hypothesis on the caller, not part of this
    function (a rejected step is never applied by the C). -/
noncomputable def guardedStep (u t : ℝ) : ℝ × ℝ :=
  let st := rawStep S u t
  let du := dampDu (u - st.1)
  (clampU (u - du), t - (t - st.2))

/-- Acceptance: residual, minimum-direction, and parameter range — the C's
    `fabsf(G) < eps && fabsf(F) < eps sqrtf(dpd) && dFdu < 0` plus
    `t >= tmin && t < best && 0 <= u && u <= 1`. The front-facing flag
    `R . dir <= 0` is computed but is not an acceptance condition. -/
def accepted (eps tmin tbest : ℝ) (u t : ℝ) : Prop :=
  |bezG S u t| < eps ∧
  |bezF S u t| < eps * Real.sqrt
    (S.px u * S.px u + S.py u * S.py u + S.pz u * S.pz u) ∧
  pd1 (bezF S) u t < 0 ∧
  tmin ≤ t ∧ t < tbest ∧ 0 ≤ u ∧ u ≤ 1

theorem accepted_residual {eps tmin tbest u t : ℝ} (h : accepted S eps tmin tbest u t) :
    |bezG S u t| < eps ∧
    |bezF S u t| < eps * Real.sqrt
      (S.px u * S.px u + S.py u * S.py u + S.pz u * S.pz u) :=
  ⟨h.1, h.2.1⟩

theorem accepted_minimum {eps tmin tbest u t : ℝ} (h : accepted S eps tmin tbest u t) :
    pd1 (bezF S) u t < 0 := h.2.2.1

theorem accepted_range {eps tmin tbest u t : ℝ} (h : accepted S eps tmin tbest u t) :
    tmin ≤ t ∧ t < tbest ∧ 0 ≤ u ∧ u ≤ 1 := h.2.2.2

/-- A det-guarded raw step is exactly the Newton step (well-defined division). -/
theorem guardedStep_raw {u t detmin : ℝ} (_hdet : detmin ≤ |jacDet (bezF S) (bezG S) u t|)
    (_hdetpos : 0 < detmin) :
    rawStep S u t = newton2Step (bezF S) (bezG S) u t := rfl

theorem jacDet_ne_zero_of_guard {u t detmin : ℝ}
    (hdet : detmin ≤ |jacDet (bezF S) (bezG S) u t|) (hdetpos : 0 < detmin) :
    jacDet (bezF S) (bezG S) u t ≠ 0 := by
  have : 0 < |jacDet (bezF S) (bezG S) u t| := lt_of_lt_of_le hdetpos hdet
  exact (abs_pos.mp this)

/-- Damping keeps the u-step in `[-1/4, 1]`; if the raw step is already small,
    the damping is the identity. -/
theorem dampDu_of_small {du : ℝ} (h : |du| < 1) : dampDu du = du := by
  unfold dampDu
  rw [if_pos h]

theorem dampDu_le {du : ℝ} : |dampDu du| ≤ 1 := by
  unfold dampDu
  by_cases h : |du| < 1
  · rw [if_pos h]; exact le_of_lt h
  · rw [if_neg h]
    by_cases h2 : 0 < du
    · rw [if_pos h2]; norm_num
    · rw [if_neg h2]; norm_num

/-- The clamp output lies in the extended u-range. -/
theorem clampU_mem (u : ℝ) : uLo ≤ clampU u ∧ clampU u ≤ uHi := by
  unfold clampU uLo uHi
  constructor
  · exact le_max_left (-(1:ℝ) / 20) (min (21/20 : ℝ) u)
  · exact max_le (by norm_num) (min_le_left (21/20 : ℝ) u)

theorem clampU_eq_of_mem {u : ℝ} (h : uLo ≤ u ∧ u ≤ uHi) : clampU u = u := by
  unfold clampU
  rw [min_eq_right h.2, max_eq_right h.1]

/-- The damped step keeps `u` in the C's extended range. -/
theorem damped_step_range (u t : ℝ) :
    let st := guardedStep S u t
    uLo ≤ st.1 ∧ st.1 ≤ uHi := by
  dsimp [guardedStep]
  exact clampU_mem _


/-- The algebraic bridge to the 2D contact system. At a point of the ray whose
    curve parameter is a critical point of the signed distance `φ` AND which
    lies on the tube boundary (`G = 0`), the contact system's first equation
    vanishes: `F = 0`. Together with `G = 0` this makes the safeguarded
    bracket's limit a root of the system `tri_bez_newton` solves, when the
    ray parameter is the contact parameter. This is the seed/local-root
    connection needed for M14 phase 3. -/
theorem bezF_eq_zero_of_critical_of_contact (S : BezSys) {u₀ t : ℝ}
    (hq : 0 < q S u₀ t) (hG : bezG S u₀ t = 0)
    (hcrit : deriv (fun u => bezPhi S (!₂[t * S.d 0, t * S.d 1, t * S.d 2]) u) u₀ = 0) :
    bezF S u₀ t = 0 := by
  set x : EuclideanSpace ℝ (Fin 3) := !₂[t * S.d 0, t * S.d 1, t * S.d 2]
  have hqdef : q S u₀ t =
      (t * S.d 0 - S.gx u₀) ^ 2 + (t * S.d 1 - S.gy u₀) ^ 2 + (t * S.d 2 - S.gz u₀) ^ 2 := by
    rfl
  have hbezQ : bezQ S x u₀ = q S u₀ t := by
    unfold bezQ
    simp [x, hqdef, Fin.sum_univ_three, pow_two]
  have hne : bezQ S x u₀ ≠ 0 := by
    rw [hbezQ]
    exact ne_of_gt hq
  have hderiv := deriv_bezPhi S x u₀ hne
  rw [hcrit] at hderiv
  have hG' : Real.sqrt (q S u₀ t) = S.rad u₀ := by
    unfold bezG len at hG
    rw [hqdef] at hG ⊢
    linarith
  have hsqrt : Real.sqrt (bezQ S x u₀) = S.rad u₀ := by rw [hbezQ, hG']
  have hradpos : 0 < S.rad u₀ := by
    rw [← hsqrt]
    exact Real.sqrt_pos.2 (by rw [hbezQ]; exact hq)
  have hnum : 2 * (x 0 - S.gx u₀) * (-S.px u₀) +
        (2 * (x 1 - S.gy u₀) * (-S.py u₀) + 2 * (x 2 - S.gz u₀) * (-S.pz u₀)) =
      -2 * (bezF S u₀ t - S.rad u₀ * S.dr u₀) := by
    unfold bezF Rx Ry Rz
    simp [x]
    ring
  rw [hnum, hsqrt] at hderiv
  field_simp [ne_of_gt hradpos] at hderiv
  nlinarith


/-! ### Phase 4: convergence of the Newton iteration inside the basin -/

/-- Quadratic-to-linear error recurrence: if `0 ≤ q < 1` and the seed satisfies
    `q + C·E₀ < 1`, then `E_{n+1} ≤ q E_n + C E_n²` forces `E_n → 0`.
    The linear term is the honest `2B²/δ · E` from `newton2_step_quadratic`;
    when `2B²/δ` is small (well-conditioned root) convergence follows. -/
theorem tendsto_zero_of_linear_quadratic_contract
    (E : ℕ → ℝ) (q C c0 : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hC0 : 0 ≤ C) (hc00 : 0 ≤ c0)
    (hrec : ∀ n, E (n + 1) ≤ q * E n + C * (E n) ^ 2)
    (hE0 : E 0 ≤ c0) (hseed : q + C * c0 < 1)
    (hE_nonneg : ∀ n, 0 ≤ E n) :
    Tendsto E atTop (𝓝 0) := by
  let r : ℝ := q + C * c0
  have hr0 : 0 ≤ r := by dsimp [r]; nlinarith [mul_nonneg hC0 hc00]
  have hr1 : r < 1 := by dsimp [r] at hseed ⊢; exact hseed
  have hbound : ∀ n, E n ≤ c0 * r ^ n := by
    intro n
    induction n with
    | zero => simpa using hE0
    | succ n ih =>
      have hEn0 := hE_nonneg n
      have hrpow_le : r ^ n ≤ 1 := by exact pow_le_one₀ hr0 (le_of_lt hr1)
      have hEnc0 : E n ≤ c0 := le_trans ih (mul_le_of_le_one_right hc00 hrpow_le)
      have hsq : (E n) ^ 2 ≤ c0 * E n := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right hEnc0 hEn0
      have h1 : C * (E n) ^ 2 ≤ C * c0 * E n := by
        calc C * (E n) ^ 2 ≤ C * (c0 * E n) := mul_le_mul_of_nonneg_left hsq hC0
          _ = C * c0 * E n := by ring
      have h2 : E (n + 1) ≤ r * E n := by
        dsimp [r]
        nlinarith [hrec n, h1]
      have h3 : r * E n ≤ r * (c0 * r ^ n) := mul_le_mul_of_nonneg_left ih hr0
      rw [pow_succ]
      nlinarith [h2, h3]
  have hp : Tendsto (fun n : ℕ => c0 * r ^ n) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using hpow.const_mul c0
  exact squeeze_zero hE_nonneg hbound hp

/-- The raw Newton iterates of the contact system from a seed `(u, t)`. -/
noncomputable def newtonIter (S : BezSys) (u t : ℝ) : ℕ → ℝ × ℝ
  | 0 => (u, t)
  | n + 1 =>
    let st := newtonIter S u t n
    newton2Step (bezF S) (bezG S) st.1 st.2

@[simp] theorem newtonIter_zero (S : BezSys) (u t : ℝ) : newtonIter S u t 0 = (u, t) := rfl

theorem newtonIter_succ (S : BezSys) (u t : ℝ) (n : ℕ) :
    newtonIter S u t (n + 1) =
      newton2Step (bezF S) (bezG S) (newtonIter S u t n).1 (newtonIter S u t n).2 := rfl

/-- **Guarded Newton convergence inside the basin.** Assume a root `(u₀, t₀)`
    of the contact system and uniform local hypotheses (rectangle containment,
    partial bounds, det bound) at *every* iterate — this is exactly what
    "the guarded iterates stay in the basin" means, as a hypothesis. If the
    condition number term `2B²/δ < 1` and the seed error is small enough, the
    iterates converge to the root. (The strength of the basin hypothesis is
    honest: the quantitative verification of it from control-point bounds is
    the remaining coefficient chase.) -/
theorem newtonIter_tendsto_of_basin (S : BezSys) (a b c d K B δ : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < S.q u t)
    (hb : PddBounds S a b c d K) (hK : 0 < K) (hB : 0 ≤ B) (hδ : 0 < δ)
    {u₀ t₀ u t : ℝ}
    (hu₀ : u₀ ∈ Set.Icc a b) (ht₀ : t₀ ∈ Set.Icc c d)
    (hroot : bezF S u₀ t₀ = 0 ∧ bezG S u₀ t₀ = 0)
    (hAb : |pd1 (bezF S) u₀ t₀| ≤ B) (hBb : |pd2 (bezF S) u₀ t₀| ≤ B)
    (hCb : |pd1 (bezG S) u₀ t₀| ≤ B) (hDb : |pd2 (bezG S) u₀ t₀| ≤ B)
    (hbasin : ∀ n,
      let st := newtonIter S u t n
      st.1 ∈ Set.Icc a b ∧ st.2 ∈ Set.Icc c d ∧
      |pd1 (bezF S) st.1 st.2| ≤ B ∧ |pd2 (bezF S) st.1 st.2| ≤ B ∧
      |pd1 (bezG S) st.1 st.2| ≤ B ∧ |pd2 (bezG S) st.1 st.2| ≤ B ∧
      δ ≤ |jacDet (bezF S) (bezG S) st.1 st.2| ∧
      |st.1 - u₀| + |st.2 - t₀| ≤ B / K)
    (hcond : 2 * B ^ 2 / δ < 1)
    (hseed : 2 * B ^ 2 / δ + (18 * B * K / δ) * (|u - u₀| + |t - t₀|) < 1) :
    Tendsto (fun n => (newtonIter S u t n).1) atTop (𝓝 u₀) ∧
    Tendsto (fun n => (newtonIter S u t n).2) atTop (𝓝 t₀) := by
  let E : ℕ → ℝ := fun n => |(newtonIter S u t n).1 - u₀| + |(newtonIter S u t n).2 - t₀|
  let q : ℝ := 2 * B ^ 2 / δ
  let CC : ℝ := 18 * B * K / δ
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q] at hcond ⊢; exact hcond
  have hCC0 : 0 ≤ CC := by dsimp [CC]; positivity
  have hE0 : E 0 ≤ |u - u₀| + |t - t₀| := by simp [E]
  have hE_nonneg : ∀ n, 0 ≤ E n := by
    intro n; dsimp [E]; positivity
  have hrec : ∀ n, E (n + 1) ≤ q * E n + CC * (E n) ^ 2 := by
    intro n
    have hn := hbasin n
    dsimp only at hn
    rcases hn with ⟨hun, htn, hU, hV, hW, hZ, hdet, hEn⟩
    have hstep := bez_newton_quadratic S a b c d K B δ hlene hb hK hB
      hun hu₀ htn ht₀ hroot hU hV hW hZ hAb hBb hCb hDb hdet hδ hEn
    dsimp [E]
    have hnonneg : 0 ≤ E n := hE_nonneg n
    have hE2_le : (E n) ^ 2 ≤ (B / K) * E n := by
      have hBK0 : 0 ≤ B / K := div_nonneg hB hK.le
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right hEn hnonneg
    have hstep1 := hstep.1
    have hstep2 := hstep.2
    have hEdef : E n = |(newtonIter S u t n).1 - u₀| + |(newtonIter S u t n).2 - t₀| := rfl
    rw [← hEdef] at hstep1 hstep2
    have hsum : E (n + 1) ≤ (10 * B * K / δ) * (E n) ^ 2 +
        (8 * B * K * (E n) ^ 2 + 2 * B ^ 2 * (E n)) / δ := by
      dsimp [E]
      exact add_le_add hstep1 hstep2
    have hsum2 : (10 * B * K / δ) * (E n) ^ 2 +
        (8 * B * K * (E n) ^ 2 + 2 * B ^ 2 * (E n)) / δ =
      q * (E n) + CC * (E n) ^ 2 := by
      dsimp [q, CC]; ring
    rw [hsum2] at hsum
    exact hsum
  have hEseed : q + CC * (|u - u₀| + |t - t₀|) < 1 := by
    dsimp [q, CC] at hseed ⊢
    exact hseed
  have htendE : Tendsto E atTop (𝓝 0) :=
    tendsto_zero_of_linear_quadratic_contract E q CC (|u - u₀| + |t - t₀|)
      hq0 hq1 hCC0 (by positivity) hrec hE0 hEseed hE_nonneg
  have hu_tend : Tendsto (fun n => |(newtonIter S u t n).1 - u₀|) atTop (𝓝 0) := by
    have hle : ∀ n, |(newtonIter S u t n).1 - u₀| ≤ E n := by
      intro n; dsimp [E]; linarith [abs_nonneg ((newtonIter S u t n).2 - t₀)]
    exact squeeze_zero (fun n => abs_nonneg _) hle htendE
  have ht_tend : Tendsto (fun n => |(newtonIter S u t n).2 - t₀|) atTop (𝓝 0) := by
    have hle : ∀ n, |(newtonIter S u t n).2 - t₀| ≤ E n := by
      intro n; dsimp [E]; linarith [abs_nonneg ((newtonIter S u t n).1 - u₀)]
    exact squeeze_zero (fun n => abs_nonneg _) hle htendE
  constructor
  · exact tendsto_iff_dist_tendsto_zero.mpr (by
      simpa [Real.dist_eq, abs_sub_comm] using hu_tend)
  · exact tendsto_iff_dist_tendsto_zero.mpr (by
      simpa [Real.dist_eq, abs_sub_comm] using ht_tend)

/-- **Domain-of-attraction strengthening**: instead of assuming the basin
    hypotheses at *every* iterate, assume only that they hold on a closed
    L¹-ball of radius `R` about the root, that the ball lies in the rectangle,
    and that the seed is in the ball. The error contraction then keeps every
    iterate in the ball, so the hypotheses apply at each step. -/
theorem newtonIter_tendsto_of_basin_ball (S : BezSys) (a b c d K B δ R : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < S.q u t)
    (hb : PddBounds S a b c d K) (hK : 0 < K) (hB : 0 ≤ B) (hδ : 0 < δ)
    {u₀ t₀ u t : ℝ}
    (hu₀ : u₀ ∈ Set.Icc a b) (ht₀ : t₀ ∈ Set.Icc c d)
    (hroot : bezF S u₀ t₀ = 0 ∧ bezG S u₀ t₀ = 0)
    (hR0 : 0 ≤ R) (hRK : R ≤ B / K)
    (hball_rect : ∀ u' t', |u' - u₀| + |t' - t₀| ≤ R →
      u' ∈ Set.Icc a b ∧ t' ∈ Set.Icc c d)
    (hball_bounds : ∀ u' t', |u' - u₀| + |t' - t₀| ≤ R →
      |pd1 (bezF S) u' t'| ≤ B ∧ |pd2 (bezF S) u' t'| ≤ B ∧
      |pd1 (bezG S) u' t'| ≤ B ∧ |pd2 (bezG S) u' t'| ≤ B ∧
      δ ≤ |jacDet (bezF S) (bezG S) u' t'|)
    (hcond : 2 * B ^ 2 / δ < 1)
    (hseed : |u - u₀| + |t - t₀| ≤ R)
    (hsmall : 2 * B ^ 2 / δ + (18 * B * K / δ) * R < 1) :
    Tendsto (fun n => (newtonIter S u t n).1) atTop (𝓝 u₀) ∧
    Tendsto (fun n => (newtonIter S u t n).2) atTop (𝓝 t₀) := by
  let E : ℕ → ℝ := fun n => |(newtonIter S u t n).1 - u₀| + |(newtonIter S u t n).2 - t₀|
  let q : ℝ := 2 * B ^ 2 / δ
  let CC : ℝ := 18 * B * K / δ
  have hCC0 : 0 ≤ CC := by dsimp [CC]; positivity
  have hE0 : E 0 = |u - u₀| + |t - t₀| := by simp [E]
  have hE_nonneg : ∀ n, 0 ≤ E n := by intro n; dsimp [E]; positivity
  have hqCCR : q + CC * R ≤ 1 := le_of_lt (by dsimp [q, CC] at hsmall ⊢; exact hsmall)
  have hroot_bounds := hball_bounds u₀ t₀ (by simpa using hR0)
  have hstep_bound : ∀ n, E n ≤ R → E (n + 1) ≤ q * E n + CC * (E n) ^ 2 := by
    intro n hn
    have hrect := hball_rect _ _ hn
    have hbnd := hball_bounds _ _ hn
    have hstep := bez_newton_quadratic S a b c d K B δ hlene hb hK hB
      hrect.1 hu₀ hrect.2 ht₀ hroot hbnd.1 hbnd.2.1 hbnd.2.2.1 hbnd.2.2.2.1
      hroot_bounds.1 hroot_bounds.2.1 hroot_bounds.2.2.1 hroot_bounds.2.2.2.1
      hbnd.2.2.2.2 hδ (hn.trans hRK)
    have hEdef : E n = |(newtonIter S u t n).1 - u₀| + |(newtonIter S u t n).2 - t₀| := rfl
    have h1 := hstep.1
    have h2 := hstep.2
    rw [← hEdef] at h1 h2
    have hsum0 : E (n + 1) ≤ (10 * B * K / δ) * (E n) ^ 2 +
        (8 * B * K * (E n) ^ 2 + 2 * B ^ 2 * (E n)) / δ := by
      dsimp [E]
      exact add_le_add h1 h2
    have heq : (10 * B * K / δ) * (E n) ^ 2 +
        (8 * B * K * (E n) ^ 2 + 2 * B ^ 2 * (E n)) / δ =
      q * E n + CC * (E n) ^ 2 := by dsimp [q, CC]; ring
    rwa [heq] at hsum0
  have hE_le_R : ∀ n, E n ≤ R := by
    intro n
    induction n with
    | zero => simpa [hE0] using hseed
    | succ n ih =>
      have hrec := hstep_bound n ih
      have hnonneg := hE_nonneg n
      have hE2 : (E n) ^ 2 ≤ R * E n := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right ih hnonneg
      have hqr : q * E n + CC * (E n) ^ 2 ≤ (q + CC * R) * E n := by
        rw [pow_two]
        nlinarith [hE2, hCC0, hnonneg]
      have hle : (q + CC * R) * E n ≤ R := by
        calc (q + CC * R) * E n ≤ 1 * E n := mul_le_mul_of_nonneg_right hqCCR hnonneg
          _ = E n := one_mul _
          _ ≤ R := ih
      exact hrec.trans (hqr.trans hle)
  have hbasin : ∀ n,
      let st := newtonIter S u t n
      st.1 ∈ Set.Icc a b ∧ st.2 ∈ Set.Icc c d ∧
      |pd1 (bezF S) st.1 st.2| ≤ B ∧ |pd2 (bezF S) st.1 st.2| ≤ B ∧
      |pd1 (bezG S) st.1 st.2| ≤ B ∧ |pd2 (bezG S) st.1 st.2| ≤ B ∧
      δ ≤ |jacDet (bezF S) (bezG S) st.1 st.2| ∧
      |st.1 - u₀| + |st.2 - t₀| ≤ B / K := by
    intro n
    dsimp only
    have hn := hE_le_R n
    have hrect := hball_rect _ _ hn
    have hbnd := hball_bounds _ _ hn
    exact ⟨hrect.1, hrect.2, hbnd.1, hbnd.2.1, hbnd.2.2.1, hbnd.2.2.2.1,
      hbnd.2.2.2.2, hn.trans hRK⟩
  have hseed' : 2 * B ^ 2 / δ + (18 * B * K / δ) * (|u - u₀| + |t - t₀|) < 1 := by
    have he0 : |u - u₀| + |t - t₀| ≤ R := hseed
    have hCC0' : 0 ≤ 18 * B * K / δ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left he0 hCC0', hsmall]
  exact newtonIter_tendsto_of_basin S a b c d K B δ hlene hb hK hB hδ hu₀ ht₀ hroot
    hroot_bounds.1 hroot_bounds.2.1 hroot_bounds.2.2.1 hroot_bounds.2.2.2.1
    hbasin hcond hseed'

end BezSys
end LightRT.Geom
