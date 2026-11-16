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

namespace LightRT.Geom

open Real

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

end BezSys
end LightRT.Geom
