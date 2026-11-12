/-
  Range-free `EXACT_NEAREST` key bound (`BVH/ExactPrune.woop_key_le_t`
  without the `InRange` hypotheses): the C-call-site instantiation of the
  range-free Woop `t` bound in `Robust/Total.lean`.

  `tri_exn_key` uses the float key `fl(m - fl(2⁻¹⁹ M))` (`2⁻¹⁹ = 32u`). The
  total (subnormal-safe) error adds `η` per rounding, so the key bound loses
  `3η` and the Woop `t` lower bound loses `49η(1+M)/a0 + η`; the key is still
  below `t` whenever that slack fits inside the `0.9uM` headroom between the
  key's `32uM` and the error's `29.1uM` (`hfit` below). For a real scene
  (`M` not subnormal) this holds when the projected area `a0` is at least
  roughly `50·2⁻¹²⁶(1+M)/M`, the same `1e-37`-scale regime as the dilation
  floor (`FP/TotalErr.fl_add_margin_ge`).
-/
import LightRT.Robust.Total
import LightRT.BVH.ExactPrune

namespace LightRT.BVH
namespace ExactPrune
open LightRT.FP LightRT.FP.Binary32 LightRT.Robust

/-- Range-free float key bound: `fl(m - fl(cM)) ≤ m - 30uM + 3η` for
    `32u ≤ c ≤ 1`. The `η` absolute errors only add `3η`; the `c` margin
    survives because `u ≤ 1/1000`. -/
theorem key_le_total (m M c : ℝ) (hmM : |m| ≤ M) (hc : 32 * model.u ≤ c)
    (hc1 : c ≤ 1) :
    model.fl (m - model.fl (c * M)) ≤ m - 30 * model.u * M + 3 * eta := by
  have u0 : 0 < model.u := model.u_pos
  have u1 : model.u ≤ 1 := le_of_lt (lt_of_lt_of_le model.u_lt_one (by norm_num))
  have un : model.u ≤ 1 / 1000 := by unfold model; norm_num [zpow_neg]
  have en : 0 ≤ eta := eta_pos.le
  have en' : 0 < eta := eta_pos
  have hM : 0 ≤ M := (abs_nonneg m).trans hmM
  have hc0 : 0 ≤ c := by linarith [model.u_pos]
  have hcM : 0 ≤ c * M := mul_nonneg hc0 hM
  have heta_eq : (2:ℝ)^(-150:ℤ) = eta := rfl
  obtain ⟨h1, h1'⟩ := abs_le.1 (model_abs_err_total (c * M))
  rw [abs_of_nonneg hcM, heta_eq] at h1 h1'
  obtain ⟨h2, h2'⟩ := abs_le.1 (model_abs_err_total (m - model.fl (c * M)))
  rw [heta_eq] at h2 h2'
  -- float bounds
  have flc_lo : c * M * (1 - model.u) - eta ≤ model.fl (c * M) := by nlinarith [h1]
  have flc_hi : model.fl (c * M) ≤ c * M + model.u * (c * M) + eta := by nlinarith [h1']
  have hflc : |model.fl (c * M)| ≤ c * M + model.u * (c * M) + eta := by
    rw [abs_le]
    exact ⟨by linarith [flc_lo], flc_hi⟩
  have hx : |m - model.fl (c * M)| ≤ M + c * M + model.u * (c * M) + eta := by
    have := abs_sub m (model.fl (c * M))
    linarith [hmM, hflc]
  have step : model.fl (m - model.fl (c * M)) ≤
      (m - model.fl (c * M)) + model.u * (M + c * M + model.u * (c * M) + eta) + eta := by
    have := mul_le_mul_of_nonneg_left hx u0.le
    linarith [h2']
  -- coefficient arithmetic
  have hcpos : 0 ≤ M * (1 - 2 * model.u - model.u ^ 2) := by
    have : 1 - 2 * model.u - model.u ^ 2 ≥ 0 := by nlinarith [u0, un]
    positivity
  have hprod := mul_le_mul_of_nonneg_right hc hcpos
  have hu3 : model.u ^ 2 ≤ model.u / 1000 := by nlinarith [un, u0]
  have hu4 : model.u ^ 3 ≤ model.u / 1000 := by nlinarith [un, u0, hu3]
  have hu5 : 64 * model.u ^ 2 + 32 * model.u ^ 3 ≤ model.u := by nlinarith [hu3, hu4]
  have hueta : model.u * eta ≤ eta := by nlinarith [u1, en]
  have hmain : model.fl (m - model.fl (c * M)) ≤
      m - c * M * (1 - 2 * model.u - model.u ^ 2) + model.u * M + eta * (2 + model.u) := by
    nlinarith [step, flc_lo]
  have hbig : m - c * M * (1 - 2 * model.u - model.u ^ 2) + model.u * M + eta * (2 + model.u) ≤
      m - 30 * model.u * M + 3 * eta := by
    nlinarith [hprod, hM, hu5, hueta, en, u0, un]
  linarith [hmain, hbig]

set_option maxHeartbeats 1600000 in
/-- **C-range instantiation of the range-free Woop bound.** The `EXACT_NEAREST`
    node key (`tri_exn_key`: `fl(m - fl(2⁻¹⁹ M))`, i.e. `c = 32u`) is below the
    watertight leaf's `t` for every accepted triangle whose vertices' *computed*
    depths lie in `[m, M]` of the node's dominant-axis slab, provided the
    `η/a0` slack fits: `49η(1+M)/a0 + 4η ≤ 0.9 u M`. The remaining C-side
    condition is a projected area `a0` not far below
    `~50·2⁻¹²⁶(1+M)/M`, i.e. the regime where the `1e-37` dilation floor
    applies. This is the `InRange`-free replacement for
    `ExactPrune.woop_key_le_t` (positive edge-sign class). -/
theorem woop_key_le_t_total_model (sz o lo hi : ℝ) (v0 v1 v2 e0 e1 e2 a0 : ℝ)
    (hv0 : lo ≤ v0 ∧ v0 ≤ hi) (hv1 : lo ≤ v1 ∧ v1 ≤ hi)
    (hv2 : lo ≤ v2 ∧ v2 ≤ hi)
    (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hD : model.fl (model.fl (e0 + e1) + e2) ≠ 0) :
    let z := fun v => model.fl (sz * model.fl (v - o))
    let m := min (z lo) (z hi)
    let M := max |z lo| |z hi|
    (0 ≤ M) → (0 < a0) → (a0 ≤ e0 + e1 + e2) → (4 * eta ≤ a0 / 2) →
    (49 * eta * (1 + M) / a0 + 4 * eta ≤ 0.9 * model.u * M) →
    model.fl (m - model.fl ((2:ℝ)^(-19:ℤ) * M)) ≤
      model.fl (model.fl (model.fl (model.fl (e0 * z v0) + model.fl (e1 * z v1)) +
        model.fl (e2 * z v2)) / model.fl (model.fl (e0 + e1) + e2)) := by
  intro z m M hM ha0 hAa0 hηa hfit
  have hu : model.u ≤ 1 / 1000 := by unfold model; norm_num [zpow_neg]
  have hc : 32 * model.u ≤ (2:ℝ)^(-19:ℤ) := by
    have e : (2:ℝ)^(-19:ℤ) = 32 * (2:ℝ)^(-24:ℤ) := by
      rw [show (-19:ℤ) = -24 + 5 by norm_num, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      norm_num
    rw [e, show model.u = (2:ℝ)^(-24:ℤ) from rfl]
  have hc1 : (2:ℝ)^(-19:ℤ) ≤ 1 := by norm_num [zpow_neg]
  obtain ⟨m0, M0⟩ := ExactPrune.depth_bounds model sz o lo hi v0 hv0.1 hv0.2
  obtain ⟨m1, M1⟩ := ExactPrune.depth_bounds model sz o lo hi v1 hv1.1 hv1.2
  obtain ⟨m2, M2⟩ := ExactPrune.depth_bounds model sz o lo hi v2 hv2.1 hv2.2
  have hmM : |m| ≤ M := by
    simp only [m, M]
    rcases min_choice (z lo) (z hi) with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hk := key_le_total m M ((2:ℝ)^(-19:ℤ)) hmM hc hc1
  have hA : 0 < e0 + e1 + e2 := lt_of_lt_of_le ha0 hAa0
  have hZ : m ≤ (e0 * z v0 + e1 * z v1 + e2 * z v2) / (e0 + e1 + e2) := by
    rw [le_div_iff₀ hA]
    nlinarith [mul_le_mul_of_nonneg_left m0 he0, mul_le_mul_of_nonneg_left m1 he1,
      mul_le_mul_of_nonneg_left m2 he2]
  have herr := woop_t_err_total_model_tight e0 e1 e2 (z v0) (z v1) (z v2) M a0
    he0 he1 he2 M0 M1 M2 hM ha0 hAa0 hηa hD
  have ht : m - (29.1 * model.u * M + 49 * eta * (1 + M) / a0 + eta) ≤
      model.fl (model.fl (model.fl (model.fl (e0 * z v0) + model.fl (e1 * z v1)) +
        model.fl (e2 * z v2)) / model.fl (model.fl (e0 + e1) + e2)) := by
    have := (abs_le.1 herr).1
    linarith
  have hfin : m - 30 * model.u * M + 3 * eta ≤
      m - (29.1 * model.u * M + 49 * eta * (1 + M) / a0 + eta) := by
    nlinarith [hfit]
  exact hk.trans (hfin.trans ht)

end ExactPrune
end LightRT.BVH
