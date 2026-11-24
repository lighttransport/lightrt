/-
  Supplying `K` / `PddBounds` for `ofCubic` from control points (M14).
  Abstract scalar bounds on the eight second partials of `bezF`/`bezG`
  (`bez_pddF_bounds`, `bez_pddG_bounds`), third-derivative control-point
  bounds, and `ofCubic_PddBounds` assembling the structure with the explicit
  bound `ofCubicK`. Requires the rectangle to lie in [0,1] and a positive
  uniform lower bound on the ray length.
-/
import Mathlib
import LightRT.Geom.BezSecondDeriv

set_option maxHeartbeats 2000000
namespace LightRT.Geom
open BezSys Filter Topology

/-- Abstract F-component second-partial bounds. -/
theorem bez_pddF_bounds (S : BezSys) (u t : ℝ)
    (Pb Qb D3b Rdb Ddb D3rb Radb Db Rb K : ℝ)
    (hK0 : 0 ≤ K)
    (hpx : |S.px u| ≤ Pb) (hpy : |S.py u| ≤ Pb) (hpz : |S.pz u| ≤ Pb)
    (hqx : |S.qx u| ≤ Qb) (hqy : |S.qy u| ≤ Qb) (hqz : |S.qz u| ≤ Qb)
    (hqx' : |deriv S.qx u| ≤ D3b) (hqy' : |deriv S.qy u| ≤ D3b) (hqz' : |deriv S.qz u| ≤ D3b)
    (hdr : |S.dr u| ≤ Rdb) (hddr : |S.ddr u| ≤ Ddb) (hddr' : |deriv S.ddr u| ≤ D3rb)
    (hrad : |S.rad u| ≤ Radb)
    (hd0 : |S.d 0| ≤ Db) (hd1 : |S.d 1| ≤ Db) (hd2 : |S.d 2| ≤ Db)
    (hRx : |S.Rx u t| ≤ Rb) (hRy : |S.Ry u t| ≤ Rb) (hRz : |S.Rz u t| ≤ Rb)
    (hbf22 : 0 ≤ K)
    (hbf12 : 3*Db*Qb ≤ K)
    (hbf11 : 9*Pb*Qb + 3*Rb*D3b + 3*Rdb*Ddb + Radb*D3rb ≤ K) :
    |pdd22 (bezF S) u t| ≤ K ∧ |pdd12 (bezF S) u t| ≤ K ∧
    |pdd21 (bezF S) u t| ≤ K ∧ |pdd11 (bezF S) u t| ≤ K := by
  have hPb0 : 0 ≤ Pb := le_trans (abs_nonneg _) hpx
  have hQb0 : 0 ≤ Qb := le_trans (abs_nonneg _) hqx
  have hD3b0 : 0 ≤ D3b := le_trans (abs_nonneg _) hqx'
  have hRdb0 : 0 ≤ Rdb := le_trans (abs_nonneg _) hdr
  have hDdb0 : 0 ≤ Ddb := le_trans (abs_nonneg _) hddr
  have hD3rb0 : 0 ≤ D3rb := le_trans (abs_nonneg _) hddr'
  have hRadb0 : 0 ≤ Radb := le_trans (abs_nonneg _) hrad
  have hDb0 : 0 ≤ Db := le_trans (abs_nonneg _) hd0
  have hRb0 : 0 ≤ Rb := le_trans (abs_nonneg _) hRx
  have h22 : |pdd22 (bezF S) u t| ≤ K := by rw [pdd22_bezF_eq_zero]; simpa using hbf22
  have hdotDQ : |S.d 0*S.qx u + S.d 1*S.qy u + S.d 2*S.qz u| ≤ 3*Db*Qb := by
    have h1 : |S.d 0*S.qx u| ≤ Db*Qb := by rw [abs_mul]; exact mul_le_mul hd0 hqx (abs_nonneg _) hDb0
    have h2 : |S.d 1*S.qy u| ≤ Db*Qb := by rw [abs_mul]; exact mul_le_mul hd1 hqy (abs_nonneg _) hDb0
    have h3 : |S.d 2*S.qz u| ≤ Db*Qb := by rw [abs_mul]; exact mul_le_mul hd2 hqz (abs_nonneg _) hDb0
    have htri := abs_add_le (S.d 0*S.qx u + S.d 1*S.qy u) (S.d 2*S.qz u)
    have htri2 := abs_add_le (S.d 0*S.qx u) (S.d 1*S.qy u)
    nlinarith
  have h12 : |pdd12 (bezF S) u t| ≤ K := by rw [pdd12_bezF]; exact hdotDQ.trans hbf12
  have h21 : |pdd21 (bezF S) u t| ≤ K := by rw [pdd21_bezF]; exact hdotDQ.trans hbf12
  -- pdd11
  have hPQ : |S.px u*S.qx u + S.py u*S.qy u + S.pz u*S.qz u| ≤ 3*Pb*Qb := by
    have h1 : |S.px u*S.qx u| ≤ Pb*Qb := by rw [abs_mul]; exact mul_le_mul hpx hqx (abs_nonneg _) hPb0
    have h2 : |S.py u*S.qy u| ≤ Pb*Qb := by rw [abs_mul]; exact mul_le_mul hpy hqy (abs_nonneg _) hPb0
    have h3 : |S.pz u*S.qz u| ≤ Pb*Qb := by rw [abs_mul]; exact mul_le_mul hpz hqz (abs_nonneg _) hPb0
    have htri := abs_add_le (S.px u*S.qx u + S.py u*S.qy u) (S.pz u*S.qz u)
    have htri2 := abs_add_le (S.px u*S.qx u) (S.py u*S.qy u)
    nlinarith
  have hRC : |S.Rx u t*deriv S.qx u + S.Ry u t*deriv S.qy u + S.Rz u t*deriv S.qz u| ≤ 3*Rb*D3b := by
    have h1 : |S.Rx u t*deriv S.qx u| ≤ Rb*D3b := by rw [abs_mul]; exact mul_le_mul hRx hqx' (abs_nonneg _) hRb0
    have h2 : |S.Ry u t*deriv S.qy u| ≤ Rb*D3b := by rw [abs_mul]; exact mul_le_mul hRy hqy' (abs_nonneg _) hRb0
    have h3 : |S.Rz u t*deriv S.qz u| ≤ Rb*D3b := by rw [abs_mul]; exact mul_le_mul hRz hqz' (abs_nonneg _) hRb0
    have htri := abs_add_le (S.Rx u t*deriv S.qx u + S.Ry u t*deriv S.qy u) (S.Rz u t*deriv S.qz u)
    have htri2 := abs_add_le (S.Rx u t*deriv S.qx u) (S.Ry u t*deriv S.qy u)
    nlinarith
  have hdrsq : |S.dr u*S.ddr u| ≤ Rdb*Ddb := by rw [abs_mul]; exact mul_le_mul hdr hddr (abs_nonneg _) hRdb0
  have hradd : |S.rad u*deriv S.ddr u| ≤ Radb*D3rb := by rw [abs_mul]; exact mul_le_mul hrad hddr' (abs_nonneg _) hRadb0
  have hneg3 : |(-3 : ℝ) * (S.px u*S.qx u + S.py u*S.qy u + S.pz u*S.qz u)| =
      3 * |S.px u*S.qx u + S.py u*S.qy u + S.pz u*S.qz u| := by rw [abs_mul]; norm_num
  have h3dr : |(3 : ℝ) * (S.dr u*S.ddr u)| = 3*|S.dr u*S.ddr u| := by rw [abs_mul]; norm_num
  have h11raw : |-3*(S.px u*S.qx u + S.py u*S.qy u + S.pz u*S.qz u) +
      (S.Rx u t*deriv S.qx u + S.Ry u t*deriv S.qy u + S.Rz u t*deriv S.qz u) +
      3*(S.dr u*S.ddr u) + S.rad u*deriv S.ddr u| ≤
      9*Pb*Qb + 3*Rb*D3b + 3*Rdb*Ddb + Radb*D3rb := by
    have htri1 := abs_add_le (-3*(S.px u*S.qx u + S.py u*S.qy u + S.pz u*S.qz u) +
        (S.Rx u t*deriv S.qx u + S.Ry u t*deriv S.qy u + S.Rz u t*deriv S.qz u) +
        3*(S.dr u*S.ddr u)) (S.rad u*deriv S.ddr u)
    have htri2 := abs_add_le (-3*(S.px u*S.qx u + S.py u*S.qy u + S.pz u*S.qz u) +
        (S.Rx u t*deriv S.qx u + S.Ry u t*deriv S.qy u + S.Rz u t*deriv S.qz u)) (3*(S.dr u*S.ddr u))
    have htri3 := abs_add_le (-3*(S.px u*S.qx u + S.py u*S.qy u + S.pz u*S.qz u))
        (S.Rx u t*deriv S.qx u + S.Ry u t*deriv S.qy u + S.Rz u t*deriv S.qz u)
    have htri3' : |-3*(S.px u*S.qx u + S.py u*S.qy u + S.pz u*S.qz u) +
        (S.Rx u t*deriv S.qx u + S.Ry u t*deriv S.qy u + S.Rz u t*deriv S.qz u)| ≤
        3*|S.px u*S.qx u + S.py u*S.qy u + S.pz u*S.qz u| + 3*Rb*D3b := by
      rw [hneg3] at htri3
      nlinarith
    rw [h3dr] at htri2
    nlinarith
  have h11 : |pdd11 (bezF S) u t| ≤ K := by
    rw [pdd11_bezF]
    convert h11raw.trans hbf11 using 1 <;> ring
  exact ⟨h22, h12, h21, h11⟩


lemma abs_div_bound {X B L Lm : ℝ} (hX : |X| ≤ B) (hB : 0 ≤ B)
    (hLm : 0 < Lm) (hL : Lm ≤ L) :
    |X / L| ≤ B / Lm := by
  have hLpos : 0 < L := lt_of_lt_of_le hLm hL
  rw [abs_div, abs_of_pos hLpos]
  calc |X| / L ≤ B / L := div_le_div_of_nonneg_right hX (le_of_lt hLpos)
    _ = B * (1 / L) := by ring
    _ ≤ B * (1 / Lm) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hLm hL) hB
    _ = B / Lm := by ring

lemma abs_div_cube_bound {X B L Lm : ℝ} (hX : |X| ≤ B) (hB : 0 ≤ B)
    (hLm : 0 < Lm) (hL : Lm ≤ L) :
    |X / L^3| ≤ B / Lm^3 := by
  have hLpos : 0 < L := lt_of_lt_of_le hLm hL
  have hL3 : Lm^3 ≤ L^3 := pow_le_pow_left₀ (le_of_lt hLm) hL 3
  have hL3pos : 0 < Lm^3 := pow_pos hLm _
  rw [abs_div, abs_of_pos (pow_pos hLpos _)]
  calc |X| / L^3 ≤ B / L^3 := div_le_div_of_nonneg_right hX (le_of_lt (pow_pos hLpos _))
    _ = B * (1 / L^3) := by ring
    _ ≤ B * (1 / Lm^3) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hL3pos hL3) hB
    _ = B / Lm^3 := by ring

theorem bez_pddG_bounds (S : BezSys) (u t : ℝ) (hlene : 0 < S.q u t)
    (Pb Qb Rdb Ddb Db Rb Lm K : ℝ)
    (hLm : 0 < Lm) (hLmL : Lm ≤ S.len u t)
    (hpx : |S.px u| ≤ Pb) (hpy : |S.py u| ≤ Pb) (hpz : |S.pz u| ≤ Pb)
    (hqx : |S.qx u| ≤ Qb) (hqy : |S.qy u| ≤ Qb) (hqz : |S.qz u| ≤ Qb)
    (hddr : |S.ddr u| ≤ Ddb)
    (hd0 : |S.d 0| ≤ Db) (hd1 : |S.d 1| ≤ Db) (hd2 : |S.d 2| ≤ Db)
    (hRx : |S.Rx u t| ≤ Rb) (hRy : |S.Ry u t| ≤ Rb) (hRz : |S.Rz u t| ≤ Rb)
    (hbg22 : 3*Db^2/Lm + (3*Rb*Db)^2/Lm^3 ≤ K)
    (hbg12 : 3*Db*Pb/Lm + (3*Rb*Pb)*(3*Rb*Db)/Lm^3 ≤ K)
    (hbg11 : (3*Pb^2 + 3*Rb*Qb)/Lm + (3*Rb*Pb)^2/Lm^3 + Ddb ≤ K) :
    |pdd22 (bezG S) u t| ≤ K ∧ |pdd12 (bezG S) u t| ≤ K ∧
    |pdd21 (bezG S) u t| ≤ K ∧ |pdd11 (bezG S) u t| ≤ K := by
  have hPb0 : 0 ≤ Pb := le_trans (abs_nonneg _) hpx
  have hQb0 : 0 ≤ Qb := le_trans (abs_nonneg _) hqx
  have hDdb0 : 0 ≤ Ddb := le_trans (abs_nonneg _) hddr
  have hDb0 : 0 ≤ Db := le_trans (abs_nonneg _) hd0
  have hRb0 : 0 ≤ Rb := le_trans (abs_nonneg _) hRx
  have hdd : |S.d 0^2 + S.d 1^2 + S.d 2^2| ≤ 3*Db^2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ S.d 0^2 + S.d 1^2 + S.d 2^2)]
    have h0 : S.d 0^2 ≤ Db^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hDb0] using hd0)
    have h1 : S.d 1^2 ≤ Db^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hDb0] using hd1)
    have h2 : S.d 2^2 ≤ Db^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hDb0] using hd2)
    nlinarith
  have hRd : |S.Rx u t*S.d 0 + S.Ry u t*S.d 1 + S.Rz u t*S.d 2| ≤ 3*Rb*Db := by
    have h1 : |S.Rx u t*S.d 0| ≤ Rb*Db := by rw [abs_mul]; exact mul_le_mul hRx hd0 (abs_nonneg _) hRb0
    have h2 : |S.Ry u t*S.d 1| ≤ Rb*Db := by rw [abs_mul]; exact mul_le_mul hRy hd1 (abs_nonneg _) hRb0
    have h3 : |S.Rz u t*S.d 2| ≤ Rb*Db := by rw [abs_mul]; exact mul_le_mul hRz hd2 (abs_nonneg _) hRb0
    have ht := abs_add_le (S.Rx u t*S.d 0 + S.Ry u t*S.d 1) (S.Rz u t*S.d 2)
    have ht2 := abs_add_le (S.Rx u t*S.d 0) (S.Ry u t*S.d 1)
    nlinarith
  have hRd_sq : |(S.Rx u t*S.d 0 + S.Ry u t*S.d 1 + S.Rz u t*S.d 2)^2| ≤ (3*Rb*Db)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq).2 (by simpa [abs_of_nonneg (by positivity : 0 ≤ 3*Rb*Db)] using hRd)
  have h22 : |pdd22 (bezG S) u t| ≤ K := by
    rw [pdd22_bezG S u t hlene]
    have htri := abs_sub ((S.d 0^2+S.d 1^2+S.d 2^2)/S.len u t)
      ((S.Rx u t*S.d 0+S.Ry u t*S.d 1+S.Rz u t*S.d 2)^2/S.len u t^3)
    have h1 := abs_div_bound hdd (by positivity) hLm hLmL
    have h2 := abs_div_cube_bound hRd_sq (by positivity) hLm hLmL
    nlinarith
  have hdp : |S.d 0*S.px u + S.d 1*S.py u + S.d 2*S.pz u| ≤ 3*Db*Pb := by
    have h1 : |S.d 0*S.px u| ≤ Db*Pb := by rw [abs_mul]; exact mul_le_mul hd0 hpx (abs_nonneg _) hDb0
    have h2 : |S.d 1*S.py u| ≤ Db*Pb := by rw [abs_mul]; exact mul_le_mul hd1 hpy (abs_nonneg _) hDb0
    have h3 : |S.d 2*S.pz u| ≤ Db*Pb := by rw [abs_mul]; exact mul_le_mul hd2 hpz (abs_nonneg _) hDb0
    have ht := abs_add_le (S.d 0*S.px u + S.d 1*S.py u) (S.d 2*S.pz u)
    have ht2 := abs_add_le (S.d 0*S.px u) (S.d 1*S.py u)
    nlinarith
  have hRp : |S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u| ≤ 3*Rb*Pb := by
    have h1 : |S.Rx u t*S.px u| ≤ Rb*Pb := by rw [abs_mul]; exact mul_le_mul hRx hpx (abs_nonneg _) hRb0
    have h2 : |S.Ry u t*S.py u| ≤ Rb*Pb := by rw [abs_mul]; exact mul_le_mul hRy hpy (abs_nonneg _) hRb0
    have h3 : |S.Rz u t*S.pz u| ≤ Rb*Pb := by rw [abs_mul]; exact mul_le_mul hRz hpz (abs_nonneg _) hRb0
    have ht := abs_add_le (S.Rx u t*S.px u + S.Ry u t*S.py u) (S.Rz u t*S.pz u)
    have ht2 := abs_add_le (S.Rx u t*S.px u) (S.Ry u t*S.py u)
    nlinarith
  have hprod : |(S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u) *
      (S.Rx u t*S.d 0 + S.Ry u t*S.d 1 + S.Rz u t*S.d 2)| ≤ (3*Rb*Pb)*(3*Rb*Db) := by
    rw [abs_mul]; exact mul_le_mul hRp hRd (abs_nonneg _) (by positivity)
  have h12 : |pdd12 (bezG S) u t| ≤ K := by
    rw [pdd12_bezG S u t hlene]
    have htri := abs_add_le (-(S.d 0*S.px u + S.d 1*S.py u + S.d 2*S.pz u)/S.len u t)
      ((S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u)*
        (S.Rx u t*S.d 0 + S.Ry u t*S.d 1 + S.Rz u t*S.d 2)/S.len u t^3)
    have h1 := abs_div_bound (by simpa using hdp) (by positivity) hLm hLmL
    have h2 := abs_div_cube_bound hprod (by positivity) hLm hLmL
    have heqneg : |-(S.d 0*S.px u + S.d 1*S.py u + S.d 2*S.pz u) / S.len u t| =
        |(S.d 0*S.px u + S.d 1*S.py u + S.d 2*S.pz u) / S.len u t| := by
      rw [neg_div, abs_neg]
    rw [heqneg] at htri
    have h1neg := h1
    nlinarith
  have h21 : |pdd21 (bezG S) u t| ≤ K := by
    rw [pdd21_bezG S u t hlene]
    have htri := abs_add_le (-(S.d 0*S.px u + S.d 1*S.py u + S.d 2*S.pz u)/S.len u t)
      ((S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u)*
        (S.Rx u t*S.d 0 + S.Ry u t*S.d 1 + S.Rz u t*S.d 2)/S.len u t^3)
    have h1 := abs_div_bound (by simpa using hdp) (by positivity) hLm hLmL
    have h2 := abs_div_cube_bound hprod (by positivity) hLm hLmL
    have heqneg : |-(S.d 0*S.px u + S.d 1*S.py u + S.d 2*S.pz u) / S.len u t| =
        |(S.d 0*S.px u + S.d 1*S.py u + S.d 2*S.pz u) / S.len u t| := by
      rw [neg_div, abs_neg]
    rw [heqneg] at htri
    have h1neg := h1
    nlinarith
  have hpp : |S.px u^2 + S.py u^2 + S.pz u^2| ≤ 3*Pb^2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ S.px u^2 + S.py u^2 + S.pz u^2)]
    have h0 : S.px u^2 ≤ Pb^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hPb0] using hpx)
    have h1 : S.py u^2 ≤ Pb^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hPb0] using hpy)
    have h2 : S.pz u^2 ≤ Pb^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hPb0] using hpz)
    nlinarith
  have hRq : |S.Rx u t*S.qx u + S.Ry u t*S.qy u + S.Rz u t*S.qz u| ≤ 3*Rb*Qb := by
    have h1 : |S.Rx u t*S.qx u| ≤ Rb*Qb := by rw [abs_mul]; exact mul_le_mul hRx hqx (abs_nonneg _) hRb0
    have h2 : |S.Ry u t*S.qy u| ≤ Rb*Qb := by rw [abs_mul]; exact mul_le_mul hRy hqy (abs_nonneg _) hRb0
    have h3 : |S.Rz u t*S.qz u| ≤ Rb*Qb := by rw [abs_mul]; exact mul_le_mul hRz hqz (abs_nonneg _) hRb0
    have ht := abs_add_le (S.Rx u t*S.qx u + S.Ry u t*S.qy u) (S.Rz u t*S.qz u)
    have ht2 := abs_add_le (S.Rx u t*S.qx u) (S.Ry u t*S.qy u)
    nlinarith
  have hnum : |(S.px u^2 + S.py u^2 + S.pz u^2) -
      (S.Rx u t*S.qx u + S.Ry u t*S.qy u + S.Rz u t*S.qz u)| ≤ 3*Pb^2 + 3*Rb*Qb := by
    have ht := abs_sub (S.px u^2 + S.py u^2 + S.pz u^2) (S.Rx u t*S.qx u + S.Ry u t*S.qy u + S.Rz u t*S.qz u)
    nlinarith
  have hRp_sq : |(S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u)^2| ≤ (3*Rb*Pb)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq).2 (by simpa [abs_of_nonneg (by positivity : 0 ≤ 3*Rb*Pb)] using hRp)
  have h11 : |pdd11 (bezG S) u t| ≤ K := by
    rw [pdd11_bezG S u t hlene]
    have htri1 := abs_sub (((S.px u^2+S.py u^2+S.pz u^2) -
      (S.Rx u t*S.qx u+S.Ry u t*S.qy u+S.Rz u t*S.qz u))/S.len u t)
      ((S.Rx u t*S.px u+S.Ry u t*S.py u+S.Rz u t*S.pz u)^2/S.len u t^3)
    have htri2 := abs_sub ((((S.px u^2+S.py u^2+S.pz u^2) -
      (S.Rx u t*S.qx u+S.Ry u t*S.qy u+S.Rz u t*S.qz u))/S.len u t) -
      ((S.Rx u t*S.px u+S.Ry u t*S.py u+S.Rz u t*S.pz u)^2/S.len u t^3)) (S.ddr u)
    have h1 := abs_div_bound hnum (by positivity) hLm hLmL
    have h2 := abs_div_cube_bound hRp_sq (by positivity) hLm hLmL
    nlinarith
  exact ⟨h22, h12, h21, h11⟩


-- === control-point third-derivative bound ===

noncomputable def dddSup (c : Fin 4 → Fin 4 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 =>
    |c 3 i - 3*c 2 i + 3*c 1 i - c 0 i|)

theorem le_dddSup (c : Fin 4 → Fin 4 → ℝ) (i : Fin 4) :
    |c 3 i - 3*c 2 i + 3*c 1 i - c 0 i| ≤ dddSup c := by
  unfold dddSup
  exact Finset.le_sup' (f := fun i : Fin 4 => |c 3 i - 3*c 2 i + 3*c 1 i - c 0 i|) (Finset.mem_univ i)

theorem dddBezP_le_dddSup (c : Fin 4 → Fin 4 → ℝ) (i : Fin 4) :
    |dddBezP (c 0 i) (c 1 i) (c 2 i) (c 3 i)| ≤ 6 * dddSup c := by
  simpa [dddBezP, abs_mul] using
    (mul_le_mul_of_nonneg_left (le_dddSup c i) (by norm_num : (0:ℝ) ≤ 6))

-- === the K bound, explicit in the control points ===

noncomputable def ofCubicK (c : Fin 4 → Fin 4 → ℝ) (d : Fin 3 → ℝ)
    (Lm T : ℝ) : ℝ :=
  let M := cSup c
  let E := edgeSup c
  let S2 := ddSup c
  let D3 := dddSup c
  let D := dSup d
  let Rb := T * D + M
  max
    (max (18 * D * S2)
      (9 * (3*E) * (6*S2) + 3 * Rb * (6*D3) + 3 * (3*E) * (6*S2) + M * (6*D3)))
    (max (3*D^2/Lm + (3*Rb*D)^2/Lm^3)
      (max (3*D*(3*E)/Lm + (3*Rb*(3*E)) * (3*Rb*D) / Lm^3)
        ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2)))

theorem ofCubic_PddBounds (c : Fin 4 → Fin 4 → ℝ) (d : Fin 3 → ℝ)
    (a b cα dα Lm T : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hLmpos : 0 < Lm)
    (hLm_le : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc cα dα,
      Lm ≤ (ofCubic c d).len u t)
    (hT0 : 0 ≤ T)
    (hT : ∀ t ∈ Set.Icc cα dα, |t| ≤ T) :
    PddBounds (ofCubic c d) a b cα dα (ofCubicK c d Lm T) := by
  let S := ofCubic c d
  let M := cSup c
  let E := edgeSup c
  let S2 := ddSup c
  let D3 := dddSup c
  let D := dSup d
  let Rb := T * D + M
  let K := ofCubicK c d Lm T
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (by simpa [M] using le_cSup c 0 0)
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) (by simpa [E] using le_edgeSup c (0 : Fin 3) (0 : Fin 4))
  have hS20 : 0 ≤ S2 := le_trans (abs_nonneg _) (by simpa [S2] using le_ddSup0 c (0 : Fin 4))
  have hD30 : 0 ≤ D3 := le_trans (abs_nonneg _) (by simpa [D3] using le_dddSup c (0 : Fin 4))
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (by simpa [D] using le_dSup d (0 : Fin 3))
  have hRb0 : 0 ≤ Rb := by dsimp [Rb]; positivity
  have hKexpr : K = max
      (max (18 * D * S2)
        (9 * (3*E) * (6*S2) + 3 * Rb * (6*D3) + 3 * (3*E) * (6*S2) + M * (6*D3)))
      (max (3*D^2/Lm + (3*Rb*D)^2/Lm^3)
        (max (3*D*(3*E)/Lm + (3*Rb*(3*E)) * (3*Rb*D) / Lm^3)
          ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2))) := rfl
  have hK0 : 0 ≤ K := by
    rw [hKexpr]
    positivity
  have hF12 : 18*D*S2 ≤ K := by
    rw [hKexpr]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hF11 : 9*(3*E)*(6*S2) + 3*Rb*(6*D3) + 3*(3*E)*(6*S2) + M*(6*D3) ≤ K := by
    rw [hKexpr]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hG22 : 3*D^2/Lm + (3*Rb*D)^2/Lm^3 ≤ K := by
    rw [hKexpr]
    exact (le_max_left (3*D^2/Lm + (3*Rb*D)^2/Lm^3)
      (max (3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3)
        ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2))).trans
      (le_max_right
        (max (18*D*S2) (9*(3*E)*(6*S2) + 3*Rb*(6*D3) + 3*(3*E)*(6*S2) + M*(6*D3)))
        (max (3*D^2/Lm + (3*Rb*D)^2/Lm^3)
          (max (3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3)
            ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2))))
  have hG12 : 3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3 ≤ K := by
    rw [hKexpr]
    exact ((le_max_left (3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3)
      ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2)).trans
      (le_max_right (3*D^2/Lm + (3*Rb*D)^2/Lm^3)
        (max (3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3)
          ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2)))).trans
      (le_max_right
        (max (18*D*S2) (9*(3*E)*(6*S2) + 3*Rb*(6*D3) + 3*(3*E)*(6*S2) + M*(6*D3)))
        (max (3*D^2/Lm + (3*Rb*D)^2/Lm^3)
          (max (3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3)
            ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2))))
  have hG11 : (3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2 ≤ K := by
    rw [hKexpr]
    exact ((le_max_right (3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3)
      ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2)).trans
      (le_max_right (3*D^2/Lm + (3*Rb*D)^2/Lm^3)
        (max (3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3)
          ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2)))).trans
      (le_max_right
        (max (18*D*S2) (9*(3*E)*(6*S2) + 3*Rb*(6*D3) + 3*(3*E)*(6*S2) + M*(6*D3)))
        (max (3*D^2/Lm + (3*Rb*D)^2/Lm^3)
          (max (3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3)
            ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2))))
  have hF : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc cα dα,
      |pdd22 (bezF S) u t| ≤ K ∧ |pdd12 (bezF S) u t| ≤ K ∧
      |pdd21 (bezF S) u t| ≤ K ∧ |pdd11 (bezF S) u t| ≤ K := by
    intro u hu t ht
    have hu0 : 0 ≤ u := ha.trans hu.1
    have hu1 : u ≤ 1 := hu.2.trans hb
    have hgx : |S.gx u| ≤ M := by change |bezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u| ≤ M; simpa [M] using bezP_le_cSup c 0 hu0 hu1
    have hgy : |S.gy u| ≤ M := by change |bezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u| ≤ M; simpa [M] using bezP_le_cSup c 1 hu0 hu1
    have hgz : |S.gz u| ≤ M := by change |bezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u| ≤ M; simpa [M] using bezP_le_cSup c 2 hu0 hu1
    have hrad : |S.rad u| ≤ M := by change |bezP (c 0 3) (c 1 3) (c 2 3) (c 3 3) u| ≤ M; simpa [M] using bezP_le_cSup c 3 hu0 hu1
    have hpx : |S.px u| ≤ 3*E := by change |dBezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u| ≤ 3*E; simpa [E] using dBezP_le_edgeSup c 0 hu0 hu1
    have hpy : |S.py u| ≤ 3*E := by change |dBezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u| ≤ 3*E; simpa [E] using dBezP_le_edgeSup c 1 hu0 hu1
    have hpz : |S.pz u| ≤ 3*E := by change |dBezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u| ≤ 3*E; simpa [E] using dBezP_le_edgeSup c 2 hu0 hu1
    have hdr : |S.dr u| ≤ 3*E := by change |dBezP (c 0 3) (c 1 3) (c 2 3) (c 3 3) u| ≤ 3*E; simpa [E] using dBezP_le_edgeSup c 3 hu0 hu1
    have hqx : |S.qx u| ≤ 6*S2 := by change |ddBezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u| ≤ 6*S2; simpa [S2] using ddBezP_le_ddSup c 0 hu0 hu1
    have hqy : |S.qy u| ≤ 6*S2 := by change |ddBezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u| ≤ 6*S2; simpa [S2] using ddBezP_le_ddSup c 1 hu0 hu1
    have hqz : |S.qz u| ≤ 6*S2 := by change |ddBezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u| ≤ 6*S2; simpa [S2] using ddBezP_le_ddSup c 2 hu0 hu1
    have hddr : |S.ddr u| ≤ 6*S2 := by change |ddBezP (c 0 3) (c 1 3) (c 2 3) (c 3 3) u| ≤ 6*S2; simpa [S2] using ddBezP_le_ddSup c 3 hu0 hu1
    have hqx' : |deriv S.qx u| ≤ 6*D3 := by
      change |deriv (ddBezP (c 0 0) (c 1 0) (c 2 0) (c 3 0)) u| ≤ 6*D3
      rw [deriv_ddBezP]
      simpa [D3] using dddBezP_le_dddSup c 0
    have hqy' : |deriv S.qy u| ≤ 6*D3 := by
      change |deriv (ddBezP (c 0 1) (c 1 1) (c 2 1) (c 3 1)) u| ≤ 6*D3
      rw [deriv_ddBezP]
      simpa [D3] using dddBezP_le_dddSup c 1
    have hqz' : |deriv S.qz u| ≤ 6*D3 := by
      change |deriv (ddBezP (c 0 2) (c 1 2) (c 2 2) (c 3 2)) u| ≤ 6*D3
      rw [deriv_ddBezP]
      simpa [D3] using dddBezP_le_dddSup c 2
    have hddr' : |deriv S.ddr u| ≤ 6*D3 := by
      change |deriv (ddBezP (c 0 3) (c 1 3) (c 2 3) (c 3 3)) u| ≤ 6*D3
      rw [deriv_ddBezP]
      simpa [D3] using dddBezP_le_dddSup c 3
    have hd0 : |S.d 0| ≤ D := by change |d 0| ≤ D; simpa [D] using le_dSup d (0 : Fin 3)
    have hd1 : |S.d 1| ≤ D := by change |d 1| ≤ D; simpa [D] using le_dSup d (1 : Fin 3)
    have hd2 : |S.d 2| ≤ D := by change |d 2| ≤ D; simpa [D] using le_dSup d (2 : Fin 3)
    have ht := hT t ht
    have mkrx : ∀ (g : ℝ → ℝ) (di : ℝ), |g u| ≤ M → |di| ≤ D → |t * di - g u| ≤ Rb := by
      intro g di hg hdi
      have hmul : |t * di| ≤ T*D := by rw [abs_mul]; exact mul_le_mul ht hdi (abs_nonneg _) hT0
      have htri := abs_sub (t*di) (g u)
      dsimp [Rb]
      nlinarith
    have hRx : |S.Rx u t| ≤ Rb := by change |t*d 0 - S.gx u| ≤ Rb; exact mkrx S.gx (d 0) hgx hd0
    have hRy : |S.Ry u t| ≤ Rb := by change |t*d 1 - S.gy u| ≤ Rb; exact mkrx S.gy (d 1) hgy hd1
    have hRz : |S.Rz u t| ≤ Rb := by change |t*d 2 - S.gz u| ≤ Rb; exact mkrx S.gz (d 2) hgz hd2
    exact bez_pddF_bounds S u t (3*E) (6*S2) (6*D3) (3*E) (6*S2) (6*D3) M D Rb K
      hK0 hpx hpy hpz hqx hqy hqz hqx' hqy' hqz' hdr hddr hddr' hrad hd0 hd1 hd2 hRx hRy hRz
      (by simpa using hK0) (by nlinarith [hF12]) (by nlinarith [hF11])
  have hG : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc cα dα,
      |pdd22 (bezG S) u t| ≤ K ∧ |pdd12 (bezG S) u t| ≤ K ∧
      |pdd21 (bezG S) u t| ≤ K ∧ |pdd11 (bezG S) u t| ≤ K := by
    intro u hu t ht
    have hu0 : 0 ≤ u := ha.trans hu.1
    have hu1 : u ≤ 1 := hu.2.trans hb
    have hlenepos : 0 < S.q u t := by
      have hL := hLm_le u hu t ht
      have hlenpos : 0 < S.len u t := lt_of_lt_of_le hLmpos hL
      dsimp [S, len] at hlenpos
      exact Real.sqrt_pos.1 hlenpos
    have hpx : |S.px u| ≤ 3*E := by change |dBezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u| ≤ 3*E; simpa [E] using dBezP_le_edgeSup c 0 hu0 hu1
    have hpy : |S.py u| ≤ 3*E := by change |dBezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u| ≤ 3*E; simpa [E] using dBezP_le_edgeSup c 1 hu0 hu1
    have hpz : |S.pz u| ≤ 3*E := by change |dBezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u| ≤ 3*E; simpa [E] using dBezP_le_edgeSup c 2 hu0 hu1
    have hqx : |S.qx u| ≤ 6*S2 := by change |ddBezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u| ≤ 6*S2; simpa [S2] using ddBezP_le_ddSup c 0 hu0 hu1
    have hqy : |S.qy u| ≤ 6*S2 := by change |ddBezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u| ≤ 6*S2; simpa [S2] using ddBezP_le_ddSup c 1 hu0 hu1
    have hqz : |S.qz u| ≤ 6*S2 := by change |ddBezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u| ≤ 6*S2; simpa [S2] using ddBezP_le_ddSup c 2 hu0 hu1
    have hddr : |S.ddr u| ≤ 6*S2 := by change |ddBezP (c 0 3) (c 1 3) (c 2 3) (c 3 3) u| ≤ 6*S2; simpa [S2] using ddBezP_le_ddSup c 3 hu0 hu1
    have hd0 : |S.d 0| ≤ D := by change |d 0| ≤ D; simpa [D] using le_dSup d (0 : Fin 3)
    have hd1 : |S.d 1| ≤ D := by change |d 1| ≤ D; simpa [D] using le_dSup d (1 : Fin 3)
    have hd2 : |S.d 2| ≤ D := by change |d 2| ≤ D; simpa [D] using le_dSup d (2 : Fin 3)
    have hgx : |S.gx u| ≤ M := by change |bezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u| ≤ M; simpa [M] using bezP_le_cSup c 0 hu0 hu1
    have hgy : |S.gy u| ≤ M := by change |bezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u| ≤ M; simpa [M] using bezP_le_cSup c 1 hu0 hu1
    have hgz : |S.gz u| ≤ M := by change |bezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u| ≤ M; simpa [M] using bezP_le_cSup c 2 hu0 hu1
    have htb := hT t ht
    have mkrx : ∀ (g : ℝ → ℝ) (di : ℝ), |g u| ≤ M → |di| ≤ D → |t * di - g u| ≤ Rb := by
      intro g di hg hdi
      have hmul : |t * di| ≤ T*D := by rw [abs_mul]; exact mul_le_mul htb hdi (abs_nonneg _) hT0
      have htri := abs_sub (t*di) (g u)
      dsimp [Rb]
      nlinarith
    have hRx : |S.Rx u t| ≤ Rb := by change |t*d 0 - S.gx u| ≤ Rb; exact mkrx S.gx (d 0) hgx hd0
    have hRy : |S.Ry u t| ≤ Rb := by change |t*d 1 - S.gy u| ≤ Rb; exact mkrx S.gy (d 1) hgy hd1
    have hRz : |S.Rz u t| ≤ Rb := by change |t*d 2 - S.gz u| ≤ Rb; exact mkrx S.gz (d 2) hgz hd2
    exact bez_pddG_bounds S u t hlenepos (3*E) (6*S2) (3*E) (6*S2) D Rb Lm K
      hLmpos (hLm_le u hu t ht) hpx hpy hpz hqx hqy hqz hddr hd0 hd1 hd2 hRx hRy hRz
      (by nlinarith [hG22]) (by nlinarith [hG12]) (by nlinarith [hG11])
  exact ⟨fun u hu t ht => (hF u hu t ht).2.2.2,
    fun u hu t ht => (hF u hu t ht).2.1,
    fun u hu t ht => (hF u hu t ht).2.2.1,
    fun u hu t ht => (hF u hu t ht).1,
    fun u hu t ht => (hG u hu t ht).2.2.2,
    fun u hu t ht => (hG u hu t ht).2.1,
    fun u hu t ht => (hG u hu t ht).2.2.1,
    fun u hu t ht => (hG u hu t ht).1⟩


theorem ofCubicK_pos (c : Fin 4 → Fin 4 → ℝ) (d : Fin 3 → ℝ) (Lm T : ℝ)
    (hLm : 0 < Lm) (hDpos : 0 < dSup d) :
    0 < ofCubicK c d Lm T := by
  let M := cSup c
  let E := edgeSup c
  let S2 := ddSup c
  let D3 := dddSup c
  let D := dSup d
  let Rb := T * D + M
  let G22 := 3*D^2/Lm + (3*Rb*D)^2/Lm^3
  have hD0 : 0 < D := by simpa [D] using hDpos
  have hD2 : 0 < D^2 := sq_pos_of_pos hD0
  have hpart : 0 < 3 * D^2 / Lm := div_pos (mul_pos (by norm_num) hD2) hLm
  have hnonneg : 0 ≤ (3*Rb*D)^2 / Lm^3 := div_nonneg (sq_nonneg _) (le_of_lt (pow_pos hLm _))
  have hG22 : 0 < G22 := by dsimp [G22]; exact add_pos_of_pos_of_nonneg hpart hnonneg
  dsimp [ofCubicK]
  exact lt_of_lt_of_le hG22 ((le_max_left G22
    (max (3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3)
      ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2))).trans
    (le_max_right
      (max (18*D*S2) (9*(3*E)*(6*S2) + 3*Rb*(6*D3) + 3*(3*E)*(6*S2) + M*(6*D3)))
      (max G22
        (max (3*D*(3*E)/Lm + (3*Rb*(3*E))*(3*Rb*D)/Lm^3)
          ((3*(3*E)^2 + 3*Rb*(6*S2))/Lm + (3*Rb*(3*E))^2/Lm^3 + 6*S2)))))

/-- **Fully data-supplied M14 convergence.** Both `B0` and `K` are derived
    from the control points (via `ofCubicB0` and `ofCubicK`); what remains as
    hypotheses are nondegeneracy of the root (`det0`, `hroot`), the length
    floor and parameter bounds, and the radius/geometry conditions. -/
theorem ofCubic_newton_tendsto_of_control_points
    (c : Fin 4 → Fin 4 → ℝ) (d : Fin 3 → ℝ)
    (a b cα dα det0 R Lm T : ℝ) {u₀ t₀ u t : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hLmpos : 0 < Lm)
    (hLm_le : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc cα dα,
      Lm ≤ (ofCubic c d).len u t)
    (hT0 : 0 ≤ T) (hT : ∀ t ∈ Set.Icc cα dα, |t| ≤ T)
    (hu₀01 : u₀ ∈ Set.Icc 0 1)
    (hDpos : 0 < dSup d)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc cα dα, 0 < (ofCubic c d).q u t)
    (hdet0pos : 0 < det0)
    (hu₀ : u₀ ∈ Set.Icc a b) (ht₀ : t₀ ∈ Set.Icc cα dα)
    (hroot : bezF (ofCubic c d) u₀ t₀ = 0 ∧ bezG (ofCubic c d) u₀ t₀ = 0)
    (hdet0 : det0 ≤ |jacDet (bezF (ofCubic c d)) (bezG (ofCubic c d)) u₀ t₀|)
    (hR0 : 0 ≤ R) (hKR : R ≤ 1 / ofCubicK c d Lm T)
    (hvar : 4 * ofCubicB0 c d u₀ t₀ * ofCubicK c d Lm T * R +
        4 * (ofCubicK c d Lm T * R)^2 ≤ det0 / 2)
    (hcond : 2 * (ofCubicB0 c d u₀ t₀ + ofCubicK c d Lm T * R + 1)^2 / (det0 / 2) < 1)
    (hsmall : 2 * (ofCubicB0 c d u₀ t₀ + ofCubicK c d Lm T * R + 1)^2 / (det0 / 2) +
        18 * (ofCubicB0 c d u₀ t₀ + ofCubicK c d Lm T * R + 1) * ofCubicK c d Lm T /
          (det0 / 2) * R < 1)
    (hrect : ∀ u' t', |u' - u₀| + |t' - t₀| ≤ R →
      u' ∈ Set.Icc a b ∧ t' ∈ Set.Icc cα dα)
    (hseed : |u - u₀| + |t - t₀| ≤ R) :
    Tendsto (fun n => (newtonIter (ofCubic c d) u t n).1) atTop (𝓝 u₀) ∧
    Tendsto (fun n => (newtonIter (ofCubic c d) u t n).2) atTop (𝓝 t₀) := by
  have hKpos : 0 < ofCubicK c d Lm T := ofCubicK_pos c d Lm T hLmpos hDpos
  have hbnd := ofCubic_PddBounds c d a b cα dα Lm T ha hb hLmpos hLm_le hT0 hT
  exact ofCubic_newton_tendsto_of_root_data c d a b cα dα (ofCubicK c d Lm T)
      det0 R hu₀01 hbnd hlene hKpos (le_of_lt hKpos) hdet0pos hu₀ ht₀ hroot
      hdet0 hR0 (by simpa [mul_comm] using (le_div_iff₀' hKpos).mp hKR) hvar hcond hsmall hrect hseed

end LightRT.Geom
