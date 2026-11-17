/-
  Control-point data supply for M14 (final step): explicit bounds on the
  first partials of `ofCubic`'s contact system, produced from the Bézier
  control points. Together with `newtonIter_tendsto_of_root_data` this gives
  a conditional Newton convergence theorem for the concrete system; the
  remaining hypothesis is nondegeneracy of the Jacobian determinant (which
  cannot be proved for arbitrary control points).
-/
import Mathlib
import LightRT.Geom.BezNewton
import LightRT.Geom.BezNewtonGuards
import LightRT.Geom.BezBounds

set_option maxHeartbeats 2000000

namespace LightRT.Geom

open BezSys
open Filter Topology

-- === helper suprema over control points ===

noncomputable def cSup (c : Fin 4 → Fin 4 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k : Fin 4 =>
    Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 => |c k i|))

theorem le_cSup (c : Fin 4 → Fin 4 → ℝ) (k i : Fin 4) : |c k i| ≤ cSup c := by
  unfold cSup
  apply le_trans (Finset.le_sup' (f := fun i : Fin 4 => |c k i|) (Finset.mem_univ i))
  exact Finset.le_sup' (f := fun k : Fin 4 =>
    Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 => |c k i|)) (Finset.mem_univ k)

noncomputable def edgeSup (c : Fin 4 → Fin 4 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 =>
    Finset.univ.sup' Finset.univ_nonempty (fun k : Fin 3 =>
      |c ⟨k.1+1, by omega⟩ i - c ⟨k.1, by omega⟩ i|))

theorem le_edgeSup (c : Fin 4 → Fin 4 → ℝ) (k : Fin 3) (i : Fin 4) :
    |c ⟨k.1+1, by omega⟩ i - c ⟨k.1, by omega⟩ i| ≤ edgeSup c := by
  unfold edgeSup
  apply le_trans (Finset.le_sup' (f := fun k : Fin 3 =>
    |c ⟨k.1+1, by omega⟩ i - c ⟨k.1, by omega⟩ i|) (Finset.mem_univ k))
  exact Finset.le_sup' (f := fun i : Fin 4 =>
    Finset.univ.sup' Finset.univ_nonempty (fun k : Fin 3 =>
      |c ⟨k.1+1, by omega⟩ i - c ⟨k.1, by omega⟩ i|)) (Finset.mem_univ i)

noncomputable def ddSup (c : Fin 4 → Fin 4 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 =>
    max |c 2 i - 2*c 1 i + c 0 i| |c 3 i - 2*c 2 i + c 1 i|)

theorem le_ddSup0 (c : Fin 4 → Fin 4 → ℝ) (i : Fin 4) :
    |c 2 i - 2*c 1 i + c 0 i| ≤ ddSup c := by
  unfold ddSup
  apply le_trans (le_max_left _ _)
  exact Finset.le_sup' (f := fun i : Fin 4 =>
    max |c 2 i - 2*c 1 i + c 0 i| |c 3 i - 2*c 2 i + c 1 i|) (Finset.mem_univ i)

theorem le_ddSup1 (c : Fin 4 → Fin 4 → ℝ) (i : Fin 4) :
    |c 3 i - 2*c 2 i + c 1 i| ≤ ddSup c := by
  unfold ddSup
  apply le_trans (le_max_right _ _)
  exact Finset.le_sup' (f := fun i : Fin 4 =>
    max |c 2 i - 2*c 1 i + c 0 i| |c 3 i - 2*c 2 i + c 1 i|) (Finset.mem_univ i)

noncomputable def dSup (d : Fin 3 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 3 => |d i|)

theorem le_dSup (d : Fin 3 → ℝ) (i : Fin 3) : |d i| ≤ dSup d := by
  unfold dSup
  exact Finset.le_sup' (f := fun i : Fin 3 => |d i|) (Finset.mem_univ i)

-- === abstract partial bounds (from scratch) ===
theorem bez_root_partial_bounds (S : BezSys) (u t : ℝ)
    (hlene : 0 < S.q u t)
    (Rb Pb Qb Rdb Radb Ddb Db Lb : ℝ)
    (hRx : |S.Rx u t| ≤ Rb) (hRy : |S.Ry u t| ≤ Rb) (hRz : |S.Rz u t| ≤ Rb)
    (hpx : |S.px u| ≤ Pb) (hpy : |S.py u| ≤ Pb) (hpz : |S.pz u| ≤ Pb)
    (hqx : |S.qx u| ≤ Qb) (hqy : |S.qy u| ≤ Qb) (hqz : |S.qz u| ≤ Qb)
    (hdr : |S.dr u| ≤ Rdb) (hrad : |S.rad u| ≤ Radb) (hddr : |S.ddr u| ≤ Ddb)
    (hd0 : |S.d 0| ≤ Db) (hd1 : |S.d 1| ≤ Db) (hd2 : |S.d 2| ≤ Db)
    (hLbpos : 0 < Lb) (hLb : Lb ≤ S.len u t) :
    |pd1 (bezF S) u t| ≤ 3*Pb^2 + 3*Rb*Qb + Rdb^2 + Radb*Ddb ∧
    |pd2 (bezF S) u t| ≤ 3*Db*Pb ∧
    |pd1 (bezG S) u t| ≤ (3*Rb*Pb)/Lb + Rdb ∧
    |pd2 (bezG S) u t| ≤ (3*Rb*Db)/Lb := by
  have hRb0 : 0 ≤ Rb := le_trans (abs_nonneg _) hRx
  have hPb0 : 0 ≤ Pb := le_trans (abs_nonneg _) hpx
  have hQb0 : 0 ≤ Qb := le_trans (abs_nonneg _) hqx
  have hRdb0 : 0 ≤ Rdb := le_trans (abs_nonneg _) hdr
  have hRadb0 : 0 ≤ Radb := le_trans (abs_nonneg _) hrad
  have hDdb0 : 0 ≤ Ddb := le_trans (abs_nonneg _) hddr
  have hDb0 : 0 ≤ Db := le_trans (abs_nonneg _) hd0
  -- pd2 F
  have hp2x : |S.d 0 * S.px u| ≤ Db * Pb := by rw [abs_mul]; exact mul_le_mul hd0 hpx (abs_nonneg _) hDb0
  have hp2y : |S.d 1 * S.py u| ≤ Db * Pb := by rw [abs_mul]; exact mul_le_mul hd1 hpy (abs_nonneg _) hDb0
  have hp2z : |S.d 2 * S.pz u| ≤ Db * Pb := by rw [abs_mul]; exact mul_le_mul hd2 hpz (abs_nonneg _) hDb0
  have hp2tri : |S.d 0*S.px u + S.d 1*S.py u + S.d 2*S.pz u| ≤
      |S.d 0*S.px u| + |S.d 1*S.py u| + |S.d 2*S.pz u| := by
    have a := abs_add_le (S.d 0*S.px u + S.d 1*S.py u) (S.d 2*S.pz u)
    have b := abs_add_le (S.d 0*S.px u) (S.d 1*S.py u)
    linarith
  have hpd2F : |pd2 (bezF S) u t| ≤ 3*Db*Pb := by
    rw [pd2_bezF]
    nlinarith
  -- pd1 F
  have hpxsq : (S.px u)^2 ≤ Pb^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hPb0] using hpx)
  have hpysq : (S.py u)^2 ≤ Pb^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hPb0] using hpy)
  have hpzsq : (S.pz u)^2 ≤ Pb^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hPb0] using hpz)
  have hsumsq : |S.px u ^2 + S.py u ^2 + S.pz u ^2| ≤ 3*Pb^2 := by
    have htri : |S.px u ^2 + S.py u ^2 + S.pz u ^2| ≤ |S.px u ^2| + |S.py u ^2| + |S.pz u ^2| := by
      have a := abs_add_le (S.px u^2 + S.py u^2) (S.pz u^2)
      have b := abs_add_le (S.px u^2) (S.py u^2)
      linarith
    have hsqa : |S.px u^2 + S.py u^2 + S.pz u^2| = S.px u^2 + S.py u^2 + S.pz u^2 := abs_of_nonneg (by positivity)
    rw [hsqa]
    nlinarith [hpxsq, hpysq, hpzsq]
  have hRxqx : |S.Rx u t * S.qx u| ≤ Rb*Qb := by rw [abs_mul]; exact mul_le_mul hRx hqx (abs_nonneg _) hRb0
  have hRyqy : |S.Ry u t * S.qy u| ≤ Rb*Qb := by rw [abs_mul]; exact mul_le_mul hRy hqy (abs_nonneg _) hRb0
  have hRzqz : |S.Rz u t * S.qz u| ≤ Rb*Qb := by rw [abs_mul]; exact mul_le_mul hRz hqz (abs_nonneg _) hRb0
  have hsumR : |S.Rx u t*S.qx u + S.Ry u t*S.qy u + S.Rz u t*S.qz u| ≤ 3*Rb*Qb := by
    have htri : |S.Rx u t*S.qx u + S.Ry u t*S.qy u + S.Rz u t*S.qz u| ≤
        |S.Rx u t*S.qx u| + |S.Ry u t*S.qy u| + |S.Rz u t*S.qz u| := by
      have a := abs_add_le (S.Rx u t*S.qx u + S.Ry u t*S.qy u) (S.Rz u t*S.qz u)
      have b := abs_add_le (S.Rx u t*S.qx u) (S.Ry u t*S.qy u)
      linarith
    nlinarith
  have hdrsq : (S.dr u)^2 ≤ Rdb^2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hRdb0] using hdr)
  have hradd : |S.rad u * S.ddr u| ≤ Radb*Ddb := by rw [abs_mul]; exact mul_le_mul hrad hddr (abs_nonneg _) hRadb0
  have hpd1F : |pd1 (bezF S) u t| ≤ 3*Pb^2 + 3*Rb*Qb + Rdb^2 + Radb*Ddb := by
    rw [pd1_bezF]
    have htri : |-(S.px u^2 + S.py u^2 + S.pz u^2) +
        (S.Rx u t*S.qx u + S.Ry u t*S.qy u + S.Rz u t*S.qz u) +
        S.dr u^2 + S.rad u*S.ddr u| ≤
        |S.px u^2 + S.py u^2 + S.pz u^2| +
        |S.Rx u t*S.qx u + S.Ry u t*S.qy u + S.Rz u t*S.qz u| +
        |S.dr u^2| + |S.rad u*S.ddr u| := by
      have a := abs_add_le (-(S.px u^2+S.py u^2+S.pz u^2) +
        (S.Rx u t*S.qx u+S.Ry u t*S.qy u+S.Rz u t*S.qz u) + S.dr u^2) (S.rad u*S.ddr u)
      have b := abs_add_le (-(S.px u^2+S.py u^2+S.pz u^2) +
        (S.Rx u t*S.qx u+S.Ry u t*S.qy u+S.Rz u t*S.qz u)) (S.dr u^2)
      have c := abs_add_le (-(S.px u^2+S.py u^2+S.pz u^2)) (S.Rx u t*S.qx u+S.Ry u t*S.qy u+S.Rz u t*S.qz u)
      have d := abs_neg (S.px u^2+S.py u^2+S.pz u^2)
      linarith
    have hdrsqa : |S.dr u^2| = S.dr u^2 := abs_of_nonneg (sq_nonneg _)
    rw [hdrsqa] at htri
    nlinarith
  -- len positive
  have hlenpos : 0 < S.len u t := lt_of_lt_of_le hLbpos hLb
  -- pd1 G
  have hnum1 : |S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u| ≤ 3*Rb*Pb := by
    have h1 : |S.Rx u t*S.px u| ≤ Rb*Pb := by rw [abs_mul]; exact mul_le_mul hRx hpx (abs_nonneg _) hRb0
    have h2 : |S.Ry u t*S.py u| ≤ Rb*Pb := by rw [abs_mul]; exact mul_le_mul hRy hpy (abs_nonneg _) hRb0
    have h3 : |S.Rz u t*S.pz u| ≤ Rb*Pb := by rw [abs_mul]; exact mul_le_mul hRz hpz (abs_nonneg _) hRb0
    have htri : |S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u| ≤
        |S.Rx u t*S.px u| + |S.Ry u t*S.py u| + |S.Rz u t*S.pz u| := by
      have a := abs_add_le (S.Rx u t*S.px u + S.Ry u t*S.py u) (S.Rz u t*S.pz u)
      have b := abs_add_le (S.Rx u t*S.px u) (S.Ry u t*S.py u)
      linarith
    nlinarith
  have hdiv1 : |(S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u) / S.len u t| ≤ (3*Rb*Pb)/Lb := by
    rw [abs_div, abs_of_pos hlenpos]
    calc |S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u| / S.len u t
        ≤ (3*Rb*Pb) / S.len u t := div_le_div_of_nonneg_right hnum1 (le_of_lt hlenpos)
      _ = (3*Rb*Pb) * (1 / S.len u t) := by ring
      _ ≤ (3*Rb*Pb) * (1 / Lb) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hLbpos hLb) (by positivity)
      _ = (3*Rb*Pb) / Lb := by ring
  have hpd1G : |pd1 (bezG S) u t| ≤ (3*Rb*Pb)/Lb + Rdb := by
    rw [pd1_bezG S u t hlene]
    have htri : |-(S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u) / S.len u t - S.dr u| ≤
        |(S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u) / S.len u t| + |S.dr u| := by
      have a := abs_sub (-(S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u) / S.len u t) (S.dr u)
      have b : |-(S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u) / S.len u t| =
          |(S.Rx u t*S.px u + S.Ry u t*S.py u + S.Rz u t*S.pz u) / S.len u t| := by
        rw [neg_div, abs_neg]
      linarith
    nlinarith
  -- pd2 G
  have hnum2 : |S.Rx u t*S.d 0 + S.Ry u t*S.d 1 + S.Rz u t*S.d 2| ≤ 3*Rb*Db := by
    have h1 : |S.Rx u t*S.d 0| ≤ Rb*Db := by rw [abs_mul]; exact mul_le_mul hRx hd0 (abs_nonneg _) hRb0
    have h2 : |S.Ry u t*S.d 1| ≤ Rb*Db := by rw [abs_mul]; exact mul_le_mul hRy hd1 (abs_nonneg _) hRb0
    have h3 : |S.Rz u t*S.d 2| ≤ Rb*Db := by rw [abs_mul]; exact mul_le_mul hRz hd2 (abs_nonneg _) hRb0
    have htri : |S.Rx u t*S.d 0 + S.Ry u t*S.d 1 + S.Rz u t*S.d 2| ≤
        |S.Rx u t*S.d 0| + |S.Ry u t*S.d 1| + |S.Rz u t*S.d 2| := by
      have a := abs_add_le (S.Rx u t*S.d 0 + S.Ry u t*S.d 1) (S.Rz u t*S.d 2)
      have b := abs_add_le (S.Rx u t*S.d 0) (S.Ry u t*S.d 1)
      linarith
    nlinarith
  have hpd2G : |pd2 (bezG S) u t| ≤ (3*Rb*Db)/Lb := by
    rw [pd2_bezG S u t hlene]
    rw [abs_div, abs_of_pos hlenpos]
    calc |S.Rx u t*S.d 0 + S.Ry u t*S.d 1 + S.Rz u t*S.d 2| / S.len u t
        ≤ (3*Rb*Db) / S.len u t := div_le_div_of_nonneg_right hnum2 (le_of_lt hlenpos)
      _ = (3*Rb*Db) * (1 / S.len u t) := by ring
      _ ≤ (3*Rb*Db) * (1 / Lb) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hLbpos hLb) (by positivity)
      _ = (3*Rb*Db) / Lb := by ring
  exact ⟨hpd1F, hpd2F, hpd1G, hpd2G⟩


-- === component bounds from control points ===

theorem bezP_le_cSup (c : Fin 4 → Fin 4 → ℝ) (i : Fin 4) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |bezP (c 0 i) (c 1 i) (c 2 i) (c 3 i) u| ≤ cSup c := by
  have h := abs_bezP_le_max (c 0 i) (c 1 i) (c 2 i) (c 3 i) u hu0 hu1
  have hsup : Finset.univ.sup' Finset.univ_nonempty
      (fun k : Fin 4 => |![c 0 i, c 1 i, c 2 i, c 3 i] k|) ≤ cSup c := by
    rw [Finset.sup'_le_iff]; intro k hk
    fin_cases k
    · simpa using le_cSup c 0 i
    · simpa using le_cSup c 1 i
    · simpa using le_cSup c 2 i
    · simpa using le_cSup c 3 i
  exact h.trans hsup

theorem dBezP_le_edgeSup (c : Fin 4 → Fin 4 → ℝ) (i : Fin 4) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |dBezP (c 0 i) (c 1 i) (c 2 i) (c 3 i) u| ≤ 3 * edgeSup c := by
  have h := abs_dBezP_le (c 0 i) (c 1 i) (c 2 i) (c 3 i) u hu0 hu1
  have h01 : |c 1 i - c 0 i| ≤ edgeSup c := by simpa using le_edgeSup c (0 : Fin 3) i
  have h12 : |c 2 i - c 1 i| ≤ edgeSup c := by simpa using le_edgeSup c (1 : Fin 3) i
  have h23 : |c 3 i - c 2 i| ≤ edgeSup c := by simpa using le_edgeSup c (2 : Fin 3) i
  have hm : max (max |c 1 i - c 0 i| |c 2 i - c 1 i|) |c 3 i - c 2 i| ≤ edgeSup c :=
    max_le (max_le h01 h12) h23
  nlinarith

theorem ddBezP_le_ddSup (c : Fin 4 → Fin 4 → ℝ) (i : Fin 4) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |ddBezP (c 0 i) (c 1 i) (c 2 i) (c 3 i) u| ≤ 6 * ddSup c := by
  have h := abs_ddBezP_le (c 0 i) (c 1 i) (c 2 i) (c 3 i) u hu0 hu1
  have h0 : |c 2 i - 2*c 1 i + c 0 i| ≤ ddSup c := le_ddSup0 c i
  have h1 : |c 3 i - 2*c 2 i + c 1 i| ≤ ddSup c := le_ddSup1 c i
  have hm : max |c 2 i - 2*c 1 i + c 0 i| |c 3 i - 2*c 2 i + c 1 i| ≤ ddSup c := max_le h0 h1
  nlinarith

-- === the final B0 supply ===

/-- Explicit bound `B0` on the four first partials of `ofCubic`'s contact
    system at a root, expressed directly from the Bézier control points, the
    ray direction, the seed parameter `t₀`, and the local ray length. -/
noncomputable def ofCubicB0 (c : Fin 4 → Fin 4 → ℝ) (d : Fin 3 → ℝ)
    (u₀ t₀ : ℝ) : ℝ :=
  let M := cSup c
  let E := edgeSup c
  let S2 := ddSup c
  let D := dSup d
  let T := |t₀|
  let Lb := (ofCubic c d).len u₀ t₀
  max (max (36*E^2 + 18*S2*(T*D+M) + 6*M*S2) (9*D*E))
      (max (9*E*(T*D+M)/Lb + 3*E) (3*(T*D+M)*D/Lb))

theorem ofCubic_root_data_B0 (c : Fin 4 → Fin 4 → ℝ) (d : Fin 3 → ℝ) (u₀ t₀ : ℝ)
    (hu₀ : u₀ ∈ Set.Icc 0 1)
    (hlene : 0 < (ofCubic c d).q u₀ t₀) :
    0 ≤ ofCubicB0 c d u₀ t₀ ∧
      |pd1 (bezF (ofCubic c d)) u₀ t₀| ≤ ofCubicB0 c d u₀ t₀ ∧
      |pd2 (bezF (ofCubic c d)) u₀ t₀| ≤ ofCubicB0 c d u₀ t₀ ∧
      |pd1 (bezG (ofCubic c d)) u₀ t₀| ≤ ofCubicB0 c d u₀ t₀ ∧
      |pd2 (bezG (ofCubic c d)) u₀ t₀| ≤ ofCubicB0 c d u₀ t₀ := by
  let S := ofCubic c d
  let M := cSup c
  let E := edgeSup c
  let S2 := ddSup c
  let D := dSup d
  let T := |t₀|
  let Lb := S.len u₀ t₀
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (by simpa [M] using le_cSup c 0 0)
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) (by simpa [E] using le_edgeSup c (0 : Fin 3) (0 : Fin 4))
  have hS20 : 0 ≤ S2 := le_trans (abs_nonneg _) (by simpa [S2] using le_ddSup0 c (0 : Fin 4))
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (by simpa [D] using le_dSup d (0 : Fin 3))
  have hT0 : 0 ≤ T := by dsimp [T]; exact abs_nonneg _
  have hu0 : 0 ≤ u₀ := hu₀.1
  have hu1 : u₀ ≤ 1 := hu₀.2
  have hgx : |S.gx u₀| ≤ M := by
    change |bezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u₀| ≤ M
    simpa [M] using bezP_le_cSup c 0 hu0 hu1
  have hgy : |S.gy u₀| ≤ M := by
    change |bezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u₀| ≤ M
    simpa [M] using bezP_le_cSup c 1 hu0 hu1
  have hgz : |S.gz u₀| ≤ M := by
    change |bezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u₀| ≤ M
    simpa [M] using bezP_le_cSup c 2 hu0 hu1
  have hrad : |S.rad u₀| ≤ M := by
    change |bezP (c 0 3) (c 1 3) (c 2 3) (c 3 3) u₀| ≤ M
    simpa [M] using bezP_le_cSup c 3 hu0 hu1
  have hpx : |S.px u₀| ≤ 3*E := by
    change |dBezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u₀| ≤ 3*E
    simpa [E] using dBezP_le_edgeSup c 0 hu0 hu1
  have hpy : |S.py u₀| ≤ 3*E := by
    change |dBezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u₀| ≤ 3*E
    simpa [E] using dBezP_le_edgeSup c 1 hu0 hu1
  have hpz : |S.pz u₀| ≤ 3*E := by
    change |dBezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u₀| ≤ 3*E
    simpa [E] using dBezP_le_edgeSup c 2 hu0 hu1
  have hdr : |S.dr u₀| ≤ 3*E := by
    change |dBezP (c 0 3) (c 1 3) (c 2 3) (c 3 3) u₀| ≤ 3*E
    simpa [E] using dBezP_le_edgeSup c 3 hu0 hu1
  have hqx : |S.qx u₀| ≤ 6*S2 := by
    change |ddBezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u₀| ≤ 6*S2
    simpa [S2] using ddBezP_le_ddSup c 0 hu0 hu1
  have hqy : |S.qy u₀| ≤ 6*S2 := by
    change |ddBezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u₀| ≤ 6*S2
    simpa [S2] using ddBezP_le_ddSup c 1 hu0 hu1
  have hqz : |S.qz u₀| ≤ 6*S2 := by
    change |ddBezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u₀| ≤ 6*S2
    simpa [S2] using ddBezP_le_ddSup c 2 hu0 hu1
  have hddr : |S.ddr u₀| ≤ 6*S2 := by
    change |ddBezP (c 0 3) (c 1 3) (c 2 3) (c 3 3) u₀| ≤ 6*S2
    simpa [S2] using ddBezP_le_ddSup c 3 hu0 hu1
  have hd0 : |S.d 0| ≤ D := by
    change |d 0| ≤ D
    simpa [D] using le_dSup d (0 : Fin 3)
  have hd1 : |S.d 1| ≤ D := by
    change |d 1| ≤ D
    simpa [D] using le_dSup d (1 : Fin 3)
  have hd2 : |S.d 2| ≤ D := by
    change |d 2| ≤ D
    simpa [D] using le_dSup d (2 : Fin 3)
  have hRx : |S.Rx u₀ t₀| ≤ T*D + M := by
    change |t₀ * d 0 - bezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u₀| ≤ T*D + M
    have hmul : |t₀ * d 0| ≤ T*D := by
      rw [abs_mul]
      exact mul_le_mul (by rfl : |t₀| ≤ T) hd0 (abs_nonneg _) (abs_nonneg _)
    have hgx' : |bezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u₀| ≤ M := by
      change |S.gx u₀| ≤ M
      exact hgx
    have htri := abs_sub (t₀ * d 0) (bezP (c 0 0) (c 1 0) (c 2 0) (c 3 0) u₀)
    nlinarith
  have hRy : |S.Ry u₀ t₀| ≤ T*D + M := by
    change |t₀ * d 1 - bezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u₀| ≤ T*D + M
    have hmul : |t₀ * d 1| ≤ T*D := by
      rw [abs_mul]
      exact mul_le_mul (by rfl : |t₀| ≤ T) hd1 (abs_nonneg _) (abs_nonneg _)
    have hgx' : |bezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u₀| ≤ M := by
      change |S.gy u₀| ≤ M
      exact hgy
    have htri := abs_sub (t₀ * d 1) (bezP (c 0 1) (c 1 1) (c 2 1) (c 3 1) u₀)
    nlinarith
  have hRz : |S.Rz u₀ t₀| ≤ T*D + M := by
    change |t₀ * d 2 - bezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u₀| ≤ T*D + M
    have hmul : |t₀ * d 2| ≤ T*D := by
      rw [abs_mul]
      exact mul_le_mul (by rfl : |t₀| ≤ T) hd2 (abs_nonneg _) (abs_nonneg _)
    have hgx' : |bezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u₀| ≤ M := by
      change |S.gz u₀| ≤ M
      exact hgz
    have htri := abs_sub (t₀ * d 2) (bezP (c 0 2) (c 1 2) (c 2 2) (c 3 2) u₀)
    nlinarith
  have hLbpos : 0 < Lb := by
    dsimp [Lb, S]
    exact Real.sqrt_pos.2 hlene
  have hbnd := bez_root_partial_bounds S u₀ t₀ hlene (T*D+M) (3*E) (6*S2) (3*E) M (6*S2) D Lb
      hRx hRy hRz hpx hpy hpz hqx hqy hqz hdr hrad hddr hd0 hd1 hd2 hLbpos (le_rfl)
  let B0 := max (max (36*E^2 + 18*S2*(T*D+M) + 6*M*S2) (9*D*E))
                (max (9*E*(T*D+M)/Lb + 3*E) (3*(T*D+M)*D/Lb))
  have hA : 36*E^2 + 18*S2*(T*D+M) + 6*M*S2 ≤ B0 := by
    dsimp [B0]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hB : 9*D*E ≤ B0 := by
    dsimp [B0]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hC : 9*E*(T*D+M)/Lb + 3*E ≤ B0 := by
    dsimp [B0]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hD : 3*(T*D+M)*D/Lb ≤ B0 := by
    dsimp [B0]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  change 0 ≤ B0 ∧ |pd1 (bezF S) u₀ t₀| ≤ B0 ∧ |pd2 (bezF S) u₀ t₀| ≤ B0 ∧
      |pd1 (bezG S) u₀ t₀| ≤ B0 ∧ |pd2 (bezG S) u₀ t₀| ≤ B0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [B0]
    positivity
  · calc |pd1 (bezF S) u₀ t₀| ≤ 3*(3*E)^2 + 3*(T*D+M)*(6*S2) + (3*E)^2 + M*(6*S2) := hbnd.1
      _ = 36*E^2 + 18*S2*(T*D+M) + 6*M*S2 := by ring
      _ ≤ B0 := hA
  · calc |pd2 (bezF S) u₀ t₀| ≤ 3*D*(3*E) := hbnd.2.1
      _ = 9*D*E := by ring
      _ ≤ B0 := hB
  · calc |pd1 (bezG S) u₀ t₀| ≤ (3*(T*D+M)*(3*E))/Lb + 3*E := hbnd.2.2.1
      _ = 9*E*(T*D+M)/Lb + 3*E := by ring
      _ ≤ B0 := hC
  · calc |pd2 (bezG S) u₀ t₀| ≤ (3*(T*D+M)*D)/Lb := hbnd.2.2.2
      _ = 3*(T*D+M)*D/Lb := by ring
      _ ≤ B0 := hD



/-- **M14 conditional convergence for the concrete cubic system.** The bound
    `B0` on the four root partials is supplied automatically from the control
    points by `ofCubic_root_data_B0`; what remains as hypotheses are exactly
    the genuinely nondegenerate data: the `C²`/length guards on the rectangle,
    the nonvanishing Jacobian determinant `det0`, the radius conditions, and
    the rectangle/seed geometry. -/
theorem ofCubic_newton_tendsto_of_root_data
    (c : Fin 4 → Fin 4 → ℝ) (d : Fin 3 → ℝ)
    (a b cα dα K det0 R : ℝ) {u₀ t₀ u t : ℝ}
    (hu₀01 : u₀ ∈ Set.Icc 0 1)
    (hb : PddBounds (ofCubic c d) a b cα dα K)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc cα dα, 0 < (ofCubic c d).q u t)
    (hK : 0 < K) (hK0 : 0 ≤ K) (hdet0pos : 0 < det0)
    (hu₀ : u₀ ∈ Set.Icc a b) (ht₀ : t₀ ∈ Set.Icc cα dα)
    (hroot : bezF (ofCubic c d) u₀ t₀ = 0 ∧ bezG (ofCubic c d) u₀ t₀ = 0)
    (hdet0 : det0 ≤ |jacDet (bezF (ofCubic c d)) (bezG (ofCubic c d)) u₀ t₀|)
    (hR0 : 0 ≤ R) (hKR : K * R ≤ 1)
    (hvar : 4 * ofCubicB0 c d u₀ t₀ * K * R + 4 * (K * R)^2 ≤ det0 / 2)
    (hcond : 2 * (ofCubicB0 c d u₀ t₀ + K * R + 1)^2 / (det0 / 2) < 1)
    (hsmall : 2 * (ofCubicB0 c d u₀ t₀ + K * R + 1)^2 / (det0 / 2) +
        18 * (ofCubicB0 c d u₀ t₀ + K * R + 1) * K / (det0 / 2) * R < 1)
    (hrect : ∀ u' t', |u' - u₀| + |t' - t₀| ≤ R →
      u' ∈ Set.Icc a b ∧ t' ∈ Set.Icc cα dα)
    (hseed : |u - u₀| + |t - t₀| ≤ R) :
    Tendsto (fun n => (newtonIter (ofCubic c d) u t n).1) atTop (𝓝 u₀) ∧
    Tendsto (fun n => (newtonIter (ofCubic c d) u t n).2) atTop (𝓝 t₀) := by
  have hdata := ofCubic_root_data_B0 c d u₀ t₀ hu₀01 (hlene u₀ hu₀ t₀ ht₀)
  exact newtonIter_tendsto_of_root_data (ofCubic c d) a b cα dα K
      (ofCubicB0 c d u₀ t₀) det0 R hb hlene hK hK0 hdata.1 hdet0pos
      hu₀ ht₀ hroot hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2
      hdet0 hR0 hKR hvar hcond hsmall hrect hseed

end LightRT.Geom
