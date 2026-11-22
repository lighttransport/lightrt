/-
  Closed-form second partial derivatives of the Bézier contact system
  (`bezF`, `bezG`) — the analytic core for supplying `K` / `PddBounds`
  from control points (M14). The `bezG` fields require `0 < q` at the point.
-/
import Mathlib
import LightRT.Geom.BezData

set_option maxHeartbeats 2000000

namespace LightRT.Geom
open BezSys
open Filter Topology
open Polynomial

def dddBezP (b0 b1 b2 b3 : ℝ) : ℝ := 6 * (b3 - 3*b2 + 3*b1 - b0)

theorem hasDerivAt_ddBezP (b0 b1 b2 b3 u : ℝ) :
    HasDerivAt (ddBezP b0 b1 b2 b3) (dddBezP b0 b1 b2 b3) u := by
  have e : ddBezP b0 b1 b2 b3 = fun x => (derivative (derivative (bezPoly b0 b1 b2 b3))).eval x :=
    funext fun x => ddBezP_eq_eval b0 b1 b2 b3 x
  rw [e]
  convert (derivative (derivative (bezPoly b0 b1 b2 b3))).hasDerivAt u using 1
  simp [bezPoly, Polynomial.derivative_add, Polynomial.derivative_monomial, dddBezP]
  ring

theorem deriv_ddBezP (b0 b1 b2 b3 u : ℝ) :
    deriv (ddBezP b0 b1 b2 b3) u = dddBezP b0 b1 b2 b3 :=
  (hasDerivAt_ddBezP b0 b1 b2 b3 u).deriv


theorem pdd22_bezF_eq_zero (S : BezSys) (u t : ℝ) :
    pdd22 (bezF S) u t = 0 := by
  unfold pdd22
  have hfun : (fun s => pd2 (bezF S) u s) =
      fun _ => S.d 0 * S.px u + S.d 1 * S.py u + S.d 2 * S.pz u := by
    funext s
    rw [pd2_bezF]
  rw [hfun]
  have hc : HasDerivAt (fun _ : ℝ =>
      S.d 0 * S.px u + S.d 1 * S.py u + S.d 2 * S.pz u) 0 t := hasDerivAt_const t _
  exact hc.deriv

theorem pdd12_bezF (S : BezSys) (u t : ℝ) :
    pdd12 (bezF S) u t = S.d 0 * S.qx u + S.d 1 * S.qy u + S.d 2 * S.qz u := by
  unfold pdd12
  have hfun : (fun s => pd1 (bezF S) u s) = fun s =>
      -(S.px u ^ 2 + S.py u ^ 2 + S.pz u ^ 2) +
      ((s * S.d 0 - S.gx u) * S.qx u + (s * S.d 1 - S.gy u) * S.qy u +
        (s * S.d 2 - S.gz u) * S.qz u) +
      (S.dr u ^ 2 + S.rad u * S.ddr u) := by
    funext s
    rw [pd1_bezF]
    simp [Rx, Ry, Rz]
    ring
  rw [hfun]
  have h1 : HasDerivAt (fun s : ℝ => (s * S.d 0 - S.gx u) * S.qx u) (S.d 0 * S.qx u) t := by
    simpa [id] using (((hasDerivAt_id t).mul_const (S.d 0)).sub_const (S.gx u)).mul_const (S.qx u)
  have h2 : HasDerivAt (fun s : ℝ => (s * S.d 1 - S.gy u) * S.qy u) (S.d 1 * S.qy u) t := by
    simpa [id] using (((hasDerivAt_id t).mul_const (S.d 1)).sub_const (S.gy u)).mul_const (S.qy u)
  have h3 : HasDerivAt (fun s : ℝ => (s * S.d 2 - S.gz u) * S.qz u) (S.d 2 * S.qz u) t := by
    simpa [id] using (((hasDerivAt_id t).mul_const (S.d 2)).sub_const (S.gz u)).mul_const (S.qz u)
  have hsum := (h1.add h2).add h3
  have hc : HasDerivAt (fun s : ℝ =>
      -(S.px u ^ 2 + S.py u ^ 2 + S.pz u ^ 2) + ((s * S.d 0 - S.gx u) * S.qx u +
        (s * S.d 1 - S.gy u) * S.qy u + (s * S.d 2 - S.gz u) * S.qz u) +
      (S.dr u ^ 2 + S.rad u * S.ddr u))
      (S.d 0 * S.qx u + S.d 1 * S.qy u + S.d 2 * S.qz u) t := by
    convert ((hasDerivAt_const t (-(S.px u ^ 2 + S.py u ^ 2 + S.pz u ^ 2))).add hsum).add
      (hasDerivAt_const t (S.dr u ^ 2 + S.rad u * S.ddr u)) using 1 <;>
      (first | (ext s; simp [id]; ring_nf) | ring_nf)
  exact hc.deriv

theorem pdd21_bezF (S : BezSys) (u t : ℝ) :
    pdd21 (bezF S) u t = S.d 0 * S.qx u + S.d 1 * S.qy u + S.d 2 * S.qz u := by
  unfold pdd21
  have hfun : (fun s => pd2 (bezF S) s t) = fun s =>
      S.d 0 * S.px s + S.d 1 * S.py s + S.d 2 * S.pz s := by
    funext s
    rw [pd2_bezF]
  rw [hfun]
  have h1 := (S.hγx' u).const_mul (S.d 0)
  have h2 := (S.hγy' u).const_mul (S.d 1)
  have h3 := (S.hγz' u).const_mul (S.d 2)
  have hc : HasDerivAt (fun s : ℝ => S.d 0 * S.px s + S.d 1 * S.py s + S.d 2 * S.pz s)
      (S.d 0 * S.qx u + S.d 1 * S.qy u + S.d 2 * S.qz u) u := by
    convert (h1.add h2).add h3 using 1 <;>
      (first | (ext s; simp [id]; ring_nf) | ring_nf)
  exact hc.deriv



theorem pdd11_bezF (S : BezSys) (u t : ℝ) :
    pdd11 (bezF S) u t =
      -3 * (S.px u * S.qx u + S.py u * S.qy u + S.pz u * S.qz u) +
      (S.Rx u t * deriv S.qx u + S.Ry u t * deriv S.qy u + S.Rz u t * deriv S.qz u) +
      3 * S.dr u * S.ddr u + S.rad u * deriv S.ddr u := by
  unfold pdd11
  have hfun : (fun s => pd1 (bezF S) s t) = fun s =>
      -(S.px s ^ 2 + S.py s ^ 2 + S.pz s ^ 2) +
      (S.Rx s t * S.qx s + S.Ry s t * S.qy s + S.Rz s t * S.qz s) +
      (S.dr s ^ 2 + S.rad s * S.ddr s) := by
    funext s
    rw [pd1_bezF]
    ring
  rw [hfun]
  have hp1 := (S.hγx' u).mul (S.hγx' u)
  have hp2 := (S.hγy' u).mul (S.hγy' u)
  have hp3 := (S.hγz' u).mul (S.hγz' u)
  have hqx' := (S.hdγx u).hasDerivAt
  have hqy' := (S.hdγy u).hasDerivAt
  have hqz' := (S.hdγz u).hasDerivAt
  have hdr' := (S.hdρ u).hasDerivAt
  have hr1 := (hRx S u t).mul hqx'
  have hr2 := (hRy S u t).mul hqy'
  have hr3 := (hRz S u t).mul hqz'
  have hdr2 := (S.hρ' u).mul (S.hρ' u)
  have hra := (S.hρ u).mul hdr'
  have hsq := ((hp1.add hp2).add hp3).neg
  have hR := (hr1.add hr2).add hr3
  have htail := hdr2.add hra
  have hall := (hsq.add hR).add htail
  have hfn_eq : (fun s => -(S.px s ^ 2 + S.py s ^ 2 + S.pz s ^ 2) +
        (S.Rx s t * S.qx s + S.Ry s t * S.qy s + S.Rz s t * S.qz s) +
        (S.dr s ^ 2 + S.rad s * S.ddr s)) =
      (fun s => -(S.px s * S.px s + S.py s * S.py s + S.pz s * S.pz s) +
        ((t * S.d 0 - S.gx s) * S.qx s + (t * S.d 1 - S.gy s) * S.qy s +
          (t * S.d 2 - S.gz s) * S.qz s) +
        (S.dr s * S.dr s + S.rad s * S.ddr s)) := by
    funext s
    simp [Rx, Ry, Rz]
    ring
  rw [hfn_eq]
  exact hall.deriv.trans (by simp [Rx, Ry, Rz]; ring_nf)


theorem len_hasDerivAt_t (S : BezSys) (u t : ℝ) (hlene : 0 < S.q u t) :
    HasDerivAt (fun s => S.len u s)
      ((S.Rx u t * S.d 0 + S.Ry u t * S.d 1 + S.Rz u t * S.d 2) / S.len u t) t := by
  have hq := hdq_t S u t
  have hs := hq.sqrt (ne_of_gt hlene)
  convert hs using 1
  · ext s; rfl
  · unfold len
    field_simp [Real.sqrt_ne_zero'.mpr hlene] <;> ring

theorem len_hasDerivAt_u (S : BezSys) (u t : ℝ) (hlene : 0 < S.q u t) :
    HasDerivAt (fun s => S.len s t)
      (-(S.Rx u t * S.px u + S.Ry u t * S.py u + S.Rz u t * S.pz u) / S.len u t) u := by
  have hq := hdq_u S u t
  have hs := hq.sqrt (ne_of_gt hlene)
  convert hs using 1
  · ext s; rfl
  · unfold len
    field_simp [Real.sqrt_ne_zero'.mpr hlene] <;> ring



theorem pdd22_bezG (S : BezSys) (u t : ℝ) (hlene : 0 < S.q u t) :
    pdd22 (bezG S) u t =
      (S.d 0 ^ 2 + S.d 1 ^ 2 + S.d 2 ^ 2) / S.len u t -
      (S.Rx u t * S.d 0 + S.Ry u t * S.d 1 + S.Rz u t * S.d 2) ^ 2 / S.len u t ^ 3 := by
  unfold pdd22
  have hcont : ContinuousAt (fun s => S.q u s) t := by unfold q Rx Ry Rz; fun_prop
  have hevq : ∀ᶠ s in 𝓝 t, 0 < S.q u s := hcont.eventually (isOpen_Ioi.mem_nhds hlene)
  have heq : (fun s => pd2 (bezG S) u s) =ᶠ[𝓝 t]
      (fun s => ((s * S.d 0 - S.gx u) * S.d 0 + (s * S.d 1 - S.gy u) * S.d 1 +
        (s * S.d 2 - S.gz u) * S.d 2) / S.len u s) := by
    filter_upwards [hevq] with s hs
    rw [pd2_bezG S u s hs]
    simp [Rx, Ry, Rz]
  have hn0 : HasDerivAt (fun s : ℝ => (s * S.d 0 - S.gx u) * S.d 0) (S.d 0 ^ 2) t := by
    simpa [id, pow_two] using (((hasDerivAt_id t).mul_const (S.d 0)).sub_const (S.gx u)).mul_const (S.d 0)
  have hn1 : HasDerivAt (fun s : ℝ => (s * S.d 1 - S.gy u) * S.d 1) (S.d 1 ^ 2) t := by
    simpa [id, pow_two] using (((hasDerivAt_id t).mul_const (S.d 1)).sub_const (S.gy u)).mul_const (S.d 1)
  have hn2 : HasDerivAt (fun s : ℝ => (s * S.d 2 - S.gz u) * S.d 2) (S.d 2 ^ 2) t := by
    simpa [id, pow_two] using (((hasDerivAt_id t).mul_const (S.d 2)).sub_const (S.gz u)).mul_const (S.d 2)
  have hnum := (hn0.add hn1).add hn2
  have hlen := len_hasDerivAt_t S u t hlene
  have hlen_ne : S.len u t ≠ 0 := ne_of_gt (lt_of_lt_of_le (show 0 < Real.sqrt (S.q u t) from Real.sqrt_pos.2 hlene) le_rfl)
  have hdiv := hnum.div hlen hlen_ne
  have htarget : HasDerivAt
      (fun s => ((s * S.d 0 - S.gx u) * S.d 0 + (s * S.d 1 - S.gy u) * S.d 1 +
        (s * S.d 2 - S.gz u) * S.d 2) / S.len u s)
      ((S.d 0 ^ 2 + S.d 1 ^ 2 + S.d 2 ^ 2) / S.len u t -
        (S.Rx u t * S.d 0 + S.Ry u t * S.d 1 + S.Rz u t * S.d 2) ^ 2 / S.len u t ^ 3) t := by
    convert hdiv using 1 <;>
      (first | (ext s; simp [Pi.add_apply]) | (simp [Rx, Ry, Rz]; field_simp [hlen_ne] <;> ring))
  exact (htarget.congr_of_eventuallyEq heq).deriv



theorem pdd12_bezG (S : BezSys) (u t : ℝ) (hlene : 0 < S.q u t) :
    pdd12 (bezG S) u t =
      -(S.d 0 * S.px u + S.d 1 * S.py u + S.d 2 * S.pz u) / S.len u t +
      (S.Rx u t * S.px u + S.Ry u t * S.py u + S.Rz u t * S.pz u) *
        (S.Rx u t * S.d 0 + S.Ry u t * S.d 1 + S.Rz u t * S.d 2) / S.len u t ^ 3 := by
  unfold pdd12
  have hcont : ContinuousAt (fun s => S.q u s) t := by unfold q Rx Ry Rz; fun_prop
  have hevq : ∀ᶠ s in 𝓝 t, 0 < S.q u s := hcont.eventually (isOpen_Ioi.mem_nhds hlene)
  have heq : (fun s => pd1 (bezG S) u s) =ᶠ[𝓝 t]
      (fun s => -(((s * S.d 0 - S.gx u) * S.px u + (s * S.d 1 - S.gy u) * S.py u +
        (s * S.d 2 - S.gz u) * S.pz u) / S.len u s) - S.dr u) := by
    filter_upwards [hevq] with s hs
    rw [pd1_bezG S u s hs]
    simp [Rx, Ry, Rz]
    ring
  have hn0 : HasDerivAt (fun s : ℝ => (s * S.d 0 - S.gx u) * S.px u) (S.d 0 * S.px u) t := by
    simpa [id] using (((hasDerivAt_id t).mul_const (S.d 0)).sub_const (S.gx u)).mul_const (S.px u)
  have hn1 : HasDerivAt (fun s : ℝ => (s * S.d 1 - S.gy u) * S.py u) (S.d 1 * S.py u) t := by
    simpa [id] using (((hasDerivAt_id t).mul_const (S.d 1)).sub_const (S.gy u)).mul_const (S.py u)
  have hn2 : HasDerivAt (fun s : ℝ => (s * S.d 2 - S.gz u) * S.pz u) (S.d 2 * S.pz u) t := by
    simpa [id] using (((hasDerivAt_id t).mul_const (S.d 2)).sub_const (S.gz u)).mul_const (S.pz u)
  have hnum := (hn0.add hn1).add hn2
  have hlen := len_hasDerivAt_t S u t hlene
  have hlen_ne : S.len u t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlene)
  have hdiv := hnum.div hlen hlen_ne
  have hneg := hdiv.neg
  have hconst : HasDerivAt (fun _ : ℝ => -S.dr u) 0 t := hasDerivAt_const t _
  have hall := hneg.add hconst
  have htarget : HasDerivAt
      (fun s => -(((s * S.d 0 - S.gx u) * S.px u + (s * S.d 1 - S.gy u) * S.py u +
        (s * S.d 2 - S.gz u) * S.pz u) / S.len u s) - S.dr u)
      (-(S.d 0 * S.px u + S.d 1 * S.py u + S.d 2 * S.pz u) / S.len u t +
        (S.Rx u t * S.px u + S.Ry u t * S.py u + S.Rz u t * S.pz u) *
          (S.Rx u t * S.d 0 + S.Ry u t * S.d 1 + S.Rz u t * S.d 2) / S.len u t ^ 3) t := by
    convert hall using 1 <;>
      (first | (funext s; simp [Pi.add_apply]) | (simp [Rx, Ry, Rz]; field_simp [hlen_ne] <;> ring))
  exact (htarget.congr_of_eventuallyEq heq).deriv

theorem pdd21_bezG (S : BezSys) (u t : ℝ) (hlene : 0 < S.q u t) :
    pdd21 (bezG S) u t =
      -(S.d 0 * S.px u + S.d 1 * S.py u + S.d 2 * S.pz u) / S.len u t +
      (S.Rx u t * S.px u + S.Ry u t * S.py u + S.Rz u t * S.pz u) *
        (S.Rx u t * S.d 0 + S.Ry u t * S.d 1 + S.Rz u t * S.d 2) / S.len u t ^ 3 := by
  unfold pdd21
  have hcont : ContinuousAt (fun s => S.q s t) u := by
    unfold q Rx Ry Rz
    exact (((((S.hγx u).continuousAt.const_sub (t * S.d 0)).pow 2).add
      (((S.hγy u).continuousAt.const_sub (t * S.d 1)).pow 2)).add
      (((S.hγz u).continuousAt.const_sub (t * S.d 2)).pow 2))
  have hevq : ∀ᶠ s in 𝓝 u, 0 < S.q s t := hcont.eventually (isOpen_Ioi.mem_nhds hlene)
  have heq : (fun s => pd2 (bezG S) s t) =ᶠ[𝓝 u]
      (fun s => ((t * S.d 0 - S.gx s) * S.d 0 + (t * S.d 1 - S.gy s) * S.d 1 +
        (t * S.d 2 - S.gz s) * S.d 2) / S.len s t) := by
    filter_upwards [hevq] with s hs
    rw [pd2_bezG S s t hs]
    simp [Rx, Ry, Rz]
  -- numerator as a function of u: derivative = d·px + Rx·qx + ...
  have hn0 : HasDerivAt (fun s : ℝ => (t * S.d 0 - S.gx s) * S.d 0) (-(S.px u * S.d 0)) u := by
    simpa [id, mul_comm] using (((hasDerivAt_const u (t * S.d 0)).sub (S.hγx u)).mul_const (S.d 0))
  have hn1 : HasDerivAt (fun s : ℝ => (t * S.d 1 - S.gy s) * S.d 1) (-(S.py u * S.d 1)) u := by
    simpa [id, mul_comm] using (((hasDerivAt_const u (t * S.d 1)).sub (S.hγy u)).mul_const (S.d 1))
  have hn2 : HasDerivAt (fun s : ℝ => (t * S.d 2 - S.gz s) * S.d 2) (-(S.pz u * S.d 2)) u := by
    simpa [id, mul_comm] using (((hasDerivAt_const u (t * S.d 2)).sub (S.hγz u)).mul_const (S.d 2))
  have hnum := (hn0.add hn1).add hn2
  have hlen := len_hasDerivAt_u S u t hlene
  have hlen_ne : S.len u t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlene)
  have hdiv := hnum.div hlen hlen_ne
  have htarget : HasDerivAt
      (fun s => ((t * S.d 0 - S.gx s) * S.d 0 + (t * S.d 1 - S.gy s) * S.d 1 +
        (t * S.d 2 - S.gz s) * S.d 2) / S.len s t)
      (-(S.d 0 * S.px u + S.d 1 * S.py u + S.d 2 * S.pz u) / S.len u t +
        (S.Rx u t * S.px u + S.Ry u t * S.py u + S.Rz u t * S.pz u) *
          (S.Rx u t * S.d 0 + S.Ry u t * S.d 1 + S.Rz u t * S.d 2) / S.len u t ^ 3) u := by
    convert hdiv using 1 <;>
      (first | (funext s; simp [Pi.add_apply, Rx, Ry, Rz]; ring) | (simp [Rx, Ry, Rz]; field_simp [hlen_ne] <;> ring))
  exact (htarget.congr_of_eventuallyEq heq).deriv



theorem pdd11_bezG (S : BezSys) (u t : ℝ) (hlene : 0 < S.q u t) :
    pdd11 (bezG S) u t =
      ((S.px u ^ 2 + S.py u ^ 2 + S.pz u ^ 2) -
        (S.Rx u t * S.qx u + S.Ry u t * S.qy u + S.Rz u t * S.qz u)) / S.len u t -
      (S.Rx u t * S.px u + S.Ry u t * S.py u + S.Rz u t * S.pz u) ^ 2 / S.len u t ^ 3 -
      S.ddr u := by
  unfold pdd11
  have hcont : ContinuousAt (fun s => S.q s t) u := by
    unfold q Rx Ry Rz
    exact (((((S.hγx u).continuousAt.const_sub (t * S.d 0)).pow 2).add
      (((S.hγy u).continuousAt.const_sub (t * S.d 1)).pow 2)).add
      (((S.hγz u).continuousAt.const_sub (t * S.d 2)).pow 2))
  have hevq : ∀ᶠ s in 𝓝 u, 0 < S.q s t := hcont.eventually (isOpen_Ioi.mem_nhds hlene)
  have heq : (fun s => pd1 (bezG S) s t) =ᶠ[𝓝 u]
      (fun s => -(((t * S.d 0 - S.gx s) * S.px s + (t * S.d 1 - S.gy s) * S.py s +
        (t * S.d 2 - S.gz s) * S.pz s) / S.len s t) - S.dr s) := by
    filter_upwards [hevq] with s hs
    rw [pd1_bezG S s t hs]
    simp [Rx, Ry, Rz]
    ring
  have hp0 := ((hasDerivAt_const u (t * S.d 0)).sub (S.hγx u)).mul (S.hγx' u)
  have hp1 := ((hasDerivAt_const u (t * S.d 1)).sub (S.hγy u)).mul (S.hγy' u)
  have hp2 := ((hasDerivAt_const u (t * S.d 2)).sub (S.hγz u)).mul (S.hγz' u)
  have hnum := (hp0.add hp1).add hp2
  have hlen := len_hasDerivAt_u S u t hlene
  have hlen_ne : S.len u t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlene)
  have hdiv := hnum.div hlen hlen_ne
  have hall := hdiv.neg.sub (S.hρ' u)
  have htarget : HasDerivAt
      (fun s => -(((t * S.d 0 - S.gx s) * S.px s + (t * S.d 1 - S.gy s) * S.py s +
        (t * S.d 2 - S.gz s) * S.pz s) / S.len s t) - S.dr s)
      (((S.px u ^ 2 + S.py u ^ 2 + S.pz u ^ 2) -
        (S.Rx u t * S.qx u + S.Ry u t * S.qy u + S.Rz u t * S.qz u)) / S.len u t -
        (S.Rx u t * S.px u + S.Ry u t * S.py u + S.Rz u t * S.pz u) ^ 2 / S.len u t ^ 3 -
        S.ddr u) u := by
    convert hall using 1 <;>
      (first | (funext s; simp [Pi.add_apply]) |
        (simp [Rx, Ry, Rz]; field_simp [hlen_ne] <;> ring))
  exact (htarget.congr_of_eventuallyEq heq).deriv


end LightRT.Geom
