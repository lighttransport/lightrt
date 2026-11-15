/-
  The Bézier contact system `tri_bez_newton` solves, and the two-dimensional
  Newton step for it.

  The C solves for a point of a *round cubic Bézier curve* (cubic `C(u)` in
  `ℝ³` with radius `r(u)` in the fourth control-point lane) hit by ray
  `x = t·d` (ray in local space, i.e. origin at 0):

    `F(u, t) = ( ⟨R, C′(u)⟩ + r(u)·r′(u), |R| − r(u) ) = 0`,   `R = t·d − C(u)`.

  `F = 0` is the envelope condition `∂_u (|R|² − r²) = 0` jointly with the
  contact condition `|R| = r`; geometrically the contact is where the ray
  touches the surface of the union of balls `B(C(u), r(u))`.

  This file specializes `Geom.Newton2D` (the general quadratic contraction of
  a `C²` two-dimensional Newton step near a simple root) to this concrete
  system:

  - the Jacobian entries are explicit polynomial sums (plus the `1/|R|`
    entries of `∂g`), matching the C's `dFdu`, `dFdt`, `dGdu`, `dGdt`;
  - `jacDet` is literally the C's `det = dFdu·dGdt − dFdt·dGdu`;
  - `BezF` / `BezG` are given `C2Seg` structure on any closed rectangle where
    the radius row is modeled unclamped (`r`, `r′`, `r″` an ordinary cubic
    row; the C clamps at 0, in which case `F` is only piecewise smooth — the
    model stays honest by staying away from the kink);
  - the curve/radius derivatives are ordinary (unclamped) functions with
    `HasDerivAt` hypotheses — the concrete instance
    `BezSys.ofCubic` proves them for the cubic control-point polynomials, and
    `dBezP`/`ddBezP` are exactly `tri_bez_eval`'s `dP`/`ddP`;
  - second-derivative bounds `K` and Jacobian bounds `B` are hypotheses
    (hypotheses `E ≤ B / K`, `δ ≤ |det|` mirror the C's own `det` guard and
    the ball the iterates live in — same standing as `newton2_step_quadratic`).

  Acceptance conditions of the C that are NOT modeled: the `dF/du < 0`
  "front-facing contact is a minimum" selection, the eps-convergence test, the
  unit-`u` clamp `[-0.05, 1.05]`, and the radius clamp `max P[3] 0`. The
  contraction corollary holds at interior points where the unclamped system is
  `C²`; it says nothing about the accepted outputs' classification.

  Not claimed: explicit `K`/`B` from the control points (a coefficient bound
  chase), and any floating-point analysis of the step itself.
-/
import Mathlib
import LightRT.Geom.Newton2D

namespace LightRT.Geom

open Real

/-- The abstract round Bézier contact system: a cubic-like curve `γ = (gx, gy, gz)`
    with its first two derivatives, an unclamped radius row `rad` with its first two
    derivatives, and a direction `d`. Each `HasDerivAt` hypothesis is what the
    concrete `BezSys.ofCubic` instance proves for the Bézier control-point polynomials. -/
structure BezSys where
  gx : ℝ → ℝ
  gy : ℝ → ℝ
  gz : ℝ → ℝ
  px : ℝ → ℝ
  py : ℝ → ℝ
  pz : ℝ → ℝ
  qx : ℝ → ℝ
  qy : ℝ → ℝ
  qz : ℝ → ℝ
  rad : ℝ → ℝ
  dr : ℝ → ℝ
  ddr : ℝ → ℝ
  d : Fin 3 → ℝ
  hγx : ∀ u, HasDerivAt gx (px u) u
  hγy : ∀ u, HasDerivAt gy (py u) u
  hγz : ∀ u, HasDerivAt gz (pz u) u
  hγx' : ∀ u, HasDerivAt px (qx u) u
  hγy' : ∀ u, HasDerivAt py (qy u) u
  hγz' : ∀ u, HasDerivAt pz (qz u) u
  hdγx : ∀ u, DifferentiableAt ℝ qx u
  hdγy : ∀ u, DifferentiableAt ℝ qy u
  hdγz : ∀ u, DifferentiableAt ℝ qz u
  hρ : ∀ u, HasDerivAt rad (dr u) u
  hρ' : ∀ u, HasDerivAt dr (ddr u) u
  hdρ : ∀ u, DifferentiableAt ℝ ddr u

namespace BezSys

variable (S : BezSys)

/-- `R = t·d − C(u)`, the ray offset from the curve in local space. -/
def Rx (u t : ℝ) : ℝ := t * S.d 0 - S.gx u
def Ry (u t : ℝ) : ℝ := t * S.d 1 - S.gy u
def Rz (u t : ℝ) : ℝ := t * S.d 2 - S.gz u

/-- `q = |R|²`, the polynomial inside the norm. -/
def q (u t : ℝ) : ℝ := Rx S u t ^ 2 + Ry S u t ^ 2 + Rz S u t ^ 2
/-- `len = |R|` (as `real.sqrt`). -/
noncomputable def len (u t : ℝ) : ℝ := Real.sqrt (q S u t)

/-- The contact system `F = (⟨R, C′⟩ + r r′, |R| − r)`. -/
def bezF (u t : ℝ) : ℝ :=
  Rx S u t * S.px u + Ry S u t * S.py u + Rz S u t * S.pz u + S.rad u * S.dr u

/-- The second component of the system, `G = |R| − r`. -/
noncomputable def bezG (u t : ℝ) : ℝ :=
  len S u t - S.rad u

section Derivatives

variable (u t : ℝ)

theorem hRx : HasDerivAt (fun s => t * S.d 0 - S.gx s) (-S.px u) u :=
  (S.hγx u).const_sub _

theorem hRy : HasDerivAt (fun s => t * S.d 1 - S.gy s) (-S.py u) u :=
  (S.hγy u).const_sub _

theorem hRz : HasDerivAt (fun s => t * S.d 2 - S.gz s) (-S.pz u) u :=
  (S.hγz u).const_sub _

theorem hRxt : HasDerivAt (fun s => s * S.d 0 - S.gx u) (S.d 0) t := by
  have h := (hasDerivAt_id t).mul_const (S.d 0)
  have h' := h.sub_const (S.gx u)
  simpa using h'

theorem hRyt : HasDerivAt (fun s => s * S.d 1 - S.gy u) (S.d 1) t := by
  have h := (hasDerivAt_id t).mul_const (S.d 1)
  have h' := h.sub_const (S.gy u)
  simpa using h'

theorem hRzt : HasDerivAt (fun s => s * S.d 2 - S.gz u) (S.d 2) t := by
  have h := (hasDerivAt_id t).mul_const (S.d 2)
  have h' := h.sub_const (S.gz u)
  simpa using h'

theorem hdq_u : HasDerivAt (fun s => q S s t)
    (2 * Rx S u t * -S.px u + 2 * Ry S u t * -S.py u + 2 * Rz S u t * -S.pz u) u := by
  have h1 := (hRx S u t).pow 2
  have h2 := (hRy S u t).pow 2
  have h3 := (hRz S u t).pow 2
  have h := ((h1.add h2).add h3)
  have he : ∀ s, q S s t = (t * S.d 0 - S.gx s) ^ 2 + (t * S.d 1 - S.gy s) ^ 2 + (t * S.d 2 - S.gz s) ^ 2 := by
    intro s; rfl
  rw [funext he]
  exact h.congr_deriv (by unfold Rx Ry Rz; simp)

theorem hdq_t : HasDerivAt (fun s => q S u s)
    (2 * Rx S u t * S.d 0 + 2 * Ry S u t * S.d 1 + 2 * Rz S u t * S.d 2) t := by
  have h1 := (hRxt S u t).pow 2
  have h2 := (hRyt S u t).pow 2
  have h3 := (hRzt S u t).pow 2
  have h := ((h1.add h2).add h3)
  have he : ∀ s, q S u s = (s * S.d 0 - S.gx u) ^ 2 + (s * S.d 1 - S.gy u) ^ 2 + (s * S.d 2 - S.gz u) ^ 2 := by
    intro s; rfl
  rw [funext he]
  exact h.congr_deriv (by unfold Rx Ry Rz; simp)

/-- `∂F/∂u` — the C's `dFdu`. -/
theorem pd1_bezF : pd1 (bezF S) u t =
    -(S.px u ^ 2 + S.py u ^ 2 + S.pz u ^ 2) +
      (Rx S u t * S.qx u + Ry S u t * S.qy u + Rz S u t * S.qz u) +
      S.dr u ^ 2 + S.rad u * S.ddr u := by
  have t0 := (hRx S u t).mul (S.hγx' u)
  have t1 := (hRy S u t).mul (S.hγy' u)
  have t2 := (hRz S u t).mul (S.hγz' u)
  have t3 := (S.hρ u).mul (S.hρ' u)
  have h := ((t0.add t1).add t2).add t3
  have hval : deriv (fun s => bezF S s t) u = _ := h.deriv
  unfold pd1
  exact hval.trans (by simp only [Rx, Ry, Rz]; ring)

/-- `∂F/∂t` — the C's `dFdt`. -/
theorem pd2_bezF : pd2 (bezF S) u t =
    S.d 0 * S.px u + S.d 1 * S.py u + S.d 2 * S.pz u := by
  have t0 := (hRxt S u t).mul_const (S.px u)
  have t1 := (hRyt S u t).mul_const (S.py u)
  have t2 := (hRzt S u t).mul_const (S.pz u)
  have t3 : HasDerivAt (fun _ : ℝ => S.rad u * S.dr u) 0 t := hasDerivAt_const t _
  have h := ((t0.add t1).add t2).add t3
  have hval : deriv (fun s => bezF S u s) t = _ := h.deriv
  unfold pd2
  exact hval.trans (by ring)

/-- `∂G/∂u` — the C's `dGdu`. Requires a nonzero `|R|`, mirroring the C's
    `lenR > 1e-30` guard. -/
theorem pd1_bezG (hlene : 0 < q S u t) : pd1 (bezG S) u t =
    -(Rx S u t * S.px u + Ry S u t * S.py u + Rz S u t * S.pz u) / len S u t - S.dr u := by
  have hq := hdq_u S u t
  have hlen := hq.sqrt hlene.ne'
  have hg := hlen.sub (S.hρ u)
  have heq : deriv ((fun y => √(S.q y t)) - S.rad) u =
      (2 * Rx S u t * -S.px u + 2 * Ry S u t * -S.py u + 2 * Rz S u t * -S.pz u) /
        (2 * Real.sqrt (q S u t)) - S.dr u := hg.deriv
  unfold pd1
  rw [show (fun s => bezG S s t) = (fun y => √(S.q y t)) - S.rad from rfl, heq]
  unfold len
  field_simp [Real.sqrt_ne_zero'.mpr hlene]
  ring

/-- `∂G/∂t` — the C's `dGdt`. -/
theorem pd2_bezG (hlene : 0 < q S u t) : pd2 (bezG S) u t =
    (Rx S u t * S.d 0 + Ry S u t * S.d 1 + Rz S u t * S.d 2) / len S u t := by
  have hq := hdq_t S u t
  have hlen := hq.sqrt hlene.ne'
  have ht3 : HasDerivAt (fun _ : ℝ => S.rad u) 0 t := hasDerivAt_const t _
  have hg := hlen.sub ht3
  have heq : deriv ((fun y => √(S.q u y)) - fun x => S.rad u) t =
      (2 * Rx S u t * S.d 0 + 2 * Ry S u t * S.d 1 + 2 * Rz S u t * S.d 2) /
        (2 * Real.sqrt (q S u t)) - 0 := hg.deriv
  unfold pd2
  rw [show (fun s => bezG S u s) = (fun y => √(S.q u y)) - fun x => S.rad u from rfl, heq]
  unfold len
  field_simp [Real.sqrt_ne_zero'.mpr hlene]
  ring

/-- The C's acceptance guard, literally: `det = dFdu·dGdt − dFdt·dGdu`. -/
theorem jacDet_bez (hlene : 0 < q S u t) : jacDet (bezF S) (bezG S) u t =
    (-(S.px u ^ 2 + S.py u ^ 2 + S.pz u ^ 2) +
        (Rx S u t * S.qx u + Ry S u t * S.qy u + Rz S u t * S.qz u) +
        S.dr u ^ 2 + S.rad u * S.ddr u) *
        ((Rx S u t * S.d 0 + Ry S u t * S.d 1 + Rz S u t * S.d 2) / len S u t) -
      (S.d 0 * S.px u + S.d 1 * S.py u + S.d 2 * S.pz u) *
        (-(Rx S u t * S.px u + Ry S u t * S.py u + Rz S u t * S.pz u) / len S u t -
          S.dr u) := by
  unfold jacDet
  rw [pd1_bezF S u t, pd2_bezF S u t, pd1_bezG S u t hlene, pd2_bezG S u t hlene]

end Derivatives

end BezSys

end LightRT.Geom

namespace LightRT.Geom

namespace BezSys

variable (S : BezSys)

section Diff
variable {a b c d : ℝ}

private theorem diff_gx : Differentiable ℝ S.gx := fun u => (S.hγx u).differentiableAt
private theorem diff_gy : Differentiable ℝ S.gy := fun u => (S.hγy u).differentiableAt
private theorem diff_gz : Differentiable ℝ S.gz := fun u => (S.hγz u).differentiableAt
private theorem diff_px : Differentiable ℝ S.px := fun u => (S.hγx' u).differentiableAt
private theorem diff_py : Differentiable ℝ S.py := fun u => (S.hγy' u).differentiableAt
private theorem diff_pz : Differentiable ℝ S.pz := fun u => (S.hγz' u).differentiableAt
private theorem diff_qx : Differentiable ℝ S.qx := S.hdγx
private theorem diff_qy : Differentiable ℝ S.qy := S.hdγy
private theorem diff_qz : Differentiable ℝ S.qz := S.hdγz
private theorem diff_rad : Differentiable ℝ S.rad := fun u => (S.hρ u).differentiableAt
private theorem diff_dr : Differentiable ℝ S.dr := fun u => (S.hρ' u).differentiableAt
private theorem diff_ddr : Differentiable ℝ S.ddr := S.hdρ

private theorem fun_Rxu (t : ℝ) : (fun s => S.Rx s t) = fun s => t * S.d 0 - S.gx s := rfl
private theorem fun_Ryu (t : ℝ) : (fun s => S.Ry s t) = fun s => t * S.d 1 - S.gy s := rfl
private theorem fun_Rzu (t : ℝ) : (fun s => S.Rz s t) = fun s => t * S.d 2 - S.gz s := rfl
private theorem fun_Rxt (u : ℝ) : (fun s => S.Rx u s) = fun s => s * S.d 0 - S.gx u := rfl
private theorem fun_Ryt (u : ℝ) : (fun s => S.Ry u s) = fun s => s * S.d 1 - S.gy u := rfl
private theorem fun_Rzt (u : ℝ) : (fun s => S.Rz u s) = fun s => s * S.d 2 - S.gz u := rfl

private theorem diff_Rxu (t : ℝ) : Differentiable ℝ fun s => S.Rx s t := by
  rw [fun_Rxu]; exact (differentiable_const _).sub (diff_gx S)
private theorem diff_Ryu (t : ℝ) : Differentiable ℝ fun s => S.Ry s t := by
  rw [fun_Ryu]; exact (differentiable_const _).sub (diff_gy S)
private theorem diff_Rzu (t : ℝ) : Differentiable ℝ fun s => S.Rz s t := by
  rw [fun_Rzu]; exact (differentiable_const _).sub (diff_gz S)
private theorem diff_Rxt (u : ℝ) : Differentiable ℝ fun s => S.Rx u s := by
  rw [fun_Rxt]; exact differentiable_id.mul_const _ |>.sub_const _
private theorem diff_Ryt (u : ℝ) : Differentiable ℝ fun s => S.Ry u s := by
  rw [fun_Ryt]; exact differentiable_id.mul_const _ |>.sub_const _
private theorem diff_Rzt (u : ℝ) : Differentiable ℝ fun s => S.Rz u s := by
  rw [fun_Rzt]; exact differentiable_id.mul_const _ |>.sub_const _
private theorem diff_q_u (t : ℝ) : Differentiable ℝ fun s => S.q s t := by
  unfold q
  exact ((diff_Rxu S t).pow 2 |>.add ((diff_Ryu S t).pow 2)).add ((diff_Rzu S t).pow 2)
private theorem diff_q_t (u : ℝ) : Differentiable ℝ fun s => S.q u s := by
  unfold q
  exact ((diff_Rxt S u).pow 2 |>.add ((diff_Ryt S u).pow 2)).add ((diff_Rzt S u).pow 2)
end Diff

/-- The hypothesis bundle for the closed rectangle the C iterates on. Two
    things must hold there, both mirrored by the C's own guards:
    `0 < |R|²` (the C's `lenR > 1e-30`) everywhere in the rectangle, and the
    eight second partials of `F` and `G` bounded by `K`. -/
structure PddBounds (S : BezSys) (a b c d K : ℝ) : Prop where
  f11 : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd11 (bezF S) u t| ≤ K
  f12 : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd12 (bezF S) u t| ≤ K
  f21 : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd21 (bezF S) u t| ≤ K
  f22 : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd22 (bezF S) u t| ≤ K
  g11 : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd11 (bezG S) u t| ≤ K
  g12 : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd12 (bezG S) u t| ≤ K
  g21 : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd21 (bezG S) u t| ≤ K
  g22 : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, |pdd22 (bezG S) u t| ≤ K

section C2Seg

variable {a b c d K : ℝ}

private theorem hdiffAt_sqrt_u (t : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < S.q u t)
    (ht : t ∈ Set.Icc c d) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    DifferentiableAt ℝ (fun y => √(S.q y t)) x :=
  ((diff_q_u S t) x).sqrt (hlene x hx t ht).ne'

private theorem hdiffAt_sqrt_t (u : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < S.q u t)
    (hu : u ∈ Set.Icc a b) {y : ℝ} (hs : y ∈ Set.Icc c d) :
    DifferentiableAt ℝ (fun y => √(S.q u y)) y :=
  ((diff_q_t S u) y).sqrt (hlene u hu y hs).ne'

private theorem hdiffAt_len_u (t : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < S.q u t)
    (ht : t ∈ Set.Icc c d) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    DifferentiableAt ℝ (fun y => S.len y t) x := by
  have e : (fun y => S.len y t) = fun y => √(S.q y t) := rfl
  rw [e]
  exact hdiffAt_sqrt_u S t hlene ht hx

private theorem hdiffAt_len_t (u : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < S.q u t)
    (hu : u ∈ Set.Icc a b) {y : ℝ} (hs : y ∈ Set.Icc c d) :
    DifferentiableAt ℝ (fun y => S.len u y) y := by
  have e : (fun y => S.len u y) = fun y => √(S.q u y) := rfl
  rw [e]
  exact hdiffAt_sqrt_t S u hlene hu hs

private theorem hlen_ne_u (t : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < S.q u t)
    (ht : t ∈ Set.Icc c d) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    S.len x t ≠ 0 := by
  unfold len
  exact Real.sqrt_ne_zero'.mpr (hlene x hx t ht)

private theorem hlen_ne_t (u : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < S.q u t)
    (hu : u ∈ Set.Icc a b) {y : ℝ} (hs : y ∈ Set.Icc c d) :
    S.len u y ≠ 0 := by
  unfold len
  exact Real.sqrt_ne_zero'.mpr (hlene u hu y hs)

/-- `F` is `C²` on the rectangle; the second-derivative bounds are the `f`-fields
    of `PddBounds`, everything else is proved. -/
theorem bezF_C2Seg (S : BezSys) (a b c d K : ℝ) (hb : PddBounds S a b c d K) :
    C2Seg (bezF S) a b c d K := by
  have hRx := diff_Rxu S; have hRy := diff_Ryu S; have hRz := diff_Rzu S
  have hRxt := diff_Rxt S; have hRyt := diff_Ryt S; have hRzt := diff_Rzt S
  have hpx := diff_px S; have hpy := diff_py S; have hpz := diff_pz S
  have hqx := diff_qx S; have hqy := diff_qy S; have hqz := diff_qz S
  have hdx := diff_dr S; have hdxr := diff_ddr S
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hb.f11, hb.f12, hb.f21, hb.f22⟩
  · intro t ht s hs
    have hA : DifferentiableAt ℝ (fun y => S.Rx y t * S.px y) s := ((hRx t) s).mul (hpx s)
    have hB : DifferentiableAt ℝ (fun y => S.Ry y t * S.py y) s := ((hRy t) s).mul (hpy s)
    have hC : DifferentiableAt ℝ (fun y => S.Rz y t * S.pz y) s := ((hRz t) s).mul (hpz s)
    have hD : DifferentiableAt ℝ (fun y => S.rad y * S.dr y) s := (diff_rad S s).mul (diff_dr S s)
    exact (((hA.add hB).add hC).add hD).differentiableWithinAt
  · intro u hu s hs
    have hA : DifferentiableAt ℝ (fun y => S.Rx u y * S.px u) s :=
      ((hRxt u) s).mul_const (S.px u)
    have hB : DifferentiableAt ℝ (fun y => S.Ry u y * S.py u) s :=
      ((hRyt u) s).mul_const (S.py u)
    have hC : DifferentiableAt ℝ (fun y => S.Rz u y * S.pz u) s :=
      ((hRzt u) s).mul_const (S.pz u)
    have hD : DifferentiableAt ℝ (fun y => S.rad u * S.dr u) s := differentiableAt_const _
    exact (((hA.add hB).add hC).add hD).differentiableWithinAt
  · intro t ht
    apply DifferentiableOn.congr (f := fun s =>
      -(S.px s ^ 2 + S.py s ^ 2 + S.pz s ^ 2) +
        (S.Rx s t * S.qx s + S.Ry s t * S.qy s + S.Rz s t * S.qz s) +
        S.dr s ^ 2 + S.rad s * S.ddr s) ?_ (fun x hx => pd1_bezF S x t)
    intro s hs
    have h1 : DifferentiableAt ℝ (fun y => -(S.px y ^ 2 + S.py y ^ 2 + S.pz y ^ 2)) s :=
      (((((hpx s).pow 2).add ((hpy s).pow 2)).add ((hpz s).pow 2)).neg)
    have h2 : DifferentiableAt ℝ
        (fun y => S.Rx y t * S.qx y + S.Ry y t * S.qy y + S.Rz y t * S.qz y) s :=
      ((((hRx t) s).mul (hqx s)).add (((hRy t) s).mul (hqy s))) |>.add (((hRz t) s).mul (hqz s))
    have h3 : DifferentiableAt ℝ (fun y => S.dr y ^ 2) s := (hdx s).pow 2
    have h4 : DifferentiableAt ℝ (fun y => S.rad y * S.ddr y) s := (diff_rad S s).mul (hdxr s)
    exact (((h1.add h2).add h3).add h4).differentiableWithinAt
  · intro u hu
    apply DifferentiableOn.congr (f := fun s =>
      -(S.px u ^ 2 + S.py u ^ 2 + S.pz u ^ 2) +
        (S.Rx u s * S.qx u + S.Ry u s * S.qy u + S.Rz u s * S.qz u) +
        S.dr u ^ 2 + S.rad u * S.ddr u) ?_ (fun x hx => pd1_bezF S u x)
    intro s hs
    have h1 : DifferentiableAt ℝ (fun y => -(S.px u ^ 2 + S.py u ^ 2 + S.pz u ^ 2)) s :=
      differentiableAt_const _
    have h2 : DifferentiableAt ℝ
        (fun y => S.Rx u y * S.qx u + S.Ry u y * S.qy u + S.Rz u y * S.qz u) s :=
      ((((hRxt u) s).mul_const (S.qx u)).add (((hRyt u) s).mul_const (S.qy u))) |>.add
        (((hRzt u) s).mul_const (S.qz u))
    have h3 : DifferentiableAt ℝ (fun y => S.dr u ^ 2) s := differentiableAt_const _
    have h4 : DifferentiableAt ℝ (fun y => S.rad u * S.ddr u) s := differentiableAt_const _
    exact (((h1.add h2).add h3).add h4).differentiableWithinAt
  · intro t ht
    apply DifferentiableOn.congr (f := fun s =>
      S.d 0 * S.px s + S.d 1 * S.py s + S.d 2 * S.pz s) ?_ (fun x hx => pd2_bezF S x t)
    intro s hs
    have hA : DifferentiableAt ℝ (fun y => S.d 0 * S.px y) s := differentiableAt_const _ |>.mul (hpx s)
    have hB : DifferentiableAt ℝ (fun y => S.d 1 * S.py y) s := differentiableAt_const _ |>.mul (hpy s)
    have hC : DifferentiableAt ℝ (fun y => S.d 2 * S.pz y) s := differentiableAt_const _ |>.mul (hpz s)
    exact ((hA.add hB).add hC).differentiableWithinAt
  · intro u hu
    apply DifferentiableOn.congr (f := fun _ : ℝ =>
      S.d 0 * S.px u + S.d 1 * S.py u + S.d 2 * S.pz u) ?_ (fun x hx => pd2_bezF S u x)
    intro s hs
    exact (differentiableAt_const _ : DifferentiableAt ℝ
      (fun _ : ℝ => S.d 0 * S.px u + S.d 1 * S.py u + S.d 2 * S.pz u) s).differentiableWithinAt

/-- `G` is `C²` on the rectangle where `|R|² > 0`; the `g`-fields of `PddBounds`
    close it. -/
theorem bezG_C2Seg (S : BezSys) (a b c d K : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < S.q u t) (hb : PddBounds S a b c d K) :
    C2Seg (bezG S) a b c d K := by
  have hRx := diff_Rxu S; have hRy := diff_Ryu S; have hRz := diff_Rzu S
  have hRxt := diff_Rxt S; have hRyt := diff_Ryt S; have hRzt := diff_Rzt S
  have hpx := diff_px S; have hpy := diff_py S; have hpz := diff_pz S
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hb.g11, hb.g12, hb.g21, hb.g22⟩
  · intro t ht s hs
    have hl := hdiffAt_len_u S t hlene ht (x := s) hs
    exact (hl.sub (S.hρ s).differentiableAt).differentiableWithinAt
  · intro u hu s hs
    have hl := hdiffAt_len_t S u hlene hu (y := s) hs
    exact (hl.sub (hasDerivAt_const s (S.rad u)).differentiableAt).differentiableWithinAt
  · intro t ht
    apply DifferentiableOn.congr (f := fun s =>
      -(S.Rx s t * S.px s + S.Ry s t * S.py s + S.Rz s t * S.pz s) / S.len s t - S.dr s)
      ?_ (fun x hx => pd1_bezG S x t (hlene x hx t ht))
    intro s hs
    have hl := hdiffAt_len_u S t hlene ht (x := s) hs
    have hl0 : S.len s t ≠ 0 := hlen_ne_u S t hlene ht (x := s) hs
    have hnum : DifferentiableAt ℝ
        (fun y => S.Rx y t * S.px y + S.Ry y t * S.py y + S.Rz y t * S.pz y) s :=
      (((((hRx t) s).mul ((hpx) s)).add (((hRy t) s).mul ((hpy) s))).add (((hRz t) s).mul ((hpz) s)))
    have hdiv : DifferentiableAt ℝ
        (fun y => (-(S.Rx y t * S.px y + S.Ry y t * S.py y + S.Rz y t * S.pz y)) / S.len y t) s :=
      hnum.neg.div hl hl0
    exact (hdiv.sub (S.hρ' s).differentiableAt).differentiableWithinAt
  · intro u hu
    apply DifferentiableOn.congr (f := fun s =>
      -(S.Rx u s * S.px u + S.Ry u s * S.py u + S.Rz u s * S.pz u) / S.len u s - S.dr u)
      ?_ (fun x hx => pd1_bezG S u x (hlene u hu x hx))
    intro s hs
    have hl := hdiffAt_len_t S u hlene hu (y := s) hs
    have hl0 : S.len u s ≠ 0 := hlen_ne_t S u hlene hu (y := s) hs
    have hnum : DifferentiableAt ℝ
        (fun y => S.Rx u y * S.px u + S.Ry u y * S.py u + S.Rz u y * S.pz u) s :=
      (((((hRxt u) s).mul_const _).add (((hRyt u) s).mul_const _)).add (((hRzt u) s).mul_const _))
    have hdiv : DifferentiableAt ℝ
        (fun y => (-(S.Rx u y * S.px u + S.Ry u y * S.py u + S.Rz u y * S.pz u)) / S.len u y) s :=
      hnum.neg.div hl hl0
    exact (hdiv.sub (hasDerivAt_const s (S.dr u)).differentiableAt).differentiableWithinAt
  · intro t ht
    apply DifferentiableOn.congr (f := fun s =>
      (S.Rx s t * S.d 0 + S.Ry s t * S.d 1 + S.Rz s t * S.d 2) / S.len s t)
      ?_ (fun x hx => pd2_bezG S x t (hlene x hx t ht))
    intro s hs
    have hl := hdiffAt_len_u S t hlene ht (x := s) hs
    have hl0 : S.len s t ≠ 0 := hlen_ne_u S t hlene ht (x := s) hs
    have hnum : DifferentiableAt ℝ
        (fun y => S.Rx y t * S.d 0 + S.Ry y t * S.d 1 + S.Rz y t * S.d 2) s :=
      (((((hRx t) s).mul_const _).add (((hRy t) s).mul_const _)).add (((hRz t) s).mul_const _))
    exact (hnum.div hl hl0).differentiableWithinAt
  · intro u hu
    apply DifferentiableOn.congr (f := fun s =>
      (S.Rx u s * S.d 0 + S.Ry u s * S.d 1 + S.Rz u s * S.d 2) / S.len u s)
      ?_ (fun x hx => pd2_bezG S u x (hlene u hu x hx))
    intro s hs
    have hl := hdiffAt_len_t S u hlene hu (y := s) hs
    have hl0 : S.len u s ≠ 0 := hlen_ne_t S u hlene hu (y := s) hs
    have hnum : DifferentiableAt ℝ
        (fun y => S.Rx u y * S.d 0 + S.Ry u y * S.d 1 + S.Rz u y * S.d 2) s :=
      (((((hRxt u) s).mul_const _).add (((hRyt u) s).mul_const _)).add (((hRzt u) s).mul_const _))
    exact (hnum.div hl hl0).differentiableWithinAt

end C2Seg

/-- **The final contraction corollary**: under the same side conditions as
    `newton2_step_quadratic` (rectangle containment, `E ≤ B/K`, `δ ≤ |det|`
    with `0 < δ`), one Newton step on the Bézier contact system squares the
    error. This is the theorem the C's acceptance logic operates under; the
    radius clamp and the `dF/du < 0` selection are intentionally not modeled. -/
theorem bez_newton_quadratic (S : BezSys) (a b c d K B δ : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, 0 < S.q u t)
    (hb : PddBounds S a b c d K) (hK : 0 < K) (hB : 0 ≤ B)
    {u₀ t₀ u t : ℝ}
    (hu : u ∈ Set.Icc a b) (hu₀ : u₀ ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc c d) (ht₀ : t₀ ∈ Set.Icc c d)
    (hroot : BezSys.bezF S u₀ t₀ = 0 ∧ BezSys.bezG S u₀ t₀ = 0)
    (hUb : |pd1 (bezF S) u t| ≤ B) (hVb : |pd2 (bezF S) u t| ≤ B)
    (hWb : |pd1 (bezG S) u t| ≤ B) (hZb : |pd2 (bezG S) u t| ≤ B)
    (hAb : |pd1 (bezF S) u₀ t₀| ≤ B) (hBb : |pd2 (bezF S) u₀ t₀| ≤ B)
    (hCb : |pd1 (bezG S) u₀ t₀| ≤ B) (hDb : |pd2 (bezG S) u₀ t₀| ≤ B)
    (hden : δ ≤ |jacDet (bezF S) (bezG S) u t|) (hδ : 0 < δ)
    (hE : |u - u₀| + |t - t₀| ≤ B / K) :
    |(newton2Step (bezF S) (bezG S) u t).1 - u₀| ≤
        (10 * B * K / δ) * (|u - u₀| + |t - t₀|) ^ 2 ∧
    |(newton2Step (bezF S) (bezG S) u t).2 - t₀| ≤
        (8 * B * K * (|u - u₀| + |t - t₀|) ^ 2 + 2 * B ^ 2 *
          (|u - u₀| + |t - t₀|)) / δ :=
  newton2_step_quadratic (bezF_C2Seg S a b c d K hb) (bezG_C2Seg S a b c d K hlene hb)
    hK hB hu hu₀ ht ht₀ hroot hUb hVb hWb hZb hAb hBb hCb hDb hden hδ hE

end BezSys

end LightRT.Geom

namespace LightRT.Geom

open Polynomial

/-- The Bézier component polynomial, in the unexpanded control-point form used
    by `tri_bez_eval`. -/
def bezP (b0 b1 b2 b3 u : ℝ) : ℝ :=
  (1 - u) ^ 3 * b0 + 3 * (1 - u) ^ 2 * u * b1 + 3 * (1 - u) * u ^ 2 * b2 + u ^ 3 * b3

/-- The C's `dP` (`tri_bez_eval`'s first derivative; the edge differences). -/
def dBezP (b0 b1 b2 b3 u : ℝ) : ℝ :=
  3 * ((1 - u) ^ 2 * (b1 - b0) + 2 * (1 - u) * u * (b2 - b1) + u ^ 2 * (b3 - b2))

/-- The C's `ddP` (the second derivative). -/
def ddBezP (b0 b1 b2 b3 u : ℝ) : ℝ :=
  6 * ((1 - u) * (b2 - 2 * b1 + b0) + u * (b3 - 2 * b2 + b1))

/-- The same cubic as a `Polynomial`, expanded about `0`. -/
noncomputable def bezPoly (b0 b1 b2 b3 : ℝ) : ℝ[X] :=
  monomial 0 b0 + monomial 1 (3 * (b1 - b0)) + monomial 2 (3 * (b2 - 2 * b1 + b0)) +
    monomial 3 (b3 - 3 * b2 + 3 * b1 - b0)

theorem bezP_eq_eval (b0 b1 b2 b3 u : ℝ) :
    bezP b0 b1 b2 b3 u = (bezPoly b0 b1 b2 b3).eval u := by
  simp [bezP, bezPoly]; ring

theorem dBezP_eq_eval (b0 b1 b2 b3 u : ℝ) :
    dBezP b0 b1 b2 b3 u = (Polynomial.derivative (bezPoly b0 b1 b2 b3)).eval u := by
  simp [dBezP, bezPoly, Polynomial.derivative_add]; ring

theorem ddBezP_eq_eval (b0 b1 b2 b3 u : ℝ) :
    ddBezP b0 b1 b2 b3 u =
      (Polynomial.derivative (Polynomial.derivative (bezPoly b0 b1 b2 b3))).eval u := by
  simp [ddBezP, bezPoly, Polynomial.derivative_add]; ring

theorem hasDerivAt_bezP (b0 b1 b2 b3 u : ℝ) :
    HasDerivAt (bezP b0 b1 b2 b3) (dBezP b0 b1 b2 b3 u) u := by
  have e : bezP b0 b1 b2 b3 = fun x => (bezPoly b0 b1 b2 b3).eval x :=
    funext fun x => bezP_eq_eval b0 b1 b2 b3 x
  rw [e, dBezP_eq_eval]
  exact (bezPoly b0 b1 b2 b3).hasDerivAt u

theorem hasDerivAt_dBezP (b0 b1 b2 b3 u : ℝ) :
    HasDerivAt (dBezP b0 b1 b2 b3) (ddBezP b0 b1 b2 b3 u) u := by
  have e : dBezP b0 b1 b2 b3 = fun x => (Polynomial.derivative (bezPoly b0 b1 b2 b3)).eval x :=
    funext fun x => dBezP_eq_eval b0 b1 b2 b3 x
  rw [e, ddBezP_eq_eval]
  exact (Polynomial.derivative (bezPoly b0 b1 b2 b3)).hasDerivAt u

theorem differentiable_ddBezP (b0 b1 b2 b3 u : ℝ) :
    DifferentiableAt ℝ (ddBezP b0 b1 b2 b3) u := by
  have e : ddBezP b0 b1 b2 b3 =
      fun x => (Polynomial.derivative (Polynomial.derivative (bezPoly b0 b1 b2 b3))).eval x :=
    funext fun x => ddBezP_eq_eval b0 b1 b2 b3 x
  rw [e]
  exact (Polynomial.derivative (Polynomial.derivative (bezPoly b0 b1 b2 b3))).hasDerivAt u
    |>.differentiableAt

namespace BezSys

/-- The `BezSys` of the actual cubic contact system from `tri_bez_newton`: `c k i`
    is control point `k` (`0..3`), component `i` (`0..2` = xyz, `3` = the radius
    lane of the 16-control-point array); `d i` is the ray direction.

    The radius row is left unclamped (`max r 0` in the C is piecewise smooth,
    not `C²` at the kink); on components where it matters, work with
    `0 < rad u`. The clamp of `r`, `dr`, `ddr` to zero below is the C's
    behavior for control-radius lanes that go negative; the model covers the
    interior there. -/
noncomputable def ofCubic (c : Fin 4 → Fin 4 → ℝ) (d : Fin 3 → ℝ) : BezSys where
  gx := bezP (c 0 0) (c 1 0) (c 2 0) (c 3 0)
  gy := bezP (c 0 1) (c 1 1) (c 2 1) (c 3 1)
  gz := bezP (c 0 2) (c 1 2) (c 2 2) (c 3 2)
  px := dBezP (c 0 0) (c 1 0) (c 2 0) (c 3 0)
  py := dBezP (c 0 1) (c 1 1) (c 2 1) (c 3 1)
  pz := dBezP (c 0 2) (c 1 2) (c 2 2) (c 3 2)
  qx := ddBezP (c 0 0) (c 1 0) (c 2 0) (c 3 0)
  qy := ddBezP (c 0 1) (c 1 1) (c 2 1) (c 3 1)
  qz := ddBezP (c 0 2) (c 1 2) (c 2 2) (c 3 2)
  rad := bezP (c 0 3) (c 1 3) (c 2 3) (c 3 3)
  dr := dBezP (c 0 3) (c 1 3) (c 2 3) (c 3 3)
  ddr := ddBezP (c 0 3) (c 1 3) (c 2 3) (c 3 3)
  d := d
  hγx u := hasDerivAt_bezP _ _ _ _ u
  hγy u := hasDerivAt_bezP _ _ _ _ u
  hγz u := hasDerivAt_bezP _ _ _ _ u
  hγx' u := hasDerivAt_dBezP _ _ _ _ u
  hγy' u := hasDerivAt_dBezP _ _ _ _ u
  hγz' u := hasDerivAt_dBezP _ _ _ _ u
  hdγx u := differentiable_ddBezP _ _ _ _ u
  hdγy u := differentiable_ddBezP _ _ _ _ u
  hdγz u := differentiable_ddBezP _ _ _ _ u
  hρ u := hasDerivAt_bezP _ _ _ _ u
  hρ' u := hasDerivAt_dBezP _ _ _ _ u
  hdρ u := differentiable_ddBezP _ _ _ _ u

/-- A monic specialization of the contraction for the concrete `tri_bez_newton`
    system: everything except the two genuinely `C²` side conditions
    (`|R|² > 0` on the rectangle and the shared second-derivative bound `K`) is
    proved; the Jacobian entries and `det` are the C's own polynomial sums
    (`pd1_bezF` … `jacDet_bez`). -/
theorem ofCubic_newton_quadratic (c : Fin 4 → Fin 4 → ℝ) (d : Fin 3 → ℝ)
    (a b cα dα K B δ : ℝ)
    (hlene : ∀ u ∈ Set.Icc a b, ∀ t ∈ Set.Icc cα dα, 0 < (ofCubic c d).q u t)
    (hb : PddBounds (ofCubic c d) a b cα dα K)
    (hK : 0 < K) (hB : 0 ≤ B)
    {u₀ t₀ u t : ℝ}
    (hu : u ∈ Set.Icc a b) (hu₀ : u₀ ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc cα dα) (ht₀ : t₀ ∈ Set.Icc cα dα)
    (hroot : bezF (ofCubic c d) u₀ t₀ = 0 ∧ bezG (ofCubic c d) u₀ t₀ = 0)
    (hUb : |pd1 (bezF (ofCubic c d)) u t| ≤ B) (hVb : |pd2 (bezF (ofCubic c d)) u t| ≤ B)
    (hWb : |pd1 (bezG (ofCubic c d)) u t| ≤ B) (hZb : |pd2 (bezG (ofCubic c d)) u t| ≤ B)
    (hAb : |pd1 (bezF (ofCubic c d)) u₀ t₀| ≤ B) (hBb : |pd2 (bezF (ofCubic c d)) u₀ t₀| ≤ B)
    (hCb : |pd1 (bezG (ofCubic c d)) u₀ t₀| ≤ B) (hDb : |pd2 (bezG (ofCubic c d)) u₀ t₀| ≤ B)
    (hden : δ ≤ |jacDet (bezF (ofCubic c d)) (bezG (ofCubic c d)) u t|) (hδ : 0 < δ)
    (hE : |u - u₀| + |t - t₀| ≤ B / K) :
    |(newton2Step (bezF (ofCubic c d)) (bezG (ofCubic c d)) u t).1 - u₀| ≤
        (10 * B * K / δ) * (|u - u₀| + |t - t₀|) ^ 2 ∧
    |(newton2Step (bezF (ofCubic c d)) (bezG (ofCubic c d)) u t).2 - t₀| ≤
        (8 * B * K * (|u - u₀| + |t - t₀|) ^ 2 + 2 * B ^ 2 *
          (|u - u₀| + |t - t₀|)) / δ :=
  bez_newton_quadratic (ofCubic c d) a b cα dα K B δ hlene hb hK hB hu hu₀ ht ht₀
    hroot hUb hVb hWb hZb hAb hBb hCb hDb hden hδ hE

end BezSys

end LightRT.Geom
