/-
  Stage 3: conservative floating-point slab test (no false misses).

  Two evaluation orders appear in LightRT:
  * scalar `tri_slab_scalar`:   t = fl(fl(bound - org) * invd)        (relative error)
  * SIMD  `*_slab_avx/sse`:     t = fl(bound * invd - oinv)  (FMA)    (absolute error!)
  where `invd = fl(1 / d)` and `oinv = fl(org * invd)`.

  Every rounding has its own δ (via `RoundingModel.rel`); nothing below assumes
  all operations contribute the same ε.

  Note (derived here, Ize's exact constant is UNVERIFIED against the paper):
  if the far value is inflated by a *rounded* multiply `fl(tfar * K)`, the
  sufficient condition is `(1 + γ₃) ≤ (1 - γ₃)(1 - u) K`; `K = 1 + 2γ₃` does
  NOT satisfy it, `K = 1 + 2γ₄` does (`ize_constant_sufficient`).
-/
import LightRT.FP.Gamma
import LightRT.FP.Binary32
import LightRT.Geom.SlabReal

namespace LightRT.Robust
open LightRT.FP LightRT.Geom
noncomputable section

variable (R : RoundingModel)

/-- `invd = fl(1/d)` (direction components assumed nonzero here). -/
def fpInvd (r : Ray) (i : Fin 3) : ℝ := R.div 1 (r.d i)

/-- Scalar order: `fl(fl(x - o) * invd)`. -/
def fpT (r : Ray) (x : ℝ) (i : Fin 3) : ℝ := R.mul (R.sub x (r.o i)) (fpInvd R r i)

/-- FMA order: `fl(x * invd - fl(o * invd))` (one rounding for the fused op). -/
def fpTfma (r : Ray) (x : ℝ) (i : Fin 3) : ℝ :=
  R.fma x (fpInvd R r i) (-(R.mul (r.o i) (fpInvd R r i)))

def fpNear (r : Ray) (b : Box) (i : Fin 3) : ℝ := min (fpT R r (b.lo i) i) (fpT R r (b.hi i) i)
def fpFar (r : Ray) (b : Box) (i : Fin 3) : ℝ := max (fpT R r (b.lo i) i) (fpT R r (b.hi i) i)

/-- Floating-point slab test with the far value inflated by a rounded multiply by `K`.
    `K = 1` is exactly the current `tri_slab_scalar` (min/max are exact in FP). -/
def fpSlab (r : Ray) (b : Box) (K : ℝ) : Prop :=
  max (max (fpNear R r b 0) (fpNear R r b 1)) (max (fpNear R r b 2) r.tmin) ≤
    R.mul (min (min (fpFar R r b 0) (fpFar R r b 1)) (min (fpFar R r b 2) r.tmax)) K

/-- Every intermediate exact result lies where the standard model applies. -/
def SlabInRange (r : Ray) (b : Box) (K : ℝ) : Prop :=
  (∀ i, R.InRange (1 / r.d i)) ∧
  (∀ i, ∀ x ∈ ({b.lo i, b.hi i} : Set ℝ),
    R.InRange (x - r.o i) ∧ R.InRange (R.sub x (r.o i) * fpInvd R r i)) ∧
  R.InRange (min (min (fpFar R r b 0) (fpFar R r b 1)) (min (fpFar R r b 2) r.tmax) * K)

theorem u_le_gamma1 {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : u ≤ gamma u 1 := by
  unfold gamma; rw [le_div_iff₀ (by norm_num; linarith)]; norm_num; nlinarith

/-- Three independent roundings compose to one `1 + θ`, `|θ| ≤ γ₃`. -/
theorem three_rel {u a b c : ℝ} (h0 : 0 ≤ u) (hu : (3 : ℝ) * u < 1)
    (ha : |a| ≤ u) (hb : |b| ≤ u) (hc : |c| ≤ u) :
    |(1 + a) * (1 + b) * (1 + c) - 1| ≤ gamma u 3 := by
  have hu1 : u < 1 := by linarith
  have g1 := u_le_gamma1 h0 hu1
  have hab := gamma_compose (m := 1) (n := 1) h0 (by norm_num; linarith) (ha.trans g1) (hb.trans g1)
  have habc := gamma_compose (m := 1 + 1) (n := 1) h0 (by norm_num; linarith)
    (a := (1 + a) * (1 + b) - 1) (by simpa using hab) (hc.trans g1)
  simpa using habc

/-- Relative form of the scalar slab parameter: `fpT = t (1 + θ)`, `|θ| ≤ γ₃`,
    with the three `δ`s of `fl(1/d)`, `fl(x-o)` and the product independent. -/
theorem fpT_rel (r : Ray) (x : ℝ) (i : Fin 3) (hd : r.d i ≠ 0)
    (hu : (3 : ℝ) * R.u < 1)
    (h1 : R.InRange (1 / r.d i)) (h2 : R.InRange (x - r.o i))
    (h3 : R.InRange (R.sub x (r.o i) * fpInvd R r i)) :
    ∃ θ, |θ| ≤ gamma R.u 3 ∧ fpT R r x i = (x - r.o i) / r.d i * (1 + θ) := by
  obtain ⟨c, hc, ec⟩ := R.rel _ h3
  obtain ⟨a, ha, ea⟩ := R.rel _ h2
  obtain ⟨b, hb, eb⟩ := R.rel _ h1
  refine ⟨(1 + a) * (1 + b) * (1 + c) - 1, three_rel R.u_pos.le hu ha hb hc, ?_⟩
  unfold fpT RoundingModel.mul
  rw [ec]; unfold RoundingModel.sub fpInvd RoundingModel.div
  rw [ea, eb]; field_simp; ring

/-- Per-operation error of one slab parameter (scalar order): three roundings. -/
theorem slab_t_err (r : Ray) (x : ℝ) (i : Fin 3) (hd : r.d i ≠ 0)
    (hu : (3 : ℝ) * R.u < 1)
    (h1 : R.InRange (1 / r.d i)) (h2 : R.InRange (x - r.o i))
    (h3 : R.InRange (R.sub x (r.o i) * fpInvd R r i)) :
    |fpT R r x i - (x - r.o i) / r.d i| ≤ gamma R.u 3 * |(x - r.o i) / r.d i| := by
  obtain ⟨θ, hθ, e⟩ := fpT_rel R r x i hd hu h1 h2 h3
  rw [e, show (x - r.o i) / r.d i * (1 + θ) - (x - r.o i) / r.d i = θ * ((x - r.o i) / r.d i)
    by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)

/-- Ize's FMA observation: the FMA order has an *absolute* error that scales
    with `|o|/|d|`, not with `|t|` (catastrophic cancellation in `x·invd - oinv`). -/
theorem slab_t_err_fma (r : Ray) (x : ℝ) (i : Fin 3) (hd : r.d i ≠ 0)
    (hu : (3 : ℝ) * R.u < 1)
    (h1 : R.InRange (1 / r.d i)) (h2 : R.InRange (r.o i * fpInvd R r i))
    (h3 : R.InRange (x * fpInvd R r i - R.mul (r.o i) (fpInvd R r i))) :
    |fpTfma R r x i - (x - r.o i) / r.d i| ≤
      gamma R.u 3 * (|x - r.o i| + |r.o i|) / |r.d i| := by
  have u0 := R.u_pos
  have hu1 : R.u < 1 := R.u_lt_one
  obtain ⟨b, hb, eb⟩ := R.rel _ h1
  obtain ⟨c, hc, ec⟩ := R.rel _ h2
  obtain ⟨e, he, ee⟩ := R.rel _ h3
  have hb' := abs_le.1 hb; have hc' := abs_le.1 hc; have he' := abs_le.1 he
  set P := (1 + b) * (1 + e) - 1
  set Q := -(c * (1 + b) * (1 + e))
  have hP : |P| ≤ gamma R.u 3 := by
    have g1 := u_le_gamma1 u0.le hu1
    have := gamma_compose (m := 1) (n := 1) u0.le (by norm_num; linarith) (hb.trans g1) (he.trans g1)
    exact this.trans (gamma_mono u0.le (by norm_num) (by norm_num; linarith))
  have hQ : |Q| ≤ gamma R.u 3 := by
    have q1 : |Q| ≤ R.u * ((1 + R.u) * (1 + R.u)) := by
      simp only [Q, abs_neg, abs_mul]
      rw [mul_assoc]
      refine mul_le_mul hc ?_ (by positivity) u0.le
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (by linarith)
      · rw [abs_le]; constructor <;> linarith
      · rw [abs_le]; constructor <;> linarith
    refine q1.trans ?_
    unfold gamma; rw [le_div_iff₀ (by norm_num; linarith)]; push_cast
    nlinarith [mul_pos u0 u0, mul_pos (mul_pos u0 u0) u0]
  have hd' : 0 < |r.d i| := abs_pos.2 hd
  have expand : fpTfma R r x i - (x - r.o i) / r.d i =
      (x - r.o i) / r.d i * P + r.o i / r.d i * Q := by
    unfold fpTfma RoundingModel.fma
    rw [← sub_eq_add_neg, ee]
    unfold RoundingModel.mul
    rw [ec]; unfold fpInvd RoundingModel.div
    rw [eb]; simp only [P, Q]; field_simp; ring
  rw [expand]
  calc |(x - r.o i) / r.d i * P + r.o i / r.d i * Q|
      ≤ |(x - r.o i) / r.d i| * |P| + |r.o i / r.d i| * |Q| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |(x - r.o i) / r.d i| * gamma R.u 3 + |r.o i / r.d i| * gamma R.u 3 := by
        gcongr
    _ = _ := by rw [abs_div, abs_div]; field_simp

/-- The inflation condition needed when `tfar * K` is itself rounded. -/
def InflationOK (u K : ℝ) : Prop := 1 + gamma u 3 ≤ (1 - gamma u 3) * (1 - u) * K

/-- `K = 1 + 2γ₄` is sufficient for every `u ≤ 2⁻²⁴`. -/
theorem ize_constant_sufficient {u : ℝ} (hu0 : 0 < u) (hu : u ≤ (2 : ℝ) ^ (-24 : ℤ)) :
    InflationOK u (1 + 2 * gamma u 4) := by
  have hs : u ≤ 1 / 16777216 := by norm_num at hu; linarith
  unfold InflationOK gamma; push_cast
  have d3 : 0 < 1 - 3 * u := by linarith
  have d4 : 0 < 1 - 4 * u := by linarith
  rw [show 1 + 3 * u / (1 - 3 * u) = 1 / (1 - 3 * u) by field_simp; ring,
    show 1 - 3 * u / (1 - 3 * u) = (1 - 6 * u) / (1 - 3 * u) by field_simp; ring,
    show 1 + 2 * (4 * u / (1 - 4 * u)) = (1 + 4 * u) / (1 - 4 * u) by field_simp; ring,
    div_mul_eq_mul_div, div_mul_div_comm, div_le_div_iff₀ d3 (by positivity)]
  nlinarith [mul_pos hu0 hu0, mul_pos (mul_pos hu0 hu0) hu0]

/-- `K = 1 + 2γ₃` is NOT sufficient once the final multiply is rounded. -/
theorem ize_constant_gamma3_insufficient {u : ℝ} (hu0 : 0 < u) (hu : u ≤ (2 : ℝ) ^ (-24 : ℤ)) :
    ¬ InflationOK u (1 + 2 * gamma u 3) := by
  have hs : u ≤ 1 / 16777216 := by norm_num at hu; linarith
  unfold InflationOK gamma; push_cast
  have d3 : 0 < 1 - 3 * u := by linarith
  rw [show 1 + 3 * u / (1 - 3 * u) = 1 / (1 - 3 * u) by field_simp; ring,
    show 1 - 3 * u / (1 - 3 * u) = (1 - 6 * u) / (1 - 3 * u) by field_simp; ring,
    show 1 + 2 * (3 * u / (1 - 3 * u)) = (1 + 3 * u) / (1 - 3 * u) by field_simp; ring,
    div_mul_eq_mul_div, div_mul_div_comm, div_le_div_iff₀ d3 (by positivity), not_le]
  nlinarith [mul_pos hu0 hu0, mul_pos (mul_pos hu0 hu0) hu0]

/-- **Stage 3 main theorem: no false misses.** If the exact ray segment meets the
    box, the inflated floating-point slab test reports a hit. Direction of the
    implication: geometric hit ⇒ algorithm hit (conservativeness). -/
theorem slab_no_false_miss (r : Ray) (b : Box) (K : ℝ)
    (hd : ∀ i, r.d i ≠ 0) (htmin : 0 ≤ r.tmin)
    (hu : (6 : ℝ) * R.u < 1) (hK : InflationOK R.u K)
    (hrange : SlabInRange R r b K) :
    HitsBox r b → fpSlab R r b K := by
  rintro ⟨tE, hmin, hmax, hm⟩
  have hu3 : (3 : ℝ) * R.u < 1 := by linarith [R.u_pos]
  have hE : 0 ≤ tE := htmin.trans hmin
  have g0 : 0 ≤ gamma R.u 3 := gamma_nonneg R.u_pos.le (by norm_num; linarith)
  have g1 : gamma R.u 3 ≤ 1 := by
    unfold gamma; rw [div_le_one (by norm_num; linarith)]; norm_num; linarith
  obtain ⟨h1, h2, h3⟩ := hrange
  have rel : ∀ i, ∀ x ∈ ({b.lo i, b.hi i} : Set ℝ),
      ∃ θ, |θ| ≤ gamma R.u 3 ∧ fpT R r x i = (x - r.o i) / r.d i * (1 + θ) :=
    fun i x hx => fpT_rel R r x i (hd i) hu3 (h1 i) (h2 i x hx).1 (h2 i x hx).2
  have hN : ∀ i, fpNear R r b i ≤ tE * (1 + gamma R.u 3) := by
    intro i
    obtain ⟨v, -, hv, -, hv', -⟩ := slab_axis_of_mem r b i (hd i) tE (hm i)
    have key : ∀ x ∈ ({b.lo i, b.hi i} : Set ℝ), (x - r.o i) / r.d i = v →
        fpT R r x i ≤ tE * (1 + gamma R.u 3) := by
      intro x hx e
      obtain ⟨θ, hθ, eθ⟩ := rel i x hx
      rw [eθ, e]; have := abs_le.1 hθ
      rcases le_total 0 v with h | h <;> nlinarith
    unfold fpNear
    rcases hv' with e | e
    · exact (min_le_left _ _).trans (key _ (by simp) e.symm)
    · exact (min_le_right _ _).trans (key _ (by simp) e.symm)
  have hF : ∀ i, tE * (1 - gamma R.u 3) ≤ fpFar R r b i := by
    intro i
    obtain ⟨-, w, -, hw, -, hw'⟩ := slab_axis_of_mem r b i (hd i) tE (hm i)
    have key : ∀ x ∈ ({b.lo i, b.hi i} : Set ℝ), (x - r.o i) / r.d i = w →
        tE * (1 - gamma R.u 3) ≤ fpT R r x i := by
      intro x hx e
      obtain ⟨θ, hθ, eθ⟩ := rel i x hx
      rw [eθ, e]; have := abs_le.1 hθ; nlinarith
    unfold fpFar
    rcases hw' with e | e
    · exact (key _ (by simp) e.symm).trans (le_max_left _ _)
    · exact (key _ (by simp) e.symm).trans (le_max_right _ _)
  set m := min (min (fpFar R r b 0) (fpFar R r b 1)) (min (fpFar R r b 2) r.tmax)
  have hmL : tE * (1 - gamma R.u 3) ≤ m :=
    le_min (le_min (hF 0) (hF 1)) (le_min (hF 2) (by nlinarith))
  have hK0 : 0 < K := by
    by_contra hk; rw [not_lt] at hk
    have : (1 - gamma R.u 3) * (1 - R.u) * K ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) (by linarith [R.u_lt_one])) hk
    unfold InflationOK at hK; linarith
  obtain ⟨δ, hδ, eδ⟩ := R.rel _ h3
  have hδ' := abs_le.1 hδ
  unfold fpSlab RoundingModel.mul; rw [eδ]
  have hm0 : 0 ≤ m := (mul_nonneg hE (by linarith)).trans hmL
  have step : tE * (1 + gamma R.u 3) ≤ m * K * (1 + δ) := by
    have a1 : tE * ((1 - gamma R.u 3) * (1 - R.u) * K) ≤ m * K * (1 - R.u) := by
      have := mul_le_mul_of_nonneg_right hmL (mul_nonneg hK0.le (by linarith [R.u_lt_one] : (0:ℝ) ≤ 1 - R.u))
      nlinarith
    have a2 : m * K * (1 - R.u) ≤ m * K * (1 + δ) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hm0 hK0.le)
    have a3 := mul_le_mul_of_nonneg_left hK hE
    linarith
  refine le_trans ?_ step
  exact max_le (max_le (hN 0) (hN 1)) (max_le (hN 2) (by nlinarith))

/-- Without inflation the scalar LightRT test can miss a real hit in binary32.
    To be discharged by an explicit witness found with `tools/cdiff.py --search-miss`. -/
theorem tri_slab_scalar_false_miss_exists :
    ∃ (r : Ray) (b : Box), (∀ i, r.d i ≠ 0) ∧ 0 ≤ r.tmin ∧
      (∀ i, Binary32.model.Repr (r.o i) ∧ Binary32.model.Repr (r.d i) ∧
            Binary32.model.Repr (b.lo i) ∧ Binary32.model.Repr (b.hi i)) ∧
      HitsBox r b ∧ ¬ fpSlab Binary32.model r b 1 := by
  sorry

end
end LightRT.Robust
