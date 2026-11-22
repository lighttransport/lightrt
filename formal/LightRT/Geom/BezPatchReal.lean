/-
  Bicubic Bezier patch over R (`tri_bezpatch_eval` / `tri_bezpatch_isect_one`):
  tensor Bernstein evaluation, control-hull containment, continuity and u
  partial derivative, ray/patch hit soundness, and culling soundness (a ray
  missing the control hull cannot hit the patch). Tier 1 item 1 (parametric
  surfaces), building on `Geom/Hull.lean`.
-/
import Mathlib
import LightRT.Geom.Hull
import LightRT.Geom.Basic
import LightRT.Geom.Newton2D

namespace LightRT.Geom
noncomputable section
open Matrix
open LightRT.Geom.Hull

/-- Tensor-product bicubic Bézier patch evaluation: `Σ_k B(u,v,k) · cp k`. -/
def bicubicEval (cp : Fin 16 → Vec3) (u v : ℝ) : Vec3 :=
  ∑ k : Fin 16, bern33 u v k • cp k

/-- Every coordinate of a patch point lies in the box of the control points. -/
theorem bicubicEval_in_box (cp : Fin 16 → Vec3) (lo hi : Vec3)
    (hlo : ∀ k i, lo i ≤ cp k i) (hhi : ∀ k i, cp k i ≤ hi i)
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Box.Mem ⟨lo, hi⟩ (bicubicEval cp u v) := by
  intro i
  have h := bicubic_in_box (fun k => cp k i) u v (lo i) (hi i) hu0 hu1 hv0 hv1
    (fun k => hlo k i) (fun k => hhi k i)
  constructor
  · simpa [bicubicEval, dotProduct] using h.1
  · simpa [bicubicEval, dotProduct] using h.2

/-- A ray/patch hit: some `(u,v)` in the unit square and `t` in range with the
    ray point on the patch. -/
def HitsBezPatchRay (o d : Vec3) (cp : Fin 16 → Vec3) (tmin tbest : ℝ) : Prop :=
  ∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1, ∃ t,
    tmin ≤ t ∧ t < tbest ∧ o + t • d = bicubicEval cp u v

/-- Soundness of accepting a Newton-refined sample: the reported parameter
    gives a genuine patch hit. -/
theorem hitsBezPatchRay_of_accept (o d : Vec3) (cp : Fin 16 → Vec3) {tmin tbest u v t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hpt : o + t • d = bicubicEval cp u v) :
    HitsBezPatchRay o d cp tmin tbest :=
  ⟨u, ⟨hu0, hu1⟩, v, ⟨hv0, hv1⟩, t, htmin, htbest, hpt⟩

/-- Culling soundness: if every ray point in range misses the control-point
    hull, the ray misses the patch (no false cull). -/
theorem bezpatch_cull_sound (o d : Vec3) (cp : Fin 16 → Vec3) (lo hi : Vec3)
    (hlo : ∀ k i, lo i ≤ cp k i) (hhi : ∀ k i, cp k i ≤ hi i) {tmin tbest : ℝ}
    (hmiss : ∀ t, tmin ≤ t → t < tbest → ¬ Box.Mem ⟨lo, hi⟩ (o + t • d)) :
    ¬ HitsBezPatchRay o d cp tmin tbest := by
  rintro ⟨u, hu, v, hv, t, htmin, htbest, hpt⟩
  apply hmiss t htmin htbest
  rw [hpt]
  exact bicubicEval_in_box cp lo hi hlo hhi hu.1 hu.2 hv.1 hv.2


/-- The bicubic patch evaluation is continuous in (u,v). -/
theorem continuous_bicubicEval (cp : Fin 16 → Vec3) :
    Continuous (fun p : ℝ × ℝ => bicubicEval cp p.1 p.2) := by
  unfold bicubicEval bern33 bern3
  fun_prop

/-- Derivative of a cubic Bernstein weight. -/
def bern3' (t : ℝ) (k : Fin 4) : ℝ :=
  match k with
  | ⟨0, _⟩ => -3 * (1 - t) ^ 2
  | ⟨1, _⟩ => 3 * (1 - t) ^ 2 - 6 * (1 - t) * t
  | ⟨2, _⟩ => 6 * (1 - t) * t - 3 * t ^ 2
  | ⟨_, _⟩ => 3 * t ^ 2

theorem hasDerivAt_bern3 (t : ℝ) (k : Fin 4) :
    HasDerivAt (fun t => bern3 t k) (bern3' t k) t := by
  fin_cases k
  · convert (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 3) using 1
    · ext x <;> simp [bern3, Pi.sub_apply, Pi.pow_apply, id_eq] <;> ring_nf
    · change (-3 * (1 - t)^2) = _
      simp [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring_nf
  · convert ((hasDerivAt_id t).mul (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2)).const_mul 3 using 1
    · ext x <;> simp [bern3, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring_nf
    · change (3 * (1 - t)^2 - 6 * (1 - t) * t) = _
      simp [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring_nf
  · convert (((hasDerivAt_id t).pow 2).mul (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)))).const_mul 3 using 1
    · ext x <;> simp [bern3, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring_nf
    · change (6 * (1 - t) * t - 3 * t^2) = _
      simp [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq] <;> ring_nf
  · convert ((hasDerivAt_id t).pow 3) using 1
    · ext x <;> simp [bern3, id_eq] <;> ring_nf
    · simp [bern3', id_eq] <;> ring_nf

/-- Partial derivative of the patch with respect to u. -/
def bicubicEval_du (cp : Fin 16 → Vec3) (u v : ℝ) : Vec3 :=
  ∑ k : Fin 16, (bern3' u ⟨k.val % 4, by omega⟩ * bern3 v ⟨k.val / 4, by omega⟩) • cp k

theorem bicubicEval_hasDerivAt_u (cp : Fin 16 → Vec3) (u v : ℝ) :
    HasDerivAt (fun u => bicubicEval cp u v) (bicubicEval_du cp u v) u := by
  unfold bicubicEval bicubicEval_du bern33
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 u ⟨k.val % 4, by omega⟩).mul_const
      (bern3 v ⟨k.val / 4, by omega⟩)).smul_const (cp k))) using 1
  · ext y; simp [bern33] <;> ring_nf

theorem bezpatch_cull_complete (o d : Vec3) (cp : Fin 16 → Vec3) (lo hi : Vec3)
    (hlo : ∀ k i, lo i ≤ cp k i) (hhi : ∀ k i, cp k i ≤ hi i)
    {tmin tbest : ℝ} (hhit : HitsBezPatchRay o d cp tmin tbest) :
    ∃ t, tmin ≤ t ∧ t < tbest ∧ Box.Mem ⟨lo, hi⟩ (o + t • d) := by
  rcases hhit with ⟨u, hu, v, hv, t, htmin, htbest, hpt⟩
  refine ⟨t, htmin, htbest, ?_⟩
  rw [hpt]
  exact bicubicEval_in_box cp lo hi hlo hhi hu.1 hu.2 hv.1 hv.2

def bez3Vec (P : Fin 4 → Vec3) (t : ℝ) : Vec3 :=
  ∑ i : Fin 4, bern3 t i • P i

def splitLVec (P : Fin 4 → Vec3) (t : ℝ) : Fin 4 → Vec3 :=
  fun i a => splitL (fun j => P j a) t i

theorem bez3Vec_decasteljau_left (P : Fin 4 → Vec3) (t s : ℝ) :
    bez3Vec (splitLVec P t) s = bez3Vec P (t * s) := by
  ext a
  change Hull.bez3 (fun i => splitLVec P t i a) s = Hull.bez3 (fun i => P i a) (t * s)
  exact Hull.decasteljau_left (fun i => P i a) t s

def patchRows (cp : Fin 16 → Vec3) (j : Fin 4) : Fin 4 → Vec3 :=
  fun i => cp ⟨j.val * 4 + i.val, by omega⟩

def bicubicEval_rows (cp : Fin 16 → Vec3) (u v : ℝ) : Vec3 :=
  ∑ j : Fin 4, bern3 v j • bez3Vec (patchRows cp j) u

theorem bern33_ji (u v : ℝ) (j i : Fin 4) :
    bern33 u v ⟨j.val * 4 + i.val, by omega⟩ = bern3 u i * bern3 v j := by
  have h1 : i.val % 4 = i.val := Nat.mod_eq_of_lt i.isLt
  have h2 : (j.val * 4 + i.val) / 4 = j.val := by omega
  simp [bern33, h1, h2]

theorem fin_idx_eq (j i : Fin 4) :
    finProdFinEquiv (j, i) = (⟨j.val * 4 + i.val, by omega⟩ : Fin 16) := by
  apply Fin.ext
  simp [finProdFinEquiv]
  omega

theorem bicubicEval_eq_rows (cp : Fin 16 → Vec3) (u v : ℝ) :
    bicubicEval cp u v = bicubicEval_rows cp u v := by
  unfold bicubicEval bicubicEval_rows bez3Vec
  rw [← Equiv.sum_comp (finProdFinEquiv (m:=4) (n:=4))]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fin_idx_eq, bern33_ji]
  simp [patchRows, smul_smul, mul_comm, mul_assoc]


/-- Split a bicubic patch's control net in the u direction at t (left half). -/
def splitBicubicU (cp : Fin 16 → Vec3) (t : ℝ) : Fin 16 → Vec3 :=
  fun k => splitLVec (patchRows cp ⟨k.val / 4, by omega⟩) t ⟨k.val % 4, by omega⟩

/-- Full tensor de Casteljau split: the left u-subpatch evaluated at `s` equals
    the original patch at `t*s`. -/
theorem bicubic_split_left (cp : Fin 16 → Vec3) (t s v : ℝ) :
    bicubicEval (splitBicubicU cp t) s v = bicubicEval cp (t * s) v := by
  rw [bicubicEval_eq_rows (splitBicubicU cp t) s v, bicubicEval_eq_rows cp (t * s) v]
  unfold bicubicEval_rows
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hrows : patchRows (splitBicubicU cp t) j = splitLVec (patchRows cp j) t := by
    ext i a
    simp [patchRows, splitBicubicU]
    have h1 : (j.val * 4 + i.val) / 4 = j.val := by omega
    have h2 : (j.val * 4 + i.val) % 4 = i.val := by omega
    simp [h1, h2, Nat.mod_eq_of_lt i.isLt]
  rw [hrows]
  exact bez3Vec_decasteljau_left (patchRows cp j) t s

theorem continuous_bicubicEval_cheap (cp : Fin 16 → Vec3) :
    Continuous (fun p : ℝ × ℝ => bicubicEval cp p.1 p.2) := by
  unfold bicubicEval bern33 bern3
  apply continuous_finset_sum
  intro k hk
  fun_prop

/-- Parameter triples for ray/patch hits. -/
def BezPatchHitParams (o d : Vec3) (cp : Fin 16 → Vec3) (tmin tbest : ℝ) :
    Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2.1 ∈ Set.Icc (0:ℝ) 1 ∧
       p.2.2 ∈ Set.Icc tmin tbest ∧ o + p.2.2 • d = bicubicEval cp p.1 p.2.1}

theorem bezpatch_exists_nearest_hit (o d : Vec3) (cp : Fin 16 → Vec3) {tmin tbest : ℝ}
    (hab : tmin ≤ tbest) (hhit : HitsBezPatchRay o d cp tmin tbest) :
    ∃ tstar, (∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1,
              o + tstar • d = bicubicEval cp u v) ∧
         tmin ≤ tstar ∧ tstar ≤ tbest ∧
         (∀ t, tmin ≤ t → t ≤ tbest →
            (∃ u ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Set.Icc (0:ℝ) 1,
              o + t • d = bicubicEval cp u v) → tstar ≤ t) := by
  let S := BezPatchHitParams o d cp tmin tbest
  have hclosed : IsClosed S := by
    unfold S BezPatchHitParams
    have h1 : Continuous (fun p : ℝ × ℝ × ℝ => o + p.2.2 • d) := by
      exact continuous_const.add ((continuous_snd.comp continuous_snd).smul continuous_const)
    have h2 : Continuous (fun p : ℝ × ℝ × ℝ => bicubicEval cp p.1 p.2.1) := by
      unfold bicubicEval bern33 bern3
      apply continuous_finset_sum
      intro k hk
      fun_prop
    have hz : IsClosed {p : ℝ × ℝ × ℝ | o + p.2.2 • d = bicubicEval cp p.1 p.2.1} :=
      isClosed_eq h1 h2
    have hbox : IsClosed ({p : ℝ × ℝ × ℝ |
        p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2.2 ∈ Set.Icc tmin tbest}) := by
      change IsClosed ((Set.Icc (0:ℝ) 1) ×ˢ ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc tmin tbest)))
      exact isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)
    simpa [Set.setOf_and, Set.inter_assoc] using hbox.inter hz
  let K : Set (ℝ × ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc tmin tbest)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hsub : S ⊆ K := by intro p hp; exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  have hcomp : IsCompact S := hK.of_isClosed_subset hclosed hsub
  have hne : S.Nonempty := by
    rcases hhit with ⟨u, hu, v, hv, t, htmin, htbest, hpt⟩
    exact ⟨(u, v, t), hu, hv, ⟨htmin, le_of_lt htbest⟩, hpt⟩
  have hcont_t : ContinuousOn (fun p : ℝ × ℝ × ℝ => p.2.2) S := (continuous_snd.comp continuous_snd).continuousOn
  obtain ⟨pstar, hpstar, hmin⟩ := hcomp.exists_isMinOn hne hcont_t
  refine ⟨pstar.2.2, ?_, ?_, ?_, ?_⟩
  · exact ⟨pstar.1, hpstar.1, pstar.2.1, hpstar.2.1, hpstar.2.2.2⟩
  · exact hpstar.2.2.1.1
  · exact hpstar.2.2.1.2
  · intro t htmin htbest ht
    rcases ht with ⟨u, hu, v, hv, hpt⟩
    exact hmin (show (u, v, t) ∈ S from ⟨hu, hv, ⟨htmin, htbest⟩, hpt⟩)

def bezPatchContact (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) : Vec3 :=
  bicubicEval cp u v - (o + t • d)

/-- A converged Newton contact (`F = 0`) is a genuine patch hit. -/
theorem newton_patch_hit_of_contact_zero (o d : Vec3) (cp : Fin 16 → Vec3) {tmin tbest u v t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hres : bezPatchContact o d cp t u v = 0) :
    HitsBezPatchRay o d cp tmin tbest := by
  apply hitsBezPatchRay_of_accept o d cp hu0 hu1 hv0 hv1 htmin htbest
  unfold bezPatchContact at hres
  exact (sub_eq_zero.mp hres).symm

/-- A converged Newton contact parameter is no smaller than the nearest hit. -/
theorem newton_patch_contact_ge_nearest (o d : Vec3) (cp : Fin 16 → Vec3) {tmin tbest u v t : ℝ}
    (hab : tmin ≤ tbest)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (htmin : tmin ≤ t) (htbest : t < tbest)
    (hres : bezPatchContact o d cp t u v = 0) :
    ∃ tstar, tstar ∈ Set.Icc tmin tbest ∧
      (∃ u' ∈ Set.Icc (0:ℝ) 1, ∃ v' ∈ Set.Icc (0:ℝ) 1,
        o + tstar • d = bicubicEval cp u' v') ∧
      (∀ s, s ∈ Set.Icc tmin tbest →
        (∃ u' ∈ Set.Icc (0:ℝ) 1, ∃ v' ∈ Set.Icc (0:ℝ) 1,
          o + s • d = bicubicEval cp u' v') → tstar ≤ s) ∧
      tstar ≤ t := by
  have hhit := newton_patch_hit_of_contact_zero o d cp hu0 hu1 hv0 hv1 htmin htbest hres
  obtain ⟨tstar, hsh, hslo, hshi, hmin⟩ := bezpatch_exists_nearest_hit o d cp hab hhit
  refine ⟨tstar, ⟨hslo, hshi⟩, hsh, ?_, ?_⟩
  · intro s hs hsh'
    exact hmin s hs.1 hs.2 hsh'
  · exact hmin t htmin (le_of_lt htbest) ⟨u, ⟨hu0, hu1⟩, v, ⟨hv0, hv1⟩, by
      unfold bezPatchContact at hres
      exact (sub_eq_zero.mp hres).symm⟩

def patchF (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) : ℝ :=
  (bezPatchContact o d cp t u v) 0

def patchG (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) : ℝ :=
  (bezPatchContact o d cp t u v) 1

/-- Newton2D quadratic contraction instantiated at the patch contact system.
    The C2/bounds hypotheses are the standing Newton2D data (as in
    `ofCubic_newton_quadratic`); deriving them from control points is the
    remaining coefficient bound chase. -/
theorem bezpatch_newton_quadratic (o d : Vec3) (cp : Fin 16 → Vec3) (t : ℝ)
    (a b c dv K B δ : ℝ)
    (hF : C2Seg (patchF o d cp t) a b c dv K)
    (hG : C2Seg (patchG o d cp t) a b c dv K)
    (hK : 0 < K) (hB : 0 ≤ B)
    {u₀ v₀ u v : ℝ}
    (hu : u ∈ Set.Icc a b) (hu₀ : u₀ ∈ Set.Icc a b)
    (hv : v ∈ Set.Icc c dv) (hv₀ : v₀ ∈ Set.Icc c dv)
    (hroot : patchF o d cp t u₀ v₀ = 0 ∧ patchG o d cp t u₀ v₀ = 0)
    (hUb : |pd1 (patchF o d cp t) u v| ≤ B) (hVb : |pd2 (patchF o d cp t) u v| ≤ B)
    (hWb : |pd1 (patchG o d cp t) u v| ≤ B) (hZb : |pd2 (patchG o d cp t) u v| ≤ B)
    (hAb : |pd1 (patchF o d cp t) u₀ v₀| ≤ B) (hBb : |pd2 (patchF o d cp t) u₀ v₀| ≤ B)
    (hCb : |pd1 (patchG o d cp t) u₀ v₀| ≤ B) (hDb : |pd2 (patchG o d cp t) u₀ v₀| ≤ B)
    (hden : δ ≤ |jacDet (patchF o d cp t) (patchG o d cp t) u v|) (hδ : 0 < δ)
    (hE : |u - u₀| + |v - v₀| ≤ B / K) :
    |(newton2Step (patchF o d cp t) (patchG o d cp t) u v).1 - u₀| ≤
        (10 * B * K / δ) * (|u - u₀| + |v - v₀|) ^ 2 ∧
    |(newton2Step (patchF o d cp t) (patchG o d cp t) u v).2 - v₀| ≤
        (8 * B * K * (|u - u₀| + |v - v₀|) ^ 2 + 2 * B ^ 2 *
          (|u - u₀| + |v - v₀|)) / δ :=
  newton2_step_quadratic hF hG hK hB hu hu₀ hv hv₀ hroot
    hUb hVb hWb hZb hAb hBb hCb hDb hden hδ hE

/-- Second derivative of a cubic Bernstein weight. -/
def bern3'' (t : ℝ) (k : Fin 4) : ℝ :=
  match k with
  | ⟨0, _⟩ => 6 * (1 - t)
  | ⟨1, _⟩ => 18 * t - 12
  | ⟨2, _⟩ => 6 - 18 * t
  | ⟨_, _⟩ => 6 * t

theorem bern3'_vec (t : ℝ) (k : Fin 4) :
    bern3' t k = ![-(3*(1-t)^2), 3*(1-t)^2 - 6*(1-t)*t,
                     6*(1-t)*t - 3*t^2, 3*t^2] k := by
  fin_cases k
  · change -3*(1-t)^2 = _; simp
  · change 3*(1-t)^2 - 6*(1-t)*t = _; simp
  · change 6*(1-t)*t - 3*t^2 = _; simp
  · change 3*t^2 = _; simp

theorem abs_bern3'_le {t : ℝ} (h0:0≤t) (h1:t≤1) (k:Fin 4) : |bern3' t k| ≤ 3 := by
  rw [bern3'_vec]
  fin_cases k <;> simp
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · ring_nf
    apply abs_le.mpr; constructor
    · nlinarith [sq_nonneg (3*t-2)]
    · have hmul : t*(3*t-4) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 (by nlinarith)
      nlinarith
  · ring_nf
    apply abs_le.mpr; constructor
    · nlinarith [sq_nonneg (3*t-1)]
    · have hmul : (3*t+1)*(t-1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      nlinarith
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem bern3''_vec (t : ℝ) (k : Fin 4) :
    bern3'' t k = ![6*(1-t), 18*t-12, 6-18*t, 6*t] k := by
  fin_cases k
  · change 6*(1-t) = _; simp
  · change 18*t-12 = _; simp
  · change 6-18*t = _; simp
  · change 6*t = _; simp

theorem abs_bern3''_le {t : ℝ} (h0:0≤t) (h1:t≤1) (k:Fin 4) : |bern3'' t k| ≤ 12 := by
  rw [bern3''_vec]
  fin_cases k <;> simp
  · have h : |1 - t| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have h : |t| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith

theorem bern3_le_one {t:ℝ} (h0:0≤t) (h1:t≤1) (k:Fin 4) : bern3 t k ≤ 1 := by
  fin_cases k <;> simp [bern3] <;> nlinarith [sq_nonneg t, sq_nonneg (1-t)]


theorem abs_bicubic_du_le (cp : Fin 16 → Vec3) (M : ℝ) (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M)
    {u v : ℝ} (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) (a : Fin 3) :
    |(bicubicEval_du cp u v) a| ≤ 48 * M := by
  unfold bicubicEval_du
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc |∑ k : Fin 16, (bern3' u ⟨k.val % 4, by omega⟩ * bern3 v ⟨k.val / 4, by omega⟩) * cp k a|
      ≤ ∑ k : Fin 16, |(bern3' u ⟨k.val % 4, by omega⟩ * bern3 v ⟨k.val / 4, by omega⟩) * cp k a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin 16, (3 * M) := by
        apply Finset.sum_le_sum; intro k hk
        rw [abs_mul, abs_mul]
        have h1 := abs_bern3'_le hu0 hu1 ⟨k.val % 4, by omega⟩
        have h2 := bern3_nonneg hv0 hv1 ⟨k.val / 4, by omega⟩
        have h2' : |bern3 v ⟨k.val / 4, by omega⟩| ≤ 1 := by
          rw [abs_of_nonneg h2]
          exact bern3_le_one hv0 hv1 ⟨k.val / 4, by omega⟩
        have h12 : |bern3' u ⟨k.val % 4, by omega⟩| * |bern3 v ⟨k.val / 4, by omega⟩| ≤ 3 * 1 :=
          mul_le_mul h1 h2' (abs_nonneg _) (by norm_num)
        have h123 : (|bern3' u ⟨k.val % 4, by omega⟩| * |bern3 v ⟨k.val / 4, by omega⟩|) * |cp k a| ≤ (3*1) * M :=
          mul_le_mul h12 (hM k a) (abs_nonneg _) (by norm_num)
        simpa [mul_assoc] using h123
    _ = 48 * M := by simp; ring

theorem hasDerivAt_bern3' (t : ℝ) (k : Fin 4) :
    HasDerivAt (fun t => bern3' t k) (bern3'' t k) t := by
  fin_cases k
  · change HasDerivAt (fun t => -3 * (1 - t)^2) (6 * (1 - t)) t
    convert (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2).const_mul (-3) using 1 <;>
      (first | (ext x <;> simp [Pi.sub_apply, Pi.pow_apply, id_eq] <;> ring_nf) | (simp [Pi.sub_apply, Pi.pow_apply, id_eq] <;> ring_nf))
  · change HasDerivAt (fun t => 3 * (1 - t)^2 - 6 * (1 - t) * t) (18 * t - 12) t
    have h1 := ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2 |>.const_mul 3
    have h2 := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul (hasDerivAt_id t)).const_mul 6
    convert h1.sub h2 using 1 <;> (first | (ext x; simp [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq]; ring_nf) | (simp [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq]; ring_nf))
  · change HasDerivAt (fun t => 6 * (1 - t) * t - 3 * t^2) (6 - 18*t) t
    have h1 := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul (hasDerivAt_id t)).const_mul 6
    have h2 := (hasDerivAt_id t).pow 2 |>.const_mul 3
    convert h1.sub h2 using 1 <;> (first | (ext x; simp [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq]; ring_nf) | (simp [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq]; ring_nf))
  · change HasDerivAt (fun t => 3 * t^2) (6 * t) t
    convert ((hasDerivAt_id t).pow 2).const_mul 3 using 1 <;>
      (first | (ext x <;> simp [Pi.pow_apply, id_eq] <;> ring_nf) | (simp [Pi.pow_apply, id_eq] <;> ring_nf))


/-- Partial derivative of the patch with respect to v. -/
def bicubicEval_dv (cp : Fin 16 → Vec3) (u v : ℝ) : Vec3 :=
  ∑ k : Fin 16, (bern3 u ⟨k.val % 4, by omega⟩ * bern3' v ⟨k.val / 4, by omega⟩) • cp k

theorem bicubicEval_hasDerivAt_v (cp : Fin 16 → Vec3) (u v : ℝ) :
    HasDerivAt (fun v => bicubicEval cp u v) (bicubicEval_dv cp u v) v := by
  unfold bicubicEval bicubicEval_dv bern33
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 v ⟨k.val / 4, by omega⟩).const_mul
      (bern3 u ⟨k.val % 4, by omega⟩)).smul_const (cp k))) using 1
  · ext y; simp [bern33, mul_comm] <;> ring_nf

/-- Second partial uu. -/
def bicubicEval_duu (cp : Fin 16 → Vec3) (u v : ℝ) : Vec3 :=
  ∑ k : Fin 16, (bern3'' u ⟨k.val % 4, by omega⟩ * bern3 v ⟨k.val / 4, by omega⟩) • cp k

theorem bicubicEval_du_hasDerivAt_u (cp : Fin 16 → Vec3) (u v : ℝ) :
    HasDerivAt (fun u => bicubicEval_du cp u v) (bicubicEval_duu cp u v) u := by
  unfold bicubicEval_du bicubicEval_duu
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3' u ⟨k.val % 4, by omega⟩).mul_const
      (bern3 v ⟨k.val / 4, by omega⟩)).smul_const (cp k))) using 1
  · ext y; simp <;> ring_nf


/-- Second partial vv. -/
def bicubicEval_dvv (cp : Fin 16 → Vec3) (u v : ℝ) : Vec3 :=
  ∑ k : Fin 16, (bern3 u ⟨k.val % 4, by omega⟩ * bern3'' v ⟨k.val / 4, by omega⟩) • cp k

theorem bicubicEval_dv_hasDerivAt_v (cp : Fin 16 → Vec3) (u v : ℝ) :
    HasDerivAt (fun v => bicubicEval_dv cp u v) (bicubicEval_dvv cp u v) v := by
  unfold bicubicEval_dv bicubicEval_dvv
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3' v ⟨k.val / 4, by omega⟩).const_mul
      (bern3 u ⟨k.val % 4, by omega⟩)).smul_const (cp k))) using 1
  · ext y; simp [mul_comm] <;> ring_nf

/-- Mixed partial uv. -/
def bicubicEval_duv (cp : Fin 16 → Vec3) (u v : ℝ) : Vec3 :=
  ∑ k : Fin 16, (bern3' u ⟨k.val % 4, by omega⟩ * bern3' v ⟨k.val / 4, by omega⟩) • cp k

theorem bicubicEval_du_hasDerivAt_v (cp : Fin 16 → Vec3) (u v : ℝ) :
    HasDerivAt (fun v => bicubicEval_du cp u v) (bicubicEval_duv cp u v) v := by
  unfold bicubicEval_du bicubicEval_duv
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 v ⟨k.val / 4, by omega⟩).const_mul
      (bern3' u ⟨k.val % 4, by omega⟩)).smul_const (cp k))) using 1
  · ext y; simp [mul_comm] <;> ring_nf

theorem bicubicEval_dv_hasDerivAt_u (cp : Fin 16 → Vec3) (u v : ℝ) :
    HasDerivAt (fun u => bicubicEval_dv cp u v) (bicubicEval_duv cp u v) u := by
  unfold bicubicEval_dv bicubicEval_duv
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 u ⟨k.val % 4, by omega⟩).mul_const
      (bern3' v ⟨k.val / 4, by omega⟩)).smul_const (cp k))) using 1
  · ext y; simp <;> ring_nf

theorem abs_sum_scalar_bound {ι : Type*} [Fintype ι] (f : ι → ℝ) (B : ℝ)
    (h : ∀ k, |f k| ≤ B) : |∑ k, f k| ≤ Fintype.card ι * B := by
  calc |∑ k, f k| ≤ ∑ k, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : ι, B := Finset.sum_le_sum (fun k hk => h k)
    _ = Fintype.card ι * B := by simp

theorem abs_bicubic_du_le2 (cp : Fin 16 → Vec3) (M : ℝ) (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M)
    {u v : ℝ} (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) (a : Fin 3) :
    |(bicubicEval_du cp u v) a| ≤ 48 * M := by
  unfold bicubicEval_du
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc |∑ k : Fin 16, (bern3' u ⟨k.val % 4, by omega⟩ * bern3 v ⟨k.val / 4, by omega⟩) * cp k a|
      ≤ 16 * (3 * M) := by
        apply abs_sum_scalar_bound
        intro k
        rw [abs_mul, abs_mul]
        have h1 := abs_bern3'_le hu0 hu1 ⟨k.val % 4, by omega⟩
        have h2 := bern3_nonneg hv0 hv1 ⟨k.val / 4, by omega⟩
        have h2' : |bern3 v ⟨k.val / 4, by omega⟩| ≤ 1 := by
          rw [abs_of_nonneg h2]
          exact bern3_le_one hv0 hv1 ⟨k.val / 4, by omega⟩
        have h12 : |bern3' u ⟨k.val % 4, by omega⟩| * |bern3 v ⟨k.val / 4, by omega⟩| ≤ 3 * 1 :=
          mul_le_mul h1 h2' (abs_nonneg _) (by norm_num)
        have h123 := mul_le_mul h12 (hM k a) (abs_nonneg _) (by norm_num : 0 ≤ (3:ℝ)*1)
        simpa [mul_assoc] using h123
    _ = 48 * M := by ring

theorem abs_bicubic_dv_le (cp : Fin 16 → Vec3) (M : ℝ) (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M)
    {u v : ℝ} (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) (a : Fin 3) :
    |(bicubicEval_dv cp u v) a| ≤ 48 * M := by
  unfold bicubicEval_dv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc |∑ k : Fin 16, (bern3 u ⟨k.val % 4, by omega⟩ * bern3' v ⟨k.val / 4, by omega⟩) * cp k a|
      ≤ 16 * (3 * M) := by
        apply abs_sum_scalar_bound
        intro k
        rw [abs_mul, abs_mul]
        have h1 := bern3_nonneg hu0 hu1 ⟨k.val % 4, by omega⟩
        have h1' : |bern3 u ⟨k.val % 4, by omega⟩| ≤ 1 := by
          rw [abs_of_nonneg h1]
          exact bern3_le_one hu0 hu1 ⟨k.val % 4, by omega⟩
        have h2 := abs_bern3'_le hv0 hv1 ⟨k.val / 4, by omega⟩
        have h12 : |bern3 u ⟨k.val % 4, by omega⟩| * |bern3' v ⟨k.val / 4, by omega⟩| ≤ 1 * 3 :=
          mul_le_mul h1' h2 (abs_nonneg _) (by norm_num)
        have h123 := mul_le_mul h12 (hM k a) (abs_nonneg _) (by norm_num : 0 ≤ (1:ℝ)*3)
        simpa [mul_assoc] using h123
    _ = 48 * M := by ring

theorem abs_bicubic_uv_le (cp : Fin 16 → Vec3) (M : ℝ) (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M)
    {u v : ℝ} (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) (a : Fin 3) :
    |(bicubicEval_duv cp u v) a| ≤ 144 * M := by
  unfold bicubicEval_duv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc |∑ k : Fin 16, (bern3' u ⟨k.val % 4, by omega⟩ * bern3' v ⟨k.val / 4, by omega⟩) * cp k a|
      ≤ 16 * (9 * M) := by
        apply abs_sum_scalar_bound
        intro k
        rw [abs_mul, abs_mul]
        have h1 := abs_bern3'_le hu0 hu1 ⟨k.val % 4, by omega⟩
        have h2 := abs_bern3'_le hv0 hv1 ⟨k.val / 4, by omega⟩
        have h12 : |bern3' u ⟨k.val % 4, by omega⟩| * |bern3' v ⟨k.val / 4, by omega⟩| ≤ 3 * 3 :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        have h123 := mul_le_mul h12 (hM k a) (abs_nonneg _) (by norm_num : 0 ≤ (3:ℝ)*3)
        nlinarith [h123]
    _ = 144 * M := by ring

theorem abs_bicubic_vv_le (cp : Fin 16 → Vec3) (M : ℝ) (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M)
    {u v : ℝ} (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) (a : Fin 3) :
    |(bicubicEval_dvv cp u v) a| ≤ 192 * M := by
  unfold bicubicEval_dvv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc |∑ k : Fin 16, (bern3 u ⟨k.val % 4, by omega⟩ * bern3'' v ⟨k.val / 4, by omega⟩) * cp k a|
      ≤ 16 * (12 * M) := by
        apply abs_sum_scalar_bound
        intro k
        rw [abs_mul, abs_mul]
        have h1 := bern3_nonneg hu0 hu1 ⟨k.val % 4, by omega⟩
        have h1' : |bern3 u ⟨k.val % 4, by omega⟩| ≤ 1 := by
          rw [abs_of_nonneg h1]
          exact bern3_le_one hu0 hu1 ⟨k.val % 4, by omega⟩
        have h2 := abs_bern3''_le hv0 hv1 ⟨k.val / 4, by omega⟩
        have h12 : |bern3 u ⟨k.val % 4, by omega⟩| * |bern3'' v ⟨k.val / 4, by omega⟩| ≤ 1 * 12 :=
          mul_le_mul h1' h2 (abs_nonneg _) (by norm_num)
        have h123 := mul_le_mul h12 (hM k a) (abs_nonneg _) (by norm_num : 0 ≤ (1:ℝ)*12)
        simpa [mul_assoc] using h123
    _ = 192 * M := by ring

theorem patchF_hasDerivAt_u (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun u => patchF o d cp t u v) ((bicubicEval_du cp u v) 0) u := by
  unfold patchF bezPatchContact bicubicEval bicubicEval_du
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 u ⟨k.val % 4, by omega⟩).mul_const
      (bern3 v ⟨k.val / 4, by omega⟩)).mul_const (cp k 0))).sub_const ((o 0) + t * (d 0)) using 1
  · ext y <;> simp [bern33] <;> ring_nf

theorem patchF_hasDerivAt_v (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun v => patchF o d cp t u v) ((bicubicEval_dv cp u v) 0) v := by
  unfold patchF bezPatchContact bicubicEval bicubicEval_dv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 v ⟨k.val / 4, by omega⟩).const_mul
      (bern3 u ⟨k.val % 4, by omega⟩)).mul_const (cp k 0))).sub_const ((o 0) + t * (d 0)) using 1
  · ext y
    simp [bern33, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem pd1_patchF (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    pd1 (patchF o d cp t) u v = (bicubicEval_du cp u v) 0 :=
  (patchF_hasDerivAt_u o d cp t u v).deriv

theorem pd2_patchF (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    pd2 (patchF o d cp t) u v = (bicubicEval_dv cp u v) 0 :=
  (patchF_hasDerivAt_v o d cp t u v).deriv


/-- HasDerivAt for `u ↦ pd1 patchF u v` (derivative = pdd11). -/
theorem pd1_patchF_hasDerivAt_u (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun u => pd1 (patchF o d cp t) u v)
      ((bicubicEval_duu cp u v) 0) u := by
  rw [show (fun u => pd1 (patchF o d cp t) u v) =
      (fun u => (bicubicEval_du cp u v) 0) by
    funext u; exact pd1_patchF o d cp t u v]
  -- derivative of (fun u => (bicubicEval_du cp u v) 0) is (bicubicEval_duu cp u v) 0
  unfold bicubicEval_du bicubicEval_duu
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3' u ⟨k.val % 4, by omega⟩).mul_const
      (bern3 v ⟨k.val / 4, by omega⟩)).mul_const (cp k 0))) using 1
  · ext y; simp <;> ring_nf

/-- HasDerivAt for `v ↦ pd1 patchF u v` (derivative = pdd12). -/
theorem pd1_patchF_hasDerivAt_v (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun v => pd1 (patchF o d cp t) u v)
      ((bicubicEval_duv cp u v) 0) v := by
  rw [show (fun v => pd1 (patchF o d cp t) u v) =
      (fun v => (bicubicEval_du cp u v) 0) by
    funext v; exact pd1_patchF o d cp t u v]
  unfold bicubicEval_du bicubicEval_duv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 v ⟨k.val / 4, by omega⟩).const_mul
      (bern3' u ⟨k.val % 4, by omega⟩)).mul_const (cp k 0))) using 1
  · ext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]


theorem pd2_patchF_hasDerivAt_u (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun u => pd2 (patchF o d cp t) u v)
      ((bicubicEval_duv cp u v) 0) u := by
  rw [show (fun u => pd2 (patchF o d cp t) u v) =
      (fun u => (bicubicEval_dv cp u v) 0) by
    funext u; exact pd2_patchF o d cp t u v]
  unfold bicubicEval_dv bicubicEval_duv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 u ⟨k.val % 4, by omega⟩).mul_const
      (bern3' v ⟨k.val / 4, by omega⟩)).mul_const (cp k 0))) using 1
  · ext y; simp <;> ring_nf

theorem pd2_patchF_hasDerivAt_v (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun v => pd2 (patchF o d cp t) u v)
      ((bicubicEval_dvv cp u v) 0) v := by
  rw [show (fun v => pd2 (patchF o d cp t) u v) =
      (fun v => (bicubicEval_dv cp u v) 0) by
    funext v; exact pd2_patchF o d cp t u v]
  unfold bicubicEval_dv bicubicEval_dvv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3' v ⟨k.val / 4, by omega⟩).const_mul
      (bern3 u ⟨k.val % 4, by omega⟩)).mul_const (cp k 0))) using 1
  · ext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem abs_bicubic_du_uu_le (cp : Fin 16 → Vec3) (M : ℝ) (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M)
    {u v : ℝ} (hu0:0≤u) (hu1:u≤1) (hv0:0≤v) (hv1:v≤1) (a : Fin 3) :
    |(bicubicEval_duu cp u v) a| ≤ 192 * M := by
  unfold bicubicEval_duu
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc |∑ k : Fin 16, (bern3'' u ⟨k.val % 4, by omega⟩ * bern3 v ⟨k.val / 4, by omega⟩) * cp k a|
      ≤ 16 * (12 * M) := by
        apply abs_sum_scalar_bound
        · intro k
          rw [abs_mul, abs_mul]
          have h1 := abs_bern3''_le hu0 hu1 ⟨k.val % 4, by omega⟩
          have h2 := bern3_nonneg hv0 hv1 ⟨k.val / 4, by omega⟩
          have h2' : |bern3 v ⟨k.val / 4, by omega⟩| ≤ 1 := by
            rw [abs_of_nonneg h2]
            exact bern3_le_one hv0 hv1 ⟨k.val / 4, by omega⟩
          have h12 : |bern3'' u ⟨k.val % 4, by omega⟩| * |bern3 v ⟨k.val / 4, by omega⟩| ≤ 12 * 1 :=
            mul_le_mul h1 h2' (abs_nonneg _) (by norm_num)
          have h123 := mul_le_mul h12 (hM k a) (abs_nonneg _) (by norm_num : 0 ≤ (12:ℝ)*1)
          simpa [mul_assoc] using h123
    _ = 192 * M := by ring


theorem patchG_hasDerivAt_u (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun u => patchG o d cp t u v) ((bicubicEval_du cp u v) 1) u := by
  unfold patchG bezPatchContact bicubicEval bicubicEval_du
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 u ⟨k.val % 4, by omega⟩).mul_const
      (bern3 v ⟨k.val / 4, by omega⟩)).mul_const (cp k 1))).sub_const ((o 1) + t * (d 1)) using 1
  · ext y <;> simp [bern33] <;> ring_nf

theorem patchG_hasDerivAt_v (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun v => patchG o d cp t u v) ((bicubicEval_dv cp u v) 1) v := by
  unfold patchG bezPatchContact bicubicEval bicubicEval_dv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 v ⟨k.val / 4, by omega⟩).const_mul
      (bern3 u ⟨k.val % 4, by omega⟩)).mul_const (cp k 1))).sub_const ((o 1) + t * (d 1)) using 1
  · ext y
    simp [bern33, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem pd1_patchG (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    pd1 (patchG o d cp t) u v = (bicubicEval_du cp u v) 1 :=
  (patchG_hasDerivAt_u o d cp t u v).deriv

theorem pd2_patchG (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    pd2 (patchG o d cp t) u v = (bicubicEval_dv cp u v) 1 :=
  (patchG_hasDerivAt_v o d cp t u v).deriv


/-- HasDerivAt for `u ↦ pd1 patchG u v` (derivative = pdd11). -/
theorem pd1_patchG_hasDerivAt_u (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun u => pd1 (patchG o d cp t) u v)
      ((bicubicEval_duu cp u v) 1) u := by
  rw [show (fun u => pd1 (patchG o d cp t) u v) =
      (fun u => (bicubicEval_du cp u v) 1) by
    funext u; exact pd1_patchG o d cp t u v]
  -- derivative of (fun u => (bicubicEval_du cp u v) 1) is (bicubicEval_duu cp u v) 1
  unfold bicubicEval_du bicubicEval_duu
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3' u ⟨k.val % 4, by omega⟩).mul_const
      (bern3 v ⟨k.val / 4, by omega⟩)).mul_const (cp k 1))) using 1
  · ext y; simp <;> ring_nf

/-- HasDerivAt for `v ↦ pd1 patchG u v` (derivative = pdd12). -/
theorem pd1_patchG_hasDerivAt_v (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun v => pd1 (patchG o d cp t) u v)
      ((bicubicEval_duv cp u v) 1) v := by
  rw [show (fun v => pd1 (patchG o d cp t) u v) =
      (fun v => (bicubicEval_du cp u v) 1) by
    funext v; exact pd1_patchG o d cp t u v]
  unfold bicubicEval_du bicubicEval_duv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 v ⟨k.val / 4, by omega⟩).const_mul
      (bern3' u ⟨k.val % 4, by omega⟩)).mul_const (cp k 1))) using 1
  · ext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]


theorem pd2_patchG_hasDerivAt_u (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun u => pd2 (patchG o d cp t) u v)
      ((bicubicEval_duv cp u v) 1) u := by
  rw [show (fun u => pd2 (patchG o d cp t) u v) =
      (fun u => (bicubicEval_dv cp u v) 1) by
    funext u; exact pd2_patchG o d cp t u v]
  unfold bicubicEval_dv bicubicEval_duv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3 u ⟨k.val % 4, by omega⟩).mul_const
      (bern3' v ⟨k.val / 4, by omega⟩)).mul_const (cp k 1))) using 1
  · ext y; simp <;> ring_nf

theorem pd2_patchG_hasDerivAt_v (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    HasDerivAt (fun v => pd2 (patchG o d cp t) u v)
      ((bicubicEval_dvv cp u v) 1) v := by
  rw [show (fun v => pd2 (patchG o d cp t) u v) =
      (fun v => (bicubicEval_dv cp u v) 1) by
    funext v; exact pd2_patchG o d cp t u v]
  unfold bicubicEval_dv bicubicEval_dvv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  convert (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    ((hasDerivAt_bern3' v ⟨k.val / 4, by omega⟩).const_mul
      (bern3 u ⟨k.val % 4, by omega⟩)).mul_const (cp k 1))) using 1
  · ext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- C2Seg for the patch contact function patchG on [0,1]^2, with K = 192*M. -/
theorem patchG_C2Seg (o d : Vec3) (cp : Fin 16 → Vec3) (t M : ℝ)
    (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M) :
    C2Seg (patchG o d cp t) 0 1 0 1 (192*M) where
  row := by
    intro v hv u hu
    exact (patchG_hasDerivAt_u o d cp t u v).differentiableAt.differentiableWithinAt
  col := by
    intro u hu v hv
    exact (patchG_hasDerivAt_v o d cp t u v).differentiableAt.differentiableWithinAt
  row₁ := by
    intro v hv u hu
    exact (pd1_patchG_hasDerivAt_u o d cp t u v).differentiableAt.differentiableWithinAt
  col₁ := by
    intro u hu v hv
    exact (pd1_patchG_hasDerivAt_v o d cp t u v).differentiableAt.differentiableWithinAt
  row₂ := by
    intro v hv u hu
    exact (pd2_patchG_hasDerivAt_u o d cp t u v).differentiableAt.differentiableWithinAt
  col₂ := by
    intro u hu v hv
    exact (pd2_patchG_hasDerivAt_v o d cp t u v).differentiableAt.differentiableWithinAt
  b₁₁ := by
    intro u hu v hv
    rw [show pdd11 (patchG o d cp t) u v = (bicubicEval_duu cp u v) 1 from
      (pd1_patchG_hasDerivAt_u o d cp t u v).deriv]
    exact abs_bicubic_du_uu_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 1
  b₁₂ := by
    intro u hu v hv
    rw [show pdd12 (patchG o d cp t) u v = (bicubicEval_duv cp u v) 1 from
      (pd1_patchG_hasDerivAt_v o d cp t u v).deriv]
    exact (abs_bicubic_uv_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 1).trans (by nlinarith [hM0])
  b₂₁ := by
    intro u hu v hv
    rw [show pdd21 (patchG o d cp t) u v = (bicubicEval_duv cp u v) 1 from
      (pd2_patchG_hasDerivAt_u o d cp t u v).deriv]
    exact (abs_bicubic_uv_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 1).trans (by nlinarith [hM0])
  b₂₂ := by
    intro u hu v hv
    rw [show pdd22 (patchG o d cp t) u v = (bicubicEval_dvv cp u v) 1 from
      (pd2_patchG_hasDerivAt_v o d cp t u v).deriv]
    exact abs_bicubic_vv_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 1


/-- C2Seg for the patch contact function patchF on [0,1]^2, with K = 192*M. -/
theorem patchF_C2Seg (o d : Vec3) (cp : Fin 16 → Vec3) (t M : ℝ)
    (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M) :
    C2Seg (patchF o d cp t) 0 1 0 1 (192*M) where
  row := by
    intro v hv u hu
    exact (patchF_hasDerivAt_u o d cp t u v).differentiableAt.differentiableWithinAt
  col := by
    intro u hu v hv
    exact (patchF_hasDerivAt_v o d cp t u v).differentiableAt.differentiableWithinAt
  row₁ := by
    intro v hv u hu
    exact (pd1_patchF_hasDerivAt_u o d cp t u v).differentiableAt.differentiableWithinAt
  col₁ := by
    intro u hu v hv
    exact (pd1_patchF_hasDerivAt_v o d cp t u v).differentiableAt.differentiableWithinAt
  row₂ := by
    intro v hv u hu
    exact (pd2_patchF_hasDerivAt_u o d cp t u v).differentiableAt.differentiableWithinAt
  col₂ := by
    intro u hu v hv
    exact (pd2_patchF_hasDerivAt_v o d cp t u v).differentiableAt.differentiableWithinAt
  b₁₁ := by
    intro u hu v hv
    rw [show pdd11 (patchF o d cp t) u v = (bicubicEval_duu cp u v) 0 from
      (pd1_patchF_hasDerivAt_u o d cp t u v).deriv]
    exact abs_bicubic_du_uu_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 0
  b₁₂ := by
    intro u hu v hv
    rw [show pdd12 (patchF o d cp t) u v = (bicubicEval_duv cp u v) 0 from
      (pd1_patchF_hasDerivAt_v o d cp t u v).deriv]
    exact (abs_bicubic_uv_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 0).trans (by nlinarith [hM0])
  b₂₁ := by
    intro u hu v hv
    rw [show pdd21 (patchF o d cp t) u v = (bicubicEval_duv cp u v) 0 from
      (pd2_patchF_hasDerivAt_u o d cp t u v).deriv]
    exact (abs_bicubic_uv_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 0).trans (by nlinarith [hM0])
  b₂₂ := by
    intro u hu v hv
    rw [show pdd22 (patchF o d cp t) u v = (bicubicEval_dvv cp u v) 0 from
      (pd2_patchF_hasDerivAt_v o d cp t u v).deriv]
    exact abs_bicubic_vv_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 0


/-- `bezpatch_newton_quadratic` with C2Seg and partial bounds derived from the
    16 control points: only the determinant lower bound δ and the ball radius
    remain as data (the former necessarily so, as in M14). -/
theorem bezpatch_newton_quadratic_of_controls (o d : Vec3) (cp : Fin 16 → Vec3)
    (t M δ : ℝ) (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M)
    (hMpos : 0 < M) {u₀ v₀ u v : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) 1) (hu₀ : u₀ ∈ Set.Icc (0:ℝ) 1)
    (hv : v ∈ Set.Icc (0:ℝ) 1) (hv₀ : v₀ ∈ Set.Icc (0:ℝ) 1)
    (hroot : patchF o d cp t u₀ v₀ = 0 ∧ patchG o d cp t u₀ v₀ = 0)
    (hden : δ ≤ |jacDet (patchF o d cp t) (patchG o d cp t) u v|) (hδ : 0 < δ)
    (hE : |u - u₀| + |v - v₀| ≤ 48*M / (192*M)) :
    |(newton2Step (patchF o d cp t) (patchG o d cp t) u v).1 - u₀| ≤
        (10 * (48*M) * (192*M) / δ) * (|u - u₀| + |v - v₀|) ^ 2 ∧
    |(newton2Step (patchF o d cp t) (patchG o d cp t) u v).2 - v₀| ≤
        (8 * (48*M) * (192*M) * (|u - u₀| + |v - v₀|) ^ 2 + 2 * (48*M)^2 *
          (|u - u₀| + |v - v₀|)) / δ := by
  apply bezpatch_newton_quadratic o d cp t 0 1 0 1 (192*M) (48*M) δ
      (patchF_C2Seg o d cp t M hM hM0) (patchG_C2Seg o d cp t M hM hM0)
      (by positivity) (by positivity) hu hu₀ hv hv₀ hroot
  · rw [pd1_patchF]
    exact abs_bicubic_du_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 0
  · rw [pd2_patchF]
    exact abs_bicubic_dv_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 0
  · rw [pd1_patchG]
    exact abs_bicubic_du_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 1
  · rw [pd2_patchG]
    exact abs_bicubic_dv_le cp M hM hM0 hu.1 hu.2 hv.1 hv.2 1
  · rw [pd1_patchF]
    exact abs_bicubic_du_le cp M hM hM0 hu₀.1 hu₀.2 hv₀.1 hv₀.2 0
  · rw [pd2_patchF]
    exact abs_bicubic_dv_le cp M hM hM0 hu₀.1 hu₀.2 hv₀.1 hv₀.2 0
  · rw [pd1_patchG]
    exact abs_bicubic_du_le cp M hM hM0 hu₀.1 hu₀.2 hv₀.1 hv₀.2 1
  · rw [pd2_patchG]
    exact abs_bicubic_dv_le cp M hM hM0 hu₀.1 hu₀.2 hv₀.1 hv₀.2 1
  · exact hden
  · exact hδ
  · exact hE


end
end LightRT.Geom
