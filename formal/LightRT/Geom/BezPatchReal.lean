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

end
end LightRT.Geom
