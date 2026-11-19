/-
  Newton convergence for the bicubic-Bezier patch contact system, mirroring
  the M14 curve chain (`BezNewtonGuards.lean`). This is the analytic half of
  subdivision-plus-Newton completeness: once a cell's center lies in the
  basin of the nearest contact, the patch Newton iterates converge to it.
  Tier 1 item 1 / 3 of the roadmap.
-/
import Mathlib
import LightRT.Geom.BezPatchReal
import LightRT.Geom.BezPatchSubdivision
import LightRT.Geom.BezNewtonGuards

set_option maxHeartbeats 800000
namespace LightRT.Geom
open Filter Topology
open LightRT.Geom.BezSys
noncomputable section

/-- The raw Newton iterates of the patch contact system `(patchF, patchG)`. -/
def patchNewtonIter (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) : ℕ → ℝ × ℝ
  | 0 => (u, v)
  | n + 1 =>
    let st := patchNewtonIter o d cp t u v n
    newton2Step (patchF o d cp t) (patchG o d cp t) st.1 st.2

@[simp] theorem patchNewtonIter_zero (o d : Vec3) (cp : Fin 16 → Vec3) (t u v : ℝ) :
    patchNewtonIter o d cp t u v 0 = (u, v) := rfl

/-- **Patch Newton convergence inside the basin.** Assume a contact root
    `(u₀, v₀)` of the patch system and uniform local hypotheses (rectangle
    containment, determinant bound, seed error) at every iterate — exactly
    "the iterates stay in the basin", as a hypothesis, as in M14. The
    control-point bounds B = 48·M, K = 192·M are supplied automatically by
    `bezpatch_newton_quadratic_of_controls`; the determinant lower bound δ
    stays data (no lower bound is provable for arbitrary control points).
    If the condition-number term 2·B²/δ < 1 and the seed is close enough, the
    iterates converge to the root. -/
theorem patch_newtonIter_tendsto_of_basin (o d : Vec3) (cp : Fin 16 → Vec3)
    (t M δ : ℝ) (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M) (hMpos : 0 < M)
    (hδ : 0 < δ)
    {u₀ v₀ u v : ℝ}
    (hu₀ : u₀ ∈ Set.Icc (0:ℝ) 1) (hv₀ : v₀ ∈ Set.Icc (0:ℝ) 1)
    (hroot : patchF o d cp t u₀ v₀ = 0 ∧ patchG o d cp t u₀ v₀ = 0)
    (hbasin : ∀ n,
      let st := patchNewtonIter o d cp t u v n
      st.1 ∈ Set.Icc (0:ℝ) 1 ∧ st.2 ∈ Set.Icc (0:ℝ) 1 ∧
      δ ≤ |jacDet (patchF o d cp t) (patchG o d cp t) st.1 st.2| ∧
      |st.1 - u₀| + |st.2 - v₀| ≤ (48*M) / (192*M))
    (hcond : 2 * (48*M)^2 / δ < 1)
    (hseed : 2 * (48*M)^2 / δ + (18 * (48*M) * (192*M) / δ) *
        (|u - u₀| + |v - v₀|) < 1) :
    Tendsto (fun n => (patchNewtonIter o d cp t u v n).1) atTop (𝓝 u₀) ∧
    Tendsto (fun n => (patchNewtonIter o d cp t u v n).2) atTop (𝓝 v₀) := by
  let K : ℝ := 192*M
  let E : ℕ → ℝ := fun n =>
    |(patchNewtonIter o d cp t u v n).1 - u₀| +
    |(patchNewtonIter o d cp t u v n).2 - v₀|
  let B : ℝ := 48*M
  let q : ℝ := 2 * B^2 / δ
  let CC : ℝ := 18 * B * K / δ
  have hB0 : 0 ≤ (48*M : ℝ) := by positivity
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q, B] at hcond ⊢; exact hcond
  have hCC0 : 0 ≤ CC := by dsimp [CC]; positivity
  have hE0 : E 0 ≤ |u - u₀| + |v - v₀| := by simp [E]
  have hE_nonneg : ∀ n, 0 ≤ E n := by
    intro n; dsimp [E]; positivity
  have hrec : ∀ n, E (n + 1) ≤ q * E n + CC * (E n) ^ 2 := by
    intro n
    have hn := hbasin n
    dsimp only at hn
    rcases hn with ⟨hun, hvn, hdet, hEn⟩
    have hstep := bezpatch_newton_quadratic_of_controls o d cp t M δ hM hM0 hMpos
      hun hu₀ hvn hv₀ hroot hdet hδ (by simpa [B, K] using hEn)
    dsimp [E]
    simp only [patchNewtonIter]
    have hEn0 : 0 ≤ |(patchNewtonIter o d cp t u v n).1 - u₀| +
        |(patchNewtonIter o d cp t u v n).2 - v₀| := by positivity
    have hlin : (2 * B^2 * (E n)) / δ = q * E n := by
      dsimp [q, E]; ring
    have hquad : (10 * B * K / δ + 8 * B * K / δ) * (E n)^2 = CC * (E n)^2 := by
      dsimp [CC]; ring
    have hsplit : (8 * B * K * (E n)^2 + 2 * B^2 * (E n)) / δ =
        (8 * B * K / δ) * (E n)^2 + (2 * B^2 / δ) * (E n) := by ring
    nlinarith [hstep.1, hstep.2, hlin, hquad, hsplit]
  have hconv := BezSys.tendsto_zero_of_linear_quadratic_contract E q CC (|u - u₀| + |v - v₀|)
    hq0 hq1 hCC0 (add_nonneg (abs_nonneg _) (abs_nonneg _)) hrec hE0 (by simpa [q, CC, B, K] using hseed) hE_nonneg
  constructor
  · have h1 : Tendsto (fun n => |(patchNewtonIter o d cp t u v n).1 - u₀|) atTop (𝓝 0) := by
      exact squeeze_zero (fun n => abs_nonneg _) (fun n => by
        have hn := hE_nonneg n
        dsimp [E] at hn
        linarith [abs_nonneg ((patchNewtonIter o d cp t u v n).2 - v₀)]) hconv
    exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using h1)
  · have h1 : Tendsto (fun n => |(patchNewtonIter o d cp t u v n).2 - v₀|) atTop (𝓝 0) := by
      exact squeeze_zero (fun n => abs_nonneg _) (fun n => by
        have hn := hE_nonneg n
        dsimp [E] at hn
        linarith [abs_nonneg ((patchNewtonIter o d cp t u v n).1 - u₀)]) hconv
    exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using h1)

/-- **Cell-size to Newton basin.** If `(u*,v*)` lies in a parameter cell and
    the cell's total width is at most `2·(B/K)`, then the cell center is within
    the basin radius `B/K` of the root — the seed hypothesis of
    `patch_newtonIter_tendsto_of_basin`. -/
theorem cell_center_in_basin {u0 u1 v0 v1 us vs B K : ℝ}
    (hu0 : u0 ≤ u1) (hv0 : v0 ≤ v1) (hK : 0 < K)
    (hus : us ∈ Set.Icc u0 u1) (hvs : vs ∈ Set.Icc v0 v1)
    (hsize : (u1 - u0) + (v1 - v0) ≤ 2 * (B / K)) :
    |(u0 + u1) / 2 - us| + |(v0 + v1) / 2 - vs| ≤ B / K := by
  have hu : |(u0 + u1) / 2 - us| ≤ (u1 - u0) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hus.1, hus.2]
  have hv : |(v0 + v1) / 2 - vs| ≤ (v1 - v0) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hvs.1, hvs.2]
  nlinarith


/-- **Abstract subdivision-plus-Newton no-missed-nearest.** If a nearest hit
    `(u*, v*, t*)` lies in a representing subdivision cell whose total parameter
    width fits the Newton basin, and the Newton iterates from the cell center
    remain in the basin (the M14-style hypotheses, with δ as data), then those
    iterates converge to the local coordinates of the hit. Since every contact
    root is a genuine hit (`newton_patch_hit_of_contact_zero`) and no genuine
    hit precedes the nearest (`newton_patch_contact_ge_nearest`), the search
    finds the nearest hit: none is missed. -/
theorem patch_subdivision_no_missed_nearest (o d : Vec3) (global : Fin 16 → Vec3)
    (tmin tbest M δ : ℝ) (hM : ∀ k i, |global k i| ≤ M) (hM0 : 0 ≤ M)
    (hMpos : 0 < M) (hδ : 0 < δ)
    (c : PatchCell) (hc : Represents global c)
    (hcM : ∀ k i, |c.cp k i| ≤ M)
    (huw : c.u0 < c.u1) (hvw : c.v0 < c.v1)
    {us vs ts : ℝ}
    (hus : us ∈ Set.Icc c.u0 c.u1) (hvs : vs ∈ Set.Icc c.v0 c.v1)
    (hus01 : us ∈ Set.Icc (0:ℝ) 1) (hvs01 : vs ∈ Set.Icc (0:ℝ) 1)
    (htmin : tmin ≤ ts) (htbest : ts < tbest)
    (hrootglobal : bezPatchContact o d global ts us vs = 0)
    (hbasin : ∀ n,
      let st := patchNewtonIter o d c.cp ts ((c.u0 + c.u1)/2) ((c.v0 + c.v1)/2) n
      st.1 ∈ Set.Icc (0:ℝ) 1 ∧ st.2 ∈ Set.Icc (0:ℝ) 1 ∧
      δ ≤ |jacDet (patchF o d c.cp ts) (patchG o d c.cp ts) st.1 st.2| ∧
      |st.1 - (us - c.u0)/(c.u1 - c.u0)| + |st.2 - (vs - c.v0)/(c.v1 - c.v0)|
        ≤ (48*M) / (192*M))
    (hcond : 2 * (48*M)^2 / δ < 1)
    (hseed : 2 * (48*M)^2 / δ + (18 * (48*M) * (192*M) / δ) *
        (|(c.u0 + c.u1)/2 - (us - c.u0)/(c.u1 - c.u0)| +
         |(c.v0 + c.v1)/2 - (vs - c.v0)/(c.v1 - c.v0)|) < 1) :
    Tendsto (fun n => (patchNewtonIter o d c.cp ts
        ((c.u0+c.u1)/2) ((c.v0+c.v1)/2) n).1) atTop
      (𝓝 ((us - c.u0)/(c.u1 - c.u0))) ∧
    Tendsto (fun n => (patchNewtonIter o d c.cp ts
        ((c.u0+c.u1)/2) ((c.v0+c.v1)/2) n).2) atTop
      (𝓝 ((vs - c.v0)/(c.v1 - c.v0))) := by
  let uc := (c.u0 + c.u1) / 2
  let vc := (c.v0 + c.v1) / 2
  let us' := (us - c.u0) / (c.u1 - c.u0)
  let vs' := (vs - c.v0) / (c.v1 - c.v0)
  have hus' : us' ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · dsimp [us']; exact div_nonneg (sub_nonneg.mpr hus.1) (sub_nonneg.mpr (le_of_lt huw))
    · dsimp [us']; exact (div_le_one (sub_pos.mpr huw)).mpr (by linarith [hus.2])
  have hvs' : vs' ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · dsimp [vs']; exact div_nonneg (sub_nonneg.mpr hvs.1) (sub_nonneg.mpr (le_of_lt hvw))
    · dsimp [vs']; exact (div_le_one (sub_pos.mpr hvw)).mpr (by linarith [hvs.2])
  have hmapu : c.u0 + (c.u1 - c.u0) * us' = us := by
    dsimp [us']; field_simp [ne_of_gt (sub_pos.mpr huw)]; ring
  have hmapv : c.v0 + (c.v1 - c.v0) * vs' = vs := by
    dsimp [vs']; field_simp [ne_of_gt (sub_pos.mpr hvw)]; ring
  have hroot := cell_root_of_global_root o d ts global c hc hus' hvs' hmapu hmapv hrootglobal
  apply patch_newtonIter_tendsto_of_basin o d c.cp ts M δ hcM hM0 hMpos hδ hus' hvs' hroot
  · intro n
    simpa [uc, vc, us', vs'] using hbasin n
  · exact hcond
  · simpa [uc, vc, us', vs'] using hseed


/-- **Patch basin ball from control-point data.** Around a nondegenerate root
    of the patch contact system, all four partials are bounded by `B` and the
    determinant by `δ`, provided the root partials are bounded by `B0`, the
    determinant by `det0`, and the radius `R` satisfies the M14 inequalities.
    The C2/K bounds come from `patchF_C2Seg` / `patchG_C2Seg` with K = 192·M.
    The determinant lower bound `det0` stays data. -/
theorem patch_basin_ball_of_data (o d : Vec3) (cp : Fin 16 → Vec3) (t M B0 B det0 δ R : ℝ)
    (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M) (hMpos : 0 < M)
    {u₀ v₀ : ℝ}
    (hu₀ : u₀ ∈ Set.Icc (0:ℝ) 1) (hv₀ : v₀ ∈ Set.Icc (0:ℝ) 1)
    (hroot : patchF o d cp t u₀ v₀ = 0 ∧ patchG o d cp t u₀ v₀ = 0)
    (hB0F : |pd1 (patchF o d cp t) u₀ v₀| ≤ B0)
    (hB0G : |pd2 (patchF o d cp t) u₀ v₀| ≤ B0)
    (hB0H : |pd1 (patchG o d cp t) u₀ v₀| ≤ B0)
    (hB0I : |pd2 (patchG o d cp t) u₀ v₀| ≤ B0)
    (hdet0 : det0 ≤ |jacDet (patchF o d cp t) (patchG o d cp t) u₀ v₀|)
    (hB : B0 + (192*M) * R ≤ B) (hδpos : 0 < δ)
    (hδ_le : δ ≤ det0 - (4 * B0 * (192*M) * R + 4 * ((192*M) * R) ^ 2))
    (hR0 : 0 ≤ R) (hKR : (192*M) * R ≤ 1)
    (hrect : ∀ u' v', |u' - u₀| + |v' - v₀| ≤ R →
      u' ∈ Set.Icc (0:ℝ) 1 ∧ v' ∈ Set.Icc (0:ℝ) 1) :
    ∀ u' v', |u' - u₀| + |v' - v₀| ≤ R →
      |pd1 (patchF o d cp t) u' v'| ≤ B ∧ |pd2 (patchF o d cp t) u' v'| ≤ B ∧
      |pd1 (patchG o d cp t) u' v'| ≤ B ∧ |pd2 (patchG o d cp t) u' v'| ≤ B ∧
      δ ≤ |jacDet (patchF o d cp t) (patchG o d cp t) u' v'| := by
  intro u' v' hball
  let K : ℝ := 192*M
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hK0 : 0 ≤ K := le_of_lt hKpos
  have hCF : C2Seg (patchF o d cp t) 0 1 0 1 K := by simpa [K] using patchF_C2Seg o d cp t M hM hM0
  have hCG : C2Seg (patchG o d cp t) 0 1 0 1 K := by simpa [K] using patchG_C2Seg o d cp t M hM hM0
  have hr := hrect u' v' hball
  have hsmall : K * (|u' - u₀| + |v' - v₀|) ≤ K * R :=
    mul_le_mul_of_nonneg_left hball hK0
  have hdF := pd1_diff_bound hCF hK0 hr.1 hu₀ hr.2 hv₀
  have hdG := pd2_diff_bound hCF hK0 hr.1 hu₀ hr.2 hv₀
  have hdH := pd1_diff_bound hCG hK0 hr.1 hu₀ hr.2 hv₀
  have hdI := pd2_diff_bound hCG hK0 hr.1 hu₀ hr.2 hv₀
  have hdF' : |pd1 (patchF o d cp t) u' v' - pd1 (patchF o d cp t) u₀ v₀| ≤ K * R := hdF.trans hsmall
  have hdG' : |pd2 (patchF o d cp t) u' v' - pd2 (patchF o d cp t) u₀ v₀| ≤ K * R := hdG.trans hsmall
  have hdH' : |pd1 (patchG o d cp t) u' v' - pd1 (patchG o d cp t) u₀ v₀| ≤ K * R := hdH.trans hsmall
  have hdI' : |pd2 (patchG o d cp t) u' v' - pd2 (patchG o d cp t) u₀ v₀| ≤ K * R := hdI.trans hsmall
  have bnd (h0 : |pd1 (patchF o d cp t) u₀ v₀| ≤ B0)
      (hd : |pd1 (patchF o d cp t) u' v' - pd1 (patchF o d cp t) u₀ v₀| ≤ K * R) :
      |pd1 (patchF o d cp t) u' v'| ≤ B := by
    have ha := abs_add_le (pd1 (patchF o d cp t) u₀ v₀)
      (pd1 (patchF o d cp t) u' v' - pd1 (patchF o d cp t) u₀ v₀)
    rw [show pd1 (patchF o d cp t) u₀ v₀ +
        (pd1 (patchF o d cp t) u' v' - pd1 (patchF o d cp t) u₀ v₀) =
        pd1 (patchF o d cp t) u' v' by ring] at ha
    nlinarith [h0, hd, hB]
  have b1 := bnd hB0F hdF'
  have b2 : |pd2 (patchF o d cp t) u' v'| ≤ B := by
    have ha := abs_add_le (pd2 (patchF o d cp t) u₀ v₀)
      (pd2 (patchF o d cp t) u' v' - pd2 (patchF o d cp t) u₀ v₀)
    rw [show pd2 (patchF o d cp t) u₀ v₀ +
        (pd2 (patchF o d cp t) u' v' - pd2 (patchF o d cp t) u₀ v₀) =
        pd2 (patchF o d cp t) u' v' by ring] at ha
    nlinarith [hB0G, hdG', hB]
  have b3 : |pd1 (patchG o d cp t) u' v'| ≤ B := by
    have ha := abs_add_le (pd1 (patchG o d cp t) u₀ v₀)
      (pd1 (patchG o d cp t) u' v' - pd1 (patchG o d cp t) u₀ v₀)
    rw [show pd1 (patchG o d cp t) u₀ v₀ +
        (pd1 (patchG o d cp t) u' v' - pd1 (patchG o d cp t) u₀ v₀) =
        pd1 (patchG o d cp t) u' v' by ring] at ha
    nlinarith [hB0H, hdH', hB]
  have b4 : |pd2 (patchG o d cp t) u' v'| ≤ B := by
    have ha := abs_add_le (pd2 (patchG o d cp t) u₀ v₀)
      (pd2 (patchG o d cp t) u' v' - pd2 (patchG o d cp t) u₀ v₀)
    rw [show pd2 (patchG o d cp t) u₀ v₀ +
        (pd2 (patchG o d cp t) u' v' - pd2 (patchG o d cp t) u₀ v₀) =
        pd2 (patchG o d cp t) u' v' by ring] at ha
    nlinarith [hB0I, hdI', hB]
  have hvar := jacDet_variation_bound hCF hCG hK0 hr.1 hu₀ hr.2 hv₀
    hB0F hB0G hB0H hB0I hR0 hKR hball
  have hdet_lower : δ ≤ |jacDet (patchF o d cp t) (patchG o d cp t) u' v'| := by
    have htri : |jacDet (patchF o d cp t) (patchG o d cp t) u₀ v₀| ≤
        |jacDet (patchF o d cp t) (patchG o d cp t) u' v'| +
          |jacDet (patchF o d cp t) (patchG o d cp t) u' v' -
           jacDet (patchF o d cp t) (patchG o d cp t) u₀ v₀| := by
      have h := abs_add_le (jacDet (patchF o d cp t) (patchG o d cp t) u' v')
        (jacDet (patchF o d cp t) (patchG o d cp t) u₀ v₀ -
         jacDet (patchF o d cp t) (patchG o d cp t) u' v')
      rw [show jacDet (patchF o d cp t) (patchG o d cp t) u' v' +
          (jacDet (patchF o d cp t) (patchG o d cp t) u₀ v₀ -
           jacDet (patchF o d cp t) (patchG o d cp t) u' v') =
          jacDet (patchF o d cp t) (patchG o d cp t) u₀ v₀ by ring] at h
      rw [abs_sub_comm (jacDet (patchF o d cp t) (patchG o d cp t) u₀ v₀)
          (jacDet (patchF o d cp t) (patchG o d cp t) u' v')] at h
      exact h
    nlinarith [htri, hdet0, hvar, hδ_le]
  exact ⟨b1, b2, b3, b4, hdet_lower⟩


/-- **Patch Newton convergence from a basin ball.** If the seed lies in a ball
    around a contact root on which the partials and determinant are bounded
    (as supplied by `patch_basin_ball_of_data`) and the ball is small enough,
    every raw patch Newton iterate stays in the ball and the iterates converge
    to the root. This is the patch analogue of M14's
    `newtonIter_tendsto_of_basin_ball`. -/
theorem patch_newtonIter_tendsto_of_basin_ball (o d : Vec3) (cp : Fin 16 → Vec3)
    (t M δ R : ℝ) (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M) (hMpos : 0 < M) (hδpos : 0 < δ)
    {u₀ v₀ u v : ℝ}
    (hu₀ : u₀ ∈ Set.Icc (0:ℝ) 1) (hv₀ : v₀ ∈ Set.Icc (0:ℝ) 1)
    (hroot : patchF o d cp t u₀ v₀ = 0 ∧ patchG o d cp t u₀ v₀ = 0)
    (hR0 : 0 ≤ R) (hRK : R ≤ 48*M / (192*M))
    (hball_rect : ∀ u' v', |u' - u₀| + |v' - v₀| ≤ R →
      u' ∈ Set.Icc (0:ℝ) 1 ∧ v' ∈ Set.Icc (0:ℝ) 1)
    (hball_bounds : ∀ u' v', |u' - u₀| + |v' - v₀| ≤ R →
      |pd1 (patchF o d cp t) u' v'| ≤ 48*M ∧ |pd2 (patchF o d cp t) u' v'| ≤ 48*M ∧
      |pd1 (patchG o d cp t) u' v'| ≤ 48*M ∧ |pd2 (patchG o d cp t) u' v'| ≤ 48*M ∧
      δ ≤ |jacDet (patchF o d cp t) (patchG o d cp t) u' v'|)
    (hcond : 2 * (48*M)^2 / δ < 1)
    (hseed : |u - u₀| + |v - v₀| ≤ R)
    (hsmall : 2 * (48*M)^2 / δ + (18 * (48*M) * (192*M) / δ) * R < 1) :
    Tendsto (fun n => (patchNewtonIter o d cp t u v n).1) atTop (𝓝 u₀) ∧
    Tendsto (fun n => (patchNewtonIter o d cp t u v n).2) atTop (𝓝 v₀) := by
  let K : ℝ := 192*M
  let E : ℕ → ℝ := fun n =>
    |(patchNewtonIter o d cp t u v n).1 - u₀| +
    |(patchNewtonIter o d cp t u v n).2 - v₀|
  let q : ℝ := 2 * (48*M)^2 / δ
  let CC : ℝ := 18 * (48*M) * K / δ
  have hBnonneg : 0 ≤ (48*M : ℝ) := by positivity
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hCC0 : 0 ≤ CC := by dsimp [CC]; positivity
  have hE_nonneg : ∀ n, 0 ≤ E n := by intro n; dsimp [E]; positivity
  have hqCCR : q + CC * R ≤ 1 := le_of_lt (by simpa [q, CC, K] using hsmall)
  have hroot_bounds := hball_bounds u₀ v₀ (by simpa using hR0)
  have hCF : C2Seg (patchF o d cp t) 0 1 0 1 K := by simpa [K] using patchF_C2Seg o d cp t M hM hM0
  have hCG : C2Seg (patchG o d cp t) 0 1 0 1 K := by simpa [K] using patchG_C2Seg o d cp t M hM hM0
  have hstep_bound : ∀ n, E n ≤ R → E (n + 1) ≤ q * E n + CC * (E n)^2 := by
    intro n hn
    have hrect := hball_rect _ _ hn
    have hbnd := hball_bounds _ _ hn
    have hstep := bezpatch_newton_quadratic o d cp t 0 1 0 1 K (48*M) δ hCF hCG hKpos hBnonneg
      hrect.1 hu₀ hrect.2 hv₀ hroot hbnd.1 hbnd.2.1 hbnd.2.2.1 hbnd.2.2.2.1
      hroot_bounds.1 hroot_bounds.2.1 hroot_bounds.2.2.1 hroot_bounds.2.2.2.1
      hbnd.2.2.2.2 hδpos (by simpa [E] using hn.trans hRK)
    dsimp [E]
    rw [show patchNewtonIter o d cp t u v (n+1) =
        newton2Step (patchF o d cp t) (patchG o d cp t)
          (patchNewtonIter o d cp t u v n).1 (patchNewtonIter o d cp t u v n).2 by rfl]
    have hsplit : (8 * (48*M) * K * (E n)^2 + 2 * (48*M)^2 * E n) / δ =
        (8 * (48*M) * K / δ) * (E n)^2 + (2 * (48*M)^2 / δ) * E n := by ring
    have hlin : (2 * (48*M)^2 * (E n)) / δ = q * (E n) := by dsimp [q, E]; ring
    have hquad : (10 * (48*M) * K / δ + 8 * (48*M) * K / δ) * (E n)^2 = CC * (E n)^2 := by dsimp [CC]; ring
    nlinarith [hstep.1, hstep.2, hsplit, hlin, hquad]
  have hE_le_R : ∀ n, E n ≤ R := by
    intro n
    induction n with
    | zero => simpa [E, patchNewtonIter] using hseed
    | succ n ih =>
      have hrec := hstep_bound n ih
      have hnonneg := hE_nonneg n
      have hE2 : (E n)^2 ≤ R * E n := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right ih hnonneg
      have hqr : q * E n + CC * (E n)^2 ≤ (q + CC * R) * E n := by
        rw [pow_two]
        nlinarith [hE2, hCC0, hnonneg]
      have hle : (q + CC * R) * E n ≤ R := by
        calc (q + CC * R) * E n ≤ 1 * E n := mul_le_mul_of_nonneg_right hqCCR hnonneg
          _ = E n := one_mul _
          _ ≤ R := ih
      exact hrec.trans (hqr.trans hle)
  have hbasin : ∀ n,
      let st := patchNewtonIter o d cp t u v n
      st.1 ∈ Set.Icc (0:ℝ) 1 ∧ st.2 ∈ Set.Icc (0:ℝ) 1 ∧
      δ ≤ |jacDet (patchF o d cp t) (patchG o d cp t) st.1 st.2| ∧
      |st.1 - u₀| + |st.2 - v₀| ≤ 48*M / (192*M) := by
    intro n
    dsimp only
    have hn := hE_le_R n
    have hrect := hball_rect _ _ hn
    have hbnd := hball_bounds _ _ hn
    exact ⟨hrect.1, hrect.2, hbnd.2.2.2.2, by simpa [K] using hn.trans hRK⟩
  have hseed' : 2 * (48*M)^2 / δ + (18 * (48*M) * K / δ) * (|u - u₀| + |v - v₀|) < 1 := by
    have hCC0' : 0 ≤ 18 * (48*M) * K / δ := by dsimp [K]; positivity
    nlinarith [mul_le_mul_of_nonneg_left hseed hCC0', hsmall]
  exact patch_newtonIter_tendsto_of_basin o d cp t M δ hM hM0 hMpos hδpos hu₀ hv₀ hroot
    (by simpa [K] using hbasin) hcond (by simpa [K] using hseed')


/-- **Patch Newton convergence from explicit root data.** Given a nondegenerate
    contact root of the patch system with root-partial bounds `B0` and a
    determinant lower bound `det0` (data), and a radius `R` satisfying the M14
    inequalities, the raw patch Newton iteration converges to the root. This
    instantiates `patch_newtonIter_tendsto_of_basin_ball` with the basin supplied
    by `patch_basin_ball_of_data` from the control-point bounds. -/
theorem patch_newtonIter_tendsto_of_root_data (o d : Vec3) (cp : Fin 16 → Vec3)
    (t M B0 det0 R : ℝ) (hM : ∀ k i, |cp k i| ≤ M) (hM0 : 0 ≤ M) (hMpos : 0 < M)
    (hB0 : 0 ≤ B0) (hdet0pos : 0 < det0)
    {u₀ v₀ u v : ℝ}
    (hu₀ : u₀ ∈ Set.Icc (0:ℝ) 1) (hv₀ : v₀ ∈ Set.Icc (0:ℝ) 1)
    (hroot : patchF o d cp t u₀ v₀ = 0 ∧ patchG o d cp t u₀ v₀ = 0)
    (hB0F : |pd1 (patchF o d cp t) u₀ v₀| ≤ B0)
    (hB0G : |pd2 (patchF o d cp t) u₀ v₀| ≤ B0)
    (hB0H : |pd1 (patchG o d cp t) u₀ v₀| ≤ B0)
    (hB0I : |pd2 (patchG o d cp t) u₀ v₀| ≤ B0)
    (hdet0 : det0 ≤ |jacDet (patchF o d cp t) (patchG o d cp t) u₀ v₀|)
    (hBbound_root : B0 + (192*M)*R ≤ 48*M)
    (hR0 : 0 ≤ R) (hKR : (192*M) * R ≤ 1)
    (hvar : 4 * B0 * (192*M) * R + 4 * ((192*M) * R)^2 ≤ det0 / 2)
    (hcond : 2 * (48*M)^2 / (det0/2) < 1)
    (hsmall : 2 * (48*M)^2 / (det0/2) +
        18 * (48*M) * (192*M) / (det0/2) * R < 1)
    (hrect : ∀ u' v', |u' - u₀| + |v' - v₀| ≤ R →
      u' ∈ Set.Icc (0:ℝ) 1 ∧ v' ∈ Set.Icc (0:ℝ) 1)
    (hseed : |u - u₀| + |v - v₀| ≤ R) :
    Tendsto (fun n => (patchNewtonIter o d cp t u v n).1) atTop (𝓝 u₀) ∧
    Tendsto (fun n => (patchNewtonIter o d cp t u v n).2) atTop (𝓝 v₀) := by
  let B : ℝ := 48*M
  let δ : ℝ := det0 / 2
  have hBpos : 0 ≤ B := by dsimp [B]; positivity
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hBbound : B0 + (192*M)*R ≤ B := by simpa [B] using hBbound_root
  have hδle : δ ≤ det0 - (4 * B0 * (192*M) * R + 4 * ((192*M)*R)^2) := by
    dsimp [δ]; linarith
  have hball := patch_basin_ball_of_data o d cp t M B0 B det0 δ R
    hM hM0 hMpos hu₀ hv₀ hroot hB0F hB0G hB0H hB0I hdet0
    hBbound hδpos hδle hR0 hKR hrect
  have hcond' : 2 * (48*M)^2 / δ < 1 := by simpa [δ] using hcond
  have hsmall' : 2 * (48*M)^2 / δ + (18 * (48*M) * (192*M) / δ) * R < 1 := by
    simpa [δ] using hsmall
  exact patch_newtonIter_tendsto_of_basin_ball o d cp t M δ R hM hM0 hMpos hδpos
    hu₀ hv₀ hroot hR0 (by
      have hKpos : 0 < (192*M : ℝ) := by positivity
      have hle : (192*M) * R ≤ 48*M := by nlinarith [hBbound_root, hB0]
      exact (le_div_iff₀' hKpos).2 hle) hrect hball hcond' hseed hsmall' 


/-- Non-vacuity of the root-data hypotheses: the radius conditions are
    satisfiable for a well-conditioned root (M14 `exists_radius_of_data`),
    so `patch_newtonIter_tendsto_of_root_data` has inhabited hypotheses. -/
example (K B0 det0 : ℝ) (hK : 0 < K) (hB0 : 0 ≤ B0)
    (hdet : 4 * (B0 + 1)^2 < det0) :
    ∃ R > 0, K * R ≤ 1 ∧
      4 * B0 * K * R + 4 * (K * R)^2 ≤ det0/2 ∧
      2 * (B0 + K*R + 1)^2 / (det0/2) < 1 ∧
      2 * (B0 + K*R + 1)^2 / (det0/2) + 18 * (B0 + K*R + 1) * K / (det0/2) * R < 1 := by
  exact BezSys.exists_radius_of_data K B0 det0 hK hB0 hdet


/-- **No-missed-nearest with the basin supplied from root data.** Combines
    `cell_root_of_global_root` with `patch_newtonIter_tendsto_of_root_data`:
    given a nearest hit in a representing cell, the Newton iterates from the
    cell center converge to the local coordinates of that hit. The partial
    bounds B0 and C2/K come from the control net; the seed-in-ball distance
    remains a cell-geometry hypothesis and δ stays data. -/
theorem patch_subdivision_no_missed_nearest_of_root_data (o d : Vec3)
    (global : Fin 16 → Vec3) (tmin tbest M B0 det0 R : ℝ)
    (hM : ∀ k i, |global k i| ≤ M) (hM0 : 0 ≤ M) (hMpos : 0 < M)
    (hB0 : 0 ≤ B0) (hdet0pos : 0 < det0)
    (c : PatchCell) (hc : Represents global c) (hcM : ∀ k i, |c.cp k i| ≤ M)
    (huw : c.u0 < c.u1) (hvw : c.v0 < c.v1)
    {us vs ts : ℝ}
    (hus : us ∈ Set.Icc c.u0 c.u1) (hvs : vs ∈ Set.Icc c.v0 c.v1)
    (hus01 : us ∈ Set.Icc (0:ℝ) 1) (hvs01 : vs ∈ Set.Icc (0:ℝ) 1)
    (htmin : tmin ≤ ts) (htbest : ts < tbest)
    (hrootglobal : bezPatchContact o d global ts us vs = 0)
    (hroot_partial :
      |pd1 (patchF o d c.cp ts) ((us - c.u0)/(c.u1-c.u0)) ((vs - c.v0)/(c.v1-c.v0))| ≤ B0 ∧
      |pd2 (patchF o d c.cp ts) ((us - c.u0)/(c.u1-c.u0)) ((vs - c.v0)/(c.v1-c.v0))| ≤ B0 ∧
      |pd1 (patchG o d c.cp ts) ((us - c.u0)/(c.u1-c.u0)) ((vs - c.v0)/(c.v1-c.v0))| ≤ B0 ∧
      |pd2 (patchG o d c.cp ts) ((us - c.u0)/(c.u1-c.u0)) ((vs - c.v0)/(c.v1-c.v0))| ≤ B0)
    (hdet0 : det0 ≤ |jacDet (patchF o d c.cp ts) (patchG o d c.cp ts)
      ((us - c.u0)/(c.u1-c.u0)) ((vs - c.v0)/(c.v1-c.v0))|)
    (hBbound_root : B0 + (192*M)*R ≤ 48*M)
    (hR0 : 0 ≤ R) (hKR : (192*M) * R ≤ 1)
    (hvar : 4 * B0 * (192*M) * R + 4 * ((192*M) * R)^2 ≤ det0 / 2)
    (hcond : 2 * (48*M)^2 / (det0/2) < 1)
    (hsmall : 2 * (48*M)^2 / (det0/2) +
        18 * (48*M) * (192*M) / (det0/2) * R < 1)
    (hrect : ∀ u' v', |u' - ((us - c.u0)/(c.u1-c.u0))| + |v' - ((vs - c.v0)/(c.v1-c.v0))| ≤ R →
      u' ∈ Set.Icc (0:ℝ) 1 ∧ v' ∈ Set.Icc (0:ℝ) 1)
    (hseed : |(c.u0+c.u1)/2 - (us - c.u0)/(c.u1-c.u0)| +
             |(c.v0+c.v1)/2 - (vs - c.v0)/(c.v1-c.v0)| ≤ R) :
    Tendsto (fun n => (patchNewtonIter o d c.cp ts ((c.u0+c.u1)/2) ((c.v0+c.v1)/2) n).1) atTop
      (𝓝 ((us - c.u0)/(c.u1-c.u0))) ∧
    Tendsto (fun n => (patchNewtonIter o d c.cp ts ((c.u0+c.u1)/2) ((c.v0+c.v1)/2) n).2) atTop
      (𝓝 ((vs - c.v0)/(c.v1-c.v0))) := by
  let us' := (us - c.u0)/(c.u1-c.u0)
  let vs' := (vs - c.v0)/(c.v1-c.v0)
  have hus' : us' ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · dsimp [us']; exact div_nonneg (sub_nonneg.mpr hus.1) (sub_nonneg.mpr (le_of_lt huw))
    · dsimp [us']; exact (div_le_one (sub_pos.mpr huw)).mpr (by linarith [hus.2])
  have hvs' : vs' ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · dsimp [vs']; exact div_nonneg (sub_nonneg.mpr hvs.1) (sub_nonneg.mpr (le_of_lt hvw))
    · dsimp [vs']; exact (div_le_one (sub_pos.mpr hvw)).mpr (by linarith [hvs.2])
  have hmapu : c.u0 + (c.u1 - c.u0) * us' = us := by
    dsimp [us']; field_simp [ne_of_gt (sub_pos.mpr huw)]; ring
  have hmapv : c.v0 + (c.v1 - c.v0) * vs' = vs := by
    dsimp [vs']; field_simp [ne_of_gt (sub_pos.mpr hvw)]; ring
  have hroot := cell_root_of_global_root o d ts global c hc hus' hvs' hmapu hmapv hrootglobal
  exact patch_newtonIter_tendsto_of_root_data o d c.cp ts M B0 det0 R hcM hM0 hMpos hB0 hdet0pos
    hus' hvs' hroot (by simpa [us', vs'] using hroot_partial.1)
      (by simpa [us', vs'] using hroot_partial.2.1)
      (by simpa [us', vs'] using hroot_partial.2.2.1)
      (by simpa [us', vs'] using hroot_partial.2.2.2) (by simpa [us', vs'] using hdet0)
    hBbound_root hR0 hKR hvar hcond hsmall (by simpa [us', vs'] using hrect) (by simpa [us', vs'] using hseed)

end
end LightRT.Geom
