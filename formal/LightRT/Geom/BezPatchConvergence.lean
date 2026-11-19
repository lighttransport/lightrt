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
  let B : ℝ := 48*M
  let K : ℝ := 192*M
  let E : ℕ → ℝ := fun n =>
    |(patchNewtonIter o d cp t u v n).1 - u₀| +
    |(patchNewtonIter o d cp t u v n).2 - v₀|
  let q : ℝ := 2 * B^2 / δ
  let CC : ℝ := 18 * B * K / δ
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
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

end
end LightRT.Geom
