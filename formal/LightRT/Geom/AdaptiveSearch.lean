import Mathlib
import LightRT.Geom.BezPatchSubdivision
import LightRT.Geom.BezPatchConvergence

namespace LightRT.Geom
noncomputable section
open Classical

/-- A genuine global patch hit at parameter `t` with local parameters `u,v`. -/
def GlobalPatchHit (o d : Vec3) (cp : Fin 16 → Vec3) (tmin tbest t u v : ℝ) : Prop :=
  tmin ≤ t ∧ t < tbest ∧ u ∈ Set.Icc (0:ℝ) 1 ∧ v ∈ Set.Icc (0:ℝ) 1 ∧
    o + t • d = bicubicEval cp u v

/-- Abstract per-cell Newton solver contract. -/
structure CellSolve (o d : Vec3) (global : Fin 16 → Vec3) (tmin tbest : ℝ) where
  solve : PatchCell → Option ℝ
  sound : ∀ c (hc : Represents global c) t, solve c = some t →
    ∃ u v, GlobalPatchHit o d c.cp tmin tbest t u v
  complete : ∀ c (hc : Represents global c) tstar u v,
    GlobalPatchHit o d global tmin tbest tstar u v →
    u ∈ Set.Icc c.u0 c.u1 → v ∈ Set.Icc c.v0 c.v1 →
    ∃ t', solve c = some t' ∧ t' ≤ tstar

/-- Adaptive search: solve each cell, keep the smallest candidate. -/
def adaptiveSearch (cells : List PatchCell) (solve : PatchCell → Option ℝ) : Option ℝ :=
  (cells.filterMap solve).minimum

lemma adaptiveSearch_some_mem (cells : List PatchCell) (solve : PatchCell → Option ℝ)
    {m : ℝ} (hres : adaptiveSearch cells solve = some m) : some m ∈ cells.map solve := by
  change (cells.filterMap solve).minimum = (some m : WithTop ℝ) at hres
  have hmem : m ∈ cells.filterMap solve := List.minimum_mem hres
  simpa using hmem

lemma adaptiveSearch_le (cells : List PatchCell) (solve : PatchCell → Option ℝ)
    (c : PatchCell) (t : ℝ) (hc : c ∈ cells) (hsolve : solve c = some t)
    {m : ℝ} (hres : adaptiveSearch cells solve = some m) : m ≤ t := by
  change (cells.filterMap solve).minimum = (some m : WithTop ℝ) at hres
  exact List.minimum_le_of_mem (by simpa using ⟨c, hc, hsolve⟩) hres

theorem adaptiveSearch_sound (o d : Vec3) (global : Fin 16 → Vec3)
    (tmin tbest : ℝ) (S : CellSolve o d global tmin tbest)
    (cells : List PatchCell) (hrep : ∀ c ∈ cells, Represents global c)
    (huw : ∀ c ∈ cells, c.u0 ≤ c.u1) (hvw : ∀ c ∈ cells, c.v0 ≤ c.v1)
    (hcell : ∀ c ∈ cells, 0 ≤ c.u0 ∧ c.u1 ≤ 1 ∧ 0 ≤ c.v0 ∧ c.v1 ≤ 1)
    {m : ℝ} (hres : adaptiveSearch cells S.solve = some m) :
    ∃ u v, GlobalPatchHit o d global tmin tbest m u v := by
  have hmem := adaptiveSearch_some_mem cells S.solve hres
  simp at hmem
  rcases hmem with ⟨c, hc, hsolve⟩
  rcases S.sound c (hrep c hc) m hsolve with ⟨uv, hv, hhit⟩
  let s : ℝ := uv
  let r : ℝ := hv
  have hs : s ∈ Set.Icc (0:ℝ) 1 := by simpa [s] using hhit.2.2.1
  have hr : r ∈ Set.Icc (0:ℝ) 1 := by simpa [r] using hhit.2.2.2.1
  have hrep_c := hrep c hc s hs r hr
  refine ⟨c.u0 + (c.u1 - c.u0) * s, c.v0 + (c.v1 - c.v0) * r, ?_, ?_, ?_, ?_, ?_⟩
  · exact hhit.1
  · exact hhit.2.1
  · constructor <;> nlinarith [hs.1, hs.2, huw c hc, (hcell c hc).1, (hcell c hc).2.1]
  · constructor <;> nlinarith [hr.1, hr.2, hvw c hc, (hcell c hc).2.2.1, (hcell c hc).2.2]
  · rw [← hrep_c, ← hhit.2.2.2.2]

theorem adaptiveSearch_nearest (o d : Vec3) (global : Fin 16 → Vec3)
    (tmin tbest : ℝ) (S : CellSolve o d global tmin tbest)
    (cells : List PatchCell) (hrep : ∀ c ∈ cells, Represents global c)
    (huw : ∀ c ∈ cells, c.u0 < c.u1) (hvw : ∀ c ∈ cells, c.v0 < c.v1)
    (hcell : ∀ c ∈ cells, 0 ≤ c.u0 ∧ c.u1 ≤ 1 ∧ 0 ≤ c.v0 ∧ c.v1 ≤ 1)
    {tstar u v : ℝ}
    (hnearest : GlobalPatchHit o d global tmin tbest tstar u v)
    (hmin : ∀ t, (∃ u v, GlobalPatchHit o d global tmin tbest t u v) → tstar ≤ t)
    {c : PatchCell} (hc : c ∈ cells)
    (huc : u ∈ Set.Icc c.u0 c.u1) (hvc : v ∈ Set.Icc c.v0 c.v1) :
    adaptiveSearch cells S.solve = some tstar := by
  rcases S.complete c (hrep c hc) tstar u v hnearest huc hvc with ⟨t', hsolve, hle⟩
  cases hres : adaptiveSearch cells S.solve with
  | none =>
      change (cells.filterMap S.solve).minimum = (none : WithTop ℝ) at hres
      have hmin' := hres
      have hempty : cells.filterMap S.solve = [] := List.minimum_eq_top.mp hmin'
      have hmem' : t' ∈ cells.filterMap S.solve := by simpa using ⟨c, hc, hsolve⟩
      simp [hempty] at hmem'
  | some m =>
      have hm_le_t' := adaptiveSearch_le cells S.solve c t' hc hsolve hres
      have hm_ge : tstar ≤ m := by
        rcases adaptiveSearch_sound o d global tmin tbest S cells hrep (fun c hc => le_of_lt (huw c hc)) (fun c hc => le_of_lt (hvw c hc)) hcell hres with ⟨um, vm, hhitm⟩
        exact hmin m ⟨um, vm, hhitm⟩
      have h_eq : m = tstar := le_antisymm (le_trans hm_le_t' hle) hm_ge
      simpa [h_eq] using hres

end
end LightRT.Geom
