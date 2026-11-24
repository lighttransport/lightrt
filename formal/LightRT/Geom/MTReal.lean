/-
  Stage 1: Möller–Trumbore over ℝ (baseline, non-watertight in floating point).
  Mirrors `tri_mt_one` in lightrt_c_tri.c, including the `|det| < ε` rejection.
-/
import LightRT.Geom.Basic

namespace LightRT.Geom
noncomputable section
open Matrix

/-- Möller–Trumbore with determinant threshold `ε`; returns `(t, u, v)`. -/
def mtReal (o d v0 v1 v2 : Vec3) (ε tmin tbest : ℝ) : Option (ℝ × ℝ × ℝ) :=
  let e1 := v1 - v0
  let e2 := v2 - v0
  let p := crossProduct d e2
  let det := e1 ⬝ᵥ p
  if -ε < det ∧ det < ε then none else
  let tv := o - v0
  let u := (tv ⬝ᵥ p) / det
  if u < 0 ∨ 1 < u then none else
  let q := crossProduct tv e1
  let v := (d ⬝ᵥ q) / det
  if v < 0 ∨ 1 < u + v then none else
  let t := (e2 ⬝ᵥ q) / det
  if t < tmin ∨ tbest ≤ t then none else some (t, u, v)

/-- Helper: Cramer's rule for the 3×3 system `[-d | e1 | e2] (t,u,v) = o - v0`. -/
theorem mt_cramer (o d v0 v1 v2 : Vec3) (t u v : ℝ)
    (hdet : (v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0)) ≠ 0) :
    o + t • d = v0 + u • (v1 - v0) + v • (v2 - v0) ↔
      (u = ((o - v0) ⬝ᵥ (crossProduct d (v2 - v0))) / ((v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0))) ∧
       v = (d ⬝ᵥ (crossProduct (o - v0) (v1 - v0))) / ((v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0))) ∧
       t = ((v2 - v0) ⬝ᵥ (crossProduct (o - v0) (v1 - v0))) / ((v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0)))) := by
  simp only [cross_apply, dotProduct, Fin.sum_univ_three, Pi.sub_apply, cons_val_zero, cons_val_one, cons_val_two, LinearMap.mk₂_apply, vecHead, vecTail, Function.comp_apply, Fin.succ_zero_eq_one] at hdet ⊢
  rw [funext_iff, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩ <;> rw [eq_div_iff hdet]
    · linear_combination (-(d 1 * (v2 2 - v0 2) - d 2 * (v2 1 - v0 1))) * h0 - (d 2 * (v2 0 - v0 0) - d 0 * (v2 2 - v0 2)) * h1 - (d 0 * (v2 1 - v0 1) - d 1 * (v2 0 - v0 0)) * h2
    · linear_combination (-((v1 1 - v0 1) * d 2 - (v1 2 - v0 2) * d 1)) * h0 - ((v1 2 - v0 2) * d 0 - (v1 0 - v0 0) * d 2) * h1 - ((v1 0 - v0 0) * d 1 - (v1 1 - v0 1) * d 0) * h2
    · linear_combination (-((v1 1 - v0 1) * (v2 2 - v0 2) - (v1 2 - v0 2) * (v2 1 - v0 1))) * h0 - ((v1 2 - v0 2) * (v2 0 - v0 0) - (v1 0 - v0 0) * (v2 2 - v0 2)) * h1 - ((v1 0 - v0 0) * (v2 1 - v0 1) - (v1 1 - v0 1) * (v2 0 - v0 0)) * h2
  · rintro ⟨rfl, rfl, rfl⟩
    generalize hD : (v1 0 - v0 0) * (d 1 * (v2 2 - v0 2) - d 2 * (v2 1 - v0 1)) +
        (v1 1 - v0 1) * (d 2 * (v2 0 - v0 0) - d 0 * (v2 2 - v0 2)) +
      (v1 2 - v0 2) * (d 0 * (v2 1 - v0 1) - d 1 * (v2 0 - v0 0)) = D at hdet ⊢
    refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> rw [← hD] <;> ring

/-- Soundness: a reported hit is a geometric hit with the reported barycentrics. -/
theorem mtReal_sound {o d v0 v1 v2 : Vec3} {ε tmin tbest t u v : ℝ} (hε : 0 < ε)
    (h : mtReal o d v0 v1 v2 ε tmin tbest = some (t, u, v)) :
    HitsTriangleAt o d v0 v1 v2 tmin tbest t ∧
      o + t • d = v0 + u • (v1 - v0) + v • (v2 - v0) := by
  unfold mtReal at h
  simp only at h
  split_ifs at h with h1 h2 h3 h4
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hdet : (v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0)) ≠ 0 := by
    intro h0; rw [h0] at h1; exact h1 ⟨by linarith, hε⟩
  have he := (mt_cramer o d v0 v1 v2 _ _ _ hdet).2 ⟨rfl, rfl, rfl⟩
  push_neg at h2 h3 h4
  exact ⟨⟨h4.1, h4.2, _, _, h2.1, h3.1, h3.2, he⟩, he⟩

/-- Completeness away from the threshold: if `|det| ≥ ε` (and `ε > 0`, or the
    ray is not parallel to the plane when `ε = 0`) every geometric hit is found. -/
theorem mtReal_complete {o d v0 v1 v2 : Vec3} {ε tmin tbest t : ℝ}
    (hdet : ε ≤ |(v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0))|) (hdet0 : (v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0)) ≠ 0)
    (h : HitsTriangleAt o d v0 v1 v2 tmin tbest t) :
    ∃ u v, mtReal o d v0 v1 v2 ε tmin tbest = some (t, u, v) := by
  obtain ⟨ht1, ht2, u, v, hu, hv, huv, he⟩ := h
  obtain ⟨eu, ev, et⟩ := (mt_cramer o d v0 v1 v2 t u v hdet0).1 he
  refine ⟨u, v, ?_⟩
  unfold mtReal; simp only
  have hn : ¬(-ε < (v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0)) ∧
      (v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0)) < ε) := by
    rintro ⟨a, b⟩; rcases abs_cases ((v1 - v0) ⬝ᵥ (crossProduct d (v2 - v0))) with ⟨c, _⟩ | ⟨c, _⟩ <;>
      linarith
  rw [if_neg hn, ← eu, ← ev, ← et, if_neg (by push_neg; exact ⟨hu, by linarith⟩),
    if_neg (by push_neg; exact ⟨hv, huv⟩), if_neg (by push_neg; exact ⟨ht1, ht2⟩)]

end
end LightRT.Geom
