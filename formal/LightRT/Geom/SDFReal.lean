/-
  SDF primitive intersector over R: sphere-trace soundness (the limit is a
  surface point), no-overshoot (the trace never steps past a contact) and
  boundary existence, composing SphereTrace / SphereTrace3 /
  SphereTraceConvergence. Tier 1 item 1 of the roadmap.
-/
import Mathlib
import LightRT.Geom.SphereTraceConvergence
import LightRT.Geom.SphereTrace3
import LightRT.Geom.Basic
import LightRT.Geom.CapsuleReal

namespace LightRT.Geom
noncomputable section
open Filter Topology

/-- **SDF trace soundness**: the sphere-trace limit is a surface point. -/
theorem sdf_trace_sound {f : ℝ → ℝ} (hf : Lipschitz1 f)
    {root : ℝ} (hroot : f root ≤ 0) {t : ℝ} (ht : t ≤ root)
    (hnonneg : ∀ s, t ≤ s → s ≤ root → 0 ≤ f s) :
    ∃ L ≤ root, Tendsto (fun n => stTrace f t n) atTop (𝓝 L) ∧ f L = 0 :=
  stTrace_tendsto_contact hf hroot ht hnonneg

/-- **SDF no-overshoot**: for an SDF-like field along a ray with ‖v‖ ≤ 1,
    tracing never steps past a contact at `root`. -/
theorem sdf_ray_no_overshoot {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {x₀ v : X} (hv : ‖v‖ ≤ 1)
    {t₀ root : ℝ} (hstart : t₀ ≤ root)
    (hroot : x₀ + root • v ∈ S) (n : ℕ) :
    stTrace (fun s => Metric.infDist (x₀ + s • v) S) t₀ n ≤ root :=
  stTrace3_le_root S hv (le_of_eq (Metric.infDist_zero_of_mem hroot)) hstart n

/-- **SDF boundary existence**: if the ray starts outside the surface set and
    a later parameter lies in it, some intermediate parameter is on the
    boundary (infDist = 0). -/
theorem sdf_boundary_exists {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {x₀ v : X} (hv : ‖v‖ ≤ 1) {t₀ root : ℝ} (ht : t₀ < root)
    (hout : 0 < Metric.infDist (x₀ + t₀ • v) S)
    (hin : x₀ + root • v ∈ S) :
    ∃ s ∈ Set.Icc t₀ root, Metric.infDist (x₀ + s • v) S = 0 := by
  let g : ℝ → ℝ := fun s => Metric.infDist (x₀ + s • v) S
  have hcont : ContinuousOn g (Set.Icc t₀ root) :=
    (continuous_of_Lipschitz1 (lipschitz1_infDist_line S hv)).continuousOn
  have hzero : g root = 0 := Metric.infDist_zero_of_mem hin
  have hy : (0 : ℝ) ∈ Set.Icc (g root) (g t₀) := by
    constructor
    · rw [hzero]
    · simpa [g] using le_of_lt hout
  have himg := intermediate_value_Icc' (le_of_lt ht) hcont hy
  rcases himg with ⟨s, hs, hsg⟩
  exact ⟨s, hs, by simpa [g] using hsg⟩

/-- The sphere SDF `p ↦ dist p c - r` is 1-Lipschitz. -/
theorem sdfSphere_AbsLipschitz (c : Vec3) (r : ℝ) :
    AbsLipschitz (fun p : Vec3 => dist p c - r) := by
  intro x y
  have h := absLipschitz_infDist ({c} : Set Vec3) x y
  simpa [Metric.infDist_singleton] using h

/-- The sphere SDF along a ray with `‖v‖ ≤ 1` is 1-Lipschitz in the parameter. -/
theorem sdfSphere_line_lipschitz (c : Vec3) (r : ℝ) {x₀ v : Vec3} (hv : ‖v‖ ≤ 1) (t u : ℝ) :
    |(dist (x₀ + t • v) c - r) - (dist (x₀ + u • v) c - r)| ≤ |t - u| := by
  simpa [Metric.infDist_singleton] using
    (infDist_line_lipschitz ({c} : Set Vec3) hv t u)

/-- The curve-capsule intersector over ℝ is exactly the capsule model:
    a constant-radius hair segment is a capsule. Its sound/complete/nearest
    facts are `capsuleReal_sound` / `capsuleReal_complete` and the nearest-hit
    existence from compactness of the capsule section. -/
theorem crvReal_sound {o dir p0 p1 : Vec3} {r tmin tbest t : ℝ}
    (h : capsuleReal o dir p0 p1 r tmin tbest = some t) :
    HitsCapsuleAt o dir p0 p1 r tmin tbest t :=
  capsuleReal_sound h

theorem crvReal_complete {o dir p0 p1 : Vec3} {r tmin tbest t : ℝ}
    (hp0p1 : p0 ≠ p1) (hdir : perpTo dir (p1 - p0) ≠ 0)
    (hhit : HitsCapsuleAt o dir p0 p1 r tmin tbest t) :
    ∃ t', capsuleReal o dir p0 p1 r tmin tbest = some t' ∧ t' ≤ t :=
  capsuleReal_complete hp0p1 hdir hhit

def projXZ (p : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) := !₂[p 0, p 2]

/-- Torus distance (axis y), matching tri_sdf_eval. -/
def sdfTorus (R r : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ‖(!₂[‖projXZ p‖ - R, p 1] : EuclideanSpace ℝ (Fin 2))‖ - r

theorem sdfTorus_AbsLipschitz (R r : ℝ) : AbsLipschitz (sdfTorus R r) := by
  intro p q
  unfold sdfTorus
  simp only [sub_sub_sub_cancel_right]
  -- |‖v p‖ - ‖v q‖| ≤ dist p q
  calc
    |‖(!₂[‖projXZ p‖ - R, p 1] : EuclideanSpace ℝ (Fin 2))‖ -
      ‖(!₂[‖projXZ q‖ - R, q 1] : EuclideanSpace ℝ (Fin 2))‖| ≤
        ‖(!₂[‖projXZ p‖ - R, p 1] : EuclideanSpace ℝ (Fin 2)) -
          (!₂[‖projXZ q‖ - R, q 1] : EuclideanSpace ℝ (Fin 2))‖ := by
            exact abs_norm_sub_norm_le _ _
    _ ≤ dist p q := by
      rw [dist_eq_norm]
      have hsq_le : ‖(!₂[‖projXZ p‖ - R, p 1] : EuclideanSpace ℝ (Fin 2)) -
          (!₂[‖projXZ q‖ - R, q 1] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 ≤ ‖p - q‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
        simp [Fin.sum_univ_two, Fin.sum_univ_three, projXZ]
        -- need (‖projXZ p‖ - ‖projXZ q‖)^2 + (p1-q1)^2 ≤ sum of 3 squared diffs
        have hpq : |‖projXZ p‖ - ‖projXZ q‖| ≤ ‖projXZ p - projXZ q‖ :=
          abs_norm_sub_norm_le _ _
        have hsq : ‖projXZ p - projXZ q‖ ^ 2 =
            ‖(projXZ p - projXZ q) 0‖^2 + ‖(projXZ p - projXZ q) 1‖^2 := by
          rw [PiLp.norm_sq_eq_of_L2]
          simp [Fin.sum_univ_two]
        have hpq2 : (‖projXZ p‖ - ‖projXZ q‖)^2 ≤
            ‖(projXZ p - projXZ q) 0‖^2 + ‖(projXZ p - projXZ q) 1‖^2 := by
          have hpq_sq : |‖projXZ p‖ - ‖projXZ q‖| ^ 2 ≤ ‖projXZ p - projXZ q‖ ^ 2 := by
            exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg (projXZ p - projXZ q))] using hpq)
          rw [sq_abs] at hpq_sq
          nlinarith [hpq_sq]
        simp [projXZ] at hpq2
        nlinarith [hpq2, sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1), sq_nonneg (p 2 - q 2)]
      have h := sq_le_sq.mp hsq_le
      simpa using h

/-- Signed orthant distance φ(v) = ‖max(v,0)‖₂ + min(max_i v_i, 0). -/
def phiBox (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let m : EuclideanSpace ℝ (Fin 3) := !₂[max (v 0) 0, max (v 1) 0, max (v 2) 0]
  ‖m‖ + min (max (v 0) (max (v 1) (v 2))) 0

lemma max_zero_mul (a : ℝ) : max a 0 * a = (max a 0)^2 := by
  by_cases h : a ≤ 0
  · rw [max_eq_right h]; ring
  · rw [max_eq_left (le_of_not_ge h)]; ring

lemma abs_max0_sub_max0 (a b : ℝ) : |max a 0 - max b 0| ≤ |a - b| := by
  simpa using (abs_max_sub_max_le_max a 0 b 0)

lemma mul_max_zero (a : ℝ) : a * max a 0 = (max a 0)^2 := by rw [mul_comm, max_zero_mul]

lemma abs_max3_le (a b c d e f : ℝ) :
    |max a (max b c) - max d (max e f)| ≤ max (max |a-d| |b-e|) |c-f| := by
  have h1 := abs_max_sub_max_le_max a (max b c) d (max e f)
  have h2 := abs_max_sub_max_le_max b c e f
  calc
    |max a (max b c) - max d (max e f)| ≤ max (|a-d|) (|max b c - max e f|) := h1
    _ ≤ max (|a-d|) (max (|b-e|) (|c-f|)) :=
      max_le_max (le_refl (|a-d|)) h2
    _ = max (max |a-d| |b-e|) |c-f| := by rw [← max_assoc]

lemma sq_max3_le_sum (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (max a (max b c))^2 ≤ a^2 + b^2 + c^2 := by
  simp only [max_def]
  split_ifs <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

/-- Mixed case: v outside the orthant, w inside. -/
lemma phiBox_mixed (v w : EuclideanSpace ℝ (Fin 3))
    (hv : ¬ max (v 0) (max (v 1) (v 2)) ≤ 0)
    (hw : max (w 0) (max (w 1) (w 2)) ≤ 0) :
    ‖(!₂[max (v 0) 0, max (v 1) 0, max (v 2) 0] : EuclideanSpace ℝ (Fin 3))‖ -
      max (w 0) (max (w 1) (w 2)) ≤ dist v w := by
      let mv : EuclideanSpace ℝ (Fin 3) := !₂[max (v 0) 0, max (v 1) 0, max (v 2) 0]
      let mw : EuclideanSpace ℝ (Fin 3) := !₂[max (w 0) 0, max (w 1) 0, max (w 2) 0]
      change ‖mv‖ - max (w 0) (max (w 1) (w 2)) ≤ dist v w
      have hmvpos : 0 < ‖mv‖ := by
        rw [norm_pos_iff]
        intro hzero
        have hvpos : ∃ i, 0 < v i := by
          by_contra hn
          push_neg at hn
          have : max (v 0) (max (v 1) (v 2)) ≤ 0 := max_le (hn 0) (max_le (hn 1) (hn 2))
          linarith
        obtain ⟨i, hi⟩ := hvpos
        have hz := congrArg (fun f : EuclideanSpace ℝ (Fin 3) => f i) hzero
        simp [mv] at hz
        fin_cases i <;> simp [mv, max_eq_left (le_of_lt hi)] at hz <;> exact (not_lt_of_ge hz) (by simpa using hi)
      let u : EuclideanSpace ℝ (Fin 3) := (1 / ‖mv‖) • mv
      have hinvpos : 0 < 1 / ‖mv‖ := by positivity
      have hu_nonneg : ∀ i, 0 ≤ u i := by
        intro i; fin_cases i <;> simp [u, mv] <;> positivity
      have hu_norm : ‖u‖ = 1 := by
        simp [u, norm_smul, abs_of_pos (by positivity : 0 < 1 / ‖mv‖)]
        field_simp [hmvpos.ne']
      have hmvin : inner ℝ mv v = ‖mv‖^2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp [mv, inner, Fin.sum_univ_three, mul_max_zero]
      have huv : inner ℝ u v = ‖mv‖ := by
        calc
          inner ℝ u v = (1 / ‖mv‖) * inner ℝ mv v := by simp [u, inner_smul_left]
          _ = (1 / ‖mv‖) * ‖mv‖^2 := by rw [hmvin]
          _ = ‖mv‖ := by field_simp [hmvpos.ne']
      have hsum : 1 ≤ u 0 + u 1 + u 2 := by
        have hs : (u 0 + u 1 + u 2)^2 = (u 0)^2 + (u 1)^2 + (u 2)^2 +
            2*(u 0*u 1 + u 0*u 2 + u 1*u 2) := by ring
        have hcross : 0 ≤ u 0*u 1 + u 0*u 2 + u 1*u 2 := by
          nlinarith [hu_nonneg 0, hu_nonneg 1, hu_nonneg 2]
        have hn : ‖u‖^2 = (u 0)^2 + (u 1)^2 + (u 2)^2 := by
          rw [PiLp.norm_sq_eq_of_L2]; simp [Fin.sum_univ_three]
        have hsum_nonneg : 0 ≤ u 0 + u 1 + u 2 := by
          nlinarith [hu_nonneg 0, hu_nonneg 1, hu_nonneg 2]
        have hsum_sq : 1 ≤ (u 0 + u 1 + u 2)^2 := by
          nlinarith [hs, hcross, hn, hu_norm]
        nlinarith [sq_nonneg (u 0 + u 1 + u 2 - 1)]
      have hle_w : ∀ i, w i ≤ max (w 0) (max (w 1) (w 2)) := by
        intro i; fin_cases i <;> simp
      have hinner_le : inner ℝ u w ≤ (max (w 0) (max (w 1) (w 2))) * (u 0 + u 1 + u 2) := by
        simp [inner, Fin.sum_univ_three]
        nlinarith [hle_w 0, hle_w 1, hle_w 2, hu_nonneg 0, hu_nonneg 1, hu_nonneg 2]
      have hM_nonpos : max (w 0) (max (w 1) (w 2)) ≤ 0 := hw
      have hprod : (max (w 0) (max (w 1) (w 2))) * ((u 0 + u 1 + u 2) - 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hM_nonpos (sub_nonneg.mpr hsum)
      ring_nf at hprod
      have hMS : (max (w 0) (max (w 1) (w 2))) * (u 0 + u 1 + u 2) ≤ max (w 0) (max (w 1) (w 2)) := by
        nlinarith [hprod]
      have huw : inner ℝ u w ≤ max (w 0) (max (w 1) (w 2)) := le_trans hinner_le hMS
      have hcs : inner ℝ u (v - w) ≤ dist v w := by
        have := abs_real_inner_le_norm u (v - w)
        rw [hu_norm] at this
        simp only [one_mul] at this
        rw [dist_eq_norm]
        exact le_trans (le_abs_self _) this
      have hinner_sub : inner ℝ u (v - w) = inner ℝ u v - inner ℝ u w := by
        simp [inner_sub_right]
      rw [hinner_sub, huv] at hcs
      have hw0 : w 0 ≤ 0 := le_trans (le_max_left _ _) hw
      have hw1 : w 1 ≤ 0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hw
      have hw2 : w 2 ≤ 0 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hw
      have hmw0 : mw = 0 := by
        ext i; fin_cases i <;> simp [mw, max_eq_right hw0, max_eq_right hw1, max_eq_right hw2]
      nlinarith [hcs, huw]


lemma phiBox_lipschitz : AbsLipschitz phiBox := by
  intro v w
  unfold phiBox
  let mv : EuclideanSpace ℝ (Fin 3) := !₂[max (v 0) 0, max (v 1) 0, max (v 2) 0]
  let mw : EuclideanSpace ℝ (Fin 3) := !₂[max (w 0) 0, max (w 1) 0, max (w 2) 0]
  change |(‖mv‖ + min (max (v 0) (max (v 1) (v 2))) 0) -
          (‖mw‖ + min (max (w 0) (max (w 1) (w 2))) 0)| ≤ dist v w
  by_cases hv : max (v 0) (max (v 1) (v 2)) ≤ 0
  · by_cases hw : max (w 0) (max (w 1) (w 2)) ≤ 0
    · -- both inside
      have hv0 : v 0 ≤ 0 := le_trans (le_max_left _ _) hv
      have hv1 : v 1 ≤ 0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hv
      have hv2 : v 2 ≤ 0 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hv
      have hw0 : w 0 ≤ 0 := le_trans (le_max_left _ _) hw
      have hw1 : w 1 ≤ 0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hw
      have hw2 : w 2 ≤ 0 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hw
      have hmv0 : mv = 0 := by ext i; fin_cases i <;> simp [mv, max_eq_right hv0, max_eq_right hv1, max_eq_right hv2]
      have hmw0 : mw = 0 := by ext i; fin_cases i <;> simp [mw, max_eq_right hw0, max_eq_right hw1, max_eq_right hw2]
      simp [hmv0, hmw0, min_eq_left hv, min_eq_left hw]
      have habs0 := abs_max3_le (v 0) (v 1) (v 2) (w 0) (w 1) (w 2)
      rw [dist_eq_norm, PiLp.norm_eq_of_L2]
      rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
      simp [Fin.sum_univ_three]
      have hsqmax := sq_max3_le_sum (|v 0 - w 0|) (|v 1 - w 1|) (|v 2 - w 2|)
        (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      have hsqmax' : (max (max |v 0 - w 0| |v 1 - w 1|) |v 2 - w 2|)^2 ≤
          (|v 0 - w 0|)^2 + (|v 1 - w 1|)^2 + (|v 2 - w 2|)^2 := by
        simpa [max_assoc] using hsqmax
      rw [sq_abs, sq_abs, sq_abs] at hsqmax'
      have hMnonneg : 0 ≤ max (max |v 0 - w 0| |v 1 - w 1|) |v 2 - w 2| := by positivity
      have hsquare : (max (v 0) (max (v 1) (v 2)) - max (w 0) (max (w 1) (w 2)))^2 ≤
          (max (max |v 0 - w 0| |v 1 - w 1|) |v 2 - w 2|)^2 := by
        rw [← sq_abs]
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hMnonneg] using habs0)
      exact le_trans hsquare hsqmax'
    · -- v inside, w outside
      have hmwpos := phiBox_mixed w v hw hv
      rw [dist_comm] at hmwpos
      have hv0 : v 0 ≤ 0 := le_trans (le_max_left _ _) hv
      have hv1 : v 1 ≤ 0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hv
      have hv2 : v 2 ≤ 0 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hv
      have hmv0 : mv = 0 := by ext i; fin_cases i <;> simp [mv, max_eq_right hv0, max_eq_right hv1, max_eq_right hv2]
      simp [hmv0, min_eq_left hv, min_eq_right (le_of_not_ge hw)]
      rw [abs_of_nonpos]
      · nlinarith [hmwpos]
      · nlinarith [hv, norm_nonneg mw]
  · by_cases hw : max (w 0) (max (w 1) (w 2)) ≤ 0
    · -- v outside, w inside
      have hw0 : w 0 ≤ 0 := le_trans (le_max_left _ _) hw
      have hw1 : w 1 ≤ 0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hw
      have hw2 : w 2 ≤ 0 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hw
      have hmw0 : mw = 0 := by ext i; fin_cases i <;> simp [mw, max_eq_right hw0, max_eq_right hw1, max_eq_right hw2]
      simp [hmw0, min_eq_right (le_of_not_ge hv), min_eq_left hw]
      rw [abs_of_nonneg]
      · exact phiBox_mixed v w hv hw
      · nlinarith [norm_nonneg mv, hw]
    · -- both outside
      simp [min_eq_right (le_of_not_ge hv), min_eq_right (le_of_not_ge hw)]
      have hrev : |‖mv‖ - ‖mw‖| ≤ ‖mv - mw‖ := abs_norm_sub_norm_le _ _
      have hle : ‖mv - mw‖ ≤ dist v w := by
        rw [dist_eq_norm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
        apply Real.sqrt_le_sqrt
        simp only [Fin.sum_univ_three, Real.norm_eq_abs, Pi.sub_apply]
        have h0 := abs_max0_sub_max0 (v 0) (w 0)
        have h1 := abs_max0_sub_max0 (v 1) (w 1)
        have h2 := abs_max0_sub_max0 (v 2) (w 2)
        simp [mv, mw] at h0 h1 h2 ⊢
        have hs0 : (max (v 0) 0 - max (w 0) 0)^2 ≤ (v 0 - w 0)^2 := by
          have := sq_le_sq.mpr h0
          simpa [sq_abs] using this
        have hs1 : (max (v 1) 0 - max (w 1) 0)^2 ≤ (v 1 - w 1)^2 := by
          have := sq_le_sq.mpr h1
          simpa [sq_abs] using this
        have hs2 : (max (v 2) 0 - max (w 2) 0)^2 ≤ (v 2 - w 2)^2 := by
          have := sq_le_sq.mpr h2
          simpa [sq_abs] using this
        nlinarith [hs0, hs1, hs2, sq_nonneg (|v 0 - w 0| - |max (v 0) 0 - max (w 0) 0|),
          sq_nonneg (|v 1 - w 1| - |max (v 1) 0 - max (w 1) 0|),
          sq_nonneg (|v 2 - w 2| - |max (v 2) 0 - max (w 2) 0|)]
      exact le_trans hrev hle


/-- Box SDF matching tri_sdf_eval: q_i = |p_i| - h_i, signed orthant distance phi(q). -/
def sdfBox (h : Fin 3 → ℝ) (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  phiBox (!₂[|p 0| - h 0, |p 1| - h 1, |p 2| - h 2])

/-- Box SDF is 1-Lipschitz in Euclidean space. -/
theorem sdfBox_AbsLipschitz (h : Fin 3 → ℝ) : AbsLipschitz (sdfBox h) := by
  intro p q
  unfold sdfBox
  have hphi := phiBox_lipschitz
      (!₂[|p 0| - h 0, |p 1| - h 1, |p 2| - h 2] : EuclideanSpace ℝ (Fin 3))
      (!₂[|q 0| - h 0, |q 1| - h 1, |q 2| - h 2] : EuclideanSpace ℝ (Fin 3))
  have hdist : dist
      (!₂[|p 0| - h 0, |p 1| - h 1, |p 2| - h 2] : EuclideanSpace ℝ (Fin 3))
      (!₂[|q 0| - h 0, |q 1| - h 1, |q 2| - h 2] : EuclideanSpace ℝ (Fin 3)) ≤ dist p q := by
    rw [dist_eq_norm, PiLp.norm_eq_of_L2, dist_eq_norm, PiLp.norm_eq_of_L2]
    apply Real.sqrt_le_sqrt
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, Pi.sub_apply]
    have h0 := abs_sub_abs_le_abs_sub (p 0) (q 0)
    have h1 := abs_sub_abs_le_abs_sub (p 1) (q 1)
    have h2 := abs_sub_abs_le_abs_sub (p 2) (q 2)
    simp [Pi.sub_apply] at *
    have hs0 : (|p 0| - |q 0|)^2 ≤ (p 0 - q 0)^2 := by
      have hhx := abs_abs_sub_abs_le_abs_sub (p 0) (q 0)
      have := sq_le_sq.mpr hhx
      simpa [sq_abs] using this
    have hs1 : (|p 1| - |q 1|)^2 ≤ (p 1 - q 1)^2 := by
      have hhx := abs_abs_sub_abs_le_abs_sub (p 1) (q 1)
      have := sq_le_sq.mpr hhx
      simpa [sq_abs] using this
    have hs2 : (|p 2| - |q 2|)^2 ≤ (p 2 - q 2)^2 := by
      have hhx := abs_abs_sub_abs_le_abs_sub (p 2) (q 2)
      have := sq_le_sq.mpr hhx
      simpa [sq_abs] using this
    nlinarith [hs0, hs1, hs2, sq_nonneg (|p 0 - q 0|), sq_nonneg (|p 1 - q 1|), sq_nonneg (|p 2 - q 2|)]
  exact le_trans hphi hdist

end
end LightRT.Geom
