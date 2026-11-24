/-
  Stage 6 bridge: on finite, in-range inputs the bit-level reference
  (`Ref.raySetup` + `Ref.slab`) computes exactly the abstract `Robust.fpSlab`
  over `Binary32.model`. The key ingredient is the round trip
  `decode (encode (roundQ p z)) = roundQ p z` (`FP/Binary32.lean`).
-/
import LightRT.C.Ref
import LightRT.Robust.Slab

namespace LightRT.C.Proofs
open LightRT.FP LightRT.FP.Binary32 LightRT.C

/-- Value of a finite binary32 word as a real. -/
noncomputable def val (w : Ref.F) : ℝ := (((decode w).toQ?).getD 0 : ℝ)

/-- `w` encodes a finite value. -/
def FinW (w : UInt32) : Prop := ∃ s q, decode w = .num s q

theorem inRange_abs {x : ℝ} (h : Binary32.InRange x) : |x| ≤ maxFinite := by
  rcases h with h | h
  · subst h; simp only [abs_zero]; unfold maxFinite; norm_num
  · exact h.2

/-- Encoding a rounded, in-range exact result is lossless. -/
theorem encode_roundQ (p : ℚ) (z : Bool) (h : Binary32.InRange (p : ℝ)) :
    FinW (encode (roundQ p z)) ∧ val (encode (roundQ p z)) = rneR (p : ℝ) := by
  have hb : |p| ≤ maxFinite := by exact_mod_cast inRange_abs h
  obtain ⟨s, r, hr, hg, hm⟩ := roundQ_ok p z hb
  have hd : decode (encode (roundQ p z)) = roundQ p z := by
    rw [hr]; exact decode_encode_num s r hg hm
  refine ⟨⟨s, r, by rw [hd, hr]⟩, ?_⟩
  unfold val; rw [hd]; exact roundQ_toQ p z ⟨s, r, hr⟩

theorem val_num {w : UInt32} {s : Bool} {q : ℚ} (h : decode w = .num s q) :
    val w = ((if s then -q else q : ℚ) : ℝ) := by
  simp [val, h, V.toQ?]

theorem subBits_ok {a b : UInt32} (ha : FinW a) (hb : FinW b)
    (hr : Binary32.InRange (val a - val b)) :
    FinW (subBits a b) ∧ val (subBits a b) = rneR (val a - val b) := by
  obtain ⟨sa, qa, ha⟩ := ha; obtain ⟨sb, qb, hb⟩ := hb
  have hp : ((((V.num sa qa).toQ?.getD 0) + ((V.num (!sb) qb).toQ?.getD 0) : ℚ) : ℝ) =
      val a - val b := by
    rw [val_num ha, val_num hb]; cases sa <;> cases sb <;> simp [V.toQ?] <;> ring
  have e : subBits a b = encode (roundQ (((V.num sa qa).toQ?.getD 0) + ((V.num (!sb) qb).toQ?.getD 0))
      (sa && !sb)) := by
    simp only [subBits, propagate, isNaNBits_false ha, isNaNBits_false hb, ha, hb]; rfl
  rw [e, ← hp]; rw [← hp] at hr; exact encode_roundQ _ _ hr

theorem mulBits_ok {a b : UInt32} (ha : FinW a) (hb : FinW b)
    (hr : Binary32.InRange (val a * val b)) :
    FinW (mulBits a b) ∧ val (mulBits a b) = rneR (val a * val b) := by
  obtain ⟨sa, qa, ha⟩ := ha; obtain ⟨sb, qb, hb⟩ := hb
  have hp : (((if sa != sb then -1 else 1) * (qa * qb) : ℚ) : ℝ) = val a * val b := by
    rw [val_num ha, val_num hb]; cases sa <;> cases sb <;> simp <;> ring
  have e : mulBits a b = encode (roundQ ((if sa != sb then -1 else 1) * (qa * qb)) (sa != sb)) := by
    simp only [mulBits, propagate, isNaNBits_false ha, isNaNBits_false hb, ha, hb]; rfl
  rw [e, ← hp]; rw [← hp] at hr; exact encode_roundQ _ _ hr

theorem divBits_ok {a b : UInt32} (ha : FinW a) (hb : FinW b) (h0 : val b ≠ 0)
    (hr : Binary32.InRange (val a / val b)) :
    FinW (divBits a b) ∧ val (divBits a b) = rneR (val a / val b) := by
  obtain ⟨sa, qa, ha⟩ := ha; obtain ⟨sb, qb, hb⟩ := hb
  have hq : qb ≠ 0 := by
    rintro rfl; apply h0; rw [val_num hb]; simp
  have hp : (((if sa != sb then -1 else 1) * (qa / qb) : ℚ) : ℝ) = val a / val b := by
    rw [val_num ha, val_num hb]; cases sa <;> cases sb <;> simp <;> ring
  have e : divBits a b = encode (roundQ ((if sa != sb then -1 else 1) * (qa / qb)) (sa != sb)) := by
    simp only [divBits, propagate, isNaNBits_false ha, isNaNBits_false hb, ha, hb, V.div, hq]; rfl
  rw [e, ← hp]; rw [← hp] at hr; exact encode_roundQ _ _ hr

theorem leBits_ok {a b : UInt32} (ha : FinW a) (hb : FinW b) :
    leBits a b = decide (val a ≤ val b) := by
  obtain ⟨sa, qa, ha'⟩ := ha; obtain ⟨sb, qb, hb'⟩ := hb
  rw [val_num ha', val_num hb']
  simp only [leBits, ha', hb', V.cmp, V.toQ?, Option.getD_some, Rat.cast_le]
  simp only [ne_eq, not_true_eq_false, if_false, Bool.false_eq_true, ite_false]
  exact decide_eq_decide.mpr (by push_cast; split_ifs <;> simp)

theorem ltBits_ok {a b : UInt32} (ha : FinW a) (hb : FinW b) :
    ltBits a b = decide (val a < val b) := by
  obtain ⟨sa, qa, ha'⟩ := ha; obtain ⟨sb, qb, hb'⟩ := hb
  rw [val_num ha', val_num hb']
  simp only [ltBits, ha', hb', V.cmp, V.toQ?, Option.getD_some, Rat.cast_lt]
  simp only [ne_eq, not_true_eq_false, if_false, Bool.false_eq_true, ite_false]
  exact decide_eq_decide.mpr (by push_cast; split_ifs <;> simp)

theorem fmin_ok {a b : UInt32} (ha : FinW a) (hb : FinW b) :
    FinW (Ref.fmin a b) ∧ val (Ref.fmin a b) = min (val a) (val b) := by
  unfold Ref.fmin; rw [ltBits_ok ha hb]
  by_cases h : val a < val b
  · simp [h, ha, min_eq_left h.le]
  · simp [h, hb, min_eq_right (not_lt.1 h)]

theorem fmax_ok {a b : UInt32} (ha : FinW a) (hb : FinW b) :
    FinW (Ref.fmax a b) ∧ val (Ref.fmax a b) = max (val a) (val b) := by
  unfold Ref.fmax; rw [ltBits_ok hb ha]
  by_cases h : val b < val a
  · simp [h, ha, max_eq_left h.le]
  · simp [h, hb, max_eq_right (not_lt.1 h)]

/-- Finite words are fixed points of the rounding. -/
theorem val_fixed {w : UInt32} (h : FinW w) : rneR (val w) = val w := by
  obtain ⟨s, q, h⟩ := h
  have hq : rneR (q : ℝ) = q := by rw [rne_cast, grid_fixed (decode_grid h).1]
  rw [val_num h]; split_ifs
  · push_cast; rw [rneR_neg, hq]
  · exact hq

/-- `1e18f` as a real: the clamp `TRI_INVD_MAX`. -/
theorem val_invdMax : val Ref.invdMax = ((14551915 * 2 ^ (36:ℤ) : ℚ) : ℝ) := by
  rw [val_num (show decode Ref.invdMax = .num false (14551915 * 2 ^ (36:ℤ)) by decide +kernel)]; rfl
theorem val_neg_invdMax : val (Ref.neg Ref.invdMax) = -((14551915 * 2 ^ (36:ℤ) : ℚ) : ℝ) := by
  rw [show Ref.neg Ref.invdMax = 0xdd5e0b6b by decide,
    val_num (show decode 0xdd5e0b6b = .num true (14551915 * 2 ^ (36:ℤ)) by decide +kernel)]
  simp
theorem fin_invdMax : FinW Ref.invdMax := ⟨false, 14551915 * 2 ^ (36:ℤ), by decide +kernel⟩
theorem fin_neg_invdMax : FinW (Ref.neg Ref.invdMax) := ⟨true, 14551915 * 2 ^ (36:ℤ), by decide +kernel⟩
theorem fin_one : FinW Ref.one := ⟨false, 1, by decide +kernel⟩
theorem val_one : val Ref.one = 1 := by
  rw [val_num (show decode Ref.one = .num false 1 by decide +kernel)]; simp

/-- With `|d| ≥ 1e-18` the `invd` clamp of `tri_ray_setup` is inactive. -/
theorem raySetup_invd (org dir : Fin 3 → Ref.F) (tmin : Ref.F) (k : Fin 3) (hd : FinW (dir k))
    (hdir : (10 : ℝ) ^ (-18 : ℤ) ≤ |val (dir k)|) (hr : Binary32.InRange (1 / val (dir k))) :
    FinW ((Ref.raySetup org dir tmin).invd k) ∧
      val ((Ref.raySetup org dir tmin).invd k) = rneR (1 / val (dir k)) := by
  have h0 : val (dir k) ≠ 0 := by
    intro h; rw [h, abs_zero] at hdir; have : (0:ℝ) < 10 ^ (-18:ℤ) := by positivity
    linarith
  obtain ⟨hf, hv⟩ := divBits_ok fin_one hd h0 (by rwa [val_one])
  rw [val_one] at hv
  have hV : rneR (10 ^ 18 : ℝ) = ((14551915 * 2 ^ (36:ℤ) : ℚ) : ℝ) := by
    rw [show (10 ^ 18 : ℝ) = ((10 ^ 18 : ℚ) : ℝ) by norm_num, rne_cast,
      show rne (10 ^ 18 : ℚ) = 14551915 * 2 ^ (36:ℤ) by decide +kernel]
  have hb : |1 / val (dir k)| ≤ 10 ^ 18 := by
    rw [abs_div, abs_one, div_le_iff₀ (abs_pos.2 h0)]
    calc (1:ℝ) = 10 ^ 18 * 10 ^ (-18:ℤ) := by norm_num
      _ ≤ _ := by gcongr
  have hup : rneR (1 / val (dir k)) ≤ ((14551915 * 2 ^ (36:ℤ) : ℚ) : ℝ) := by
    rw [← hV]; exact rneR_mono ((le_abs_self _).trans hb)
  have hlo : -((14551915 * 2 ^ (36:ℤ) : ℚ) : ℝ) ≤ rneR (1 / val (dir k)) := by
    rw [← hV, ← rneR_neg]; exact rneR_mono (by have := neg_abs_le (1 / val (dir k)); linarith)
  have hc : (leBits (Ref.neg Ref.invdMax) (divBits Ref.one (dir k)) &&
      leBits (divBits Ref.one (dir k)) Ref.invdMax) = true := by
    rw [leBits_ok fin_neg_invdMax hf, leBits_ok hf fin_invdMax, val_neg_invdMax, val_invdMax, hv]
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]; exact ⟨hlo, hup⟩
  have e : (Ref.raySetup org dir tmin).invd k = divBits Ref.one (dir k) := by
    simp only [Ref.raySetup, hc, Bool.not_true, Bool.false_eq_true, if_false]
  rw [e]; exact ⟨hf, hv⟩

theorem slab_ref_eq_fpSlab' (org dir : Fin 3 → Ref.F) (tmin tmax : Ref.F) (lo hi : Fin 3 → Ref.F)
    (hfin : ∀ w ∈ [org 0, org 1, org 2, dir 0, dir 1, dir 2, tmin, tmax, lo 0, lo 1, lo 2,
                    hi 0, hi 1, hi 2], ∃ s q, Binary32.decode w = .num s q)
    (hdir : ∀ k, (10 : ℝ) ^ (-18 : ℤ) ≤ |val (dir k)|)
    (hrange : Robust.SlabInRange Binary32.model
      ⟨fun k => val (org k), fun k => val (dir k), val tmin, val tmax⟩
      ⟨fun k => val (lo k), fun k => val (hi k)⟩ 1) :
    (Ref.slab (Ref.raySetup org dir tmin) lo hi tmax).1 = true ↔
      Robust.fpSlab Binary32.model
        ⟨fun k => val (org k), fun k => val (dir k), val tmin, val tmax⟩
        ⟨fun k => val (lo k), fun k => val (hi k)⟩ 1 := by
  set r : Geom.Ray := ⟨fun k => val (org k), fun k => val (dir k), val tmin, val tmax⟩
  set b : Geom.Box := ⟨fun k => val (lo k), fun k => val (hi k)⟩
  set rc := Ref.raySetup org dir tmin with hrc
  have fo : ∀ k, FinW (org k) := fun k => by fin_cases k <;> exact hfin _ (by simp)
  have fd : ∀ k, FinW (dir k) := fun k => by fin_cases k <;> exact hfin _ (by simp)
  have fl : ∀ k, FinW (lo k) := fun k => by fin_cases k <;> exact hfin _ (by simp)
  have fh : ∀ k, FinW (hi k) := fun k => by fin_cases k <;> exact hfin _ (by simp)
  have ftmin : FinW tmin := hfin _ (by simp)
  have ftmax : FinW tmax := hfin _ (by simp)
  obtain ⟨hrd, hrx, -⟩ := hrange
  have hI : ∀ k, FinW (rc.invd k) ∧ val (rc.invd k) = Robust.fpInvd Binary32.model r k := fun k =>
    raySetup_invd org dir tmin k (fd k) (hdir k) (hrd k)
  have hT : ∀ k (x : Ref.F), FinW x → (val x = b.lo k ∨ val x = b.hi k) →
      FinW (mulBits (subBits x (rc.org k)) (rc.invd k)) ∧
      val (mulBits (subBits x (rc.org k)) (rc.invd k)) = Robust.fpT Binary32.model r (val x) k := by
    intro k x fx hx
    have hm : val x ∈ ({b.lo k, b.hi k} : Set ℝ) := by rcases hx with h | h <;> simp [h]
    obtain ⟨r1, r2⟩ := hrx k (val x) hm
    obtain ⟨fs, vs⟩ := subBits_ok (a := x) (b := rc.org k) fx (fo k) r1
    have r2' : Binary32.InRange (val (subBits x (rc.org k)) * val (rc.invd k)) := by
      rw [vs, (hI k).2]; exact r2
    obtain ⟨fm, vm⟩ := mulBits_ok fs (hI k).1 r2'
    refine ⟨fm, ?_⟩
    rw [vm, vs, (hI k).2]; rfl
  have tl := fun k => hT k (lo k) (fl k) (Or.inl rfl)
  have th := fun k => hT k (hi k) (fh k) (Or.inr rfl)
  have hn : ∀ k, FinW (Ref.fmin (mulBits (subBits (lo k) (rc.org k)) (rc.invd k))
        (mulBits (subBits (hi k) (rc.org k)) (rc.invd k))) ∧
      val (Ref.fmin (mulBits (subBits (lo k) (rc.org k)) (rc.invd k))
        (mulBits (subBits (hi k) (rc.org k)) (rc.invd k))) = Robust.fpNear Binary32.model r b k := by
    intro k; obtain ⟨f, v⟩ := fmin_ok (tl k).1 (th k).1
    exact ⟨f, by rw [v, (tl k).2, (th k).2]; rfl⟩
  have hf : ∀ k, FinW (Ref.fmax (mulBits (subBits (lo k) (rc.org k)) (rc.invd k))
        (mulBits (subBits (hi k) (rc.org k)) (rc.invd k))) ∧
      val (Ref.fmax (mulBits (subBits (lo k) (rc.org k)) (rc.invd k))
        (mulBits (subBits (hi k) (rc.org k)) (rc.invd k))) = Robust.fpFar Binary32.model r b k := by
    intro k; obtain ⟨f, v⟩ := fmax_ok (tl k).1 (th k).1
    exact ⟨f, by rw [v, (tl k).2, (th k).2]; rfl⟩
  obtain ⟨n01f, n01v⟩ := fmax_ok (hn 0).1 (hn 1).1
  obtain ⟨n2f, n2v⟩ := fmax_ok (hn 2).1 (show FinW rc.tmin from ftmin)
  obtain ⟨nf, nv⟩ := fmax_ok n01f n2f
  obtain ⟨f01f, f01v⟩ := fmin_ok (hf 0).1 (hf 1).1
  obtain ⟨f2f, f2v⟩ := fmin_ok (hf 2).1 ftmax
  obtain ⟨ff, fv⟩ := fmin_ok f01f f2f
  show leBits _ _ = true ↔ _
  rw [leBits_ok nf ff, decide_eq_true_iff]
  unfold Robust.fpSlab
  show _ ↔ _ ≤ rneR (_ * 1)
  rw [nv, n01v, n2v, fv, f01v, f2v, (hn 0).2, (hn 1).2, (hn 2).2, (hf 0).2, (hf 1).2, (hf 2).2,
    mul_one]
  have hfix : rneR (min (min (Robust.fpFar Binary32.model r b 0) (Robust.fpFar Binary32.model r b 1))
      (min (Robust.fpFar Binary32.model r b 2) (val tmax))) =
      min (min (Robust.fpFar Binary32.model r b 0) (Robust.fpFar Binary32.model r b 1))
      (min (Robust.fpFar Binary32.model r b 2) (val tmax)) := by
    rw [← (hf 0).2, ← (hf 1).2, ← (hf 2).2, ← f01v, ← f2v, ← fv]; exact val_fixed ff
  rw [hfix]; rfl
end LightRT.C.Proofs
