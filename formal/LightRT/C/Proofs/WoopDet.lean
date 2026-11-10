/-
  The determinant check of `tri_woop_one` is redundant after the edge-sign test:
  if `U, V, W` pass the sign test and one of them is strictly signed, then
  `det = (U + V) + W` is non-zero in binary32 (for every input; NaN included).
  Rounding a sum of same-sign values never cancels to zero, because a decoded
  binary32 value lies on the grid and is fixed by rounding.
-/
import LightRT.C.Proofs.WoopWatertight

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

/-- Values whose finite magnitude lies on the binary32 grid. -/
def GV (X : V) : Prop := ∀ s q, X = .num s q → Grid q

theorem gv_decode (w : UInt32) : GV (decode w) := fun _ _ h => (decode_grid h).1

theorem rne_mono_q {x y : ℚ} (h : x ≤ y) : rne x ≤ rne y := by
  have := rneR_mono (show (x : ℝ) ≤ y by exact_mod_cast h)
  rw [rne_cast, rne_cast] at this; exact_mod_cast this

def posV (X : V) : Bool := V.cmp true Zv X
def negV (X : V) : Bool := V.cmp true X Zv

theorem num_neg_false {a : Bool} {x : ℚ} (hx : 0 ≤ x) (h : negV (.num a x) = false) :
    0 ≤ (V.num a x).toQ?.getD 0 := by
  cases a <;> simp [posV, negV, V.cmp, Zv, V.toQ?] at h ⊢
  · exact hx
  · linarith

theorem num_pos {a : Bool} {x : ℚ} (h : posV (.num a x) = true) :
    0 < (V.num a x).toQ?.getD 0 := by
  cases a <;> simp [posV, negV, V.cmp, Zv, V.toQ?] at h ⊢ <;> try linarith

theorem num_pos_grid {a : Bool} {x : ℚ} (hg : Grid x) (h : posV (.num a x) = true) :
    rne ((V.num a x).toQ?.getD 0) = (V.num a x).toQ?.getD 0 := by
  cases a <;> simp [posV, negV, V.cmp, Zv, V.toQ?] at h ⊢
  · exact grid_fixed hg
  · rw [rne_neg_q, grid_fixed hg]

/-- Adding two non-negative values gives a non-negative value, positive if
    either summand is positive. -/
theorem add_nonneg_V (X Y : V) (gX : GV X) (gY : GV Y)
    (hXn : X ≠ .nan) (hYn : Y ≠ .nan) (nX : negV X = false) (nY : negV Y = false) :
    negV (X.add Y) = false ∧ (posV X = true ∨ posV Y = true → posV (X.add Y) = true) := by
  cases X with
  | nan => exact absurd rfl hXn
  | inf a =>
    cases a
    · cases Y with
      | nan => exact absurd rfl hYn
      | inf b => cases b <;> simp_all [posV, negV, V.add, V.cmp, Zv, V.toQ?]
      | num b y => simp [posV, negV, V.add, V.cmp, Zv, V.toQ?]
    · simp [posV, negV, V.cmp, Zv, V.toQ?] at nX
  | num a x =>
    cases Y with
    | nan => exact absurd rfl hYn
    | inf b => cases b <;> simp_all [posV, negV, V.add, V.cmp, Zv, V.toQ?]
    | num b y =>
      have hx : 0 ≤ x := by
        obtain ⟨n, q, -, -, rfl⟩ := gX a x rfl; positivity
      have hy : 0 ≤ y := by
        obtain ⟨n, q, -, -, rfl⟩ := gY b y rfl; positivity
      have px := num_neg_false hx nX
      have py := num_neg_false hy nY
      simp only [V.add]
      obtain ⟨c1, c2⟩ := cmp_roundQ ((V.num a x).toQ?.getD 0 + (V.num b y).toQ?.getD 0) (a && b)
      simp only [posV, negV]; rw [c1, c2]
      have hs := (rne_sign_q ((V.num a x).toQ?.getD 0 + (V.num b y).toQ?.getD 0)).2 (by linarith)
      refine ⟨by simpa using hs, ?_⟩
      rintro (h | h)
      · have m := rne_mono_q (show (V.num a x).toQ?.getD 0 ≤
            (V.num a x).toQ?.getD 0 + (V.num b y).toQ?.getD 0 by linarith)
        rw [num_pos_grid (gX a x rfl) h] at m
        have := num_pos h; simp; linarith
      · have m := rne_mono_q (show (V.num b y).toQ?.getD 0 ≤
            (V.num a x).toQ?.getD 0 + (V.num b y).toQ?.getD 0 by linarith)
        rw [num_pos_grid (gY b y rfl) h] at m
        have := num_pos h; simp; linarith

theorem num_pos_false {a : Bool} {x : ℚ} (hx : 0 ≤ x) (h : posV (.num a x) = false) :
    (V.num a x).toQ?.getD 0 ≤ 0 := by
  cases a <;> simp [posV, negV, V.cmp, Zv, V.toQ?] at h ⊢
  · exact h
  · linarith

theorem num_neg {a : Bool} {x : ℚ} (h : negV (.num a x) = true) :
    (V.num a x).toQ?.getD 0 < 0 := by
  cases a <;> simp [posV, negV, V.cmp, Zv, V.toQ?] at h ⊢ <;> try linarith

theorem num_neg_grid {a : Bool} {x : ℚ} (hg : Grid x) :
    rne ((V.num a x).toQ?.getD 0) = (V.num a x).toQ?.getD 0 := by
  cases a <;> simp [V.toQ?]
  · exact grid_fixed hg
  · rw [rne_neg_q, grid_fixed hg]

/-- Mirror of `add_nonneg_V`. -/
theorem add_nonpos_V (X Y : V) (gX : GV X) (gY : GV Y)
    (hXn : X ≠ .nan) (hYn : Y ≠ .nan) (nX : posV X = false) (nY : posV Y = false) :
    posV (X.add Y) = false ∧ (negV X = true ∨ negV Y = true → negV (X.add Y) = true) := by
  cases X with
  | nan => exact absurd rfl hXn
  | inf a =>
    cases a
    · simp [posV, negV, V.cmp, Zv, V.toQ?] at nX
    · cases Y with
      | nan => exact absurd rfl hYn
      | inf b => cases b <;> simp_all [posV, negV, V.add, V.cmp, Zv, V.toQ?]
      | num b y => simp [posV, negV, V.add, V.cmp, Zv, V.toQ?]
  | num a x =>
    cases Y with
    | nan => exact absurd rfl hYn
    | inf b => cases b <;> simp_all [posV, negV, V.add, V.cmp, Zv, V.toQ?]
    | num b y =>
      have hx : 0 ≤ x := by
        obtain ⟨n, q, -, -, rfl⟩ := gX a x rfl; positivity
      have hy : 0 ≤ y := by
        obtain ⟨n, q, -, -, rfl⟩ := gY b y rfl; positivity
      have px := num_pos_false hx nX
      have py := num_pos_false hy nY
      simp only [V.add]
      obtain ⟨c1, c2⟩ := cmp_roundQ ((V.num a x).toQ?.getD 0 + (V.num b y).toQ?.getD 0) (a && b)
      simp only [posV, negV]; rw [c1, c2]
      by_cases hz : (V.num a x).toQ?.getD 0 + (V.num b y).toQ?.getD 0 < 0
      · have hs := (rne_sign_q ((V.num a x).toQ?.getD 0 + (V.num b y).toQ?.getD 0)).1 hz
        refine ⟨by simp; linarith, ?_⟩
        rintro (h | h)
        · have m := rne_mono_q (show (V.num a x).toQ?.getD 0 + (V.num b y).toQ?.getD 0 ≤
              (V.num a x).toQ?.getD 0 by linarith)
          rw [num_neg_grid (gX a x rfl)] at m
          have := num_neg h; simp; linarith
        · have m := rne_mono_q (show (V.num a x).toQ?.getD 0 + (V.num b y).toQ?.getD 0 ≤
              (V.num b y).toQ?.getD 0 by linarith)
          rw [num_neg_grid (gY b y rfl)] at m
          have := num_neg h; simp; linarith
      · have h0 : (V.num a x).toQ?.getD 0 + (V.num b y).toQ?.getD 0 = 0 := by linarith
        refine ⟨by rw [h0]; simp [rne], ?_⟩
        rintro (h | h) <;> (have := num_neg h; linarith)

theorem decode_add (a b : UInt32) : decode (addBits a b) =
    if decode a = .nan ∨ decode b = .nan then .nan else (decode a).add (decode b) :=
  decode_prop a b V.add dec_enc_add

theorem pos_le (X : V) (h : posV X = true) : V.cmp false X Zv = false := by
  cases X with
  | nan => rfl
  | inf a => cases a <;> simp_all [posV, V.cmp, Zv, V.toQ?]
  | num a x => cases a <;> simp_all [posV, V.cmp, Zv, V.toQ?] <;> try linarith

theorem neg_le (X : V) (h : negV X = true) : V.cmp false Zv X = false := by
  cases X with
  | nan => rfl
  | inf a => cases a <;> simp_all [negV, V.cmp, Zv, V.toQ?]
  | num a x => cases a <;> simp_all [negV, V.cmp, Zv, V.toQ?] <;> try linarith

theorem eqF_nan {w : UInt32} (h : decode w = .nan) : Ref.eqF w Ref.zero = false := by
  simp [Ref.eqF, leBits, h, V.cmp]

/-- `(u + v) + w` is not zero when `u, v, w` pass the sign test and one is strictly signed. -/
theorem det3_ne_zero (u v w : UInt32)
    (h1 : ((ltBits u Ref.zero || ltBits v Ref.zero || ltBits w Ref.zero) &&
      (ltBits Ref.zero u || ltBits Ref.zero v || ltBits Ref.zero w)) = false)
    (hs : (ltBits Ref.zero u || ltBits Ref.zero v || ltBits Ref.zero w ||
      ltBits u Ref.zero || ltBits v Ref.zero || ltBits w Ref.zero) = true) :
    Ref.eqF (addBits (addBits u v) w) Ref.zero = false := by
  by_cases hn : decode u = .nan ∨ decode v = .nan ∨ decode w = .nan ∨ decode (addBits u v) = .nan
  · apply eqF_nan
    rw [decode_add]; rw [decode_add] at hn ⊢
    rcases hn with h | h | h | h <;> simp_all
  push Not at hn
  obtain ⟨nu, nv, nw, ns⟩ := hn
  have hS : decode (addBits u v) = (decode u).add (decode v) := by
    rw [decode_add, if_neg (by tauto)]
  have hD : decode (addBits (addBits u v) w) = ((decode u).add (decode v)).add (decode w) := by
    rw [decode_add, if_neg (by tauto), hS]
  rw [hS] at ns
  unfold Ref.eqF leBits; rw [hD, decode_zero]
  unfold ltBits at h1 hs; rw [decode_zero] at h1 hs
  change ((negV (decode u) || negV (decode v) || negV (decode w)) &&
    (posV (decode u) || posV (decode v) || posV (decode w))) = false at h1
  change (posV (decode u) || posV (decode v) || posV (decode w) ||
    negV (decode u) || negV (decode v) || negV (decode w)) = true at hs
  have gu := gv_decode u; have gv := gv_decode v; have gw := gv_decode w
  have gs : GV ((decode u).add (decode v)) := by rw [← hS]; exact gv_decode _
  cases hneg : (negV (decode u) || negV (decode v) || negV (decode w))
  · simp only [Bool.or_eq_false_iff] at hneg
    obtain ⟨⟨a1, a2⟩, a3⟩ := hneg
    have s1 := add_nonneg_V _ _ gu gv nu nv a1 a2
    have s2 := add_nonneg_V _ _ gs gw ns nw s1.1 a3
    have : posV (((decode u).add (decode v)).add (decode w)) = true := by
      simp only [a1, a2, a3, Bool.or_false] at hs
      apply s2.2
      simp only [Bool.or_eq_true] at hs
      rcases hs with (h | h) | h
      · exact Or.inl (s1.2 (Or.inl h))
      · exact Or.inl (s1.2 (Or.inr h))
      · exact Or.inr h
    rw [pos_le _ this]; rfl
  · rw [hneg, Bool.true_and] at h1
    simp only [Bool.or_eq_false_iff] at h1
    obtain ⟨⟨a1, a2⟩, a3⟩ := h1
    have s1 := add_nonpos_V _ _ gu gv nu nv a1 a2
    have s2 := add_nonpos_V _ _ gs gw ns nw s1.1 a3
    have : negV (((decode u).add (decode v)).add (decode w)) = true := by
      apply s2.2
      simp only [Bool.or_eq_true] at hneg
      rcases hneg with (h | h) | h
      · exact Or.inl (s1.2 (Or.inl h))
      · exact Or.inl (s1.2 (Or.inr h))
      · exact Or.inr h
    rw [neg_le _ this]; simp

/-- **The `det == 0` rejection of `tri_woop_one` is redundant**: once the edge-sign
    test passes and some edge function is strictly signed, `det ≠ 0`, for every
    input. So a triangle passing the sign test is rejected only by the `t` range. -/
theorem woop_det_ne_zero (k : Ref.Axes) (o d v0 v1 v2 : Fin 3 → Ref.F)
    (h1 : Ref.woopRej1 k o d v0 v1 v2 = false)
    (hs : (ltBits Ref.zero (Ref.woopU k o d v0 v1 v2) || ltBits Ref.zero (Ref.woopV k o d v0 v1 v2) ||
      ltBits Ref.zero (Ref.woopW k o d v0 v1 v2) || ltBits (Ref.woopU k o d v0 v1 v2) Ref.zero ||
      ltBits (Ref.woopV k o d v0 v1 v2) Ref.zero || ltBits (Ref.woopW k o d v0 v1 v2) Ref.zero) = true) :
    Ref.woopRej2 k o d v0 v1 v2 = false :=
  det3_ne_zero _ _ _ h1 hs

/-- **Watertightness through the det test.** In the shared-edge setting of
    `woop_no_gap_bits`, one of the two triangles passes both the sign test and
    the `det` test; only its own `t`-range check can still reject it. -/
theorem woop_no_gap_det (k : Ref.Axes) (o d a b c c' : Fin 3 → Ref.F)
    (h1 : ltBits Ref.zero (Ref.woopU k o d a b c) = true)
    (h1' : ltBits (Ref.woopV k o d a b c) Ref.zero = false)
    (h2 : ltBits Ref.zero (Ref.woopU k o d b a c') = true)
    (h2' : ltBits (Ref.woopV k o d b a c') Ref.zero = false) :
    (Ref.woopRej1 k o d a b c = false ∧ Ref.woopRej2 k o d a b c = false) ∨
    (Ref.woopRej1 k o d b a c' = false ∧ Ref.woopRej2 k o d b a c' = false) := by
  rcases woop_no_gap_bits k o d a b c c' h1 h1' h2 h2' with h | h
  · exact Or.inl ⟨h, woop_det_ne_zero _ _ _ _ _ _ h (by simp [h1])⟩
  · exact Or.inr ⟨h, woop_det_ne_zero _ _ _ _ _ _ h (by simp [h2])⟩

end LightRT.C.Proofs
