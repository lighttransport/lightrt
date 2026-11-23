/-
  Refinements for the branch-free fp32 cores of the built-in SDF shapes
  (`tri_sdf_sphere_core`, `tri_sdf_box_core`, `tri_sdf_torus_core`). The
  translation of each is a straight-line MiniC program; the witness state is
  the frame after its `set`s (memory untouched). `fabsf` is translated as
  `copysignf(x, +1)`, and the ternaries are C's NaN-asymmetric min/max, so the
  bit-level references use `Ref.fmin`/`Ref.fmax` directly.
-/
import LightRT.C.Proofs.ExnKeyRefines

namespace LightRT.C.Proofs
open LightRT.C LightRT.FP.Binary32

/-- Straight-line evaluation plus the two conditional shapes used by the box
    core (`t ? x : 0` = `fmax x 0`, `qmax ? x : y` = `fmax x y`, `< 0 ? x : 0`
    = `fmin x 0`). -/
syntax "evSdf" : tactic
macro_rules
  | `(tactic| evSdf) => `(tactic| first
      | (apply EvE.f32sub <;> (first | (apply EvE.copysign' <;> ev) | ev))
      | (apply EvE.copysign' <;> ev)
      | ev)

macro "setN" v:term : tactic => `(tactic| (apply ExS.set (v := $v); evSdf))


-- ---------------------------------------------------------------- sphere ---

theorem tri_sdf_sphere_core_refines' (px py pz r : Ref.F) (m : Mem) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_sdf_sphere_core.params
        [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 r.toNat], m, false⟩
      Gen.tri_sdf_sphere_core.body
      (.ret (some (.f32 (Ref.sdfSphereCore px py pz r).toNat))) s' ∧ s'.mem = m := by
  let s0 : State := ⟨frameLocals Gen.tri_sdf_sphere_core.params
      [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 r.toNat], m, false⟩
  refine ⟨s0, ?_, rfl⟩
  unfold Gen.tri_sdf_sphere_core
  dsimp only
  apply ExS.ret
  ev

theorem tri_sdf_sphere_core_refines (px py pz r : Ref.F) (m : Mem) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_sdf_sphere_core
        [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 r.toNat] m =
      .ok (some (.f32 (Ref.sdfSphereCore px py pz r).toNat), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_sdf_sphere_core_refines' px py pz r m
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_sdf_sphere_core)
      (fn := Gen.tri_sdf_sphere_core)
      (args := [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 r.toNat])
      (m := m) (v := some (.f32 (Ref.sdfSphereCore px py pz r).toNat)) (s' := s')
      rfl rfl hx
  simpa [hmem] using h

-- ------------------------------------------------------------------- box ---

set_option maxHeartbeats 4000000 in
theorem tri_sdf_box_core_refines' (px py pz ex ey ez : Ref.F) (m : Mem) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_sdf_box_core.params
        [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 ex.toNat,
         .f32 ey.toNat, .f32 ez.toNat], m, false⟩
      Gen.tri_sdf_box_core.body
      (.ret (some (.f32 (Ref.sdfBoxCore px py pz ex ey ez).toNat))) s' ∧ s'.mem = m := by
  let qx := subBits (Ref.copysign px Ref.one) ex
  let qy := subBits (Ref.copysign py Ref.one) ey
  let qz := subBits (Ref.copysign pz Ref.one) ez
  let mx := Ref.fmax qx Ref.zero
  let my := Ref.fmax qy Ref.zero
  let mz := Ref.fmax qz Ref.zero
  let outsideRaw := addBits (addBits (mulBits mx mx) (mulBits my my)) (mulBits mz mz)
  let outside := Ref.sqrt outsideRaw
  let inside := Ref.fmin (Ref.fmax qx (Ref.fmax qy qz)) Ref.zero
  have hres : Ref.sdfBoxCore px py pz ex ey ez = addBits outside inside := by
    rfl
  let s0 : State := ⟨frameLocals Gen.tri_sdf_box_core.params
      [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 ex.toNat,
       .f32 ey.toNat, .f32 ez.toNat], m, false⟩
  let sf : State := ⟨s0.locals.upd 6 (.f32 qx.toNat) |>.upd 7 (.f32 qy.toNat)
      |>.upd 8 (.f32 qz.toNat) |>.upd 9 (.f32 mx.toNat) |>.upd 10 (.f32 my.toNat)
      |>.upd 11 (.f32 mz.toNat) |>.upd 12 (.f32 outside.toNat)
      |>.upd 13 (.f32 inside.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_sdf_box_core
  dsimp only
  rw [hres]
  apply ExS.seq
  · apply ExS.seq
    · setN (.f32 qx.toNat)
    · apply ExS.seq
      · setN (.f32 qy.toNat)
      · setN (.f32 qz.toNat)
  · apply ExS.seq
    · apply ExS.seq
      · setN (.f32 mx.toNat)
      · apply ExS.seq
        · setN (.f32 my.toNat)
        · setN (.f32 mz.toNat)
    · apply ExS.seq
      · setN (.f32 outside.toNat)
      · apply ExS.seq
        · setN (.f32 inside.toNat)
        · apply ExS.ret; evSdf

theorem tri_sdf_box_core_refines (px py pz ex ey ez : Ref.F) (m : Mem) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_sdf_box_core
        [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 ex.toNat,
         .f32 ey.toNat, .f32 ez.toNat] m =
      .ok (some (.f32 (Ref.sdfBoxCore px py pz ex ey ez).toNat), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_sdf_box_core_refines' px py pz ex ey ez m
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_sdf_box_core)
      (fn := Gen.tri_sdf_box_core)
      (args := [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 ex.toNat,
                .f32 ey.toNat, .f32 ez.toNat])
      (m := m) (v := some (.f32 (Ref.sdfBoxCore px py pz ex ey ez).toNat)) (s' := s')
      rfl rfl hx
  simpa [hmem] using h

-- ------------------------------------------------------------------ torus ---

set_option maxHeartbeats 4000000 in
theorem tri_sdf_torus_core_refines' (px py pz major minor : Ref.F) (m : Mem) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.tri_sdf_torus_core.params
        [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 major.toNat,
         .f32 minor.toNat], m, false⟩
      Gen.tri_sdf_torus_core.body
      (.ret (some (.f32 (Ref.sdfTorusCore px py pz major minor).toNat))) s' ∧ s'.mem = m := by
  let lxz := subBits (Ref.sqrt (addBits (mulBits px px) (mulBits pz pz))) major
  have hres : Ref.sdfTorusCore px py pz major minor =
      subBits (Ref.sqrt (addBits (mulBits lxz lxz) (mulBits py py))) minor := by
    rfl
  let s0 : State := ⟨frameLocals Gen.tri_sdf_torus_core.params
      [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 major.toNat,
       .f32 minor.toNat], m, false⟩
  let sf : State := ⟨s0.locals.upd 5 (.f32 lxz.toNat), m, false⟩
  refine ⟨sf, ?_, rfl⟩
  unfold Gen.tri_sdf_torus_core
  dsimp only
  rw [hres]
  apply ExS.seq
  · setN (.f32 lxz.toNat)
  · apply ExS.ret; evSdf

theorem tri_sdf_torus_core_refines (px py pz major minor : Ref.F) (m : Mem) :
    ∃ K, ∀ n, K ≤ n → callFunc Gen.prog n Gen.fid_tri_sdf_torus_core
        [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 major.toNat,
         .f32 minor.toNat] m =
      .ok (some (.f32 (Ref.sdfTorusCore px py pz major minor).toNat), m) := by
  obtain ⟨s', hx, hmem⟩ := tri_sdf_torus_core_refines' px py pz major minor m
  have h := callFunc_of_ExS (p := Gen.prog) (f := Gen.fid_tri_sdf_torus_core)
      (fn := Gen.tri_sdf_torus_core)
      (args := [.f32 px.toNat, .f32 py.toNat, .f32 pz.toNat, .f32 major.toNat,
                .f32 minor.toNat])
      (m := m) (v := some (.f32 (Ref.sdfTorusCore px py pz major minor).toNat)) (s' := s')
      rfl rfl hx
  simpa [hmem] using h

end LightRT.C.Proofs
