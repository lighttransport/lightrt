/-
  Differential-testing driver: runs the MiniC semantics of the translated C
  (`LightRT.C.Gen`, executed with the bit-exact binary32 semantics of
  `LightRT.FP.Binary32`) on test vectors read from stdin, printing results in
  the format of `tools/cdiff_c.c` (which runs the real compiled C).
  `tools/cdiff.py` generates the vectors and compares the two outputs.

  Input lines (all floats as 8-digit hex binary32 bit patterns):
    slab o0 o1 o2 tmin d0 d1 d2 tmax lo0 lo1 lo2 hi0 hi1 hi2 tbest
    mt   o0 o1 o2 d0 d1 d2 v00 v01 v02 v10 v11 v12 v20 v21 v22 tmin tbest
    slabr <slab fields>       (default build: GenRobust vs Ref.slabRobust)
    slabk <slab fields> K     (Lean reference of the inflated slab only)
-/
import LightRT

open LightRT.C

def hexNat (s : String) : Nat :=
  s.toList.foldl (fun acc c =>
    let h := if c.isDigit then c.toNat - '0'.toNat
      else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else c.toNat - 'A'.toNat + 10
    acc * 16 + h) 0

def hex8 (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

def blockOf (ws : List Nat) : Block := ws.flatMap (fun w => encodeLE 4 w)

def mkMem (blocks : List Block) : Mem := fun b => blocks[b]?

def fuel : Nat := 10000

def rd32 (m : Mem) (b o : Nat) : Nat :=
  match m b with
  | some blk => decodeLE ((blk.drop o).take 4)
  | none => 0

def runSlab (w : List Nat) : String :=
  -- block 0: lrt_ray {org[3], tmin, dir[3], tmax}; block 1: tri_ray_ctx (56 B)
  -- blocks 2..7: lo_x lo_y lo_z hi_x hi_y hi_z (one float each); block 8: tnear_out
  let ray := blockOf (w.take 8)
  let box := (w.drop 8).take 6
  let tbest := w.getD 14 0
  let m0 := mkMem ([ray, List.replicate 56 0] ++ box.map (fun x => blockOf [x]) ++ [blockOf [0]])
  match callFunc Gen.prog fuel Gen.fid_tri_ray_setup [.ptr 0 0, .ptr 1 0] m0 with
  | .ok (_, m1) =>
    let setup := " ".intercalate ((List.range 13).map (fun k => hex8 (rd32 m1 1 (4 * k))))
    let args : List Val := [.ptr 2 0, .ptr 3 0, .ptr 4 0, .ptr 5 0, .ptr 6 0, .ptr 7 0,
      .int ⟨32, true⟩ 0, .ptr 1 0, .f32 tbest, .ptr 8 0]
    match callFunc Gen.prog fuel Gen.fid_tri_slab_scalar args m1 with
    | .ok (some (.int _ r), m2) => s!"{setup} {r} {hex8 (rd32 m2 8 0)}"
    | .ok _ => "ERR noval"
    | .ub => "UB"
    | .timeout => "TIMEOUT"
  | .ub => "UB setup"
  | _ => "ERR setup"

/-- `slabr`: the default build (`GenRobust`, 68-byte ctx with `sinv[3]`). -/
def runSlabR (w : List Nat) : String :=
  let ray := blockOf (w.take 8)
  let box := (w.drop 8).take 6
  let tbest := w.getD 14 0
  let m0 := mkMem ([ray, List.replicate 68 0] ++ box.map (fun x => blockOf [x]) ++ [blockOf [0]])
  match callFunc GenRobust.prog fuel GenRobust.fid_tri_ray_setup [.ptr 0 0, .ptr 1 0] m0 with
  | .ok (_, m1) =>
    let setup := " ".intercalate (((List.range 13).map (fun k => 4 * k) ++ [56, 60, 64]).map
      (fun o => hex8 (rd32 m1 1 o)))
    let args : List Val := [.ptr 2 0, .ptr 3 0, .ptr 4 0, .ptr 5 0, .ptr 6 0, .ptr 7 0,
      .int ⟨32, true⟩ 0, .ptr 1 0, .f32 tbest, .ptr 8 0]
    match callFunc GenRobust.prog fuel GenRobust.fid_tri_slab_scalar args m1 with
    | .ok (some (.int _ r), m2) => s!"{setup} {r} {hex8 (rd32 m2 8 0)}"
    | .ok _ => "ERR noval"
    | .ub => "UB"
    | .timeout => "TIMEOUT"
  | .ub => "UB setup"
  | _ => "ERR setup"

def runMt (w : List Nat) : String :=
  -- blocks 0..4: o d v0 v1 v2 (3 floats each); blocks 5..7: t u v outputs
  let vecs := (List.range 5).map (fun k => blockOf ((w.drop (3 * k)).take 3))
  let tmin := w.getD 15 0
  let tbest := w.getD 16 0
  let m0 := mkMem (vecs ++ [blockOf [0], blockOf [0], blockOf [0]])
  let args : List Val := [.ptr 0 0, .ptr 1 0, .ptr 2 0, .ptr 3 0, .ptr 4 0,
    .f32 tmin, .f32 tbest, .ptr 5 0, .ptr 6 0, .ptr 7 0]
  match callFunc Gen.prog fuel Gen.fid_tri_mt_one args m0 with
  | .ok (some (.int _ r), m) =>
    if r = 1 then s!"1 {hex8 (rd32 m 5 0)} {hex8 (rd32 m 6 0)} {hex8 (rd32 m 7 0)}" else s!"{r}"
  | .ok _ => "ERR noval"
  | .ub => "UB"
  | .timeout => "TIMEOUT"

def runWoop (w : List Nat) : String :=
  let vecs := (List.range 5).map (fun k => blockOf ((w.drop (3 * k)).take 3))
  let m0 := mkMem (vecs ++ [blockOf [0], blockOf [0], blockOf [0]])
  let args : List Val := [.ptr 0 0, .ptr 1 0, .ptr 2 0, .ptr 3 0, .ptr 4 0,
    .f32 (w.getD 15 0), .f32 (w.getD 16 0), .ptr 5 0, .ptr 6 0, .ptr 7 0]
  match callFunc Gen.prog fuel Gen.fid_tri_woop_one args m0 with
  | .ok (some (.int _ r), m) =>
    if r = 1 then s!"1 {hex8 (rd32 m 5 0)} {hex8 (rd32 m 6 0)} {hex8 (rd32 m 7 0)}" else s!"{r}"
  | .ok _ => "ERR noval"
  | .ub => "UB"
  | .timeout => "TIMEOUT"

def v3 (w : List Nat) (k : Nat) : Fin 3 → Ref.F := fun i => (w.getD (k + i.val) 0).toUInt32
def h (x : Ref.F) : String := hex8 x.toNat

/-- The bit-level Lean reference (`LightRT.C.Ref`) in the same output format. -/
def refSlab (w : List Nat) : String :=
  let rc := Ref.raySetup (v3 w 0) (v3 w 4) (w.getD 3 0).toUInt32
  let ws := [rc.org 0, rc.org 1, rc.org 2, rc.dir 0, rc.dir 1, rc.dir 2, rc.invd 0, rc.invd 1,
             rc.invd 2, rc.oinv 0, rc.oinv 1, rc.oinv 2, rc.tmin]
  let (hit, tn) := Ref.slab rc (v3 w 8) (v3 w 11) (w.getD 14 0).toUInt32
  " ".intercalate (ws.map h) ++ s!" {if hit then 1 else 0} {h tn}"

def refSlabR (w : List Nat) : String :=
  let rc := Ref.raySetup (v3 w 0) (v3 w 4) (w.getD 3 0).toUInt32
  let si := LightRT.C.Proofs.sinvOf rc
  let ws := [rc.org 0, rc.org 1, rc.org 2, rc.dir 0, rc.dir 1, rc.dir 2, rc.invd 0, rc.invd 1,
             rc.invd 2, rc.oinv 0, rc.oinv 1, rc.oinv 2, rc.tmin, si 0, si 1, si 2]
  let (hit, tn) := Ref.slabRobust rc (v3 w 8) (v3 w 11) (w.getD 14 0).toUInt32
  " ".intercalate (ws.map h) ++ s!" {if hit then 1 else 0} {h tn}"

def refMt (w : List Nat) : String :=
  match Ref.mt (v3 w 0) (v3 w 3) (v3 w 6) (v3 w 9) (v3 w 12) (w.getD 15 0).toUInt32
      (w.getD 16 0).toUInt32 with
  | some (t, u, v) => s!"1 {h t} {h u} {h v}"
  | none => "0"

def refWoop (w : List Nat) : String :=
  match Ref.woop (v3 w 0) (v3 w 3) (v3 w 6) (v3 w 9) (v3 w 12) (w.getD 15 0).toUInt32
      (w.getD 16 0).toUInt32 with
  | some (t, u, v) => s!"1 {h t} {h u} {h v}"
  | none => "0"

/-- MiniC result; if the Lean reference disagrees, flag it so cdiff fails. -/
def runLine (line : String) : String :=
  let check (mc ref : String) := if mc == ref then mc else mc ++ " REFDIFF " ++ ref
  match (line.trimAscii.toString.splitOn " ").filter (· ≠ "") with
  | "slab" :: rest => let w := rest.map hexNat; check (runSlab w) (refSlab w)
  | "slabr" :: rest => let w := rest.map hexNat; check (runSlabR w) (refSlabR w)
  | "mt" :: rest => let w := rest.map hexNat; check (runMt w) (refMt w)
  | "woop" :: rest => let w := rest.map hexNat; check (runWoop w) (refWoop w)
  | "slabk" :: rest =>
    let w := rest.map hexNat
    let rc := Ref.raySetup (v3 w 0) (v3 w 4) (w.getD 3 0).toUInt32
    if Ref.slabInflated rc (v3 w 8) (v3 w 11) (w.getD 14 0).toUInt32 (w.getD 15 0).toUInt32
    then "1" else "0"
  | _ => "BADLINE"

partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  o.putStrLn (runLine line)
  o.flush
  loop h o

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
