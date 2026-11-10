/-
  BVH validator: reads a scene dumped by `tools/bvhdump.c` (a BVH4/BVH8 built by
  the real C builder) on stdin and checks
  1. `checkWF` — the hypothesis of `Check.checked_run_root`: child node indices
     increase and every child box contains its child boxes / the exact
     (rational) triangles its leaves intersect;
  2. that a Lean mirror of `tri_intersect_scalar`'s loop, using the verified
     bit-level `Ref.raySetup` / `Ref.slab` (proved equal to the C functions) and
     C's per-slot leaf results, reproduces the C scalar traversal bit for bit
     (t and prim_id); and
  3. how often it differs from brute force over all reachable slots (a
     difference would be a box-test false miss, i.e. `C1` failing).
-/
import LightRT

open LightRT.C LightRT.FP.Binary32 LightRT.BVH LightRT.BVH.Check

def hexU (s : String) : UInt32 :=
  (s.toList.foldl (fun (acc : Nat) (c : Char) =>
    let h := if c.isDigit then c.toNat - '0'.toNat
      else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else c.toNat - 'A'.toNat + 10
    acc * 16 + h) 0).toUInt32

def decRef (r : UInt32) : CRef :=
  if r &&& 0x80000000 != 0 then .leaf ((r &&& 0x7fffffff) >>> 4).toNat (r &&& 0xf).toNat
  else .node r.toNat

def chunks {β : Type} (n : ℕ) : ℕ → List β → List (List β)
  | 0, _ => []
  | _, [] => []
  | f + 1, l => l.take n :: chunks n f (l.drop n)

/-- C's insertion step on the reversed (descending) hit list: shift while `prev > x`. -/
def insRev : List (CRef × Ref.F) → CRef × Ref.F → List (CRef × Ref.F)
  | [], x => [x]
  | e :: rest, x => if ltBits x.2 e.2 then e :: insRev rest x else x :: e :: rest

/-- Lean mirror of `tri_intersect_scalar` (prim-id tracking, bit-level). -/
def runC (robust : Bool) (G : Flat Box6 ℕ) (ids : ℕ → UInt32) (tab : ℕ → Option UInt32) (rc : Ref.RayCtx) :
    ℕ → List (CRef × Ref.F) → Ref.F → UInt32 → Ref.F × UInt32
  | 0, _, best, prim => (best, prim)
  | _ + 1, [], best, prim => (best, prim)
  | f + 1, (r, tn) :: st, best, prim =>
    if leBits best tn then runC robust G ids tab rc f st best prim else
    match r with
    | .leaf blk n =>
      let (b', p') := (G.leafPrims blk n).foldl (fun (b, p) s =>
        match tab s with
        | some t => if !(leBits b t) then (t, ids s) else (b, p)
        | none => (b, p)) (best, prim)
      runC robust G ids tab rc f st b' p'
    | .node i =>
      let hits := (G.children i).foldl (fun acc c =>
        let lo : Fin 3 → Ref.F := fun k => c.1[k.val]!
        let hi : Fin 3 → Ref.F := fun k => c.1[k.val + 3]!
        let (ok, tnear) := if robust then Ref.slabRobust rc lo hi best else Ref.slab rc lo hi best
        if ok then insRev acc (c.2, tnear) else acc) []
      runC robust G ids tab rc f (hits.reverse ++ st) best prim

def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut lines : Array (List String) := #[]
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    lines := lines.push ((l.trimAscii.toString.splitOn " ").filter (· ≠ ""))
  let hdr := lines[0]!
  let W := hdr[1]!.toNat!
  let root := decRef (hexU hdr[3]!)
  let nN := hdr[5]!.toNat!
  let nB := hdr[7]!.toNat!
  let robust := hdr.getD 9 "0" == "1"
  let nodes : List (List (Box6 × CRef)) := (List.range nN).map fun i =>
    let ws := (lines[1 + i]!.drop 2).map hexU
    (chunks 7 ws.length ws).map fun c => ((c.take 6).toArray, decRef (c.getD 6 0))
  let blocks : Array (Array UInt32) := (List.range nB).toArray.map fun b =>
    ((lines[1 + nN + b]!.drop 1).map hexU).toArray
  let tri : ℕ → Array UInt32 := fun s => (blocks[s / W]!).extract (10 * (s % W)) (10 * (s % W) + 9)
  let ids : ℕ → UInt32 := fun s => (blocks[s / W]!)[10 * (s % W) + 9]!
  let G : Flat Box6 ℕ := ⟨nodes, fun b => (List.range W).filterMap fun l =>
      if (blocks[b]!)[10 * l + 9]! == 0xffffffff then none else some (b * W + l), root⟩
  let wf := G.checkWF (insideQ tri) subQ
  -- per-check diagnostics on failure
  let mut badLeaf := 0
  let mut badSub := 0
  let mut badIdx := 0
  for i in List.range nN do
    for c in G.children i do
      match c.2 with
      | .leaf blk n => for p in G.leafPrims blk n do
          if !insideQ tri p c.1 then
            badLeaf := badLeaf + 1
            if badLeaf ≤ 3 then
              let t := tri p
              for k in List.range 3 do
                let v0 := (q t[k]!).getD 0
                let cs := [v0, v0 + (q t[3+k]!).getD 0, v0 + (q t[6+k]!).getD 0]
                let lo := (q c.1[k]!).getD 0
                let hi := (q c.1[k+3]!).getD 0
                for x in cs do
                  if x < lo then IO.eprintln s!"slot {p} axis {k}: below lo by {((lo - x) / (|lo| * (2:ℚ)^(-23:ℤ)) : ℚ).toFloat} ulp(lo)"
                  if x > hi then IO.eprintln s!"slot {p} axis {k}: above hi by {((x - hi) / (|hi| * (2:ℚ)^(-23:ℤ)) : ℚ).toFloat} ulp(hi)"
      | .node j =>
        if !(decide (i < j) && decide (j < nN)) then badIdx := badIdx + 1
        for c' in G.children j do if !subQ c'.1 c.1 then badSub := badSub + 1
  let reach := G.denRef root
  let mut rays := 0
  let mut agreeC := 0
  let mut agreeS := 0
  let mut agreeBrute := 0
  let mut hits := 0
  let mut maxUlpB := 0
  let mut missB := 0
  let mut maxUlpS := 0
  let mut fullS := 0
  let mut i := 1 + nN + nB
  let fuel := G.visitsRef root + 1
  while i + 1 < lines.size do
    let R := (lines[i]!.drop 1)
    let T := (lines[i + 1]!.drop 1)
    i := i + 2
    let w := R.take 8 |>.map hexU
    let org : Fin 3 → Ref.F := fun k => w[k.val]!
    let dir : Fin 3 → Ref.F := fun k => w[4 + k.val]!
    let rc := Ref.raySetup org dir w[3]!
    let tab : ℕ → Option UInt32 := fun s => match T[s]? with
      | some "-" => none
      | some x => some (hexU x)
      | none => none
    let (bt, bp) := runC robust G ids tab rc fuel [(root, rc.tmin)] w[7]! 0xffffffff
    let res : Nat × UInt32 × UInt32 := if bp == 0xffffffff then (0, 0, bp) else (1, bt, bp)
    let cS : Nat × UInt32 × UInt32 := (R[8]!.toNat!, hexU R[9]!, hexU R[10]!)
    let cV : Nat × UInt32 × UInt32 := (R[11]!.toNat!, hexU R[12]!, hexU R[13]!)
    -- brute force over all reachable slots (same accept rule)
    let (btB, bpB) := reach.foldl (fun (b, p) s => match tab s with
      | some t => if !(leBits b t) then (t, ids s) else (b, p)
      | none => (b, p)) (w[7]!, (0xffffffff : UInt32))
    let resB : Nat × UInt32 := if bpB == 0xffffffff then (0, 0) else (1, btB)
    rays := rays + 1
    if res == cS then agreeC := agreeC + 1
    else IO.eprintln s!"ray {rays}: lean {res} C {cS}"
    if res.2.1 == cV.2.1 && res.1 == cV.1 then agreeS := agreeS + 1
    if res == cV then fullS := fullS + 1
    if (res.1, res.2.1) == resB then agreeBrute := agreeBrute + 1
    else
      let tq := fun (x : UInt32) => ((q x).getD 0).toFloat
      IO.eprintln s!"ray {rays}: BVH {res.1} t={tq res.2.1} prim={res.2.2}  brute {resB.1} t={tq resB.2} prim={bpB} slot-inside-its-boxes={(reach.filter (fun s => ids s == bpB)).map (fun s => (G.nodes.zipIdx.filterMap (fun (ch, _) => (ch.find? (fun c => match c.2 with | .leaf blk n => (G.leafPrims blk n).contains s | _ => false)).map (fun c => insideQ tri s c.1))))}"
    if res.1 == 1 then hits := hits + 1
    let ulpd := fun (a b : UInt32) => if a ≥ b then (a - b).toNat else (b - a).toNat
    if res.1 == 1 && resB.1 == 1 then maxUlpB := max maxUlpB (ulpd res.2.1 resB.2)
    if res.1 != resB.1 then missB := missB + 1
    if res.1 == 1 && cV.1 == 1 then maxUlpS := max maxUlpS (ulpd res.2.1 cV.2.1)
  IO.println s!"W={W} nodes={nN} blocks={nB} reachable={reach.length} checkWF={wf} (bad leaf={badLeaf} sub={badSub} idx={badIdx})"
  IO.println s!"rays={rays} hits={hits} lean==C-scalar(t,prim)={agreeC} t==C-dispatched={agreeS} (t,prim)==C-dispatched={fullS} t==brute={agreeBrute} hit/miss-vs-brute={missB} max-ulp(t-brute)={maxUlpB} max-ulp(scalar-dispatched)={maxUlpS}"
