import Mu4Comp.Search.Dir
import Mu4Comp.Data
open Mu4.Search

def tablesOnly (X : PCtx) (d : CaseData) (K : Nat × Nat) : Nat :=
  let y1 := combo4 K.1 d.bY
  let y2 := combo4 K.2 d.bY
  let tss := d.off.map (·.2)
  let tbls := tss.map fun ts => mkTable ts y1 y2
  tbls.length + (tbls.map fun t => (t.getD 0 []).length).sum

def keysOnly (X : PCtx) (d : CaseData) (K : Nat × Nat) : Nat :=
  let y1 := combo4 K.1 d.bY
  let y2 := combo4 K.2 d.bY
  let keysT := d.rhoOff.map fun rhos =>
    X.tcols.map fun tc => keyR rhos (applyCols tc y1) (applyCols tc y2)
  (keysT.map List.sum).sum

def candsOnly (X : PCtx) (d : CaseData) (K : Nat × Nat) : Nat :=
  let y1 := combo4 K.1 d.bY
  let y2 := combo4 K.2 d.bY
  let tss := d.off.map (·.2)
  let tbls := tss.map fun ts => mkTable ts y1 y2
  let keysT := d.rhoOff.map fun rhos =>
    X.tcols.map fun tc => keyR rhos (applyCols tc y1) (applyCols tc y2)
  (dirs.filter fun c => (candsAt tbls keysT c).isSome).length

def timeIt (name : String) (f : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{name}: {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"  {name} {t1 - t0} ms"

def main (args : List String) : IO Unit := do
  let pi := (args.getD 0 "0").toNat!
  let si := (args.getD 1 "0").toNat!
  let (p0, p1) := pList.getD pi (0, 0)
  let (s0, s1) := sList.getD si (0, 0)
  let X := mkPCtx p0 p1
  let ds := patterns.filterMap fun (mu, ws) => match setupCase X s0 s1 mu ws with
    | .valid d => some d | _ => none
  IO.println s!"valid {ds.length}"
  timeIt "tables" fun _ => (ds.map fun d => (rrefPairs.map (tablesOnly X d)).sum).sum
  timeIt "keys" fun _ => (ds.map fun d => (rrefPairs.map (keysOnly X d)).sum).sum
  timeIt "cands" fun _ => (ds.map fun d => (rrefPairs.map (candsOnly X d)).sum).sum
  timeIt "solsK" fun _ => (ds.map fun d => (rrefPairs.flatMap (solsK X d)).length).sum
