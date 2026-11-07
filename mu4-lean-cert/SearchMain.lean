import Mu4Comp.Search.Dir
import Mu4Comp.Data
open Mu4.Search

def main (args : List String) : IO Unit := do
  let pi := (args.getD 0 "0").toNat!
  let sFrom := (args.getD 1 "0").toNat!
  let sTo := (args.getD 2 "69").toNat!
  let (p0, p1) := pList.getD pi (0, 0)
  for si in [sFrom:sTo] do
    let (s0, s1) := sList.getD si (0, 0)
    let t0 ← IO.monoMsNow
    let c := runPS p0 p1 s0 s1
    let t1 ← IO.monoMsNow
    IO.println s!"p={pi} s={si} cases={c.cases} invalid={c.invalid} errors={c.errors} nsol={c.sols} r0={c.r0} r1={c.r1} r2={c.r2} edges={c.edges} tri={c.tri} coll={c.collinear} pass={c.pass} ms={t1 - t0}"
