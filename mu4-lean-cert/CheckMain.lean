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
    IO.println s!"p={pi} s={si} checkPS={checkPS p0 p1 s0 s1}"
