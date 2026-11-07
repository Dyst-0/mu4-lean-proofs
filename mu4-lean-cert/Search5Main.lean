import Mu4Comp5

/-! Driver: run the mu_4(5) search natively and print the counters per `P` (cross-check with `hp2_5` and
`mu45.py`; not part of the certificate). Usage: `mu4search5`. -/

open Mu4.N5

def main : IO Unit := do
  for k in [0:pList5.length] do
    let p := pList5.getD k (0, 0)
    let c : Counts5 := sList5.foldl (fun (acc : Counts5) s => acc.add (runPS5 p.1 p.2 s.1 s.2)) {}
    IO.println s!"P {k} ({p.1},{p.2}): cases={c.cases} invalid={c.invalid} errors={c.errors} sols={c.sols} r0={c.r0} adjacent_pairs={c.adj} independent_adjacent_triples={c.triples}"
