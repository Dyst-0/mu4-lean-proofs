import Mu4Comp.Search.Case

/-!
# Direction search and triangle assembly for one valid case

Solutions are `(c, G)` with `c` a normalized direction of `A/P` (a code of GF(4)^4 on the basis
`tv`) and one operator per block (an 8-bit 2×2 matrix code at a pair, a GF(4) code at a single),
such that `E = M_{x_c} - ∑_m G_m Block_m` has rank ≤ 2 and every `G_m` is diagonalizable.
-/

namespace Mu4.Search
open F4

/-- `G Block y` for a block with terms `ts` and operator code `G`. -/
def applyG (G : Nat) (ts : List Term) (y : Nat) : Nat :=
  match ts with
  | [(g0, f0), (g1, f1)] =>
    let a := dotC f0 y
    let b := dotC f1 y
    smulC (m00 G * a + m01 G * b) g0 ^^^ smulC (m10 G * a + m11 G * b) g1
  | [(g0, f0)] => smulC (coordC G 0 * dotC f0 y) g0
  | _ => 0

/-- Lookup key of `G · B` where `B[v][col] = f_v(y_col)`: entry `[u][col]` at coordinate `2u+col`
(pairs), entry `[col]` at coordinate `col` (singles). -/
def keyG (ts : List Term) (y1 y2 G : Nat) : Nat :=
  match ts with
  | [(_, f0), (_, f1)] =>
    let b00 := dotC f0 y1
    let b01 := dotC f0 y2
    let b10 := dotC f1 y1
    let b11 := dotC f1 y2
    mat2 (m00 G * b00 + m01 G * b10) (m00 G * b01 + m01 G * b11)
      (m10 G * b00 + m11 G * b10) (m10 G * b01 + m11 G * b11)
  | [(_, f0)] => unitC (coordC G 0 * dotC f0 y1) 0 ^^^ unitC (coordC G 0 * dotC f0 y2) 1
  | _ => 0

/-- Lookup key of the right-hand side: Gam-coordinates of `x y1, x y2` in the block. -/
def keyR (rhos : List Nat) (xy1 xy2 : Nat) : Nat :=
  match rhos with
  | [r0, r1] => mat2 (dotC r0 xy1) (dotC r0 xy2) (dotC r1 xy1) (dotC r1 xy2)
  | [r0] => unitC (dotC r0 xy1) 0 ^^^ unitC (dotC r0 xy2) 1
  | _ => 0

/-- Candidate operators of a block: all 124 diagonalizable 2×2 matrices at a pair, all 4 scalars
at a single. -/
def candOps (ts : List Term) : List Nat := if ts.length = 2 then diag2 else [0, 1, 2, 3]

/-- `keyG` from the precomputed entries `b00 = f0(y1), b01 = f0(y2), b10 = f1(y1), b11 = f1(y2)`. -/
@[inline] def keyGB (two : Bool) (b00 b01 b10 b11 : F4) (G : Nat) : Nat :=
  if two then
    mat2 (m00 G * b00 + m01 G * b10) (m00 G * b01 + m01 G * b11)
      (m10 G * b00 + m11 G * b10) (m10 G * b01 + m11 G * b11)
  else unitC (coordC G 0 * b00) 0 ^^^ unitC (coordC G 0 * b01) 1

/-- The entries of `B` for a block. -/
def bEntries (ts : List Term) (y1 y2 : Nat) : F4 × F4 × F4 × F4 :=
  match ts with
  | [(_, f0), (_, f1)] => (dotC f0 y1, dotC f0 y2, dotC f1 y1, dotC f1 y2)
  | [(_, f0)] => (dotC f0 y1, dotC f0 y2, 0, 0)
  | _ => (0, 0, 0, 0)

/-- Lookup table `key ↦ operators with that key`, for the block entries `b`. -/
def tableOf (two : Bool) (b00 b01 b10 b11 : F4) : Array (List Nat) :=
  (if two then diag2 else [0, 1, 2, 3]).foldl
    (fun arr G => arr.modify (keyGB two b00 b01 b10 b11 G) (G :: ·)) (Array.replicate 256 [])

/-- All tables of pair blocks, indexed by the code `mat2 b00 b01 b10 b11` of `B`. -/
def pairTables : Array (Array (List Nat)) :=
  Array.ofFn (n := 256) fun b => tableOf true (coordC b.val 0) (coordC b.val 1) (coordC b.val 2)
    (coordC b.val 3)

/-- All tables of single blocks, indexed by the code `mat2 b00 b01 0 0`. -/
def singleTables : Array (Array (List Nat)) :=
  Array.ofFn (n := 16) fun b => tableOf false (coordC b.val 0) (coordC b.val 1) 0 0

/-- Lookup table `key ↦ operators with that key` of a block (from the global tables). -/
def mkTable (ts : List Term) (y1 y2 : Nat) : Array (List Nat) :=
  match ts with
  | [(_, f0), (_, f1)] =>
    pairTables.getD (mat2 (dotC f0 y1) (dotC f0 y2) (dotC f1 y1) (dotC f1 y2))
      (tableOf true (dotC f0 y1) (dotC f0 y2) (dotC f1 y1) (dotC f1 y2))
  | [(_, f0)] =>
    singleTables.getD (mat2 (dotC f0 y1) (dotC f0 y2) 0 0) (tableOf false (dotC f0 y1) (dotC f0 y2) 0 0)
  | _ => singleTables.getD (mat2 0 0 0 0) (tableOf false 0 0 0 0)

/-- All lists choosing one element from each list. -/
def choices : List (List Nat) → List (List Nat)
  | [] => [[]]
  | l :: ls => l.flatMap fun x => (choices ls).map (x :: ·)

/-- A solution: direction, operators of the off blocks, operator at `m0`. -/
structure Sol where
  c : Nat
  goff : List Nat
  g0 : Nat
  deriving Inhabited, DecidableEq

/-- `E y` for a solution. -/
def Eval (X : PCtx) (d : CaseData) (s : Sol) (y : Nat) : Nat :=
  applyCols (X.xcCols s.c) y ^^^
    ((d.off.zip s.goff).map fun ((_, ts), G) => applyG G ts y).foldl (· ^^^ ·) 0 ^^^
    applyG s.g0 [(d.ga, d.fa), (d.gb, d.fb)] y

/-- `E` without the `m0` block, with the columns `xcols` of `x_c`. -/
def E0val (xcols : List Nat) (d : CaseData) (goff : List Nat) (y : Nat) : Nat :=
  applyCols xcols y ^^^
    ((d.off.zip goff).map fun ((_, ts), G) => applyG G ts y).foldl (· ^^^ ·) 0

/-- Pivot list of `W_{m0}`, for reduction modulo `W_{m0}`. -/
def pivW (d : CaseData) : List (Nat × Nat) := [d.ga, d.gb].foldl (insertPivot 6) []

/-- `G Block y` from the entries `(f0(y), f1(y))` of the block at `y`. -/
@[inline] def applyGE (G : Nat) (ts : List Term) (e : F4 × F4) : Nat :=
  match ts with
  | [(g0, _), (g1, _)] =>
    smulC (m00 G * e.1 + m01 G * e.2) g0 ^^^ smulC (m10 G * e.1 + m11 G * e.2) g1
  | [(g0, _)] => smulC (coordC G 0 * e.1) g0
  | _ => 0

/-- Entries `(f0(y), f1(y))` of a block at `y`. -/
@[inline] def entriesAt (ts : List Term) (y : Nat) : F4 × F4 :=
  match ts with
  | [(_, f0), (_, f1)] => (dotC f0 y, dotC f1 y)
  | [(_, f0)] => (dotC f0 y, 0)
  | _ => (0, 0)

/-- `∑_b G_b Block_b y` over the off blocks, from per-block entries at `y`. -/
def offContrib (tss : List (List Term)) (goff : List Nat) (ents : List (F4 × F4)) : Nat :=
  match tss, goff, ents with
  | ts :: tss, G :: goff, e :: ents => applyGE G ts e ^^^ offContrib tss goff ents
  | _, _, _ => 0

/-- Insert `v` into a pivot list, unless the rank would exceed 2. -/
def push2 (piv : List (Nat × Nat)) (v : Nat) : Option (List (Nat × Nat)) :=
  let piv' := insertPivot 6 piv v
  if piv'.length ≤ 2 then some piv' else none

/-- Insert a list of vectors, failing as soon as the rank exceeds 2. -/
def pushAll2 (piv : List (Nat × Nat)) : List Nat → Option (List (Nat × Nat))
  | [] => some piv
  | v :: vs => match push2 piv v with
    | some p => pushAll2 p vs
    | none => none

/-- Candidates of each block at direction `c` (all must be nonempty). -/
def candsAt (tbls : List (Array (List Nat))) (keysT : List (List Nat)) (c : Nat) :
    Option (List (List Nat)) :=
  match tbls, keysT with
  | tb :: tbls, ks :: keysT =>
    let l := tb.getD (combo4 c ks) []
    if l.isEmpty then none else (candsAt tbls keysT c).map (l :: ·)
  | _, _ => some []

/-- Precomputed data of one `K`: the vectors `es`, `ea`, `eb`, the block entries there. -/
structure KData where
  es : List Nat
  entEs : List (List (F4 × F4))
  entA : List (F4 × F4)
  entB : List (F4 × F4)

/-- Solutions with a given first column `colA` of the operator at `m0`. -/
def solsColA (d : CaseData) (c : Nat) (goff : List Nat) (pbase : List (Nat × Nat))
    (vea veb colA : Nat) : List Sol :=
  let vA := vea ^^^ smulC (coordC colA 0) d.ga ^^^ smulC (coordC colA 1) d.gb
  match push2 pbase vA with
  | none => []
  | some pA => (List.range 16).filterMap fun colC =>
    let vC := veb ^^^ smulC (coordC colC 0) d.ga ^^^ smulC (coordC colC 1) d.gb
    let g0 := mat2 (coordC colA 0) (coordC colC 0) (coordC colA 1) (coordC colC 1)
    if (push2 pA vC).isSome && diagPred g0 then some { c, goff, g0 } else none

/-- Solutions with a given choice `goff` of the off-block operators. -/
def solsGoff (d : CaseData) (tss : List (List Term)) (kd : KData) (c : Nat) (xes : List Nat)
    (xea xeb : Nat) (goff : List Nat) : List Sol :=
  let e0 := (xes.zip kd.entEs).map fun (x, ents) => x ^^^ offContrib tss goff ents
  match pushAll2 [] (e0.map (reduceBy (pivW d))) with
  | none => []
  | some _ =>
  match pushAll2 [] (e0.take 2) with
  | none => []
  | some pbase =>
  (List.range 16).flatMap (solsColA d c goff pbase (xea ^^^ offContrib tss goff kd.entA)
    (xeb ^^^ offContrib tss goff kd.entB))

/-- Solutions found from `K` and direction `c`. -/
def solsKc (X : PCtx) (d : CaseData) (tss : List (List Term)) (tbls : List (Array (List Nat)))
    (keysT : List (List Nat)) (kd : KData) (c : Nat) : List Sol :=
  match candsAt tbls keysT c with
  | none => []
  | some cands =>
    let xcols := X.xcCols c
    (choices cands).flatMap (solsGoff d tss kd c (kd.es.map (applyCols xcols))
      (applyCols xcols d.ea) (applyCols xcols d.eb))

/-- The pivot positions of an RREF pair. -/
def pivots (K : Nat × Nat) : Nat × Nat := ((firstNZ K.1 0 4).getD 0, (firstNZ K.2 0 4).getD 0)

/-- Solutions from one `K`. -/
def solsK (X : PCtx) (d : CaseData) (K : Nat × Nat) : List Sol :=
  let y1 := combo4 K.1 d.bY
  let y2 := combo4 K.2 d.bY
  let (p, q) := pivots K
  let es := ((List.range 4).filter fun i => i != p && i != q).map (fun i => d.bY.getD i 0) ++
    [d.ea, d.eb]
  let tss := d.off.map (·.2)
  let tbls := tss.map fun ts => mkTable ts y1 y2
  let ty := X.tcols.map fun tc => (applyCols tc y1, applyCols tc y2)
  let keysT := d.rhoOff.map fun rhos => ty.map fun (a, b) => keyR rhos a b
  let kd : KData := { es, entEs := es.map fun y => tss.map fun ts => entriesAt ts y,
                      entA := tss.map fun ts => entriesAt ts d.ea,
                      entB := tss.map fun ts => entriesAt ts d.eb }
  dirs.flatMap (solsKc X d tss tbls keysT kd)

/-- Deduplicate (quadratic; the lists are short). -/
def dedupSols : List Sol → List Sol
  | [] => []
  | s :: l => let r := dedupSols l; if r.contains s then r else s :: r

/-- A recorded solution with its `E` columns and computed rank. -/
structure SolE where
  s : Sol
  cols : List Nat
  rk : Nat
  deriving Inhabited

def withE (X : PCtx) (d : CaseData) (s : Sol) : SolE :=
  let cols := (List.range 6).map fun t => Eval X d s (eC t)
  { s, cols, rk := rankC cols }

/-- All solutions of the case (computed rank ≤ 2 on all six columns). -/
def allSols (X : PCtx) (d : CaseData) : List SolE :=
  ((dedupSols (rrefPairs.flatMap (solsK X d))).map (withE X d)).filter (·.rk ≤ 2)

/-- `λ • u + v` for column lists. -/
def addCols (lam : F4) (u v : List Nat) : List Nat := (u.zip v).map fun (a, b) => smulC lam a ^^^ b

/-- Pair-block operators of a solution (for commutation). -/
def pairOps (d : CaseData) (s : Sol) : List Nat :=
  s.g0 :: ((d.off.zip s.goff).filterMap fun ((_, ts), G) => if ts.length = 2 then some G else none)

/-- Edge test: distinct directions, commuting pair operators, rank ≤ 3 on the whole line.
Returns `some interior` with `interior` = some interior point has rank ≤ 2. -/
def edge (d : CaseData) (a b : SolE) : Option Bool :=
  if a.s.c == b.s.c then none else
  if !((pairOps d a.s).zip (pairOps d b.s)).all (fun (G, H) => comm2 G H) then none else
  let rks := [o, w, w2].map fun lam => rankC (addCols lam b.cols a.cols)
  if rks.all (· ≤ 3) then some (rks.any (· ≤ 2)) else none

/-- `c3 ∈ span(c1, c2)` (codes of GF(4)^4), by search over 16 combinations. -/
def inSpan2 (c1 c2 c3 : Nat) : Bool :=
  (List.range 16).any fun ab => (smulC (coordC ab 0) c1 ^^^ smulC (coordC ab 1) c2) == c3

/-- `u, u'` independent in GF(4)^4, as a Bool on 8-bit codes. -/
def indep4 (u u' : Nat) : Bool :=
  (List.range 16).all fun ab => ab == 0 ||
    (smulC (coordC ab 0) u ^^^ smulC (coordC ab 1) u') % 256 != 0

/-- Every independent pair of 8-bit codes spans some pair of `rrefPairs` (finite check). -/
def rrefCoverOK : Bool :=
  (List.range 256).all fun u => (List.range 256).all fun u' =>
    !indep4 u u' || rrefPairs.any fun K => inSpan2 u u' K.1 && inSpan2 u u' K.2

/-- Counters of a case. -/
structure Counts where
  cases : Nat := 0
  invalid : Nat := 0
  errors : Nat := 0
  sols : Nat := 0
  r0 : Nat := 0
  r1 : Nat := 0
  r2 : Nat := 0
  edges : Nat := 0
  tri : Nat := 0
  collinear : Nat := 0
  pass : Nat := 0
  deriving Repr

def Counts.add (a b : Counts) : Counts :=
  { cases := a.cases + b.cases, invalid := a.invalid + b.invalid, errors := a.errors + b.errors,
    sols := a.sols + b.sols, r0 := a.r0 + b.r0, r1 := a.r1 + b.r1, r2 := a.r2 + b.r2,
    edges := a.edges + b.edges, tri := a.tri + b.tri, collinear := a.collinear + b.collinear,
    pass := a.pass + b.pass }

/-- Edges and triangles of a list of solutions (counters, for the cross-check with hp2). -/
def assemble (d : CaseData) (sols : Array SolE) : Counts := Id.run do
  let n := sols.size
  let mut adj : Array (Array (Option Bool)) := #[]
  let mut nedge := 0
  for i in [0:n] do
    let mut row : Array (Option Bool) := Array.replicate n none
    for j in [i+1:n] do
      let e := edge d sols[i]! sols[j]!
      if e.isSome then nedge := nedge + 1
      row := row.set! j e
    adj := adj.push row
  let mut tri := 0
  let mut coll := 0
  let mut pass := 0
  for i in [0:n] do
    for j in [i+1:n] do
      match (adj.getD i #[]).getD j none with
      | none => pure ()
      | some iij =>
        for k in [j+1:n] do
          match (adj.getD i #[]).getD k none, (adj.getD j #[]).getD k none with
          | some iik, some ijk =>
            if inSpan2 sols[i]!.s.c sols[j]!.s.c sols[k]!.s.c then coll := coll + 1
            else
              tri := tri + 1
              if sols[i]!.rk ≤ 1 || sols[j]!.rk ≤ 1 || sols[k]!.rk ≤ 1 || (iij && iik && ijk) then
                pass := pass + 1
          | _, _ => pure ()
  return { edges := nedge, tri, collinear := coll, pass }

/-- The final test on a triangle of solutions with edge flags `iij, iik, ijk`. -/
def triPass (a b c : SolE) (iab iac ibc : Bool) : Bool :=
  a.rk ≤ 1 || b.rk ≤ 1 || c.rk ≤ 1 || (iab && iac && ibc)

/-- No passing triangle: for all `i < j < k` with edges `ij, ik, jk` and independent directions,
the final test fails. This is the statement that `native_decide` checks. -/
def triFree (d : CaseData) (sols : List SolE) : Bool :=
  let arr := sols.toArray
  let n := arr.size
  let adj : Array (Array (Option Bool)) := Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j =>
    if i.val < j.val then edge d arr[i] arr[j] else none
  (List.range n).all fun i => (List.range n).all fun j =>
    match (adj.getD i #[]).getD j none with
    | none => true
    | some iij => (List.range n).all fun k =>
      !(j < k) ||
      match (adj.getD i #[]).getD k none, (adj.getD j #[]).getD k none with
      | some iik, some ijk =>
        inSpan2 (arr.getD i default).s.c (arr.getD j default).s.c (arr.getD k default).s.c ||
          !triPass (arr.getD i default) (arr.getD j default) (arr.getD k default) iij iik ijk
      | _, _ => true

/-- Term data of the off blocks, by index. -/
def blkOf (d : CaseData) (i : Nat) : List Term := (d.off.getD i (0, [])).2
def gOf (d : CaseData) (i u : Nat) : Nat := ((blkOf d i).getD u (0, 0)).1
def rhoOf (d : CaseData) (i u : Nat) : Nat := (d.rhoOff.getD i []).getD u 0

/-- Runtime certificate of the invariants of a valid case (block shapes, duality of the rows
`rhoOff` with the block vectors, the basis `bY` of `ker fa ∩ ker fb`, the duals `ea, eb`, and the
independence of `ga, gb`). -/
def wfCheck (d : CaseData) : Bool :=
  let n := d.off.length
  d.rhoOff.length == n &&
  (List.range n).all (fun i => ((blkOf d i).length == 1 || (blkOf d i).length == 2) &&
    (d.rhoOff.getD i []).length == (blkOf d i).length) &&
  (List.range n).all (fun i => (List.range (blkOf d i).length).all fun u =>
    (List.range n).all fun j => (List.range (blkOf d j).length).all fun u' =>
      dotC (rhoOf d i u) (gOf d j u') == (if i == j && u == u' then 1 else 0)) &&
  d.bY.length == 4 && d.bY.all (fun y => dotC d.fa y == 0 && dotC d.fb y == 0) &&
  rankC d.bY == 4 &&
  dotC d.fa d.ea == 1 && dotC d.fb d.ea == 0 && dotC d.fa d.eb == 0 && dotC d.fb d.eb == 1 &&
  !dependent2 d.ga d.gb

/-- The check of one case: no failed verification, and no passing triangle. -/
def caseOK (X : PCtx) (s0 s1 : Nat) (mult ws : List Nat) : Bool :=
  match setupCase X s0 s1 mult ws with
  | .invalid => true
  | .error => false
  | .valid d => wfCheck d && triFree d (allSols X d)

/-- All 255 multiplicity and single-point patterns (`hp2.c`'s `all_cases_for`). -/
def patterns : List (List Nat × List Nat) :=
  let mults := ((List.range 243).map fun code => (List.range 5).map fun m => (code / 3 ^ m) % 3).filter
    fun mu => mu.sum = 8 && (mu.filter (· = 2)).length ≥ 2
  mults.flatMap fun mu =>
    let sing := (List.range 5).filter fun m => mu.getD m 0 = 1
    (List.range (5 ^ sing.length)).map fun code =>
      (mu, (List.range 5).map fun m =>
        match sing.idxOf? m with
        | some i => (code / 5 ^ i) % 5
        | none => 0)

/-- The check of one pair `(P, Ŝ)` over all 255 patterns. -/
def checkPS (p0 p1 s0 s1 : Nat) : Bool :=
  let X := mkPCtx p0 p1
  X.ok && patterns.all fun (mu, ws) => caseOK X s0 s1 mu ws

/-- Run one case. -/
def runCase (X : PCtx) (s0 s1 : Nat) (mult ws : List Nat) : Counts :=
  match setupCase X s0 s1 mult ws with
  | .invalid => { cases := 1, invalid := 1 }
  | .error => { cases := 1, errors := 1 }
  | .valid d =>
    let sols := allSols X d
    let a := assemble d sols.toArray
    { a with cases := 1, sols := sols.length,
             r0 := (sols.filter (·.rk = 0)).length, r1 := (sols.filter (·.rk = 1)).length,
             r2 := (sols.filter (·.rk = 2)).length }

/-- Run all cases of one `(P, Ŝ)` pair. -/
def runPS (p0 p1 s0 s1 : Nat) : Counts :=
  let X := mkPCtx p0 p1
  if !X.ok then { errors := 1 } else
  patterns.foldl (fun acc (mu, ws) => acc.add (runCase X s0 s1 mu ws)) {}

end Mu4.Search
