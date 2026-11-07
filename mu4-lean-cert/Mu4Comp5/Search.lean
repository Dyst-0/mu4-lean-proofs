import Mu4Comp5.Codes
import Mu4Comp.Search.Dir

/-!
# The mu_4(5) search for one case (computational core, core Lean only)

The n = 5 analogue of `Mu4Comp/Search/Case.lean` and `Dir.lean` (`audit/PROOF.md`, N6-N9, C3(5)): a 10-term
decomposition valid on `A5 = GF(4^5)`, three W-forms with common kernel `P`, seven alive terms with multiplicities
(sum 7) at the five standard points. A case is `(P, Ŝ, multiplicities, single points)`. The search lists all
solutions `(c, G)`: `c` a normalized direction of `A5/P` (a code of GF(4)^3 on the complement basis `tv`), one
diagonalizable operator per block, with `rank E ≤ 1`, and the final test asks for three of them with pairwise distinct
directions, pairwise commuting pair operators and independent directions (`runs/hyper/mu45.py`).

Generic pieces are reused from `Mu4Comp` (`insertPivot`, `reduceBy`, the 2×2 matrix codes and their lookup tables
`tableOf`, `splitFirstPair`, `chunks`, `inW`, `dependent2`, `CaseData`, `Sol`, `SolE`, `pairOps`). Everything that
reads coordinates uses five of them (`dotC5`, `rankC5 = rankN 5`, pivots `< 5`), so that its meaning in `A5` holds for
every code, as for n = 6.
-/

namespace Mu4.N5
open Mu4 F4 Mu4.Search

/-- `∑_{k<3} coordC c k • ks[k]`. -/
@[inline] def combo3 (c : Nat) (ks : List Nat) : Nat :=
  match ks with
  | [k0, k1, k2] => smulC (coordC c 0) k0 ^^^ smulC (coordC c 1) k1 ^^^ smulC (coordC c 2) k2
  | _ => combo c ks

/-- Dot product of two codes on the first five coordinates. -/
@[inline] def dotC5 (f v : Nat) : F4 :=
  coordC f 0 * coordC v 0 + coordC f 1 * coordC v 1 + coordC f 2 * coordC v 2 +
    coordC f 3 * coordC v 3 + coordC f 4 * coordC v 4

/-- Rank by elimination on five coordinates (a lower bound for the true rank in `A5`). -/
def rankC5 (vs : List Nat) : Nat := rankN 5 vs

/-- `∑_l coordC v l • cols[l]` for a list of 5 column codes. -/
@[inline] def applyCols5 (cols : List Nat) (v : Nat) : Nat :=
  match cols with
  | [a0, a1, a2, a3, a4] =>
    smulC (coordC v 0) a0 ^^^ smulC (coordC v 1) a1 ^^^ smulC (coordC v 2) a2 ^^^
      smulC (coordC v 3) a3 ^^^ smulC (coordC v 4) a4
  | _ => combo v cols

/-! ### The pencil context -/

/-- Context of a pencil `P = span(p0, p1)` of `A5`: the five points and a complement basis `tv` (3 vectors). -/
structure PCtx5 where
  p0 : Nat
  p1 : Nat
  pts : List Nat
  tv : List Nat
  /-- `tcols[k] = [t_k * e_l]_l`. -/
  tcols : List (List Nat)
  /-- `xcTab[c] = [x_c * e_l]_l` for every code `c < 64`. -/
  xcTab : Array (List Nat)

/-- Greedy complement of `P` among the standard basis vectors (checked by `PCtx5.ok`). -/
def complement5 (p0 p1 : Nat) : List Nat :=
  (List.range 5).foldl (fun acc l =>
    if acc.length < 3 && rankC5 ([p0, p1] ++ acc ++ [eC l]) == acc.length + 3 then acc ++ [eC l]
    else acc) []

/-- Columns `x_c * e_l` from the columns of the `t_k`. -/
def xcColsOf5 (tcols : List (List Nat)) (c : Nat) : List Nat :=
  (List.range 5).map fun l => combo3 c (tcols.map fun col => col.getD l 0)

def mkPCtx5 (p0 p1 : Nat) : PCtx5 :=
  let tv := complement5 p0 p1
  let tcols := tv.map fun t => (List.range 5).map fun l => mulK5 t (eC l)
  { p0, p1, pts := (List.range 5).map (ptC p0 p1), tv, tcols,
    xcTab := Array.ofFn (n := 64) fun c => xcColsOf5 tcols c.val }

/-- `(t, p0, p1)` is a basis of `A5`. -/
def PCtx5.ok (X : PCtx5) : Bool := X.tv.length == 3 && rankC5 ([X.p0, X.p1] ++ X.tv) == 5

/-- `x_c = ∑ c_k t_k`. -/
def PCtx5.xc (X : PCtx5) (c : Nat) : Nat := combo c X.tv

/-- Columns `x_c * e_l` (table lookup). -/
def PCtx5.xcCols (X : PCtx5) (c : Nat) : List Nat := X.xcTab.getD c (xcColsOf5 X.tcols c)

/-! ### Blocks and the set-up of a case -/

/-- Basis vector `i` of `W_m = x_m⁻¹ Ŝ`. -/
def Wv5 (X : PCtx5) (s0 s1 m i : Nat) : Nat :=
  mulK5 (invC5 (X.pts.getD m 0)) (if i = 0 then s0 else s1)

/-- The blocks of a case: two vectors at a pair, the chosen point of `W_m` at a single. -/
def blockList5 (X : PCtx5) (s0 s1 : Nat) (mult ws : List Nat) : List (Nat × List Nat) :=
  (List.range 5).filterMap fun m =>
    if mult.getD m 0 = 2 then some (m, [Wv5 X s0 s1 m 0, Wv5 X s0 s1 m 1])
    else if mult.getD m 0 = 1 then
      some (m, [smulC (pcA (ws.getD m 0)) (Wv5 X s0 s1 m 0) ^^^ smulC (pcB (ws.getD m 0)) (Wv5 X s0 s1 m 1)])
    else none

/-- Rows `rho` with `rho_j · cols_j' = δ_{jj'}` (5 × 5), proposed by Gauss-Jordan and verified by `isDual5`. -/
def gjInverse5 (cols : List Nat) : Option (List Nat) := Id.run do
  let mut a : Array (Nat × Nat) := (Array.range 5).map fun i =>
    (cols.zipIdx.foldl (fun acc (v, j) => acc ^^^ unitC (coordC v i) j) 0, eC i)
  for c in [0:5] do
    let mut p := 5
    for r in [c:5] do
      if p == 5 && coordC (a[r]!).1 c != 0 then p := r
    if p == 5 then return none
    let rowp := a[p]!
    a := (a.set! p a[c]!).set! c rowp
    let iv := (coordC (a[c]!).1 c)⁻¹
    a := a.set! c (smulC iv (a[c]!).1, smulC iv (a[c]!).2)
    for r in [0:5] do
      if r != c then
        let f := coordC (a[r]!).1 c
        if f != 0 then
          a := a.set! r ((a[r]!).1 ^^^ smulC f (a[c]!).1, (a[r]!).2 ^^^ smulC f (a[c]!).2)
  return some (a.toList.map (·.2))

def isDual5 (rho cols : List Nat) : Bool :=
  rho.length == 5 && cols.length == 5 &&
  (List.range 5).all fun j => (List.range 5).all fun j' =>
    dotC5 (rho.getD j 0) (cols.getD j' 0) == (if j == j' then 1 else 0)

def dualBasis5 (cols : List Nat) : Option (List Nat) :=
  match gjInverse5 cols with
  | some rho => if isDual5 rho cols then some rho else none
  | none => none

/-- A nonzero dependency `∑ λ_j cols_j = 0` (5 columns), by exhaustive search. -/
def dependency5 (cols : List Nat) : Option Nat :=
  (List.range 1024).find? fun lam => lam != 0 && combo lam cols == 0

/-- The form `y ↦ (rho · (x_{m0} y)) / l_m(x_{m0})` as a code. -/
def formOf5 (xm0 : Nat) (l : F4) (rho : Nat) : Nat :=
  (List.range 5).foldl (fun acc t => acc ^^^ unitC (dotC5 rho (mulK5 xm0 (eC t)) * l⁻¹) t) 0

/-- Basis of `ker fa ∩ ker fb` (3 vectors) and duals `ea, eb`, verified. -/
def kernelData5 (fa fb : Nat) : Option (List Nat × Nat × Nat) :=
  match firstNZ fa 0 5 with
  | none => none
  | some pa =>
    let ra := smulC (coordC fa pa)⁻¹ fa
    let rb0 := fb ^^^ smulC (coordC fb pa) ra
    match firstNZ rb0 0 5 with
    | none => none
    | some pb =>
      let rb := smulC (coordC rb0 pb)⁻¹ rb0
      let ra' := ra ^^^ smulC (coordC ra pb) rb
      let bY := ((List.range 5).filter fun l => l != pa && l != pb).map fun l =>
        eC l ^^^ unitC (coordC ra' l) pa ^^^ unitC (coordC rb l) pb
      let pv := fun ac => unitC (coordC ac 0) pa ^^^ unitC (coordC ac 1) pb
      let ea := ((List.range 16).map pv).find? fun y => dotC5 fa y == 1 && dotC5 fb y == 0
      let eb := ((List.range 16).map pv).find? fun y => dotC5 fa y == 0 && dotC5 fb y == 1
      match ea, eb with
      | some ea, some eb =>
        if bY.length == 3 && bY.all (fun y => dotC5 fa y == 0 && dotC5 fb y == 0) && rankC5 bY == 3
        then some (bY, ea, eb) else none
      | _, _ => none

/-- The off blocks with their forms `f_j(y) = rho_j(x_{m0} y) / l_m(x_{m0})`. -/
def mkOff5 (X : PCtx5) (offB : List (Nat × List Nat)) (m0 : Nat) (rho : List Nat) :
    List (Nat × List Term) :=
  (offB.zip (chunks (offB.map (·.2.length)) rho)).map fun x =>
    (x.1.1, x.1.2.zip (x.2.map (formOf5 (X.pts.getD m0 0) (lval x.1.1 m0))))

/-- Apply the off-blocks (with forms) to `y`: `∑_j l_{m(j)}(x_q) f_j(y) g_j`. -/
def offAt5 (off : List (Nat × List Term)) (q y : Nat) : Nat :=
  (off.flatMap fun (m, ts) => ts.map fun (g, f) => smulC (lval m q * dotC5 f y) g).foldl (· ^^^ ·) 0

/-- Coefficients `(A, C)` of the residual at `e_t` on `W_{m0} = span(ga, gb)`. -/
def residualAt5 (X : PCtx5) (off : List (Nat × List Term)) (ga gb m0 t : Nat) : Option Nat :=
  inW ga gb (mulK5 (X.pts.getD (secondPt m0) 0) (eC t) ^^^ offAt5 off (secondPt m0) (eC t))

/-- The two forms of the block at `m0`, from the residual coefficients. -/
def formAB5 (res : List (Option Nat)) (m0 i : Nat) : Nat :=
  (List.range 5).foldl (fun acc t =>
    acc ^^^ unitC (coordC ((res.getD t none).getD 0) i * (lval m0 (secondPt m0))⁻¹) t) 0

/-- The case data after the dual basis. -/
def setupFrom5 (X : PCtx5) (offB : List (Nat × List Nat)) (m0 : Nat) (gs0 : List Nat)
    (rho : List Nat) : CaseResult :=
  let off := mkOff5 X offB m0 rho
  let ga := gs0.getD 0 0
  let gb := gs0.getD 1 0
  let res := (List.range 5).map (residualAt5 X off ga gb m0)
  if res.any (·.isNone) then .invalid else
  let fa := formAB5 res m0 0
  let fb := formAB5 res m0 1
  if dependent2 fa fb then .invalid else
  match kernelData5 fa fb with
  | none => .error
  | some (bY, ea, eb) =>
    .valid { off, m0, ga, gb, fa, fb, rhoOff := chunks (offB.map (·.2.length)) rho, bY, ea, eb }

/-- Set up a case: blocks, dual basis, forms, the block at `m0`, `Y` data. -/
def setupCase5 (X : PCtx5) (s0 s1 : Nat) (mult ws : List Nat) : CaseResult :=
  match splitFirstPair (blockList5 X s0 s1 mult ws) with
  | none => .error
  | some (pre, (m0, gs0), post) =>
    match dualBasis5 ((pre ++ post).flatMap (·.2)) with
    | none => match dependency5 ((pre ++ post).flatMap (·.2)) with
      | some _ => .invalid
      | none => .error
    | some rho => setupFrom5 X (pre ++ post) m0 gs0 rho

/-! ### Directions and solutions of rank ≤ 1 -/

/-- First nonzero coordinate (of 3) equal to 1. -/
def normalized3 (c : Nat) : Bool :=
  match firstNZ c 0 3 with
  | some p => coordC c p == 1
  | none => false

/-- The 21 normalized nonzero vectors of GF(4)^3 (points of PG(2,4)), as 6-bit codes. -/
def dirs3 : List Nat := (List.range 64).filter normalized3

/-- Reduced row echelon pairs of the 2-dim subspaces of GF(4)^3 (21 of them). -/
def rrefPairs3 : List (Nat × Nat) :=
  (List.range 64).flatMap fun r0 => (List.range 64).filterMap fun r1 =>
    match firstNZ r0 0 3, firstNZ r1 0 3 with
    | some p, some q =>
      if p < q && coordC r0 p == 1 && coordC r1 q == 1 && coordC r0 q == 0 then some (r0, r1)
      else none
    | _, _ => none

/-- `G Block y` for a block with terms `ts` and operator code `G`. -/
def applyG5 (G : Nat) (ts : List Term) (y : Nat) : Nat :=
  match ts with
  | [(g0, f0), (g1, f1)] =>
    let a := dotC5 f0 y
    let b := dotC5 f1 y
    smulC (m00 G * a + m01 G * b) g0 ^^^ smulC (m10 G * a + m11 G * b) g1
  | [(g0, f0)] => smulC (coordC G 0 * dotC5 f0 y) g0
  | _ => 0

/-- Lookup key of the right-hand side: Gam-coordinates of `x y1, x y2` in the block. -/
def keyR5 (rhos : List Nat) (xy1 xy2 : Nat) : Nat :=
  match rhos with
  | [r0, r1] => mat2 (dotC5 r0 xy1) (dotC5 r0 xy2) (dotC5 r1 xy1) (dotC5 r1 xy2)
  | [r0] => unitC (dotC5 r0 xy1) 0 ^^^ unitC (dotC5 r0 xy2) 1
  | _ => 0

/-- Entries `(f0(y), f1(y))` of a block at `y`. -/
@[inline] def entriesAt5 (ts : List Term) (y : Nat) : F4 × F4 :=
  match ts with
  | [(_, f0), (_, f1)] => (dotC5 f0 y, dotC5 f1 y)
  | [(_, f0)] => (dotC5 f0 y, 0)
  | _ => (0, 0)

/-- Lookup table `key ↦ operators with that key` of a block (from the global tables). -/
def mkTable5 (ts : List Term) (y1 y2 : Nat) : Array (List Nat) :=
  match ts with
  | [(_, f0), (_, f1)] =>
    pairTables.getD (mat2 (dotC5 f0 y1) (dotC5 f0 y2) (dotC5 f1 y1) (dotC5 f1 y2))
      (tableOf true (dotC5 f0 y1) (dotC5 f0 y2) (dotC5 f1 y1) (dotC5 f1 y2))
  | [(_, f0)] =>
    singleTables.getD (mat2 (dotC5 f0 y1) (dotC5 f0 y2) 0 0) (tableOf false (dotC5 f0 y1) (dotC5 f0 y2) 0 0)
  | _ => singleTables.getD (mat2 0 0 0 0) (tableOf false 0 0 0 0)

/-- Pivot list of `W_{m0}`, for reduction modulo `W_{m0}` (positions `< 5`). -/
def pivW5 (d : CaseData) : List (Nat × Nat) := [d.ga, d.gb].foldl (insertPivot 5) []

/-- `E y` for a solution. -/
def Eval5 (X : PCtx5) (d : CaseData) (s : Sol) (y : Nat) : Nat :=
  applyCols5 (X.xcCols s.c) y ^^^
    ((d.off.zip s.goff).map fun ((_, ts), G) => applyG5 G ts y).foldl (· ^^^ ·) 0 ^^^
    applyG5 s.g0 [(d.ga, d.fa), (d.gb, d.fb)] y

/-- Insert `v` into a pivot list, unless the rank would exceed 1. -/
def push1 (piv : List (Nat × Nat)) (v : Nat) : Option (List (Nat × Nat)) :=
  let piv' := insertPivot 5 piv v
  if piv'.length ≤ 1 then some piv' else none

/-- Insert a list of vectors, failing as soon as the rank exceeds 1. -/
def pushAll1 (piv : List (Nat × Nat)) : List Nat → Option (List (Nat × Nat))
  | [] => some piv
  | v :: vs => match push1 piv v with
    | some p => pushAll1 p vs
    | none => none

/-- Candidates of each block at direction `c` (all must be nonempty), keys combined over 3 coordinates. -/
def candsAt3 (tbls : List (Array (List Nat))) (keysT : List (List Nat)) (c : Nat) :
    Option (List (List Nat)) :=
  match tbls, keysT with
  | tb :: tbls, ks :: keysT =>
    let l := tb.getD (combo3 c ks) []
    if l.isEmpty then none else (candsAt3 tbls keysT c).map (l :: ·)
  | _, _ => some []

/-- Solutions with a given first column `colA` of the operator at `m0`. -/
def solsColA1 (d : CaseData) (c : Nat) (goff : List Nat) (pbase : List (Nat × Nat))
    (vea veb colA : Nat) : List Sol :=
  let vA := vea ^^^ smulC (coordC colA 0) d.ga ^^^ smulC (coordC colA 1) d.gb
  match push1 pbase vA with
  | none => []
  | some pA => (List.range 16).filterMap fun colC =>
    let vC := veb ^^^ smulC (coordC colC 0) d.ga ^^^ smulC (coordC colC 1) d.gb
    let g0 := mat2 (coordC colA 0) (coordC colC 0) (coordC colA 1) (coordC colC 1)
    if (push1 pA vC).isSome && diagPred g0 then some { c, goff, g0 } else none

/-- Solutions with a given choice `goff` of the off-block operators; `xes` are the values of `x_c` at
`[b, ea, eb]` (`b` the vector of `bY` off `K`). -/
def solsGoff1 (d : CaseData) (tss : List (List Term)) (kd : KData) (c : Nat) (xes : List Nat)
    (xea xeb : Nat) (goff : List Nat) : List Sol :=
  let e0 := (xes.zip kd.entEs).map fun (x, ents) => x ^^^ offContrib tss goff ents
  match pushAll1 [] (e0.map (reduceBy (pivW5 d))) with
  | none => []
  | some _ =>
  match pushAll1 [] (e0.take 1) with
  | none => []
  | some pbase =>
  (List.range 16).flatMap (solsColA1 d c goff pbase (xea ^^^ offContrib tss goff kd.entA)
    (xeb ^^^ offContrib tss goff kd.entB))

/-- Solutions found from `K` and direction `c`. -/
def solsKc5 (X : PCtx5) (d : CaseData) (tss : List (List Term)) (tbls : List (Array (List Nat)))
    (keysT : List (List Nat)) (kd : KData) (c : Nat) : List Sol :=
  match candsAt3 tbls keysT c with
  | none => []
  | some cands =>
    let xcols := X.xcCols c
    (choices cands).flatMap (solsGoff1 d tss kd c (kd.es.map (applyCols5 xcols))
      (applyCols5 xcols d.ea) (applyCols5 xcols d.eb))

/-- The pivot positions of an RREF pair of GF(4)^3. -/
def pivots3 (K : Nat × Nat) : Nat × Nat := ((firstNZ K.1 0 3).getD 0, (firstNZ K.2 0 3).getD 0)

/-- Solutions from one `K = span(y1, y2) ⊆ Y`. -/
def solsK5 (X : PCtx5) (d : CaseData) (K : Nat × Nat) : List Sol :=
  let y1 := combo3 K.1 d.bY
  let y2 := combo3 K.2 d.bY
  let (p, q) := pivots3 K
  let es := ((List.range 3).filter fun i => i != p && i != q).map (fun i => d.bY.getD i 0) ++
    [d.ea, d.eb]
  let tss := d.off.map (·.2)
  let tbls := tss.map fun ts => mkTable5 ts y1 y2
  let ty := X.tcols.map fun tc => (applyCols5 tc y1, applyCols5 tc y2)
  let keysT := d.rhoOff.map fun rhos => ty.map fun (a, b) => keyR5 rhos a b
  let kd : KData := { es, entEs := es.map fun y => tss.map fun ts => entriesAt5 ts y,
                      entA := tss.map fun ts => entriesAt5 ts d.ea,
                      entB := tss.map fun ts => entriesAt5 ts d.eb }
  dirs3.flatMap (solsKc5 X d tss tbls keysT kd)

def withE5 (X : PCtx5) (d : CaseData) (s : Sol) : SolE :=
  let cols := (List.range 5).map fun t => Eval5 X d s (eC t)
  { s, cols, rk := rankC5 cols }

/-- All solutions of the case of rank ≤ 1 (computed rank on all five columns). -/
def allSols5 (X : PCtx5) (d : CaseData) : List SolE :=
  ((dedupSols (rrefPairs3.flatMap (solsK5 X d))).map (withE5 X d)).filter (·.rk ≤ 1)

/-! ### The final test -/

/-- Two solutions are *adjacent*: distinct directions and commuting pair operators. -/
def adj5 (d : CaseData) (a b : SolE) : Bool :=
  a.s.c != b.s.c && ((pairOps d a.s).zip (pairOps d b.s)).all (fun (G, H) => comm2 G H)

/-- No three solutions pairwise adjacent with independent directions. -/
def tripleFree5 (d : CaseData) (sols : List SolE) : Bool :=
  let arr := sols.toArray
  let n := arr.size
  (List.range n).all fun i => (List.range n).all fun j =>
    !(i < j) || !adj5 d (arr.getD i default) (arr.getD j default) ||
    (List.range n).all fun k =>
      !(j < k) || !adj5 d (arr.getD i default) (arr.getD k default) ||
        !adj5 d (arr.getD j default) (arr.getD k default) ||
        inSpan2 (arr.getD i default).s.c (arr.getD j default).s.c (arr.getD k default).s.c

/-- The runtime certificate of the invariants of a valid case (as `wfCheck`, with `bY` of 3 vectors). -/
def wfCheck5 (d : CaseData) : Bool :=
  let n := d.off.length
  d.rhoOff.length == n &&
  (List.range n).all (fun i => ((blkOf d i).length == 1 || (blkOf d i).length == 2) &&
    (d.rhoOff.getD i []).length == (blkOf d i).length) &&
  (List.range n).all (fun i => (List.range (blkOf d i).length).all fun u =>
    (List.range n).all fun j => (List.range (blkOf d j).length).all fun u' =>
      dotC5 (rhoOf d i u) (gOf d j u') == (if i == j && u == u' then 1 else 0)) &&
  d.bY.length == 3 && d.bY.all (fun y => dotC5 d.fa y == 0 && dotC5 d.fb y == 0) &&
  rankC5 d.bY == 3 &&
  dotC5 d.fa d.ea == 1 && dotC5 d.fb d.ea == 0 && dotC5 d.fa d.eb == 0 && dotC5 d.fb d.eb == 1 &&
  !dependent2 d.ga d.gb

/-- The check of one case: no failed verification, and no adjacent independent triple. -/
def caseOK5 (X : PCtx5) (s0 s1 : Nat) (mult ws : List Nat) : Bool :=
  match setupCase5 X s0 s1 mult ws with
  | .invalid => true
  | .error => false
  | .valid d => wfCheck5 d && tripleFree5 d (allSols5 X d)

/-- All 1,350 multiplicity and single-point patterns (sum 7, at least two pairs; `hp2.c`'s `all_cases_for`). -/
def patterns5 : List (List Nat × List Nat) :=
  let mults := ((List.range 243).map fun code => (List.range 5).map fun m => (code / 3 ^ m) % 3).filter
    fun mu => mu.sum = 7 && (mu.filter (· = 2)).length ≥ 2
  mults.flatMap fun mu =>
    let sing := (List.range 5).filter fun m => mu.getD m 0 = 1
    (List.range (5 ^ sing.length)).map fun code =>
      (mu, (List.range 5).map fun m =>
        match sing.idxOf? m with
        | some i => (code / 5 ^ i) % 5
        | none => 0)

/-- The check of one pair `(P, Ŝ)` over all patterns. -/
def checkPS5 (p0 p1 s0 s1 : Nat) : Bool :=
  let X := mkPCtx5 p0 p1
  X.ok && patterns5.all fun (mu, ws) => caseOK5 X s0 s1 mu ws

/-- The certified check of one pair `(P, Ŝ)`: every multiplicity pattern `n_m ≤ 2` with sum 7 and every choice of single
points `w_m < 5` (with `w_m = 0` off the singles) passes `caseOK5`. The same 1,350 cases as `patterns5`, enumerated by
nested loops so that membership is immediate. -/
def checkAll5 (p0 p1 s0 s1 : Nat) : Bool :=
  let X := mkPCtx5 p0 p1
  X.ok && (List.range 3).all fun c0 => (List.range 3).all fun c1 => (List.range 3).all fun c2 =>
    (List.range 3).all fun c3 => (List.range 3).all fun c4 =>
      c0 + c1 + c2 + c3 + c4 != 7 ||
      (List.range 5).all fun v0 => (c0 != 1 && v0 != 0) ||
      (List.range 5).all fun v1 => (c1 != 1 && v1 != 0) ||
      (List.range 5).all fun v2 => (c2 != 1 && v2 != 0) ||
      (List.range 5).all fun v3 => (c3 != 1 && v3 != 0) ||
      (List.range 5).all fun v4 => (c4 != 1 && v4 != 0) ||
      caseOK5 X s0 s1 [c0, c1, c2, c3, c4] [v0, v1, v2, v3, v4]

/-! ### Counters (for the cross-check with `hp2_5` and `mu45.py`) -/

structure Counts5 where
  cases : Nat := 0
  invalid : Nat := 0
  errors : Nat := 0
  sols : Nat := 0
  r0 : Nat := 0
  adj : Nat := 0
  triples : Nat := 0
  deriving Repr

def Counts5.add (a b : Counts5) : Counts5 :=
  { cases := a.cases + b.cases, invalid := a.invalid + b.invalid, errors := a.errors + b.errors,
    sols := a.sols + b.sols, r0 := a.r0 + b.r0, adj := a.adj + b.adj, triples := a.triples + b.triples }

def runCase5 (X : PCtx5) (s0 s1 : Nat) (mult ws : List Nat) : Counts5 :=
  match setupCase5 X s0 s1 mult ws with
  | .invalid => { cases := 1, invalid := 1 }
  | .error => { cases := 1, errors := 1 }
  | .valid d =>
    let sols := (allSols5 X d).toArray
    let n := sols.size
    let get : Nat → SolE := fun i => sols.getD i default
    let pairs := ((List.range n).flatMap fun i => (List.range n).filterMap fun j =>
      if i < j && adj5 d (get i) (get j) then some (i, j) else none)
    let tri := ((List.range n).flatMap fun i => (List.range n).flatMap fun j => (List.range n).filter fun k =>
      i < j && j < k && adj5 d (get i) (get j) && adj5 d (get i) (get k) && adj5 d (get j) (get k) &&
        !inSpan2 (get i).s.c (get j).s.c (get k).s.c).length
    { cases := 1, errors := if wfCheck5 d then 0 else 1, sols := n,
      r0 := (sols.toList.filter (·.rk = 0)).length, adj := pairs.length, triples := tri }

def runPS5 (p0 p1 s0 s1 : Nat) : Counts5 :=
  let X := mkPCtx5 p0 p1
  if !X.ok then { errors := 1 } else
  patterns5.foldl (fun acc (mu, ws) => acc.add (runCase5 X s0 s1 mu ws)) {}

end Mu4.N5
