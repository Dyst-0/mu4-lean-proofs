import Mu4Comp.Search.Core

/-!
# The search for one case `(P, Ŝ, multiplicities, single points)`

Follows `runs/hyper/hp2.c` (`run_case`), in a functional style, with the changes listed in
`Mu4.Search.Core`. All definitions are pure functions of the case data, so that the completeness
proof (`Mu4.Lower`) can follow them with membership lemmas.
-/

namespace Mu4.Search
open F4

/-- Coordinates of the five standard points `x_m = ss_m p0 + tt_m p1` of a pencil. -/
def ssC : Nat → F4 | 0 => 1 | 1 => 0 | 2 => 1 | 3 => w | _ => w2
def ttC : Nat → F4 | 0 => 0 | _ => 1

/-- `l_m(x_q)`, the form vanishing at `x_m`, evaluated at `x_q`. -/
def lval (m q : Nat) : F4 := ttC m * ssC q + ssC m * ttC q

/-- The five points of a 2-dim space with basis `(w0, w1)`: `pcA k • w0 + pcB k • w1`. -/
def pcA : Nat → F4 | 1 => 0 | _ => 1
def pcB : Nat → F4 | 0 => 0 | 1 => 1 | 2 => 1 | 3 => w | _ => w2

/-- The standard basis vector `e_l` of GF(4^6) (code). -/
def eC (l : Nat) : Nat := 1 <<< (2 * l)

/-- `∑_l coordC v l • cols[l]` for a list of 6 column codes. -/
@[inline] def applyCols (cols : List Nat) (v : Nat) : Nat :=
  match cols with
  | [a0, a1, a2, a3, a4, a5] =>
    smulC (coordC v 0) a0 ^^^ smulC (coordC v 1) a1 ^^^ smulC (coordC v 2) a2 ^^^
      smulC (coordC v 3) a3 ^^^ smulC (coordC v 4) a4 ^^^ smulC (coordC v 5) a5
  | _ => combo v cols

/-- `∑_{k<4} coordC c k • ks[k]`. -/
@[inline] def combo4 (c : Nat) (ks : List Nat) : Nat :=
  match ks with
  | [k0, k1, k2, k3] =>
    smulC (coordC c 0) k0 ^^^ smulC (coordC c 1) k1 ^^^ smulC (coordC c 2) k2 ^^^ smulC (coordC c 3) k3
  | _ => combo c ks

/-- Context of a pencil `P = span(p0, p1)`: the five points and a complement basis `tv` of `P`. -/
structure PCtx where
  p0 : Nat
  p1 : Nat
  pts : List Nat
  tv : List Nat
  /-- `tcols[k] = [t_k * e_l]_l`. -/
  tcols : List (List Nat)
  /-- `xcTab[c] = [x_c * e_l]_l` for every code `c < 256`. -/
  xcTab : Array (List Nat)

def ptC (p0 p1 m : Nat) : Nat := smulC (ssC m) p0 ^^^ smulC (ttC m) p1

/-- Greedy complement of `P` among the standard basis vectors (checked by `PCtx.ok`). -/
def complement (p0 p1 : Nat) : List Nat :=
  (List.range 6).foldl (fun acc l =>
    if acc.length < 4 && rankC ([p0, p1] ++ acc ++ [eC l]) == acc.length + 3 then acc ++ [eC l]
    else acc) []

/-- Columns `x_c * e_l` from the columns of the `t_k`. -/
def xcColsOf (tcols : List (List Nat)) (c : Nat) : List Nat :=
  (List.range 6).map fun l => combo4 c (tcols.map fun col => col.getD l 0)

def mkPCtx (p0 p1 : Nat) : PCtx :=
  let tv := complement p0 p1
  let tcols := tv.map fun t => (List.range 6).map fun l => mulK t (eC l)
  { p0, p1, pts := (List.range 5).map (ptC p0 p1), tv, tcols,
    xcTab := Array.ofFn (n := 256) fun c => xcColsOf tcols c.val }

/-- `(t, p0, p1)` is a basis: `rankC` is a lower bound, so 6 means independent. -/
def PCtx.ok (X : PCtx) : Bool := X.tv.length == 4 && rankC ([X.p0, X.p1] ++ X.tv) == 6

/-- `x_c = ∑ c_k t_k`. -/
def PCtx.xc (X : PCtx) (c : Nat) : Nat := combo c X.tv

/-- Columns `x_c * e_l` (table lookup; `xcTab` is built from `xcColsOf`). -/
def PCtx.xcCols (X : PCtx) (c : Nat) : List Nat := X.xcTab.getD c (xcColsOf X.tcols c)

/-! ### Blocks -/

/-- Basis vector `i` of `W_m = x_m⁻¹ Ŝ`. -/
def Wv (X : PCtx) (s0 s1 m i : Nat) : Nat :=
  mulK (invC (X.pts.getD m 0)) (if i = 0 then s0 else s1)

/-- The blocks of a case: `(m, [g])` with two vectors (the basis of `W_m`) at a pair and the
chosen point of `W_m` at a single. -/
def blockList (X : PCtx) (s0 s1 : Nat) (mult ws : List Nat) : List (Nat × List Nat) :=
  (List.range 5).filterMap fun m =>
    if mult.getD m 0 = 2 then some (m, [Wv X s0 s1 m 0, Wv X s0 s1 m 1])
    else if mult.getD m 0 = 1 then
      some (m, [smulC (pcA (ws.getD m 0)) (Wv X s0 s1 m 0) ^^^ smulC (pcB (ws.getD m 0)) (Wv X s0 s1 m 1)])
    else none

/-- Split off the first pair block: `(singles before it, the pair block, the rest)`. -/
def splitFirstPair : List (Nat × List Nat) → Option (List (Nat × List Nat) × (Nat × List Nat) × List (Nat × List Nat))
  | [] => none
  | b :: bs =>
    if b.2.length = 2 then some ([], b, bs)
    else match splitFirstPair bs with
      | some (pre, p, post) => some (b :: pre, p, post)
      | none => none

/-- Rows `rho` with `rho_j · cols_j' = δ_{jj'}`, verified (Gauss-Jordan proposes them). -/
def gjInverse (cols : List Nat) : Option (List Nat) := Id.run do
  let mut a : Array (Nat × Nat) := (Array.range 6).map fun i =>
    (cols.zipIdx.foldl (fun acc (v, j) => acc ^^^ unitC (coordC v i) j) 0, eC i)
  for c in [0:6] do
    let mut p := 6
    for r in [c:6] do
      if p == 6 && coordC (a[r]!).1 c != 0 then p := r
    if p == 6 then return none
    let rowp := a[p]!
    a := (a.set! p a[c]!).set! c rowp
    let iv := (coordC (a[c]!).1 c)⁻¹
    a := a.set! c (smulC iv (a[c]!).1, smulC iv (a[c]!).2)
    for r in [0:6] do
      if r != c then
        let f := coordC (a[r]!).1 c
        if f != 0 then
          a := a.set! r ((a[r]!).1 ^^^ smulC f (a[c]!).1, (a[r]!).2 ^^^ smulC f (a[c]!).2)
  return some (a.toList.map (·.2))

def isDual (rho cols : List Nat) : Bool :=
  rho.length == 6 && cols.length == 6 &&
  (List.range 6).all fun j => (List.range 6).all fun j' =>
    dotC (rho.getD j 0) (cols.getD j' 0) == (if j == j' then 1 else 0)

def dualBasis (cols : List Nat) : Option (List Nat) :=
  match gjInverse cols with
  | some rho => if isDual rho cols then some rho else none
  | none => none

/-- A nonzero dependency `∑ λ_j cols_j = 0`, by exhaustive search. -/
def dependency (cols : List Nat) : Option Nat :=
  (List.range 4096).find? fun lam => lam != 0 && combo lam cols == 0

/-- A term of a block: `(g, f)`, with `Block y = ∑ f(y) g`. -/
abbrev Term := Nat × Nat

/-- The data of a valid case. -/
structure CaseData where
  /-- The off-`m0` blocks: `(m, terms)`, in order. -/
  off : List (Nat × List Term)
  m0 : Nat
  ga : Nat
  gb : Nat
  fa : Nat
  fb : Nat
  /-- Gam-coordinate rows of the off blocks, aligned with `off`. -/
  rhoOff : List (List Nat)
  bY : List Nat
  ea : Nat
  eb : Nat

inductive CaseResult
  | invalid
  | error
  | valid (d : CaseData)

/-- Split a flat list into chunks of the given lengths. -/
def chunks : List Nat → List Nat → List (List Nat)
  | [], _ => []
  | n :: ns, xs => xs.take n :: chunks ns (xs.drop n)

/-- The form `y ↦ (rho · (x_{m0} y)) / l_m(x_{m0})` as a code. -/
def formOf (xm0 : Nat) (l : F4) (rho : Nat) : Nat :=
  (List.range 6).foldl (fun acc t => acc ^^^ unitC (dotC rho (mulK xm0 (eC t)) * l⁻¹) t) 0

/-- Apply the off-blocks (with forms) to `y`: `∑_j l_{m(j)}(x_q) f_j(y) g_j`. -/
def offAt (off : List (Nat × List Term)) (q y : Nat) : Nat :=
  (off.flatMap fun (m, ts) => ts.map fun (g, f) => smulC (lval m q * dotC f y) g).foldl (· ^^^ ·) 0

/-- Coefficients `(A, C)` with `A ga + C gb = s`, by search over 16 pairs. -/
def inW (ga gb s : Nat) : Option Nat :=
  (List.range 16).find? fun ac => (smulC (coordC ac 0) ga ^^^ smulC (coordC ac 1) gb) == s

/-- `fa, fb` dependent (search over 15 nonzero pairs). -/
def dependent2 (fa fb : Nat) : Bool :=
  (List.range 16).any fun ab => ab != 0 && (smulC (coordC ab 0) fa ^^^ smulC (coordC ab 1) fb) == 0

/-- Basis of `ker fa ∩ ker fb` and duals `ea, eb` (`hp2.c`'s construction), verified. -/
def kernelData (fa fb : Nat) : Option (List Nat × Nat × Nat) :=
  match firstNZ fa 0 6 with
  | none => none
  | some pa =>
    let ra := smulC (coordC fa pa)⁻¹ fa
    let rb0 := fb ^^^ smulC (coordC fb pa) ra
    match firstNZ rb0 0 6 with
    | none => none
    | some pb =>
      let rb := smulC (coordC rb0 pb)⁻¹ rb0
      let ra' := ra ^^^ smulC (coordC ra pb) rb
      let bY := ((List.range 6).filter fun l => l != pa && l != pb).map fun l =>
        eC l ^^^ unitC (coordC ra' l) pa ^^^ unitC (coordC rb l) pb
      let pv := fun ac => unitC (coordC ac 0) pa ^^^ unitC (coordC ac 1) pb
      let ea := ((List.range 16).map pv).find? fun y => dotC fa y == 1 && dotC fb y == 0
      let eb := ((List.range 16).map pv).find? fun y => dotC fa y == 0 && dotC fb y == 1
      match ea, eb with
      | some ea, some eb =>
        if bY.length == 4 && bY.all (fun y => dotC fa y == 0 && dotC fb y == 0) && rankC bY == 4
        then some (bY, ea, eb) else none
      | _, _ => none

/-- The off blocks with their forms `f_j(y) = rho_j(x_{m0} y) / l_m(x_{m0})`. -/
def mkOff (X : PCtx) (offB : List (Nat × List Nat)) (m0 : Nat) (rho : List Nat) :
    List (Nat × List Term) :=
  (offB.zip (chunks (offB.map (·.2.length)) rho)).map fun x =>
    (x.1.1, x.1.2.zip (x.2.map (formOf (X.pts.getD m0 0) (lval x.1.1 m0))))

/-- The second point `q2 ≠ m0` used for the block at `m0`. -/
def secondPt (m0 : Nat) : Nat := if m0 = 0 then 1 else 0

/-- Coefficients `(A, C)` of the residual at `e_t` on `W_{m0} = span(ga, gb)`. -/
def residualAt (X : PCtx) (off : List (Nat × List Term)) (ga gb m0 t : Nat) : Option Nat :=
  inW ga gb (mulK (X.pts.getD (secondPt m0) 0) (eC t) ^^^ offAt off (secondPt m0) (eC t))

/-- The two forms of the block at `m0`, from the residual coefficients (`i = 0` gives `fa`,
`i = 1` gives `fb`). -/
def formAB (res : List (Option Nat)) (m0 i : Nat) : Nat :=
  (List.range 6).foldl (fun acc t =>
    acc ^^^ unitC (coordC ((res.getD t none).getD 0) i * (lval m0 (secondPt m0))⁻¹) t) 0

/-- The case data after the dual basis. -/
def setupFrom (X : PCtx) (offB : List (Nat × List Nat)) (m0 : Nat) (gs0 : List Nat)
    (rho : List Nat) : CaseResult :=
  let off := mkOff X offB m0 rho
  let ga := gs0.getD 0 0
  let gb := gs0.getD 1 0
  let res := (List.range 6).map (residualAt X off ga gb m0)
  if res.any (·.isNone) then .invalid else
  let fa := formAB res m0 0
  let fb := formAB res m0 1
  if dependent2 fa fb then .invalid else
  match kernelData fa fb with
  | none => .error
  | some (bY, ea, eb) =>
    .valid { off, m0, ga, gb, fa, fb, rhoOff := chunks (offB.map (·.2.length)) rho, bY, ea, eb }

/-- Set up a case: blocks, dual basis, forms, the block at `m0`, `Y1` data. -/
def setupCase (X : PCtx) (s0 s1 : Nat) (mult ws : List Nat) : CaseResult :=
  match splitFirstPair (blockList X s0 s1 mult ws) with
  | none => .error
  | some (pre, (m0, gs0), post) =>
    match dualBasis ((pre ++ post).flatMap (·.2)) with
    | none => match dependency ((pre ++ post).flatMap (·.2)) with
      | some _ => .invalid
      | none => .error
    | some rho => setupFrom X (pre ++ post) m0 gs0 rho

end Mu4.Search
