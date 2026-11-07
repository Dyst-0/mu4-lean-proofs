import Mu4Comp.Codes

/-!
# The step 5-7 search, on codes (computational core)

Lean reimplementation of the direction and assembly steps of `runs/hyper/hp2.c` (see
`runs/hyper/README.md`, steps 4-7), written so that its completeness has a short proof:

* small linear-algebra subproblems are solved and then *verified* (dual basis, kernel basis), or
  solved by exhaustive search over at most 16 candidates;
* the operators `G_m` of the off-`m0` blocks are found by lookup in tables built from all 124
  diagonalizable 2×2 matrices over GF(4) (`diag2`), keyed by `G · B_m`;
* all rank tests use `rankC`, a lower bound for the true rank (elimination);
* the final test on a triangle of solutions is: a vertex of rank ≤ 1, or an interior point of
  rank ≤ 2 on each of the three edges (`runs/hyper/README.md`, step 6, in the form used by the
  Lean proof).

Vectors of GF(4)^n are codes (`Mu4.coordC`); GF(4^6) elements are 12-bit codes.
2×2 matrices `G` are 8-bit codes with `G[u][v]` at coordinate `2u+v`.
-/

namespace Mu4.Search
open F4

/-! ### Basic vector operations -/

/-- Dot product of two 12-bit codes: `∑ l < 6, f_l v_l`. -/
@[inline] def dotC (f v : Nat) : F4 :=
  coordC f 0 * coordC v 0 + coordC f 1 * coordC v 1 + coordC f 2 * coordC v 2 +
    coordC f 3 * coordC v 3 + coordC f 4 * coordC v 4 + coordC f 5 * coordC v 5

/-- The code with coordinate `l` equal to `c` and the others 0. -/
@[inline] def unitC (c : F4) (l : Nat) : Nat := c.code <<< (2 * l)

/-- First coordinate `< n` of `v` that is nonzero. -/
def firstNZ (v : Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, k + 1 => if coordC v i != 0 then some i else firstNZ v (i + 1) k

/-- Reduce `v` by a pivot list `(position, vector with coordinate 1 there)`. -/
def reduceBy (piv : List (Nat × Nat)) (v : Nat) : Nat :=
  piv.foldl (fun v pw => v ^^^ smulC (coordC v pw.1) pw.2) v

/-- Add `v` to an echelon pivot list (vectors with `n` coordinates). -/
def insertPivot (n : Nat) (piv : List (Nat × Nat)) (v : Nat) : List (Nat × Nat) :=
  let r := reduceBy piv v
  match firstNZ r 0 n with
  | none => piv
  | some p => piv ++ [(p, smulC (coordC r p)⁻¹ r)]

/-- Rank by elimination of a list of `n`-coordinate codes (a lower bound for the true rank). -/
def rankN (n : Nat) (vs : List Nat) : Nat := (vs.foldl (insertPivot n) []).length

/-- Rank of 12-bit codes (vectors of GF(4)^6). -/
def rankC (vs : List Nat) : Nat := rankN 6 vs

/-- Linear combination `∑ coordC c k • vs[k]` (codes). -/
def combo (c : Nat) (vs : List Nat) : Nat :=
  xorFin fun k : Fin vs.length => smulC (coordC c k) (vs.get k)

/-! ### 2×2 matrices over GF(4) -/

@[inline] def m00 (G : Nat) : F4 := coordC G 0
@[inline] def m01 (G : Nat) : F4 := coordC G 1
@[inline] def m10 (G : Nat) : F4 := coordC G 2
@[inline] def m11 (G : Nat) : F4 := coordC G 3

/-- The 8-bit code of the matrix `[[a, b], [c, d]]`. -/
@[inline] def mat2 (a b c d : F4) : Nat := unitC a 0 ^^^ unitC b 1 ^^^ unitC c 2 ^^^ unitC d 3

/-- Diagonalizable over GF(4): scalar, or two distinct eigenvalues in GF(4). -/
def diagPred (G : Nat) : Bool :=
  let tr := m00 G + m11 G
  let det := m00 G * m11 G + m01 G * m10 G
  (m01 G == 0 && m10 G == 0 && m00 G == m11 G) ||
    (tr != 0 && [z, o, w, w2].any fun t => t * t + tr * t + det == 0)

/-- The 124 diagonalizable 2×2 matrices. -/
def diag2 : List Nat := (List.range 256).filter diagPred

/-- `G H = H G`. -/
def comm2 (G H : Nat) : Bool :=
  m00 G * m00 H + m01 G * m10 H == m00 H * m00 G + m01 H * m10 G &&
  m00 G * m01 H + m01 G * m11 H == m00 H * m01 G + m01 H * m11 G &&
  m10 G * m00 H + m11 G * m10 H == m10 H * m00 G + m11 H * m10 G &&
  m10 G * m01 H + m11 G * m11 H == m10 H * m01 G + m11 H * m11 G

/-! ### Directions and 2-dim subspaces of GF(4)^4 -/

/-- First nonzero coordinate (of 4) equal to 1. -/
def normalized4 (c : Nat) : Bool :=
  match firstNZ c 0 4 with
  | some p => coordC c p == 1
  | none => false

/-- The 85 normalized nonzero vectors of GF(4)^4 (points of PG(3,4)), as 8-bit codes. -/
def dirs : List Nat := (List.range 256).filter normalized4

/-- Reduced row echelon pair of a 2-dim subspace of GF(4)^4 (codes `r0, r1`), the list of
`hp2.c`'s `init_rref`: pivots `p < q`, `r0` zero left of `p` and at `q`, `r1` zero left of `q`. -/
def rrefPairs : List (Nat × Nat) :=
  (List.range 256).flatMap fun r0 => (List.range 256).filterMap fun r1 =>
    match firstNZ r0 0 4, firstNZ r1 0 4 with
    | some p, some q =>
      if p < q && coordC r0 p == 1 && coordC r1 q == 1 && coordC r0 q == 0 then some (r0, r1)
      else none
    | _, _ => none

end Mu4.Search
