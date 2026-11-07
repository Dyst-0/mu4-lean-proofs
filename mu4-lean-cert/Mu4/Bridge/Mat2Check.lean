import Mu4Comp.Search.Core

/-!
# 2×2 matrices with prescribed eigenvectors: the finite checks (kernel)

The three finite facts behind `Mu4/Bridge/Mat2.lean`, as Bool checks over explicit lists of GF(4), checked by the
kernel (`decide +kernel`; second agent, 11-06). They replace the `native_decide` proofs of the first version.
- `diag_all`: `conjC a0 a1 b0 b1 l m` is diagonalizable (`diagPred`) when `a0 b1 + b0 a1 ≠ 0` (4,096 cases);
- `eigen_all`: it has the eigenvectors `(a0, a1)`, `(b0, b1)` with eigenvalues `l`, `m` (4,096 cases);
- `comm_all_*`: two of them with the same eigenvectors commute (65,536 cases, four chunks by `a0`).
Measured (11-06): 202 s and 2.7 GB for the module (shared machine). `conjC` is `Mu4.Bridge.conjCode` with the operations of
`Mu4Comp/F4.lean`; Mat2.lean identifies the two by `rfl`. Core Lean only. No `native_decide`.
-/

set_option autoImplicit false

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search

/-- The code of `Q diag(l, m) Q⁻¹` with `Q = [[a0, b0], [a1, b1]]` (the definition of `conjCode`). -/
def conjC (a0 a1 b0 b1 l m : F4) : Nat :=
  let di := (a0 * b1 + b0 * a1)⁻¹
  mat2 (di * (a0 * l * b1 + b0 * m * a1)) (di * (a0 * l * b0 + b0 * m * a0))
    (di * (a1 * l * b1 + b1 * m * a1)) (di * (a1 * l * b0 + b1 * m * a0))

/-- The four elements of GF(4). -/
def f4List : List F4 := [z, o, w, w2]

/-- Diagonalizable for all eigenvalues, given the eigenvectors. -/
def diagOK (a0 a1 b0 b1 : F4) : Bool :=
  a0 * b1 + b0 * a1 == 0 || f4List.all fun l => f4List.all fun m => diagPred (conjC a0 a1 b0 b1 l m)

/-- The eigenvector equations for all eigenvalues, given the eigenvectors. -/
def eigenOK (a0 a1 b0 b1 : F4) : Bool :=
  a0 * b1 + b0 * a1 == 0 || f4List.all fun l => f4List.all fun m =>
    m00 (conjC a0 a1 b0 b1 l m) * a0 + m01 (conjC a0 a1 b0 b1 l m) * a1 == l * a0 &&
    m10 (conjC a0 a1 b0 b1 l m) * a0 + m11 (conjC a0 a1 b0 b1 l m) * a1 == l * a1 &&
    m00 (conjC a0 a1 b0 b1 l m) * b0 + m01 (conjC a0 a1 b0 b1 l m) * b1 == m * b0 &&
    m10 (conjC a0 a1 b0 b1 l m) * b0 + m11 (conjC a0 a1 b0 b1 l m) * b1 == m * b1

/-- Commuting for all pairs of eigenvalue pairs, given the eigenvectors. -/
def commOK (a0 a1 b0 b1 : F4) : Bool :=
  a0 * b1 + b0 * a1 == 0 || f4List.all fun l => f4List.all fun m => f4List.all fun l' => f4List.all fun m' =>
    comm2 (conjC a0 a1 b0 b1 l m) (conjC a0 a1 b0 b1 l' m')

theorem diag_all : (f4List.all fun a0 => f4List.all fun a1 => f4List.all fun b0 => f4List.all fun b1 =>
    diagOK a0 a1 b0 b1) = true := by decide +kernel

theorem eigen_all : (f4List.all fun a0 => f4List.all fun a1 => f4List.all fun b0 => f4List.all fun b1 =>
    eigenOK a0 a1 b0 b1) = true := by decide +kernel

theorem comm_all_z : (f4List.all fun a1 => f4List.all fun b0 => f4List.all fun b1 => commOK z a1 b0 b1) = true := by
  decide +kernel

theorem comm_all_o : (f4List.all fun a1 => f4List.all fun b0 => f4List.all fun b1 => commOK o a1 b0 b1) = true := by
  decide +kernel

theorem comm_all_w : (f4List.all fun a1 => f4List.all fun b0 => f4List.all fun b1 => commOK w a1 b0 b1) = true := by
  decide +kernel

theorem comm_all_w2 : (f4List.all fun a1 => f4List.all fun b0 => f4List.all fun b1 => commOK w2 a1 b0 b1) = true := by
  decide +kernel

end Mu4.Bridge
