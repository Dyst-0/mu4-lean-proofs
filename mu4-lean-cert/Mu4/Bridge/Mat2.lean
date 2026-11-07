import Mu4.Bridge.Tables
import Mu4.Bridge.Mat2Check

/-!
# 2×2 matrices with prescribed eigenvectors

`conjCode a0 a1 b0 b1 l m` is the code of `Q diag(l, m) Q⁻¹` with `Q = [[a0, b0], [a1, b1]]`
(columns the eigenvectors `α = (a0, a1)`, `β = (b0, b1)`). Finite facts: it is diagonalizable in the
sense of `diagPred`, it has `α, β` as eigenvectors with eigenvalues `l, m`, and two such matrices with
the same `Q` commute.

These are finite facts over GF(4)^6 and GF(4)^8. Since 11-06 (second agent) they are kernel checks
(Mu4/Bridge/Mat2Check.lean: Bool checks over the list of GF(4), in chunks); the first version used
`native_decide`, after a kernel `decide` on the quantified statements had exceeded 6 GB.
-/

set_option autoImplicit false

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search

/-- The code of `Q diag(l, m) Q⁻¹` (characteristic 2: `Q⁻¹ = det⁻¹ [[b1, b0], [a1, a0]]`). -/
def conjCode (a0 a1 b0 b1 l m : F4) : Nat :=
  let di := (a0 * b1 + b0 * a1)⁻¹
  mat2 (di * (a0 * l * b1 + b0 * m * a1)) (di * (a0 * l * b0 + b0 * m * a0))
    (di * (a1 * l * b1 + b1 * m * a1)) (di * (a1 * l * b0 + b1 * m * a0))

/-- `conjCode` is the function `conjC` of the kernel checks. -/
lemma conjCode_eq (a0 a1 b0 b1 l m : F4) : conjCode a0 a1 b0 b1 l m = conjC a0 a1 b0 b1 l m := rfl

/-- A check over the list of GF(4) holds at every element. -/
lemma of_f4List {p : F4 → Bool} (h : f4List.all p = true) (x : F4) : p x = true := by
  simp only [f4List, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  cases x
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- The determinant test of the checks, at a nonzero determinant. -/
lemma of_det {a0 a1 b0 b1 : F4} {r : Bool} (h : a0 * b1 + b0 * a1 ≠ 0)
    (hr : (a0 * b1 + b0 * a1 == 0 || r) = true) : r = true := by
  rcases Bool.or_eq_true_iff.mp hr with h' | h'
  · exact absurd (beq_iff_eq.mp h') h
  · exact h'

theorem conjCode_diag : ∀ a0 a1 b0 b1 l m : F4, a0 * b1 + b0 * a1 ≠ 0 →
    diagPred (conjCode a0 a1 b0 b1 l m) = true := by
  intro a0 a1 b0 b1 l m h
  have h1 : diagOK a0 a1 b0 b1 = true := of_f4List (of_f4List (of_f4List (of_f4List diag_all a0) a1) b0) b1
  rw [conjCode_eq]
  exact of_f4List (of_f4List (of_det h h1) l) m

theorem conjCode_eigen : ∀ a0 a1 b0 b1 l m : F4, a0 * b1 + b0 * a1 ≠ 0 →
    (m00 (conjCode a0 a1 b0 b1 l m) * a0 + m01 (conjCode a0 a1 b0 b1 l m) * a1 = l * a0 ∧
     m10 (conjCode a0 a1 b0 b1 l m) * a0 + m11 (conjCode a0 a1 b0 b1 l m) * a1 = l * a1) ∧
    (m00 (conjCode a0 a1 b0 b1 l m) * b0 + m01 (conjCode a0 a1 b0 b1 l m) * b1 = m * b0 ∧
     m10 (conjCode a0 a1 b0 b1 l m) * b0 + m11 (conjCode a0 a1 b0 b1 l m) * b1 = m * b1) := by
  intro a0 a1 b0 b1 l m h
  have h1 : eigenOK a0 a1 b0 b1 = true :=
    of_f4List (of_f4List (of_f4List (of_f4List eigen_all a0) a1) b0) b1
  have h2 := of_f4List (of_f4List (of_det h h1) l) m
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h2
  rw [conjCode_eq]
  exact ⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩

/-- `commOK` holds everywhere (the four chunks of Mat2Check). -/
lemma commOK_all (a0 a1 b0 b1 : F4) : commOK a0 a1 b0 b1 = true := by
  cases a0
  · exact of_f4List (of_f4List (of_f4List comm_all_z a1) b0) b1
  · exact of_f4List (of_f4List (of_f4List comm_all_o a1) b0) b1
  · exact of_f4List (of_f4List (of_f4List comm_all_w a1) b0) b1
  · exact of_f4List (of_f4List (of_f4List comm_all_w2 a1) b0) b1

theorem conjCode_comm : ∀ a0 a1 b0 b1 l m l' m' : F4, a0 * b1 + b0 * a1 ≠ 0 →
    comm2 (conjCode a0 a1 b0 b1 l m) (conjCode a0 a1 b0 b1 l' m') = true := by
  intro a0 a1 b0 b1 l m l' m' h
  rw [conjCode_eq, conjCode_eq]
  exact of_f4List (of_f4List (of_f4List (of_f4List (of_det h (commOK_all a0 a1 b0 b1)) l) m) l') m'

lemma conjCode_lt (a0 a1 b0 b1 l m : F4) : conjCode a0 a1 b0 b1 l m < 256 := mat2_lt _ _ _ _

end Mu4.Bridge
