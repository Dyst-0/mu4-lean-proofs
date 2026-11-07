import Mu4Comp.F4
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card

/-!
# The field with four elements

`F4 = {0, 1, ω, ω²}` with `ω² = ω + 1` (type and operations in `Mu4Comp/F4.lean`), as a Mathlib
`Field`. Every field axiom is a finite statement and is checked by the kernel (`decide`).
-/

namespace Mu4

namespace F4

instance : Fintype F4 := ⟨{z, o, w, w2}, fun x => by cases x <;> decide⟩

lemma zero_def : (0 : F4) = z := rfl
lemma one_def : (1 : F4) = o := rfl

instance : CommRing F4 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  neg_add_cancel := by decide
  mul_comm := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg := by decide

instance : Nontrivial F4 := ⟨⟨z, o, by decide⟩⟩

instance : Field F4 where
  mul_inv_cancel := by decide
  inv_zero := by decide
  div_eq_mul_inv := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

lemma card : Fintype.card F4 = 4 := rfl

/-- Characteristic 2. -/
lemma add_self (a : F4) : a + a = 0 := by revert a; decide

lemma w_sq : (w : F4) * w = w + 1 := by decide

end F4
end Mu4
