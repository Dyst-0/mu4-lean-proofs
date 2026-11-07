import Mu4.N5.GF5
import Mu4.Code
import Mu4Comp5.Codes

/-!
# Bit codes for GF(4)-vectors of length 5: decoding to GF(4^5)

The coordinate lemmas of `Mu4/Code.lean` (`coordC_xor`, `coordC_smulC`, `coordC_shift`) hold for any code;
`decode5` maps a code to its element of `GF5` (the first five coordinates).
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4

/-! ### Decoding to GF(4^5) -/

/-- The element of GF(4^5) with code `x`. -/
def decode5 (x : Nat) : GF5 := ⟨fun l => coordC x l.val⟩

@[simp] lemma decode5_v (x : Nat) (l : Fin 5) : (decode5 x).v l = coordC x l.val := rfl

@[simp] lemma decode5_xor (x y : Nat) : decode5 (x ^^^ y) = decode5 x + decode5 y := by
  ext l; simp

@[simp] lemma decode5_zero : decode5 0 = 0 := by ext l; simp

@[simp] lemma decode5_smulC (c : F4) (x : Nat) : decode5 (smulC c x) = c • decode5 x := by
  ext l; simp [coordC_smulC c x l.val (by omega)]

lemma decode5_foldr_xor (L : List Nat) : decode5 (L.foldr (· ^^^ ·) 0) = (L.map decode5).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

@[simp] lemma decode5_xorFin {n : Nat} (f : Fin n → Nat) :
    decode5 (xorFin f) = ∑ i : Fin n, decode5 (f i) := by
  rw [xorFin, decode5_foldr_xor, List.map_ofFn, List.sum_ofFn]; rfl

/-! ### Encoding -/

/-- The code of an element of GF(4^5). -/
def encode5 (a : GF5) : Nat := xorFin fun l : Fin 5 => (a.v l).code <<< (2 * l.val)

@[simp] lemma decode5_encode5 (a : GF5) : decode5 (encode5 a) = a := by
  ext l
  simp only [encode5, decode5_xorFin]
  rw [GF5.v_sum]
  simp [coordC_shift, Fin.val_inj]

end Mu4.N5
