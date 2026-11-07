import Mu4.GF
import Mu4Comp.Codes
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Bit codes for GF(4)-vectors

The searches work on natural numbers: coordinate `l` of a vector over GF(4) sits in bits `2l`
(coefficient of 1) and `2l+1` (coefficient of ω), the coding of `runs/hyper/hp2.c`. Addition is
`xor`; `smulC` is scalar multiplication; `mulC` is multiplication in GF(4^6).
`decode` maps a code to its element of `GF`, and the lemmas here say that the code operations
compute the field operations.
-/

namespace Mu4
open F4

lemma ofBits_xor (a b c d : Bool) :
    F4.ofBits (a ^^ c) (b ^^ d) = F4.ofBits a b + F4.ofBits c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

@[simp] lemma coordC_xor (x y l : Nat) : coordC (x ^^^ y) l = coordC x l + coordC y l := by
  simp only [coordC, Nat.testBit_xor, ofBits_xor]

@[simp] lemma coordC_zero (l : Nat) : coordC 0 l = 0 := by simp [coordC, F4.ofBits]; rfl

/-! ### Scalar multiplication -/

lemma mask5_even (l : Nat) (hl : l < 32) : mask5.testBit (2 * l) = true := by
  revert l; decide

lemma mask5_odd (l : Nat) : mask5.testBit (2 * l + 1) = false := by
  by_cases hl : l < 32
  · revert l; decide
  · apply Nat.testBit_eq_false_of_lt
    calc mask5 < 2 ^ 64 := by decide
      _ ≤ 2 ^ (2 * l + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma ofBits_mulw (a b : Bool) : F4.ofBits b (a ^^ b) = w * F4.ofBits a b := by
  cases a <;> cases b <;> rfl

lemma testBit_mulw_even (x l : Nat) (hl : l < 32) :
    (mulw x).testBit (2 * l) = x.testBit (2 * l + 1) := by
  unfold mulw
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, mask5_even l hl, Bool.and_true,
    Nat.testBit_shiftLeft, Nat.add_comm 1 (2 * l)]
  rcases l with _ | j
  · simp
  · have e : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [e, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, mask5_odd j]
    simp

lemma testBit_mulw_odd (x l : Nat) (hl : l < 32) :
    (mulw x).testBit (2 * l + 1) = (x.testBit (2 * l) ^^ x.testBit (2 * l + 1)) := by
  unfold mulw
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, mask5_odd l, Bool.and_false,
    Bool.false_or, Nat.testBit_shiftLeft]
  have e : 2 * l + 1 - 1 = 2 * l := by omega
  rw [e, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight,
    mask5_even l hl, Nat.add_comm 1 (2 * l)]
  simp

lemma coordC_mulw (x l : Nat) (hl : l < 32) : coordC (mulw x) l = w * coordC x l := by
  simp only [coordC, testBit_mulw_even x l hl, testBit_mulw_odd x l hl, ofBits_mulw]

lemma coordC_smulC (c : F4) (x l : Nat) (hl : l < 32) :
    coordC (smulC c x) l = c * coordC x l := by
  cases c with
  | z => show coordC 0 l = (0 : F4) * coordC x l; rw [coordC_zero, zero_mul]
  | o => show coordC x l = (1 : F4) * coordC x l; rw [one_mul]
  | w => exact coordC_mulw x l hl
  | w2 =>
    show coordC (x ^^^ mulw x) l = w2 * coordC x l
    rw [coordC_xor, coordC_mulw x l hl]
    generalize coordC x l = d; revert d; decide

/-! ### Decoding to GF(4^6) -/

/-- The element of GF(4^6) with code `x`. -/
def decode (x : Nat) : GF := ⟨fun l => coordC x l.val⟩

@[simp] lemma decode_v (x : Nat) (l : Fin 6) : (decode x).v l = coordC x l.val := rfl

@[simp] lemma decode_xor (x y : Nat) : decode (x ^^^ y) = decode x + decode y := by
  ext l; simp

@[simp] lemma decode_zero : decode 0 = 0 := by ext l; simp

@[simp] lemma decode_smulC (c : F4) (x : Nat) : decode (smulC c x) = c • decode x := by
  ext l; simp [coordC_smulC c x l.val (by omega)]

lemma decode_foldr_xor (L : List Nat) : decode (L.foldr (· ^^^ ·) 0) = (L.map decode).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

@[simp] lemma decode_xorFin {n : Nat} (f : Fin n → Nat) :
    decode (xorFin f) = ∑ i : Fin n, decode (f i) := by
  rw [xorFin, decode_foldr_xor, List.map_ofFn, List.sum_ofFn]; rfl

/-! ### Encoding -/

lemma coordC_shift (c : F4) (k l : Nat) :
    coordC (c.code <<< (2 * k)) l = if k = l then c else 0 := by
  have hc : c.code < 4 := by cases c <;> decide
  have big : ∀ i, 2 ≤ i → c.code.testBit i = false := fun i hi =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc (by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi))
  simp only [coordC, Nat.testBit_shiftLeft]
  by_cases hkl : k = l
  · subst hkl
    have e1 : 2 * k + 1 - 2 * k = 1 := by omega
    simp only [ge_iff_le, le_refl, decide_true, Nat.sub_self, Bool.true_and, e1, if_true,
      show 2 * k ≤ 2 * k + 1 by omega]
    cases c <;> rfl
  · rw [if_neg hkl]
    rcases Nat.lt_or_gt_of_ne hkl with h | h
    · have e0 : 2 * l - 2 * k = 2 * (l - k) := by omega
      have e1 : 2 * l + 1 - 2 * k = 2 * (l - k) + 1 := by omega
      simp only [show 2 * k ≤ 2 * l by omega, show 2 * k ≤ 2 * l + 1 by omega, decide_true,
        Bool.true_and, e0, e1, big _ (show 2 ≤ 2 * (l - k) by omega),
        big _ (show 2 ≤ 2 * (l - k) + 1 by omega)]
      rfl
    · simp only [show ¬ 2 * k ≤ 2 * l by omega, show ¬ 2 * k ≤ 2 * l + 1 by omega, decide_false,
        Bool.false_and]
      rfl

/-- The code of an element of GF(4^6). -/
def encode (a : GF) : Nat := xorFin fun l : Fin 6 => (a.v l).code <<< (2 * l.val)

@[simp] lemma decode_encode (a : GF) : decode (encode a) = a := by
  ext l
  simp only [encode, decode_xorFin]
  rw [GF.v_sum]
  simp [coordC_shift, Fin.val_inj]

end Mu4
