import Mu4.N5.Code5
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Bitwise

/-!
# GF(4^5) on codes: multiplication and inverses

`timesT5` (multiplication by `t`) and `mulK5` (multiplication, Horner form) on codes compute the multiplication of
`GF5`; the inverse table `invC5` (from `lean/tools/gen_tables5.py`) is checked by the kernel on all 1023 nonzero
codes (`decide +kernel`).
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4

/-- The element `t` of GF(4^5). -/
def tG5 : GF5 := ⟨pw5 1⟩

lemma mul_tG5_v (a : GF5) (l : Fin 5) :
    (a * tG5).v l = ∑ i : Fin 5, a.v i * T5 i 1 l := by
  rw [GF5.mul_v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_five]
  simp [tG5, pw5]

lemma testBit_1023 (l : Nat) (hl : l < 5) :
    (1023 : Nat).testBit (2 * l) = true ∧ (1023 : Nat).testBit (2 * l + 1) = true := by
  revert l; decide

lemma coordC_shl2' (v l : Nat) (hl : l < 5) :
    coordC ((v <<< 2) &&& 1023) l = if l = 0 then 0 else coordC v (l - 1) := by
  obtain ⟨h0, h1⟩ := testBit_1023 l hl
  simp only [coordC, Nat.testBit_and, Nat.testBit_shiftLeft, h0, h1, Bool.and_true]
  rcases l with _ | j
  · simp [F4.ofBits]; rfl
  · have e0 : 2 * (j + 1) - 2 = 2 * j := by omega
    have e1 : 2 * (j + 1) + 1 - 2 = 2 * j + 1 := by omega
    simp [e0, e1, show 2 ≤ 2 * (j + 1) by omega, show 2 ≤ 2 * (j + 1) + 1 by omega]

lemma T5_col1 : ∀ i l : Fin 5,
    T5 i 1 l = if i.val + 1 = l.val then 1 else if i.val = 4 then ![w, 1, 0, 0, 0] l else 0 := by
  decide

lemma coordC_6 : ∀ l : Fin 5, coordC 6 l.val = ![w, 1, 0, 0, 0] l := by decide

lemma decode5_timesT5 (v : Nat) : decode5 (timesT5 v) = decode5 v * tG5 := by
  ext l
  rw [mul_tG5_v]
  simp only [decode5_v, timesT5, coordC_xor, coordC_shl2' v l.val (by omega),
    coordC_smulC _ _ _ (show l.val < 32 by omega), coordC_6, T5_col1, Fin.sum_univ_five]
  fin_cases l <;> simp

lemma tG5_pow_v : ∀ l k : Fin 5, (tG5 ^ l.val).v k = pw5 ⟨l.val, by omega⟩ k := by decide +kernel

lemma tG5_pow (l : Fin 5) : tG5 ^ l.val = ⟨pw5 ⟨l.val, by omega⟩⟩ := GF5.ext (funext (tG5_pow_v l))

lemma decode5_eq_sum (x : Nat) : decode5 x = ∑ l : Fin 5, coordC x l • tG5 ^ l.val := by
  ext k
  rw [GF5.v_sum]
  simp only [GF5.smul_v, tG5_pow, Pi.smul_apply, smul_eq_mul, decode5_v, Fin.sum_univ_five]
  fin_cases k <;> simp [pw5]

lemma decode5_mulK5 (x y : Nat) : decode5 (mulK5 x y) = decode5 x * decode5 y := by
  rw [decode5_eq_sum x]
  simp only [mulK5, decode5_xor, decode5_smulC, decode5_timesT5, Fin.sum_univ_five, Algebra.smul_def]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  norm_num
  ring

theorem invC5_ok1 : (List.range' 1 512).all (fun x => mulK5 x (invC5 x) == 1) = true := by
  decide +kernel
theorem invC5_ok2 : (List.range' 513 511).all (fun x => mulK5 x (invC5 x) == 1) = true := by
  decide +kernel

lemma mulK5_invC5 (x : Nat) (h1 : 1 ≤ x) (h2 : x < 1024) : mulK5 x (invC5 x) = 1 := by
  have key : ∀ (s n : Nat), (List.range' s n).all (fun x => mulK5 x (invC5 x) == 1) = true →
      s ≤ x → x < s + n → mulK5 x (invC5 x) = 1 := by
    intro s n h hs hn
    have := List.all_eq_true.mp h x (List.mem_range'_1.mpr ⟨hs, hn⟩)
    simpa using this
  by_cases a : x < 513
  · exact key 1 512 invC5_ok1 h1 (by omega)
  · exact key 513 511 invC5_ok2 (by omega) (by omega)

end Mu4.N5
