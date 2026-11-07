import Mu4.Bridge.Tables

/-!
# Code equality, bounds, and the linearity of the lookup keys

The search computes the key of the right-hand side `R_b(c)` as `combo4 c keysT_b`, by linearity in
the direction `c`; `combo4_keyR` says this is the key of `R_b(c)` itself.
-/

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower

lemma ofBits_inj (a b c d : Bool) (h : F4.ofBits a b = F4.ofBits c d) : a = c ∧ b = d := by
  revert h; cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma lt_of_lt_four_pow {x n m : Nat} (hx : x < 4 ^ n) (hm : 2 * n ≤ m) : x < 2 ^ m := by
  have e : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  rw [e] at hx
  exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hm)

/-- Codes below `4^n` are determined by their first `n` coordinates. -/
lemma code_ext {x y n : Nat} (hx : x < 4 ^ n) (hy : y < 4 ^ n)
    (h : ∀ l < n, coordC x l = coordC y l) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 2 * n
  · have hl : i / 2 < n := by omega
    have hc := h (i / 2) hl
    simp only [coordC] at hc
    obtain ⟨h0, h1⟩ := ofBits_inj _ _ _ _ hc
    rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
    · have : i = 2 * (i / 2) := by omega
      rw [this]; exact h0
    · have : i = 2 * (i / 2) + 1 := by omega
      rw [this]; exact h1
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_four_pow hx (by omega)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_four_pow hy (by omega))]

lemma mulw_lt {x n : Nat} (hx : x < 2 ^ (2 * n)) : mulw x < 2 ^ (2 * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hxi : ∀ j, j ≥ 2 * n → x.testBit j = false := fun j hj =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hj))
  unfold mulw
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, hxi (1 + i) (by omega),
    Bool.false_and, Bool.false_or, Nat.testBit_shiftLeft]
  by_cases h1 : i ≥ 1
  · simp only [h1, decide_true, Bool.true_and]
    rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight]
    by_cases h2 : i - 1 ≥ 2 * n
    · rw [hxi (i - 1) h2, hxi (1 + (i - 1)) (by omega)]; simp
    · have e : i - 1 = 2 * (n - 1) + 1 := by omega
      rw [e, mask5_odd]; simp
  · simp [h1]

lemma smulC_lt (c : F4) {x n : Nat} (hx : x < 2 ^ (2 * n)) : smulC c x < 2 ^ (2 * n) := by
  cases c
  · show 0 < 2 ^ (2 * n); positivity
  · exact hx
  · exact mulw_lt hx
  · exact Nat.xor_lt_two_pow hx (mulw_lt hx)

lemma xorFin_lt {k : Nat} (f : Fin k → Nat) {m : Nat} (hf : ∀ i, f i < 2 ^ m) : xorFin f < 2 ^ m := by
  have key : ∀ L : List Nat, (∀ x ∈ L, x < 2 ^ m) → L.foldr (· ^^^ ·) 0 < 2 ^ m := by
    intro L hL
    induction L with
    | nil => simp
    | cons a L ih =>
      exact Nat.xor_lt_two_pow (hL a (by simp)) (ih fun y hy => hL y (by simp [hy]))
  apply key
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hf i

lemma combo4_lt (c : Nat) (ks : List Nat) {n : Nat} (hks : ∀ k ∈ ks, k < 2 ^ (2 * n)) :
    combo4 c ks < 2 ^ (2 * n) := by
  match ks with
  | [k0, k1, k2, k3] =>
    simp only [combo4]
    refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_) ?_ <;>
      exact smulC_lt _ (hks _ (by simp))
  | [] => exact xorFin_lt _ fun i => absurd i.isLt (by simp)
  | [_] => exact xorFin_lt _ fun i => smulC_lt _ (hks _ (List.get_mem _ _))
  | [_, _] => exact xorFin_lt _ fun i => smulC_lt _ (hks _ (List.get_mem _ _))
  | [_, _, _] => exact xorFin_lt _ fun i => smulC_lt _ (hks _ (List.get_mem _ _))
  | _ :: _ :: _ :: _ :: _ :: _ => exact xorFin_lt _ fun i => smulC_lt _ (hks _ (List.get_mem _ _))

lemma keyR_lt (rhos : List Nat) (a b : Nat) : keyR rhos a b < 2 ^ (2 * 4) := by
  match rhos with
  | [r0, r1] => simp only [keyR]; exact mat2_lt _ _ _ _
  | [r0] =>
    simp only [keyR]
    have h0 := unitC_lt (dotC r0 a) 0
    have h1 := unitC_lt (dotC r0 b) 1
    exact Nat.xor_lt_two_pow (by omega) (by omega)
  | [] => simp [keyR]
  | _ :: _ :: _ :: _ => simp [keyR]

/-- The coordinates of `keyR`. -/
lemma coordC_keyR_pair (r0 r1 a b : Nat) :
    coordC (keyR [r0, r1] a b) 0 = dotC r0 a ∧ coordC (keyR [r0, r1] a b) 1 = dotC r0 b ∧
    coordC (keyR [r0, r1] a b) 2 = dotC r1 a ∧ coordC (keyR [r0, r1] a b) 3 = dotC r1 b := by
  simp [keyR]

lemma coordC_keyR_single (r0 a b : Nat) (l : Nat) :
    coordC (keyR [r0] a b) l = (if l = 0 then dotC r0 a else 0) + (if l = 1 then dotC r0 b else 0) := by
  simp only [keyR, coordC_xor, coordC_unitC]
  by_cases h0 : l = 0 <;> by_cases h1 : l = 1 <;> simp [h0, h1, eq_comm] <;> omega

end Mu4.Bridge
