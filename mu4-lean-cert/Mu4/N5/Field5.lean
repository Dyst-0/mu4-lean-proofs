import Mu4.N5.GFField5
import Mu4.Field

/-!
# The `Field` instance on GF5(4^5)

`a⁻¹ := decode5 (invC5 (encode5 a))`; `a * a⁻¹ = 1` for `a ≠ 0` from `decode5_mulK5` and the kernel check
`mulK5_invC5`.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4

lemma encode5_lt (a : GF5) : encode5 a < 1024 := by
  have term : ∀ l : Fin 5, (a.v l).code <<< (2 * l.val) < 2 ^ 10 := by
    intro l
    rw [Nat.shiftLeft_eq]
    have h1 := code_lt (a.v l)
    have h2 : 2 ^ (2 * l.val) * 4 ≤ 2 ^ 10 := by
      have : 2 * l.val + 2 ≤ 10 := by omega
      calc 2 ^ (2 * l.val) * 4 = 2 ^ (2 * l.val + 2) := by ring
        _ ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) this
    calc (a.v l).code * 2 ^ (2 * l.val) < 4 * 2 ^ (2 * l.val) :=
          Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ (2 * l.val) * 4 := by ring
      _ ≤ 2 ^ 10 := h2
  have hfold : ∀ L : List Nat, (∀ x ∈ L, x < 2 ^ 10) → L.foldr (· ^^^ ·) 0 < 2 ^ 10 := by
    intro L hL
    induction L with
    | nil => simp
    | cons x L ih =>
      simp only [List.foldr_cons]
      exact Nat.xor_lt_two_pow (hL x (by simp)) (ih fun y hy => hL y (by simp [hy]))
  have := hfold _ (by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨l, rfl⟩ := hx
    exact term l)
  simpa [encode5, xorFin] using this

lemma encode5_ne_zero {a : GF5} (h : a ≠ 0) : encode5 a ≠ 0 := by
  intro h0; apply h; rw [← decode5_encode5 a, h0, decode5_zero]

lemma decode5_one : decode5 1 = 1 := by
  ext l; fin_cases l <;> rfl

instance : Inv GF5 := ⟨fun a => decode5 (invC5 (encode5 a))⟩

lemma inv_def (a : GF5) : a⁻¹ = decode5 (invC5 (encode5 a)) := rfl

lemma encode5_zero : encode5 0 = 0 := by decide +kernel

lemma invC5_zero : invC5 0 = 0 := by decide +kernel

protected lemma GF5.mul_inv_cancel (a : GF5) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [inv_def]
  calc a * decode5 (invC5 (encode5 a)) = decode5 (encode5 a) * decode5 (invC5 (encode5 a)) := by
        rw [decode5_encode5]
    _ = decode5 (mulK5 (encode5 a) (invC5 (encode5 a))) := (decode5_mulK5 _ _).symm
    _ = 1 := by
        rw [mulK5_invC5 _ (Nat.one_le_iff_ne_zero.mpr (encode5_ne_zero h)) (encode5_lt a), decode5_one]

instance : Nontrivial GF5 := ⟨⟨0, 1, by
  intro h; have := congrArg (fun a : GF5 => a.v 0) h; exact absurd this (by decide)⟩⟩

instance : Field GF5 where
  mul_inv_cancel := GF5.mul_inv_cancel
  inv_zero := by rw [inv_def, encode5_zero, invC5_zero, decode5_zero]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end Mu4.N5
