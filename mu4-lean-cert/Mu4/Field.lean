import Mu4.GFField

/-!
# The `Field` instance on GF(4^6)

`a⁻¹ := decode (invC (encode a))`; `a * a⁻¹ = 1` for `a ≠ 0` follows from `decode_mulK` and the
kernel check `mulK_invC`.
-/

namespace Mu4
open F4

lemma code_lt (c : F4) : c.code < 4 := by cases c <;> decide

lemma xor_lt_pow (x y n : Nat) (hx : x < 2 ^ n) (hy : y < 2 ^ n) : x ^^^ y < 2 ^ n :=
  Nat.xor_lt_two_pow hx hy

lemma encode_lt (a : GF) : encode a < 4096 := by
  have term : ∀ l : Fin 6, (a.v l).code <<< (2 * l.val) < 2 ^ 12 := by
    intro l
    rw [Nat.shiftLeft_eq]
    have h1 := code_lt (a.v l)
    have h2 : 2 ^ (2 * l.val) * 4 ≤ 2 ^ 12 := by
      have : 2 * l.val + 2 ≤ 12 := by omega
      calc 2 ^ (2 * l.val) * 4 = 2 ^ (2 * l.val + 2) := by ring
        _ ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) this
    calc (a.v l).code * 2 ^ (2 * l.val) < 4 * 2 ^ (2 * l.val) :=
          Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ (2 * l.val) * 4 := by ring
      _ ≤ 2 ^ 12 := h2
  have hfold : ∀ L : List Nat, (∀ x ∈ L, x < 2 ^ 12) → L.foldr (· ^^^ ·) 0 < 2 ^ 12 := by
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
  simpa [encode, xorFin] using this

lemma encode_ne_zero {a : GF} (h : a ≠ 0) : encode a ≠ 0 := by
  intro h0; apply h; rw [← decode_encode a, h0, decode_zero]

lemma decode_one : decode 1 = 1 := by
  ext l; fin_cases l <;> rfl

instance : Inv GF := ⟨fun a => decode (invC (encode a))⟩

lemma inv_def (a : GF) : a⁻¹ = decode (invC (encode a)) := rfl

lemma encode_zero : encode 0 = 0 := by decide +kernel

lemma invC_zero : invC 0 = 0 := by decide +kernel

protected lemma GF.mul_inv_cancel (a : GF) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [inv_def]
  calc a * decode (invC (encode a)) = decode (encode a) * decode (invC (encode a)) := by
        rw [decode_encode]
    _ = decode (mulK (encode a) (invC (encode a))) := (decode_mulK _ _).symm
    _ = 1 := by
        rw [mulK_invC _ (Nat.one_le_iff_ne_zero.mpr (encode_ne_zero h)) (encode_lt a), decode_one]

instance : Nontrivial GF := ⟨⟨0, 1, by
  intro h; have := congrArg (fun a : GF => a.v 0) h; exact absurd this (by decide)⟩⟩

instance : Field GF where
  mul_inv_cancel := GF.mul_inv_cancel
  inv_zero := by rw [inv_def, encode_zero, invC_zero, decode_zero]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end Mu4
