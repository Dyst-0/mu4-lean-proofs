import Mu4.Normal.Transport

/-!
# The Frobenius transport of L6 (`audit/PROOF.md`)

The substitution `x ↦ σ(x)` with `σ(z) = z^2`. `σ` is additive and multiplicative on GF(4^6),
`σ(c • x) = τ(c) • σ(x)` with `τ(c) = c^2` on GF(4), and `σ^12 = id`. A decomposition `D` valid on `H`
gives `D.frobT` valid on `H.frobImage = σ(H)` (the set of `x` with `σ^11 x ∈ H`), with
`a'_i = τ ∘ a_i ∘ σ^11`, `b'_i = τ ∘ b_i ∘ σ^11`, `g'_i = σ(g_i)`, and `σ(H)` has the dimension of `H`.
The step-1 data move along (`Step1Data.frobT`), and so do iterates (`Decomp.frobPow`, `Step1Data.frobPow`).
(First written as work in progress in `lean/wip/`, 11-05.)
-/

set_option autoImplicit false

namespace Mu4.Lower
open Mu4

/-- The Frobenius of GF(4^6) over GF(2). -/
def frob (x : GF) : GF := x * x

/-- The Frobenius of GF(4). -/
def tau (c : F4) : F4 := c * c

lemma GF_add_self' (x : GF) : x + x = 0 := by
  ext k; simp only [GF.add_v, Pi.add_apply, GF.zero_v, Pi.zero_apply]; exact F4.add_self _

lemma frob_add (x y : GF) : frob (x + y) = frob x + frob y := by
  have h : x * y + x * y = 0 := GF_add_self' _
  unfold frob
  linear_combination h

lemma frob_mul (x y : GF) : frob (x * y) = frob x * frob y := by unfold frob; ring

lemma frob_smul (c : F4) (x : GF) : frob (c • x) = tau c • frob x := by
  unfold frob tau; rw [smul_mul_smul_comm]

lemma tau_add : ∀ a b : F4, tau (a + b) = tau a + tau b := by decide
lemma tau_mul : ∀ a b : F4, tau (a * b) = tau a * tau b := by decide
lemma tau_tau : ∀ a : F4, tau (tau a) = a := by decide
lemma tau_iter11 : ∀ a : F4, tau^[11] a = tau a := by decide

lemma frob_iter_pow (n : ℕ) (x : GF) : frob^[n] x = x ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, frob, ← pow_two, ← pow_mul, pow_succ]

lemma frob_iter12 (x : GF) : frob^[12] x = x := by
  rw [frob_iter_pow]
  have := FiniteField.pow_card x
  rwa [GF.card_eq] at this

/-- `σ^11 = σ⁻¹`. -/
def frobInv (x : GF) : GF := frob^[11] x

lemma frob_frobInv (x : GF) : frob (frobInv x) = x := by
  rw [frobInv, ← Function.iterate_succ_apply' frob 11 x]; exact frob_iter12 x

lemma frobInv_frob (x : GF) : frobInv (frob x) = x := by
  rw [frobInv, ← Function.iterate_succ_apply frob 11 x]; exact frob_iter12 x

lemma frobInv_add (x y : GF) : frobInv (x + y) = frobInv x + frobInv y := by
  apply_fun frob using fun a b h => by rw [← frobInv_frob a, h, frobInv_frob]
  rw [frob_add, frob_frobInv, frob_frobInv, frob_frobInv]

lemma frobInv_mul (x y : GF) : frobInv (x * y) = frobInv x * frobInv y := by
  apply_fun frob using fun a b h => by rw [← frobInv_frob a, h, frobInv_frob]
  rw [frob_mul, frob_frobInv, frob_frobInv, frob_frobInv]

lemma frobInv_smul (c : F4) (x : GF) : frobInv (c • x) = tau c • frobInv x := by
  apply_fun frob using fun a b h => by rw [← frobInv_frob a, h, frobInv_frob]
  rw [frob_smul, frob_frobInv, frob_frobInv, tau_tau]

/-- `τ ∘ f ∘ σ⁻¹`, again `F4`-linear. -/
def twist (f : GF →ₗ[F4] F4) : GF →ₗ[F4] F4 where
  toFun x := tau (f (frobInv x))
  map_add' x y := by rw [frobInv_add, map_add, tau_add]
  map_smul' c x := by
    rw [frobInv_smul, map_smul, smul_eq_mul, tau_mul, tau_tau, RingHom.id_apply, smul_eq_mul]

/-- `σ(H)`, as the set of `x` with `σ⁻¹ x ∈ H`. -/
def frobImage (H : Submodule F4 GF) : Submodule F4 GF where
  carrier := {x | frobInv x ∈ H}
  add_mem' {x y} hx hy := by
    show frobInv (x + y) ∈ H
    rw [frobInv_add]; exact H.add_mem hx hy
  zero_mem' := by
    show frobInv 0 ∈ H
    have h : frobInv 0 = 0 := by
      have := frobInv_add 0 0
      rw [add_zero] at this
      have h2 : frobInv 0 + frobInv 0 = 0 := GF_add_self' _
      rw [← this] at h2; exact h2
    rw [h]; exact H.zero_mem
  smul_mem' c x hx := by
    show frobInv (c • x) ∈ H
    rw [frobInv_smul]; exact H.smul_mem _ hx

variable {r : ℕ}

/-- The Frobenius transport of a decomposition. -/
def Decomp.frobT (D : Decomp r) : Decomp r where
  a i := twist (D.a i)
  b i := twist (D.b i)
  g i := frob (D.g i)

lemma frob_sum {ι : Type*} (s : Finset ι) (f : ι → GF) : frob (∑ i ∈ s, f i) = ∑ i ∈ s, frob (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frob]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frob_add, ih]

lemma Decomp.frobT_validOn {D : Decomp r} {H : Submodule F4 GF} (hD : D.ValidOn H) :
    D.frobT.ValidOn (frobImage H) := by
  intro x hx y
  have h := hD (frobInv x) hx (frobInv y)
  calc x * y = frob (frobInv x * frobInv y) := by rw [frob_mul, frob_frobInv, frob_frobInv]
    _ = frob (∑ i, (D.a i (frobInv x) * D.b i (frobInv y)) • D.g i) := by rw [h]
    _ = ∑ i, (D.frobT.a i x * D.frobT.b i y) • D.frobT.g i := by
        rw [frob_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [frob_smul, tau_mul]
        rfl

/-- `σ(H)` has the dimension of `H` (by counting elements). -/
lemma finrank_frobImage (H : Submodule F4 GF) :
    Module.finrank F4 (frobImage H) = Module.finrank F4 H := by
  classical
  have hcard : Fintype.card (frobImage H) = Fintype.card H := by
    refine Fintype.card_congr
      { toFun := fun x => ⟨frobInv x.1, x.2⟩
        invFun := fun y => ⟨frob y.1, show frobInv (frob y.1) ∈ H by rw [frobInv_frob]; exact y.2⟩
        left_inv := fun x => Subtype.ext (frob_frobInv x.1)
        right_inv := fun y => Subtype.ext (frobInv_frob y.1) }
  rw [Module.card_eq_pow_finrank (K := F4), Module.card_eq_pow_finrank (K := F4) (V := H),
    F4.card] at hcard
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) hcard

lemma frobInv_zero : frobInv 0 = 0 := by
  have h := frobInv_add 0 0
  rw [add_zero] at h
  have h2 : frobInv 0 + frobInv 0 = 0 := GF_add_self' _
  rw [← h] at h2; exact h2

lemma tau_eq_zero : ∀ c : F4, tau c = 0 ↔ c = 0 := by decide

/-- Step-1 data along the Frobenius transport: the pencil basis becomes `σ p, σ q`. -/
def Step1Data.frobT {D : Decomp 12} {H : Submodule F4 GF} (S : Step1Data D H) :
    Step1Data D.frobT (frobImage H) where
  W := S.W
  hW := S.hW
  p := frob S.p
  q := frob S.q
  hp := by show frobInv (frob S.p) ∈ H; rw [frobInv_frob]; exact S.hp
  hq := by show frobInv (frob S.q) ∈ H; rw [frobInv_frob]; exact S.hq
  hind := by
    have hpq := LinearIndependent.pair_iff.mp S.hind
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg frobInv hst
    rw [frobInv_add, frobInv_smul, frobInv_smul, frobInv_frob, frobInv_frob, frobInv_zero] at h
    obtain ⟨hs, ht⟩ := hpq _ _ h
    exact ⟨(tau_eq_zero s).mp hs, (tau_eq_zero t).mp ht⟩
  hWvan i hi := by
    show tau (D.a i (frobInv (frob S.p))) = 0 ∧ tau (D.a i (frobInv (frob S.q))) = 0
    rw [frobInv_frob, frobInv_frob, (S.hWvan i hi).1, (S.hWvan i hi).2]
    exact ⟨rfl, rfl⟩
  hker x hx h0 := by
    have h1 : frobInv x ∈ Submodule.span F4 {S.p, S.q} :=
      S.hker _ hx fun i hi => (tau_eq_zero _).mp (h0 i hi)
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h1
    refine Submodule.mem_span_pair.mpr ⟨tau α, tau β, ?_⟩
    rw [← frob_smul, ← frob_smul, ← frob_add, hαβ, frob_frobInv]
  halive := by
    rw [← S.halive]
    ext i
    simp only [mem_alive2]
    show (tau (D.a i (frobInv (frob S.p))) ≠ 0 ∨ tau (D.a i (frobInv (frob S.q))) ≠ 0) ↔ _
    rw [frobInv_frob, frobInv_frob, Ne, Ne, tau_eq_zero, tau_eq_zero]

/-! ### Iterates -/

lemma frob_zero : frob 0 = 0 := by simp [frob]
lemma frob_one : frob 1 = 1 := by simp [frob]

lemma frobIter_mul (n : ℕ) (x y : GF) : frob^[n] (x * y) = frob^[n] x * frob^[n] y := by
  rw [frob_iter_pow, frob_iter_pow, frob_iter_pow, mul_pow]

lemma frobIter_add (n : ℕ) (x y : GF) : frob^[n] (x + y) = frob^[n] x + frob^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, frob_add, ← Function.iterate_succ_apply' frob,
      ← Function.iterate_succ_apply' frob]

lemma frobIter_smul (n : ℕ) (c : F4) (x : GF) : frob^[n] (c • x) = tau^[n] c • frob^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, frob_smul, ← Function.iterate_succ_apply' frob,
      ← Function.iterate_succ_apply' tau]

lemma frobIter_one (n : ℕ) : frob^[n] 1 = 1 := by rw [frob_iter_pow, one_pow]

lemma frobIter_inv (n : ℕ) (x : GF) : frob^[n] x⁻¹ = (frob^[n] x)⁻¹ := by
  rw [frob_iter_pow, frob_iter_pow, inv_pow]

lemma tauIter_ne_zero (n : ℕ) {c : F4} (hc : c ≠ 0) : tau^[n] c ≠ 0 := by
  induction n with
  | zero => exact hc
  | succ n ih => rw [Function.iterate_succ_apply']; exact fun h => ih ((tau_eq_zero _).mp h)

/-- `σ^r σ^s = id` for `r = 12 - s` (`s ≠ 0`) or `r = 0` (`s = 0`). -/
lemma frobIter_cancel (s : ℕ) (hs : s < 12) (x : GF) :
    frob^[if s = 0 then 0 else 12 - s] (frob^[s] x) = x := by
  rw [← Function.iterate_add_apply]
  split_ifs with h
  · subst h; rfl
  · rw [show 12 - s + s = 12 by omega]; exact frob_iter12 x

/-- Iterated Frobenius transport. -/
def Decomp.frobPow (D : Decomp r) : ℕ → Decomp r
  | 0 => D
  | n + 1 => (D.frobPow n).frobT

/-- `σ^n(H)`. -/
def frobImagePow (H : Submodule F4 GF) : ℕ → Submodule F4 GF
  | 0 => H
  | n + 1 => frobImage (frobImagePow H n)

lemma Decomp.frobPow_validOn {D : Decomp r} {H : Submodule F4 GF} (hD : D.ValidOn H) (n : ℕ) :
    (D.frobPow n).ValidOn (frobImagePow H n) := by
  induction n with
  | zero => exact hD
  | succ n ih => exact Decomp.frobT_validOn ih

lemma finrank_frobImagePow (H : Submodule F4 GF) (n : ℕ) :
    Module.finrank F4 (frobImagePow H n) = Module.finrank F4 H := by
  induction n with
  | zero => rfl
  | succ n ih => rw [frobImagePow, finrank_frobImage, ih]

/-- Step-1 data along the iterated Frobenius transport. -/
def Step1Data.frobPow {D : Decomp 12} {H : Submodule F4 GF} (S : Step1Data D H) :
    (n : ℕ) → Step1Data (D.frobPow n) (frobImagePow H n)
  | 0 => S
  | n + 1 => (S.frobPow n).frobT

lemma Step1Data.frobPow_p {D : Decomp 12} {H : Submodule F4 GF} (S : Step1Data D H) (n : ℕ) :
    (S.frobPow n).p = frob^[n] S.p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show frob (S.frobPow n).p = _
    rw [ih, Function.iterate_succ_apply']

lemma Step1Data.frobPow_q {D : Decomp 12} {H : Submodule F4 GF} (S : Step1Data D H) (n : ℕ) :
    (S.frobPow n).q = frob^[n] S.q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show frob (S.frobPow n).q = _
    rw [ih, Function.iterate_succ_apply']

end Mu4.Lower
