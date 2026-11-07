import Mu4.N5.Step15
import Mu4.Normal.Frobenius

/-!
# mu_4(5), N5: the substitutions, on `A5`

For a decomposition valid on all of `A5`: `x ↦ u x` (`scaleX`), `y ↦ v y` (`scaleY`), the rescaling
`(c_i a_i, c_i⁻¹ b_i)` (`rescale`) and the Frobenius `x ↦ σ(x)` (`frobT`, `σ(z) = z^2`, `σ^10 = id` on GF(4^5))
give decompositions valid on `A5` again, and the step-1 data move along (as `Mu4/Normal/Transport.lean`,
`Frobenius.lean`). `τ(c) = c^2` on GF(4) is that of `Mu4.Lower`.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Lower

variable {r : ℕ}

/-! ### `x ↦ u x`, `y ↦ v y`, rescaling -/

/-- `x ↦ u x`: `a'_i = a_i(u ·)`, `g'_i = u⁻¹ g_i`. -/
def Decomp5.scaleX (D : Decomp5 r) (u : GF5) : Decomp5 r where
  a i := (D.a i).comp (LinearMap.mulLeft F4 u)
  b := D.b
  g i := u⁻¹ * D.g i

lemma Decomp5.scaleX_validOn {D : Decomp5 r} (hD : D.ValidOn ⊤) {u : GF5} (hu : u ≠ 0) :
    (D.scaleX u).ValidOn ⊤ := by
  intro x _ y
  have h := hD (u * x) Submodule.mem_top y
  calc x * y = u⁻¹ * (u * x * y) := by field_simp
    _ = u⁻¹ * ∑ i, (D.a i (u * x) * D.b i y) • D.g i := by rw [h]
    _ = ∑ i, ((D.scaleX u).a i x * (D.scaleX u).b i y) • (D.scaleX u).g i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Decomp5.scaleX]

/-- `y ↦ v y`: `b'_i = b_i(v ·)`, `g'_i = v⁻¹ g_i`. -/
def Decomp5.scaleY (D : Decomp5 r) (v : GF5) : Decomp5 r where
  a := D.a
  b i := (D.b i).comp (LinearMap.mulLeft F4 v)
  g i := v⁻¹ * D.g i

lemma Decomp5.scaleY_validOn {D : Decomp5 r} {U : Submodule F4 GF5} (hD : D.ValidOn U) {v : GF5}
    (hv : v ≠ 0) : (D.scaleY v).ValidOn U := by
  intro x hx y
  have h := hD x hx (v * y)
  calc x * y = v⁻¹ * (x * (v * y)) := by field_simp
    _ = v⁻¹ * ∑ i, (D.a i x * D.b i (v * y)) • D.g i := by rw [h]
    _ = ∑ i, ((D.scaleY v).a i x * (D.scaleY v).b i y) • (D.scaleY v).g i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Decomp5.scaleY]

/-- `(a_i, b_i) ↦ (c_i a_i, c_i⁻¹ b_i)`. -/
def Decomp5.rescale (D : Decomp5 r) (c : Fin r → F4) : Decomp5 r where
  a i := c i • D.a i
  b i := (c i)⁻¹ • D.b i
  g := D.g

lemma Decomp5.rescale_validOn {D : Decomp5 r} {U : Submodule F4 GF5} (hD : D.ValidOn U)
    {c : Fin r → F4} (hc : ∀ i, c i ≠ 0) : (D.rescale c).ValidOn U := by
  intro x hx y
  rw [hD x hx y]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Decomp5.rescale, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  field_simp [hc i]

lemma rescale_a_eq_zero5 {D : Decomp5 r} {c : Fin r → F4} (hc : ∀ i, c i ≠ 0) (i : Fin r) (x : GF5) :
    (D.rescale c).a i x = 0 ↔ D.a i x = 0 := by
  simp only [Decomp5.rescale, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, hc i, false_or]

/-- Step-1 data survive `y ↦ v y` unchanged. -/
def Step1Data5.scaleY {D : Decomp5 10} {H : Submodule F4 GF5} (S : Step1Data5 D H) (v : GF5) :
    Step1Data5 (D.scaleY v) H :=
  ⟨S.W, S.hW, S.p, S.q, S.hp, S.hq, S.hind, S.hWvan, S.hker, S.halive⟩

/-- Step-1 data survive the rescaling. -/
def Step1Data5.rescale {D : Decomp5 10} {H : Submodule F4 GF5} (S : Step1Data5 D H) {c : Fin 10 → F4}
    (hc : ∀ i, c i ≠ 0) : Step1Data5 (D.rescale c) H where
  W := S.W
  hW := S.hW
  p := S.p
  q := S.q
  hp := S.hp
  hq := S.hq
  hind := S.hind
  hWvan i hi := by
    rw [rescale_a_eq_zero5 hc, rescale_a_eq_zero5 hc]; exact S.hWvan i hi
  hker x hx h0 := S.hker x hx fun i hi => (rescale_a_eq_zero5 hc i x).mp (h0 i hi)
  halive := by
    rw [← S.halive]
    ext i
    simp only [mem_alive2_5]
    rw [Ne, Ne, Ne, Ne, rescale_a_eq_zero5 hc, rescale_a_eq_zero5 hc]

/-- Step-1 data along `x ↦ u x`: the pencil basis becomes `u⁻¹ p, u⁻¹ q`. -/
def Step1Data5.scaleX {D : Decomp5 10} (S : Step1Data5 D ⊤) {u : GF5} (hu : u ≠ 0) :
    Step1Data5 (D.scaleX u) ⊤ where
  W := S.W
  hW := S.hW
  p := u⁻¹ * S.p
  q := u⁻¹ * S.q
  hp := Submodule.mem_top
  hq := Submodule.mem_top
  hind := by
    have h := S.hind.map' (LinearMap.mulLeft F4 u⁻¹)
      (LinearMap.ker_eq_bot.mpr fun a b hab => by
        simpa [LinearMap.mulLeft_apply, inv_ne_zero hu] using hab)
    convert h using 1
    funext k; fin_cases k <;> rfl
  hWvan i hi := by
    simp only [Decomp5.scaleX, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      mul_inv_cancel_left₀ hu]
    exact S.hWvan i hi
  hker x _ h0 := by
    have h1 : u * x ∈ Submodule.span F4 {S.p, S.q} := S.hker (u * x) Submodule.mem_top fun i hi => h0 i hi
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h1
    refine Submodule.mem_span_pair.mpr ⟨α, β, ?_⟩
    have : x = u⁻¹ * (u * x) := by rw [inv_mul_cancel_left₀ hu]
    rw [this, ← hαβ, mul_add, mul_smul_comm, mul_smul_comm]
  halive := by
    rw [← S.halive]
    ext i
    simp only [mem_alive2_5, Decomp5.scaleX, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply, mul_inv_cancel_left₀ hu]

/-! ### Another basis of the pencil -/

lemma form_zero_on_span5 (f : GF5 →ₗ[F4] F4) {u v x : GF5} (hu : f u = 0) (hv : f v = 0)
    (hx : x ∈ Submodule.span F4 {u, v}) : f x = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp [hu, hv]

lemma finrank_span_pair5' {u v : GF5} (h : LinearIndependent F4 ![u, v]) :
    Module.finrank F4 (Submodule.span F4 ({u, v} : Set GF5)) = 2 := by
  have hr2 : Set.range ![u, v] = {u, v} := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h) <;> simp [← h]
    · rintro (h | h) <;> simp [h]
  have := finrank_span_eq_card h
  rw [hr2] at this
  simpa using this

lemma span_pair_eq5 {u v u' v' : GF5} (hu' : u' ∈ Submodule.span F4 {u, v})
    (hv' : v' ∈ Submodule.span F4 {u, v}) (h : LinearIndependent F4 ![u, v])
    (h' : LinearIndependent F4 ![u', v']) :
    Submodule.span F4 {u', v'} = Submodule.span F4 {u, v} := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hu'
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hv'
  · rw [finrank_span_pair5' h', finrank_span_pair5' h]

/-- Step-1 data with another basis `p', q'` of the same pencil. -/
def Step1Data5.rebase {D : Decomp5 10} (S : Step1Data5 D ⊤) (p' q' : GF5)
    (hp' : p' ∈ Submodule.span F4 {S.p, S.q}) (hq' : q' ∈ Submodule.span F4 {S.p, S.q})
    (hind' : LinearIndependent F4 ![p', q']) : Step1Data5 D ⊤ where
  W := S.W
  hW := S.hW
  p := p'
  q := q'
  hp := Submodule.mem_top
  hq := Submodule.mem_top
  hind := hind'
  hWvan i hi := ⟨form_zero_on_span5 _ (S.hWvan i hi).1 (S.hWvan i hi).2 hp',
    form_zero_on_span5 _ (S.hWvan i hi).1 (S.hWvan i hi).2 hq'⟩
  hker x hx h0 := by
    rw [span_pair_eq5 hp' hq' S.hind hind']
    exact S.hker x hx h0
  halive := by
    rw [← S.halive]
    have e := span_pair_eq5 hp' hq' S.hind hind'
    have hp1 : S.p ∈ Submodule.span F4 {p', q'} := by rw [e]; exact Submodule.subset_span (Set.mem_insert _ _)
    have hq1 : S.q ∈ Submodule.span F4 {p', q'} := by
      rw [e]; exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
    ext i
    simp only [mem_alive2_5]
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      rcases h with h | h
      · exact h (form_zero_on_span5 _ hc.1 hc.2 hp')
      · exact h (form_zero_on_span5 _ hc.1 hc.2 hq')
    · intro h
      by_contra hc
      push_neg at hc
      rcases h with h | h
      · exact h (form_zero_on_span5 _ hc.1 hc.2 hp1)
      · exact h (form_zero_on_span5 _ hc.1 hc.2 hq1)

/-! ### The Frobenius -/

/-- The Frobenius of GF(4^5) over GF(2). -/
def frob5 (x : GF5) : GF5 := x * x

lemma GF5_add_self' (x : GF5) : x + x = 0 := by
  ext k; simp only [GF5.add_v, Pi.add_apply, GF5.zero_v, Pi.zero_apply]; exact F4.add_self _

lemma frob5_add (x y : GF5) : frob5 (x + y) = frob5 x + frob5 y := by
  have h : x * y + x * y = 0 := GF5_add_self' _
  unfold frob5
  linear_combination h

lemma frob5_mul (x y : GF5) : frob5 (x * y) = frob5 x * frob5 y := by unfold frob5; ring

lemma frob5_smul (c : F4) (x : GF5) : frob5 (c • x) = tau c • frob5 x := by
  unfold frob5 tau; rw [smul_mul_smul_comm]

lemma frob5_iter_pow (n : ℕ) (x : GF5) : frob5^[n] x = x ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, frob5, ← pow_two, ← pow_mul, pow_succ]

lemma frob5_iter10 (x : GF5) : frob5^[10] x = x := by
  rw [frob5_iter_pow]
  have := FiniteField.pow_card x
  rwa [GF5.card_eq] at this

/-- `σ^9 = σ⁻¹`. -/
def frobInv5 (x : GF5) : GF5 := frob5^[9] x

lemma frob5_frobInv5 (x : GF5) : frob5 (frobInv5 x) = x := by
  rw [frobInv5, ← Function.iterate_succ_apply' frob5 9 x]; exact frob5_iter10 x

lemma frobInv5_frob5 (x : GF5) : frobInv5 (frob5 x) = x := by
  rw [frobInv5, ← Function.iterate_succ_apply frob5 9 x]; exact frob5_iter10 x

lemma frobInv5_add (x y : GF5) : frobInv5 (x + y) = frobInv5 x + frobInv5 y := by
  apply_fun frob5 using fun a b h => by rw [← frobInv5_frob5 a, h, frobInv5_frob5]
  rw [frob5_add, frob5_frobInv5, frob5_frobInv5, frob5_frobInv5]

lemma frobInv5_smul (c : F4) (x : GF5) : frobInv5 (c • x) = tau c • frobInv5 x := by
  apply_fun frob5 using fun a b h => by rw [← frobInv5_frob5 a, h, frobInv5_frob5]
  rw [frob5_smul, frob5_frobInv5, frob5_frobInv5, tau_tau]

/-- `τ ∘ f ∘ σ⁻¹`, again `F4`-linear. -/
def twist5 (f : GF5 →ₗ[F4] F4) : GF5 →ₗ[F4] F4 where
  toFun x := tau (f (frobInv5 x))
  map_add' x y := by rw [frobInv5_add, map_add, tau_add]
  map_smul' c x := by
    rw [frobInv5_smul, map_smul, smul_eq_mul, tau_mul, tau_tau, RingHom.id_apply, smul_eq_mul]

/-- The Frobenius transport of a decomposition. -/
def Decomp5.frobT (D : Decomp5 r) : Decomp5 r where
  a i := twist5 (D.a i)
  b i := twist5 (D.b i)
  g i := frob5 (D.g i)

lemma frob5_sum {ι : Type*} (s : Finset ι) (f : ι → GF5) : frob5 (∑ i ∈ s, f i) = ∑ i ∈ s, frob5 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frob5]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frob5_add, ih]

lemma frob5_mul_inv (x y : GF5) : frob5 (frobInv5 x * frobInv5 y) = x * y := by
  rw [frob5_mul, frob5_frobInv5, frob5_frobInv5]

lemma Decomp5.frobT_validOn {D : Decomp5 r} (hD : D.ValidOn ⊤) : D.frobT.ValidOn ⊤ := by
  intro x _ y
  have h := hD (frobInv5 x) Submodule.mem_top (frobInv5 y)
  calc x * y = frob5 (frobInv5 x * frobInv5 y) := (frob5_mul_inv x y).symm
    _ = frob5 (∑ i, (D.a i (frobInv5 x) * D.b i (frobInv5 y)) • D.g i) := by rw [h]
    _ = ∑ i, (D.frobT.a i x * D.frobT.b i y) • D.frobT.g i := by
        rw [frob5_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [frob5_smul, tau_mul]
        rfl

lemma frobInv5_zero : frobInv5 0 = 0 := by
  have h := frobInv5_add 0 0
  rw [add_zero] at h
  have h2 : frobInv5 0 + frobInv5 0 = 0 := GF5_add_self' _
  rw [← h] at h2; exact h2

/-- Step-1 data along the Frobenius transport: the pencil basis becomes `σ p, σ q`. -/
def Step1Data5.frobT {D : Decomp5 10} (S : Step1Data5 D ⊤) : Step1Data5 D.frobT ⊤ where
  W := S.W
  hW := S.hW
  p := frob5 S.p
  q := frob5 S.q
  hp := Submodule.mem_top
  hq := Submodule.mem_top
  hind := by
    have hpq := LinearIndependent.pair_iff.mp S.hind
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg frobInv5 hst
    rw [frobInv5_add, frobInv5_smul, frobInv5_smul, frobInv5_frob5, frobInv5_frob5, frobInv5_zero] at h
    obtain ⟨hs, ht⟩ := hpq _ _ h
    exact ⟨(tau_eq_zero s).mp hs, (tau_eq_zero t).mp ht⟩
  hWvan i hi := by
    show tau (D.a i (frobInv5 (frob5 S.p))) = 0 ∧ tau (D.a i (frobInv5 (frob5 S.q))) = 0
    rw [frobInv5_frob5, frobInv5_frob5, (S.hWvan i hi).1, (S.hWvan i hi).2]
    exact ⟨rfl, rfl⟩
  hker x _ h0 := by
    have h1 : frobInv5 x ∈ Submodule.span F4 {S.p, S.q} :=
      S.hker _ Submodule.mem_top fun i hi => (tau_eq_zero _).mp (h0 i hi)
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h1
    refine Submodule.mem_span_pair.mpr ⟨tau α, tau β, ?_⟩
    rw [← frob5_smul, ← frob5_smul, ← frob5_add, hαβ, frob5_frobInv5]
  halive := by
    rw [← S.halive]
    ext i
    simp only [mem_alive2_5]
    show (tau (D.a i (frobInv5 (frob5 S.p))) ≠ 0 ∨ tau (D.a i (frobInv5 (frob5 S.q))) ≠ 0) ↔ _
    rw [frobInv5_frob5, frobInv5_frob5, Ne, Ne, tau_eq_zero, tau_eq_zero]

/-! ### Iterates -/

lemma frob5_one : frob5 1 = 1 := by simp [frob5]

lemma frob5Iter_mul (n : ℕ) (x y : GF5) : frob5^[n] (x * y) = frob5^[n] x * frob5^[n] y := by
  rw [frob5_iter_pow, frob5_iter_pow, frob5_iter_pow, mul_pow]

lemma frob5Iter_add (n : ℕ) (x y : GF5) : frob5^[n] (x + y) = frob5^[n] x + frob5^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, frob5_add, ← Function.iterate_succ_apply' frob5,
      ← Function.iterate_succ_apply' frob5]

lemma frob5Iter_smul (n : ℕ) (c : F4) (x : GF5) : frob5^[n] (c • x) = tau^[n] c • frob5^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, frob5_smul, ← Function.iterate_succ_apply' frob5,
      ← Function.iterate_succ_apply' tau]

lemma frob5Iter_one (n : ℕ) : frob5^[n] 1 = 1 := by rw [frob5_iter_pow, one_pow]

lemma frob5Iter_inv (n : ℕ) (x : GF5) : frob5^[n] x⁻¹ = (frob5^[n] x)⁻¹ := by
  rw [frob5_iter_pow, frob5_iter_pow, inv_pow]

/-- `σ^r σ^s = id` for `r = 10 - s` (`s ≠ 0`) or `r = 0` (`s = 0`). -/
lemma frob5Iter_cancel (s : ℕ) (hs : s < 10) (x : GF5) :
    frob5^[if s = 0 then 0 else 10 - s] (frob5^[s] x) = x := by
  rw [← Function.iterate_add_apply]
  split_ifs with h
  · subst h; rfl
  · rw [show 10 - s + s = 10 by omega]; exact frob5_iter10 x

/-- Iterated Frobenius transport. -/
def Decomp5.frobPow (D : Decomp5 r) : ℕ → Decomp5 r
  | 0 => D
  | n + 1 => (D.frobPow n).frobT

lemma Decomp5.frobPow_validOn {D : Decomp5 r} (hD : D.ValidOn ⊤) (n : ℕ) : (D.frobPow n).ValidOn ⊤ := by
  induction n with
  | zero => exact hD
  | succ n ih => exact Decomp5.frobT_validOn ih

/-- Step-1 data along the iterated Frobenius transport. -/
def Step1Data5.frobPow {D : Decomp5 10} (S : Step1Data5 D ⊤) : (n : ℕ) → Step1Data5 (D.frobPow n) ⊤
  | 0 => S
  | n + 1 => (S.frobPow n).frobT

lemma Step1Data5.frobPow_p {D : Decomp5 10} (S : Step1Data5 D ⊤) (n : ℕ) :
    (S.frobPow n).p = frob5^[n] S.p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show frob5 (S.frobPow n).p = _
    rw [ih, Function.iterate_succ_apply']

lemma Step1Data5.frobPow_q {D : Decomp5 10} (S : Step1Data5 D ⊤) (n : ℕ) :
    (S.frobPow n).q = frob5^[n] S.q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show frob5 (S.frobPow n).q = _
    rw [ih, Function.iterate_succ_apply']

end Mu4.N5
