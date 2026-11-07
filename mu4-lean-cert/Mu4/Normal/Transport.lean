import Mu4.Lower.Step1
import Mathlib.FieldTheory.Finite.Basic

/-!
# The transports of L6 (`audit/PROOF.md`): `x ↦ u x`, `y ↦ v y`, rescaling, and a change of pencil basis

A decomposition valid on `U` moves along
* `x ↦ u x` (`scaleX`): valid on `{x | u x ∈ U}`, of the same dimension (`finrank_comap_mulLeft`);
* `y ↦ v y` (`scaleY`): valid on the same `U`;
* `(a_i, b_i) ↦ (c_i a_i, c_i⁻¹ b_i)` (`rescale`): valid on the same `U`.
The step-1 data move along (`Step1Data.scaleX`, `scaleY`, `rescale`), and `Step1Data.rebase` replaces the
basis `p, q` of the pencil by any other basis of the same plane. The Frobenius transport is in
`Mu4/Normal/Frobenius.lean`. (First written as work in progress in `lean/wip/`, 11-05.)
-/

set_option autoImplicit false

namespace Mu4.Lower
open Mu4

variable {r : ℕ}

/-- `x ↦ u x`: `a'_i = a_i(u ·)`, `g'_i = u⁻¹ g_i`. -/
def Decomp.scaleX (D : Decomp r) (u : GF) : Decomp r where
  a i := (D.a i).comp (LinearMap.mulLeft F4 u)
  b := D.b
  g i := u⁻¹ * D.g i

lemma Decomp.scaleX_validOn {D : Decomp r} {U : Submodule F4 GF} (hD : D.ValidOn U) {u : GF}
    (hu : u ≠ 0) : (D.scaleX u).ValidOn (U.comap (LinearMap.mulLeft F4 u)) := by
  intro x hx y
  have h := hD (u * x) hx y
  calc x * y = u⁻¹ * (u * x * y) := by field_simp
    _ = u⁻¹ * ∑ i, (D.a i (u * x) * D.b i y) • D.g i := by rw [h]
    _ = ∑ i, ((D.scaleX u).a i x * (D.scaleX u).b i y) • (D.scaleX u).g i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Decomp.scaleX]

/-- `y ↦ v y`: `b'_i = b_i(v ·)`, `g'_i = v⁻¹ g_i`. -/
def Decomp.scaleY (D : Decomp r) (v : GF) : Decomp r where
  a := D.a
  b i := (D.b i).comp (LinearMap.mulLeft F4 v)
  g i := v⁻¹ * D.g i

lemma Decomp.scaleY_validOn {D : Decomp r} {U : Submodule F4 GF} (hD : D.ValidOn U) {v : GF}
    (hv : v ≠ 0) : (D.scaleY v).ValidOn U := by
  intro x hx y
  have h := hD x hx (v * y)
  calc x * y = v⁻¹ * (x * (v * y)) := by field_simp
    _ = v⁻¹ * ∑ i, (D.a i x * D.b i (v * y)) • D.g i := by rw [h]
    _ = ∑ i, ((D.scaleY v).a i x * (D.scaleY v).b i y) • (D.scaleY v).g i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Decomp.scaleY]

/-- `(a_i, b_i) ↦ (c_i a_i, c_i⁻¹ b_i)`. -/
def Decomp.rescale (D : Decomp r) (c : Fin r → F4) : Decomp r where
  a i := c i • D.a i
  b i := (c i)⁻¹ • D.b i
  g := D.g

lemma Decomp.rescale_validOn {D : Decomp r} {U : Submodule F4 GF} (hD : D.ValidOn U)
    {c : Fin r → F4} (hc : ∀ i, c i ≠ 0) : (D.rescale c).ValidOn U := by
  intro x hx y
  rw [hD x hx y]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Decomp.rescale, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  field_simp [hc i]

/-! ### Step-1 data along `scaleY` and `rescale` (the forms `a_i` keep their zeros) -/

/-- Step-1 data survive `y ↦ v y` unchanged. -/
def Step1Data.scaleY {D : Decomp 12} {H : Submodule F4 GF} (S : Step1Data D H) (v : GF) :
    Step1Data (D.scaleY v) H :=
  ⟨S.W, S.hW, S.p, S.q, S.hp, S.hq, S.hind, S.hWvan, S.hker, S.halive⟩

lemma rescale_a_eq_zero {D : Decomp r} {c : Fin r → F4} (hc : ∀ i, c i ≠ 0) (i : Fin r) (x : GF) :
    (D.rescale c).a i x = 0 ↔ D.a i x = 0 := by
  simp only [Decomp.rescale, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, hc i, false_or]

/-- Step-1 data survive the rescaling `(c_i a_i, c_i⁻¹ b_i)`. -/
def Step1Data.rescale {D : Decomp 12} {H : Submodule F4 GF} (S : Step1Data D H) {c : Fin 12 → F4}
    (hc : ∀ i, c i ≠ 0) : Step1Data (D.rescale c) H where
  W := S.W
  hW := S.hW
  p := S.p
  q := S.q
  hp := S.hp
  hq := S.hq
  hind := S.hind
  hWvan i hi := by
    rw [rescale_a_eq_zero hc, rescale_a_eq_zero hc]; exact S.hWvan i hi
  hker x hx h0 := S.hker x hx fun i hi => (rescale_a_eq_zero hc i x).mp (h0 i hi)
  halive := by
    rw [← S.halive]
    ext i
    simp only [mem_alive2]
    rw [Ne, Ne, Ne, Ne, rescale_a_eq_zero hc, rescale_a_eq_zero hc]

/-- Step-1 data along `x ↦ u x`: the pencil basis becomes `u⁻¹ p, u⁻¹ q`. -/
def Step1Data.scaleX {D : Decomp 12} {H : Submodule F4 GF} (S : Step1Data D H) {u : GF}
    (hu : u ≠ 0) : Step1Data (D.scaleX u) (H.comap (LinearMap.mulLeft F4 u)) where
  W := S.W
  hW := S.hW
  p := u⁻¹ * S.p
  q := u⁻¹ * S.q
  hp := by
    show u * (u⁻¹ * S.p) ∈ H
    rw [mul_inv_cancel_left₀ hu]; exact S.hp
  hq := by
    show u * (u⁻¹ * S.q) ∈ H
    rw [mul_inv_cancel_left₀ hu]; exact S.hq
  hind := by
    have h := S.hind.map' (LinearMap.mulLeft F4 u⁻¹)
      (LinearMap.ker_eq_bot.mpr fun a b hab => by
        simpa [LinearMap.mulLeft_apply, inv_ne_zero hu] using hab)
    convert h using 1
    funext k; fin_cases k <;> rfl
  hWvan i hi := by
    simp only [Decomp.scaleX, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      mul_inv_cancel_left₀ hu]
    exact S.hWvan i hi
  hker x hx h0 := by
    have hux : u * x ∈ H := hx
    have h1 : u * x ∈ Submodule.span F4 {S.p, S.q} := S.hker (u * x) hux fun i hi => h0 i hi
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h1
    refine Submodule.mem_span_pair.mpr ⟨α, β, ?_⟩
    have : x = u⁻¹ * (u * x) := by rw [inv_mul_cancel_left₀ hu]
    rw [this, ← hαβ, mul_add, mul_smul_comm, mul_smul_comm]
  halive := by
    rw [← S.halive]
    ext i
    simp only [mem_alive2, Decomp.scaleX, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply, mul_inv_cancel_left₀ hu]

/-! ### Spans of pairs -/

/-- A form vanishing at `u` and `v` vanishes on `span(u, v)`. -/
lemma form_zero_on_span (f : GF →ₗ[F4] F4) {u v x : GF} (hu : f u = 0) (hv : f v = 0)
    (hx : x ∈ Submodule.span F4 {u, v}) : f x = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp [hu, hv]

lemma range_pair (u v : GF) : Set.range ![u, v] = {u, v} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h) <;> simp [← h]
  · rintro (h | h) <;> simp [h]

lemma finrank_span_pair {u v : GF} (h : LinearIndependent F4 ![u, v]) :
    Module.finrank F4 (Submodule.span F4 ({u, v} : Set GF)) = 2 := by
  have := finrank_span_eq_card h
  rw [range_pair] at this
  simpa using this

/-- Two independent pairs in the same plane span the same plane. -/
lemma span_pair_eq {u v u' v' : GF} (hu' : u' ∈ Submodule.span F4 {u, v})
    (hv' : v' ∈ Submodule.span F4 {u, v}) (h : LinearIndependent F4 ![u, v])
    (h' : LinearIndependent F4 ![u', v']) :
    Submodule.span F4 {u', v'} = Submodule.span F4 {u, v} := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hu'
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hv'
  · rw [finrank_span_pair h', finrank_span_pair h]

lemma mem_span_pair_left (u v : GF) : u ∈ Submodule.span F4 ({u, v} : Set GF) :=
  Submodule.subset_span (Set.mem_insert _ _)

lemma mem_span_pair_right (u v : GF) : v ∈ Submodule.span F4 ({u, v} : Set GF) :=
  Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

/-! ### A change of basis of the pencil -/

/-- Step-1 data with another basis `p', q'` of the same pencil. -/
def Step1Data.rebase {D : Decomp 12} {H : Submodule F4 GF} (S : Step1Data D H) (p' q' : GF)
    (hp' : p' ∈ Submodule.span F4 {S.p, S.q}) (hq' : q' ∈ Submodule.span F4 {S.p, S.q})
    (hind' : LinearIndependent F4 ![p', q']) : Step1Data D H where
  W := S.W
  hW := S.hW
  p := p'
  q := q'
  hp := by
    have hle : Submodule.span F4 {S.p, S.q} ≤ H := by
      rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | hx
      · exact S.hp
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact S.hq
    exact hle hp'
  hq := by
    have hle : Submodule.span F4 {S.p, S.q} ≤ H := by
      rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | hx
      · exact S.hp
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact S.hq
    exact hle hq'
  hind := hind'
  hWvan i hi := ⟨form_zero_on_span _ (S.hWvan i hi).1 (S.hWvan i hi).2 hp',
    form_zero_on_span _ (S.hWvan i hi).1 (S.hWvan i hi).2 hq'⟩
  hker x hx h0 := by
    rw [span_pair_eq hp' hq' S.hind hind']
    exact S.hker x hx h0
  halive := by
    rw [← S.halive]
    have e := span_pair_eq hp' hq' S.hind hind'
    have hp1 : S.p ∈ Submodule.span F4 {p', q'} := by rw [e]; exact mem_span_pair_left _ _
    have hq1 : S.q ∈ Submodule.span F4 {p', q'} := by rw [e]; exact mem_span_pair_right _ _
    ext i
    simp only [mem_alive2]
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      rcases h with h | h
      · exact h (form_zero_on_span _ hc.1 hc.2 hp')
      · exact h (form_zero_on_span _ hc.1 hc.2 hq')
    · intro h
      by_contra hc
      push_neg at hc
      rcases h with h | h
      · exact h (form_zero_on_span _ hc.1 hc.2 hp1)
      · exact h (form_zero_on_span _ hc.1 hc.2 hq1)

/-! ### Dimension along `x ↦ u x` -/

/-- `{x | u x ∈ H}` has the dimension of `H` (by counting elements). -/
lemma finrank_comap_mulLeft (H : Submodule F4 GF) {u : GF} (hu : u ≠ 0) :
    Module.finrank F4 (H.comap (LinearMap.mulLeft F4 u)) = Module.finrank F4 H := by
  classical
  have hcard : Fintype.card (H.comap (LinearMap.mulLeft F4 u)) = Fintype.card H := by
    refine Fintype.card_congr
      { toFun := fun x => ⟨u * x.1, x.2⟩
        invFun := fun y => ⟨u⁻¹ * y.1, show u * (u⁻¹ * y.1) ∈ H by
          rw [mul_inv_cancel_left₀ hu]; exact y.2⟩
        left_inv := fun x => Subtype.ext (inv_mul_cancel_left₀ hu x.1)
        right_inv := fun y => Subtype.ext (mul_inv_cancel_left₀ hu y.1) }
  rw [Module.card_eq_pow_finrank (K := F4), Module.card_eq_pow_finrank (K := F4) (V := H),
    F4.card] at hcard
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) hcard

end Mu4.Lower
