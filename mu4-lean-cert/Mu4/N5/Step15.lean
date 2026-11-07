import Mu4.N5.Lower5

/-!
# mu_4(5), N3: three forms vanishing on a pencil

From a 10-term decomposition valid on `A5`: three indices `W` with independent forms; their common kernel
`P = span(p, q)` has dimension 2, and all 7 other terms are alive on `P` (`step1_5`). The structure `Step1Data5` keeps
a subspace `H` (here always `⊤`), so that the n = 6 proofs of the pencil lemmas carry over.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Lower

/-- The output of N3. -/
structure Step1Data5 (D : Decomp5 10) (H : Submodule F4 GF5) where
  W : Finset (Fin 10)
  hW : W.card = 3
  p : GF5
  q : GF5
  hp : p ∈ H
  hq : q ∈ H
  hind : LinearIndependent F4 ![p, q]
  hWvan : ∀ i ∈ W, D.a i p = 0 ∧ D.a i q = 0
  hker : ∀ x ∈ H, (∀ i ∈ W, D.a i x = 0) → x ∈ Submodule.span F4 {p, q}
  halive : alive2_5 D p q = Wᶜ

/-- The forms of a valid decomposition on `H` have no common zero in `H` except 0. -/
lemma no_common_zero5 {r : ℕ} {D : Decomp5 r} {H : Submodule F4 GF5} (hD : D.ValidOn H) {x : GF5}
    (hx : x ∈ H) (h0 : ∀ i, D.a i x = 0) : x = 0 := by
  by_contra hne
  have := point_bound5 hD hx hne
  have hempty : aliveAt5 D x = ∅ := by
    ext i; simp [mem_aliveAt5, h0 i]
  rw [hempty] at this
  simp at this

/-- A nonzero form on `Fin n → F4` has a kernel of dimension `n - 1`. -/
lemma finrank_ker_pi5 {n : ℕ} {f : (Fin n → F4) →ₗ[F4] F4} {u : Fin n → F4} (hu : f u ≠ 0) :
    Module.finrank F4 (LinearMap.ker f) + 1 = n := by
  have hrange : LinearMap.range f = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ⟨(c / f u) • u, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hu]
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
  omega

theorem step1_5 {D : Decomp5 10} (hD : D.ValidOn ⊤) : Nonempty (Step1Data5 D ⊤) := by
  classical
  let β := Module.finBasisOfFinrankEq F4 GF5 GF5.finrank_eq
  let v : Fin 10 → (Fin 5 → F4) := fun i k => D.a i (β k)
  -- the coordinate vectors span
  have hspan : Submodule.span F4 (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : Fin 5 → F4 := fun k => f (fun j => if k = j then 1 else 0)
    have hf : ∀ u : Fin 5 → F4, f u = ∑ k, c k * u k := by
      intro u
      conv_lhs => rw [pi_eq_sum_univ u]
      simp [map_sum, map_smul, c, mul_comm]
    have hc : c ≠ 0 := by
      intro hc0
      apply hf0
      apply LinearMap.ext
      intro u
      rw [hf u]
      simp [hc0]
    let x : GF5 := ∑ k, c k • β k
    have hx0 : x ≠ 0 := by
      intro h0
      have := Fintype.linearIndependent_iff.mp β.linearIndependent c h0
      exact hc (funext this)
    apply hx0
    apply no_common_zero5 hD (Submodule.mem_top)
    intro i
    have hvi : v i ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨i, rfl⟩)
    have : f (v i) = 0 := LinearMap.mem_ker.mp hvi
    rw [hf] at this
    simp only [x, map_sum, map_smul, smul_eq_mul]
    simpa [v] using this
  -- five independent ones among them
  obtain ⟨ι5, hι5, hli5⟩ : ∃ ι5 : Fin 5 → Fin 10, Function.Injective ι5 ∧
      LinearIndependent F4 (v ∘ ι5) := by
    obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' F4 v
    haveI : Finite κ := Finite.of_injective a ha
    haveI : Fintype κ := Fintype.ofFinite κ
    have hsp' : ⊤ ≤ Submodule.span F4 (Set.range (v ∘ a)) := by rw [hsp, hspan]
    let b := Module.Basis.mk hli hsp'
    have hcard : Fintype.card κ = 5 := by
      have := Module.finrank_eq_card_basis b
      rw [Module.finrank_fin_fun] at this
      exact this.symm
    let e : κ ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
    refine ⟨a ∘ e.symm, ha.comp e.symm.injective, ?_⟩
    have := hli.comp e.symm e.symm.injective
    exact this
  -- the three W-forms
  let idx : Fin 3 → Fin 10 := fun k => ι5 (Fin.castLE (by norm_num) k)
  have hidx : Function.Injective idx := by
    intro a b hab
    have := hι5 hab
    exact Fin.castLE_injective _ this
  have hli3 : LinearIndependent F4 (v ∘ idx) := by
    have := hli5.comp (Fin.castLE (by norm_num : 3 ≤ 5)) (Fin.castLE_injective _)
    exact this
  let W : Finset (Fin 10) := Finset.univ.image idx
  have hWcard : W.card = 3 := by rw [Finset.card_image_of_injective _ hidx]; simp
  -- the joint map is onto
  let Ψ : GF5 →ₗ[F4] (Fin 3 → F4) := LinearMap.pi fun k => D.a (idx k)
  have hrange : LinearMap.range Ψ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : Fin 3 → F4 := fun k => f (fun j => if k = j then 1 else 0)
    have hf : ∀ u : Fin 3 → F4, f u = ∑ k, c k * u k := by
      intro u
      conv_lhs => rw [pi_eq_sum_univ u]
      simp [map_sum, map_smul, c, mul_comm]
    have hc : c ≠ 0 := by
      intro hc0
      apply hf0
      apply LinearMap.ext
      intro u
      rw [hf u]
      simp [hc0]
    apply hc
    have h0 : ∑ k, c k • (v ∘ idx) k = 0 := by
      funext l
      have := hle (LinearMap.mem_range_self Ψ (β l))
      rw [LinearMap.mem_ker, hf] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply]
      simpa [Ψ, v] using this
    funext k
    exact Fintype.linearIndependent_iff.mp hli3 c h0 k
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [hrange, finrank_top, Module.finrank_fin_fun, GF5.finrank_eq] at hrn
  have hdim2 : Module.finrank F4 (LinearMap.ker Ψ) = 2 := by omega
  have memP : ∀ x : GF5, x ∈ LinearMap.ker Ψ ↔ ∀ k, D.a (idx k) x = 0 := by
    intro x
    rw [LinearMap.mem_ker]
    constructor
    · intro h k; have := congrFun h k; simpa [Ψ] using this
    · intro h; funext k; simpa [Ψ] using h k
  have hWvanP : ∀ x ∈ LinearMap.ker Ψ, ∀ a ∈ W, D.a a x = 0 := by
    intro x hx a ha
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
    exact (memP x).mp hx k
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_pair_of_two_le5 (le_of_eq hdim2.symm)
  have hspanpq : Submodule.span F4 {p, q} = LinearMap.ker Ψ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | hx
      · exact hp
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hq
    · rw [hdim2]
      have hr2 : Set.range ![p, q] = {p, q} := by
        ext x
        simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro (h | h) <;> simp [← h]
        · rintro (h | h) <;> simp [h]
      have := finrank_span_eq_card hpq
      rw [hr2] at this
      simpa using this
  refine ⟨⟨W, hWcard, p, q, Submodule.mem_top, Submodule.mem_top, hpq,
    fun a ha => ⟨hWvanP p hp a ha, hWvanP q hq a ha⟩, fun x _ h => ?_, ?_⟩⟩
  · rw [hspanpq, memP]
    exact fun k => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  · apply Finset.eq_of_subset_of_card_le
    · intro a ha
      rw [Finset.mem_compl]
      intro haW
      rw [mem_alive2_5] at ha
      rcases ha with h | h
      · exact h (hWvanP p hp a haW)
      · exact h (hWvanP q hq a haW)
    · have := pencil_count5 hD Submodule.mem_top Submodule.mem_top hpq
      rw [Finset.card_compl, hWcard]
      simpa using this

end Mu4.N5
