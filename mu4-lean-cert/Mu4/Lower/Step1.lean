import Mu4.Lower.Count

/-!
# Step 1 (`audit/PROOF.md`, L4): four forms vanishing on a pencil

From a 12-term decomposition valid on a hyperplane `H`: four indices `W` whose forms have a common
kernel in `H` of dimension exactly 2, `P = span(p, q)`, with all 8 other terms alive on `P`.
The geometric fact G1 is the hypothesis `Geometry` (proved in `Mu4/Lower/Geometry.lean`).
-/

namespace Mu4.Lower
open Mu4 F4

/-- G1: among 12 vectors spanning GF(4)^5, some 4 with distinct indices are dependent. -/
def Geometry : Prop :=
  ∀ v : Fin 12 → (Fin 5 → F4), Submodule.span F4 (Set.range v) = ⊤ →
    ∃ i j k l : Fin 12, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      ¬ LinearIndependent F4 ![v i, v j, v k, v l]

/-- The output of step 1. -/
structure Step1Data (D : Decomp 12) (H : Submodule F4 GF) where
  W : Finset (Fin 12)
  hW : W.card = 4
  p : GF
  q : GF
  hp : p ∈ H
  hq : q ∈ H
  hind : LinearIndependent F4 ![p, q]
  hWvan : ∀ i ∈ W, D.a i p = 0 ∧ D.a i q = 0
  hker : ∀ x ∈ H, (∀ i ∈ W, D.a i x = 0) → x ∈ Submodule.span F4 {p, q}
  halive : alive2 D p q = Wᶜ

/-- A nonzero form on `Fin n → F4` has a kernel of dimension `n - 1`. -/
lemma finrank_ker_pi {n : ℕ} {f : (Fin n → F4) →ₗ[F4] F4} {u : Fin n → F4} (hu : f u ≠ 0) :
    Module.finrank F4 (LinearMap.ker f) + 1 = n := by
  have hrange : LinearMap.range f = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ⟨(c / f u) • u, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hu]
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
  omega

/-- The forms of a valid decomposition on `H` have no common zero in `H` except 0. -/
lemma no_common_zero {r : ℕ} {D : Decomp r} {H : Submodule F4 GF} (hD : D.ValidOn H) {x : GF}
    (hx : x ∈ H) (h0 : ∀ i, D.a i x = 0) : x = 0 := by
  by_contra hne
  have := point_bound hD hx hne
  have hempty : aliveAt D x = ∅ := by
    ext i; simp [mem_aliveAt, h0 i]
  rw [hempty] at this
  simp at this

theorem step1 (hG : Geometry) {H : Submodule F4 GF} (hH : Module.finrank F4 H = 5)
    {D : Decomp 12} (hD : D.ValidOn H) : Nonempty (Step1Data D H) := by
  classical
  let β := Module.finBasisOfFinrankEq F4 H hH
  let v : Fin 12 → (Fin 5 → F4) := fun i k => D.a i (β k : GF)
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
    let x : GF := ∑ k, c k • (β k : GF)
    have hxH : x ∈ H := H.sum_mem fun k _ => H.smul_mem _ (β k).2
    have hx0 : x ≠ 0 := by
      intro h0
      have hlin := β.linearIndependent
      have : ∑ k, c k • β k = 0 := by
        apply Subtype.ext
        simpa [x] using h0
      have := Fintype.linearIndependent_iff.mp hlin c this
      exact hc (funext this)
    apply hx0
    apply no_common_zero hD hxH
    intro i
    have hvi : v i ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨i, rfl⟩)
    have : f (v i) = 0 := LinearMap.mem_ker.mp hvi
    rw [hf] at this
    simp only [x, map_sum, map_smul, smul_eq_mul]
    simpa [v] using this
  obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, hdep⟩ := hG v hspan
  obtain ⟨g, hg, m0, hm0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let idx : Fin 4 → Fin 12 := ![i, j, k, l]
  have hidx : Function.Injective idx := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [idx]
  let W : Finset (Fin 12) := Finset.univ.image idx
  have hWcard : W.card = 4 := by rw [Finset.card_image_of_injective _ hidx]; simp
  -- the combination ∑ g_m a_{idx m} vanishes on H
  have hcomb : ∀ x ∈ H, ∑ m, g m * D.a (idx m) x = 0 := by
    intro x hx
    let φ : H →ₗ[F4] F4 := ∑ m, g m • (D.a (idx m)).comp H.subtype
    have hφ : φ = 0 := by
      apply β.ext
      intro kk
      have := congrFun hg kk
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [φ, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, Submodule.subtype_apply, smul_eq_mul, LinearMap.zero_apply]
      convert this using 2 with m
      fin_cases m <;> rfl
    have := congrArg (fun f => f ⟨x, hx⟩) hφ
    simpa [φ] using this
  -- Φ : H → F^4 and ψ : F^4 → F
  let Φ : H →ₗ[F4] (Fin 4 → F4) := LinearMap.pi fun m => (D.a (idx m)).comp H.subtype
  let ψ : (Fin 4 → F4) →ₗ[F4] F4 := ∑ m, g m • LinearMap.proj m
  have hψ : ψ (Pi.single m0 1) ≠ 0 := by
    simp [ψ, LinearMap.proj_apply, Pi.single_apply, hm0]
  have hrange : LinearMap.range Φ ≤ LinearMap.ker ψ := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have := hcomb x x.2
    simpa [ψ, Φ, LinearMap.proj_apply] using this
  have hkerψ := finrank_ker_pi hψ
  have hr : Module.finrank F4 (LinearMap.range Φ) ≤ 3 := by
    have := Submodule.finrank_mono hrange
    omega
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hH] at hrn
  -- P' = ker Φ, as a subspace of GF
  let P' : Submodule F4 GF := (LinearMap.ker Φ).map H.subtype
  have hP'dim : Module.finrank F4 P' = Module.finrank F4 (LinearMap.ker Φ) :=
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype H) _).finrank_eq.symm
  have memP' : ∀ x : GF, x ∈ P' ↔ x ∈ H ∧ ∀ m, D.a (idx m) x = 0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun m => ?_⟩
      have := congrFun (LinearMap.mem_ker.mp hy) m
      simpa [Φ] using this
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      show Φ ⟨x, hx⟩ = 0
      ext m
      simpa [Φ] using h m
  have hP'H : P' ≤ H := fun x hx => ((memP' x).mp hx).1
  have hWvanP' : ∀ x ∈ P', ∀ a ∈ W, D.a a x = 0 := by
    intro x hx a ha
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp ha
    exact ((memP' x).mp hx).2 m
  -- dim P' = 2
  have hdim2 : Module.finrank F4 P' = 2 := by
    by_contra hne
    have h3 : 3 ≤ Module.finrank F4 P' := by omega
    have h9 := plane_bound hD hP'H h3
    have hsub : aliveOn D P' ⊆ Wᶜ := by
      intro a ha
      rw [Finset.mem_compl]
      intro haW
      obtain ⟨x, hx, hax⟩ := mem_aliveOn.mp ha
      exact hax (hWvanP' x hx a haW)
    have := Finset.card_le_card hsub
    rw [Finset.card_compl, hWcard] at this
    simp at this
    omega
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_pair_of_two_le (le_of_eq hdim2.symm)
  have hspanpq : Submodule.span F4 {p, q} = P' := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hp
      · exact hq
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
  refine ⟨⟨W, hWcard, p, q, hP'H hp, hP'H hq, hpq, fun a ha => ⟨hWvanP' p hp a ha,
    hWvanP' q hq a ha⟩, fun x hx h => ?_, ?_⟩⟩
  · rw [hspanpq, memP']
    exact ⟨hx, fun m => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ m))⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro a ha
      rw [Finset.mem_compl]
      intro haW
      rw [mem_alive2] at ha
      rcases ha with h | h
      · exact h (hWvanP' p hp a haW)
      · exact h (hWvanP' q hq a haW)
    · have := pencil_count hD (hP'H hp) (hP'H hq) hpq
      rw [Finset.card_compl, hWcard]
      simpa using this

end Mu4.Lower
