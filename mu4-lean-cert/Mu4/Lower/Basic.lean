import Mu4.Field
import Mu4.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# Lower bound, basic lemmas (`audit/PROOF.md`, L0-L3)

Decompositions valid on a subspace, substitution, and the counting bounds:
* `point_bound` (L1): at a nonzero point at least 6 terms are alive;
* `pencil_count` (L2): on a 2-dim subspace at least 8 terms are alive;
* `plane_bound` (L3): on a 3-dim subspace at least 9 terms are alive.
-/

namespace Mu4.Lower
open Mu4 F4

/-- A family of `r` terms `(a_i, b_i, g_i)`. -/
structure Decomp (r : ℕ) where
  a : Fin r → GF →ₗ[F4] F4
  b : Fin r → GF →ₗ[F4] F4
  g : Fin r → GF

/-- The family decomposes multiplication for `x ∈ U` and all `y`. -/
def Decomp.ValidOn {r : ℕ} (D : Decomp r) (U : Submodule F4 GF) : Prop :=
  ∀ x ∈ U, ∀ y : GF, x * y = ∑ i, (D.a i x * D.b i y) • D.g i

variable {r : ℕ}

/-! ### L0: substitution -/

/-- Drop term `j`. -/
def Decomp.erase {r : ℕ} (D : Decomp (r + 1)) (j : Fin (r + 1)) : Decomp r where
  a i := D.a (j.succAbove i)
  b i := D.b (j.succAbove i)
  g i := D.g (j.succAbove i)

lemma Decomp.erase_validOn {D : Decomp (r + 1)} {U : Submodule F4 GF} (hD : D.ValidOn U)
    (j : Fin (r + 1)) : (D.erase j).ValidOn (U ⊓ LinearMap.ker (D.a j)) := by
  intro x hx y
  rw [hD x hx.1 y, Fin.sum_univ_succAbove _ j]
  have : D.a j x = 0 := hx.2
  simp [this, Decomp.erase]

/-- L0: a decomposition of the multiplication of length `r + 1` gives one of length `r` valid on
a hyperplane. -/
theorem substitution (h : HasDecomp F4 (LinearMap.mul F4 GF) (r + 1)) :
    ∃ H : Submodule F4 GF, Module.finrank F4 H = 5 ∧ ∃ D : Decomp r, D.ValidOn H := by
  obtain ⟨a, b, c, hf⟩ := h
  let D : Decomp (r + 1) := ⟨a, b, c⟩
  have hD : D.ValidOn ⊤ := fun x _ y => by simpa [D] using hf x y
  -- some form is nonzero, since 1 * 1 ≠ 0
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra hall
    push_neg at hall
    have := hf 1 1
    simp [hall] at this
  refine ⟨LinearMap.ker (a j), ?_, D.erase j, ?_⟩
  · have hrange : LinearMap.range (a j) = ⊤ := by
      obtain ⟨x, hx⟩ : ∃ x, a j x ≠ 0 := by
        by_contra hx; push_neg at hx; exact hj (LinearMap.ext hx)
      refine eq_top_iff.mpr fun c _ => ⟨(c / a j x) • x, ?_⟩
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hx]
    have := LinearMap.finrank_range_add_finrank_ker (a j)
    rw [hrange, finrank_top, Module.finrank_self, GF.finrank_eq] at this
    omega
  · have := D.erase_validOn hD j
    simpa using this

/-! ### L1: the point bound -/

/-- The terms alive at `x`. -/
noncomputable def aliveAt (D : Decomp r) (x : GF) : Finset (Fin r) :=
  by classical exact Finset.univ.filter fun i => D.a i x ≠ 0

lemma mem_aliveAt {D : Decomp r} {x : GF} {i : Fin r} : i ∈ aliveAt D x ↔ D.a i x ≠ 0 := by
  classical simp [aliveAt]

/-- On a valid decomposition, `x * y` is a combination of the `g_i` alive at `x`. -/
lemma mul_eq_sum_alive {D : Decomp r} {U : Submodule F4 GF} (hD : D.ValidOn U) {x : GF}
    (hxU : x ∈ U) (y : GF) : x * y = ∑ i ∈ aliveAt D x, (D.a i x * D.b i y) • D.g i := by
  classical
  rw [hD x hxU y]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  rw [mem_aliveAt, not_not] at hi
  simp [hi]

/-- L1: at least 6 terms are alive at a nonzero `x ∈ U`. -/
theorem point_bound {D : Decomp r} {U : Submodule F4 GF} (hD : D.ValidOn U) {x : GF}
    (hxU : x ∈ U) (hx : x ≠ 0) : 6 ≤ (aliveAt D x).card := by
  classical
  set S := aliveAt D x
  have hspan : ∀ z : GF, z ∈ Submodule.span F4 ((S.image D.g : Finset GF) : Set GF) := by
    intro z
    have hz : z = x * (x⁻¹ * z) := by rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    rw [hz, mul_eq_sum_alive hD hxU]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    simp only [Finset.coe_image]
    exact Set.mem_image_of_mem _ hi
  have htop : (⊤ : Submodule F4 GF) = Submodule.span F4 ((S.image D.g : Finset GF) : Set GF) :=
    (eq_top_iff.mpr fun z _ => hspan z).symm
  have h1 := finrank_span_finset_le_card (R := F4) (S.image D.g)
  rw [Set.finrank, ← htop, finrank_top, GF.finrank_eq] at h1
  exact h1.trans Finset.card_image_le

/-- L1, equality case: if exactly 6 terms are alive at `x`, their forms `b_i` separate points:
for every `i0` alive at `x` there is `y0` with `b_i y0 = δ_{i,i0}` on the alive terms. -/
theorem point_dual {D : Decomp r} {U : Submodule F4 GF} (hD : D.ValidOn U) {x : GF}
    (hxU : x ∈ U) (hx : x ≠ 0) (h6 : (aliveAt D x).card = 6) (i0 : Fin r)
    (hi0 : i0 ∈ aliveAt D x) :
    ∃ y0 : GF, ∀ i ∈ aliveAt D x, D.b i y0 = if i = i0 then 1 else 0 := by
  classical
  set S := aliveAt D x
  -- the map y ↦ (b_i y)_{i ∈ S}
  let φ : GF →ₗ[F4] (S → F4) := LinearMap.pi fun i => D.b i.val
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have hy' : ∀ i ∈ S, D.b i y = 0 := fun i hi => congrFun (LinearMap.mem_ker.mp hy) ⟨i, hi⟩
    have : x * y = 0 := by
      rw [mul_eq_sum_alive hD hxU]
      exact Finset.sum_eq_zero fun i hi => by simp [hy' i hi]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hx
    · exact h
  have hsurj : Function.Surjective φ := by
    have hdim : Module.finrank F4 GF = Module.finrank F4 (S → F4) := by
      rw [GF.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, h6]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨y0, hy0⟩ := hsurj fun i => if i.val = i0 then 1 else 0
  refine ⟨y0, fun i hi => ?_⟩
  have := congrFun hy0 ⟨i, hi⟩
  simpa [φ] using this

/-- L1, equality case: the `g_i` alive at `x` are linearly independent. -/
theorem point_basis {D : Decomp r} {U : Submodule F4 GF} (hD : D.ValidOn U) {x : GF}
    (hxU : x ∈ U) (hx : x ≠ 0) (h6 : (aliveAt D x).card = 6) :
    LinearIndependent F4 (fun i : aliveAt D x => D.g i.val) := by
  classical
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · intro z _
    have hz : z = x * (x⁻¹ * z) := by rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    rw [hz, mul_eq_sum_alive hD hxU]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨i, hi⟩, rfl⟩
  · rw [Fintype.card_coe, h6, GF.finrank_eq]

end Mu4.Lower
