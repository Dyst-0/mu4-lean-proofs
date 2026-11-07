import Mu4.N5.Field5
import Mu4.Lower.Count
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# mu_4(5), lower bound: decompositions, the point bound (N1) and the pencil count (N2)

As `Mu4/Lower/Basic.lean` and `Count.lean`, for GF(4^5): at a nonzero point at least 5 terms are alive
(`point_bound5`, with the basis and separation facts `point_basis5`, `point_dual5`); on a 2-dim subspace at least 7
(`pencil_count5`, `pencil_exact5`). The finite facts on GF(4) (`ss`, `tt`, `vanish_count`, ...) are those of
`Mu4.Lower`.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Lower

/-- A family of `r` terms `(a_i, b_i, g_i)`. -/
structure Decomp5 (r : ℕ) where
  a : Fin r → GF5 →ₗ[F4] F4
  b : Fin r → GF5 →ₗ[F4] F4
  g : Fin r → GF5

/-- The family decomposes multiplication for `x ∈ U` and all `y`. -/
def Decomp5.ValidOn {r : ℕ} (D : Decomp5 r) (U : Submodule F4 GF5) : Prop :=
  ∀ x ∈ U, ∀ y : GF5, x * y = ∑ i, (D.a i x * D.b i y) • D.g i

variable {r : ℕ}

/-! ### L1: the point bound -/

/-- The terms alive at `x`. -/
noncomputable def aliveAt5 (D : Decomp5 r) (x : GF5) : Finset (Fin r) :=
  by classical exact Finset.univ.filter fun i => D.a i x ≠ 0

lemma mem_aliveAt5 {D : Decomp5 r} {x : GF5} {i : Fin r} : i ∈ aliveAt5 D x ↔ D.a i x ≠ 0 := by
  classical simp [aliveAt5]

/-- On a valid decomposition, `x * y` is a combination of the `g_i` alive at `x`. -/
lemma mul_eq_sum_alive5 {D : Decomp5 r} {U : Submodule F4 GF5} (hD : D.ValidOn U) {x : GF5}
    (hxU : x ∈ U) (y : GF5) : x * y = ∑ i ∈ aliveAt5 D x, (D.a i x * D.b i y) • D.g i := by
  classical
  rw [hD x hxU y]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  rw [mem_aliveAt5, not_not] at hi
  simp [hi]

/-- L1: at least 6 terms are alive at a nonzero `x ∈ U`. -/
theorem point_bound5 {D : Decomp5 r} {U : Submodule F4 GF5} (hD : D.ValidOn U) {x : GF5}
    (hxU : x ∈ U) (hx : x ≠ 0) : 5 ≤ (aliveAt5 D x).card := by
  classical
  set S := aliveAt5 D x
  have hspan : ∀ z : GF5, z ∈ Submodule.span F4 ((S.image D.g : Finset GF5) : Set GF5) := by
    intro z
    have hz : z = x * (x⁻¹ * z) := by rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    rw [hz, mul_eq_sum_alive5 hD hxU]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    simp only [Finset.coe_image]
    exact Set.mem_image_of_mem _ hi
  have htop : (⊤ : Submodule F4 GF5) = Submodule.span F4 ((S.image D.g : Finset GF5) : Set GF5) :=
    (eq_top_iff.mpr fun z _ => hspan z).symm
  have h1 := finrank_span_finset_le_card (R := F4) (S.image D.g)
  rw [Set.finrank, ← htop, finrank_top, GF5.finrank_eq] at h1
  exact h1.trans Finset.card_image_le

/-- L1, equality case: if exactly 6 terms are alive at `x`, their forms `b_i` separate points:
for every `i0` alive at `x` there is `y0` with `b_i y0 = δ_{i,i0}` on the alive terms. -/
theorem point_dual5 {D : Decomp5 r} {U : Submodule F4 GF5} (hD : D.ValidOn U) {x : GF5}
    (hxU : x ∈ U) (hx : x ≠ 0) (h6 : (aliveAt5 D x).card = 5) (i0 : Fin r)
    (hi0 : i0 ∈ aliveAt5 D x) :
    ∃ y0 : GF5, ∀ i ∈ aliveAt5 D x, D.b i y0 = if i = i0 then 1 else 0 := by
  classical
  set S := aliveAt5 D x
  -- the map y ↦ (b_i y)_{i ∈ S}
  let φ : GF5 →ₗ[F4] (S → F4) := LinearMap.pi fun i => D.b i.val
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have hy' : ∀ i ∈ S, D.b i y = 0 := fun i hi => congrFun (LinearMap.mem_ker.mp hy) ⟨i, hi⟩
    have : x * y = 0 := by
      rw [mul_eq_sum_alive5 hD hxU]
      exact Finset.sum_eq_zero fun i hi => by simp [hy' i hi]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hx
    · exact h
  have hsurj : Function.Surjective φ := by
    have hdim : Module.finrank F4 GF5 = Module.finrank F4 (S → F4) := by
      rw [GF5.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, h6]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨y0, hy0⟩ := hsurj fun i => if i.val = i0 then 1 else 0
  refine ⟨y0, fun i hi => ?_⟩
  have := congrFun hy0 ⟨i, hi⟩
  simpa [φ] using this

/-- L1, equality case: the `g_i` alive at `x` are linearly independent. -/
theorem point_basis5 {D : Decomp5 r} {U : Submodule F4 GF5} (hD : D.ValidOn U) {x : GF5}
    (hxU : x ∈ U) (hx : x ≠ 0) (h6 : (aliveAt5 D x).card = 5) :
    LinearIndependent F4 (fun i : aliveAt5 D x => D.g i.val) := by
  classical
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · intro z _
    have hz : z = x * (x⁻¹ * z) := by rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    rw [hz, mul_eq_sum_alive5 hD hxU]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨i, hi⟩, rfl⟩
  · rw [Fintype.card_coe, h6, GF5.finrank_eq]


variable {r : ℕ}

/-- The standard points of `span(p, q)` (`ss`, `tt` of `Mu4.Lower`). -/
def pt5 (p q : GF5) (m : Fin 5) : GF5 := ss m • p + tt m • q

lemma a_pt5 (D : Decomp5 r) (i : Fin r) (p q : GF5) (m : Fin 5) :
    D.a i (pt5 p q m) = ss m * D.a i p + tt m * D.a i q := by
  simp [pt5, map_add, map_smul, smul_eq_mul]

lemma pt_ne_zero5 {p q : GF5} (h : LinearIndependent F4 ![p, q]) (m : Fin 5) : pt5 p q m ≠ 0 := by
  intro h0
  have := (LinearIndependent.pair_iff.mp h) (ss m) (tt m) h0
  rcases sst_ne m with h1 | h1
  · exact h1 this.1
  · exact h1 this.2

/-- The terms alive on `span(p, q)`. -/
noncomputable def alive2_5 (D : Decomp5 r) (p q : GF5) : Finset (Fin r) :=
  by classical exact Finset.univ.filter fun i => D.a i p ≠ 0 ∨ D.a i q ≠ 0

lemma mem_alive2_5 {D : Decomp5 r} {p q : GF5} {i : Fin r} :
    i ∈ alive2_5 D p q ↔ (D.a i p ≠ 0 ∨ D.a i q ≠ 0) := by
  classical simp [alive2_5]

lemma aliveAt_pt_subset5 (D : Decomp5 r) (p q : GF5) (m : Fin 5) :
    aliveAt5 D (pt5 p q m) ⊆ alive2_5 D p q := by
  intro i hi
  rw [mem_aliveAt5, a_pt5] at hi
  rw [mem_alive2_5]
  by_contra h
  push_neg at h
  exact hi (by rw [h.1, h.2]; ring)

/-- Double counting: `∑_m |alive at x_m| = 4 |alive on P|`. -/
lemma sum_aliveAt_pt5 (D : Decomp5 r) (p q : GF5) :
    ∑ m : Fin 5, (aliveAt5 D (pt5 p q m)).card = 4 * (alive2_5 D p q).card := by
  classical
  have key : ∀ m : Fin 5, (aliveAt5 D (pt5 p q m)).card =
      ∑ i : Fin r, if D.a i (pt5 p q m) ≠ 0 then 1 else 0 := by
    intro m
    rw [aliveAt5, Finset.card_filter]
  simp only [key]
  rw [Finset.sum_comm]
  have inner : ∀ i : Fin r, (∑ m : Fin 5, if D.a i (pt5 p q m) ≠ 0 then 1 else 0) =
      if i ∈ alive2_5 D p q then 4 else 0 := by
    intro i
    rw [← Finset.card_filter]
    simp only [a_pt5]
    by_cases hi : i ∈ alive2_5 D p q
    · rw [if_pos hi]
      exact vanish_count _ _ (mem_alive2_5.mp hi)
    · rw [if_neg hi]
      rw [mem_alive2_5] at hi
      push_neg at hi
      simp [hi.1, hi.2]
  simp only [inner]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_comm]

/-- L2: at least 8 terms are alive on a 2-dim subspace of `U`. -/
theorem pencil_count5 {D : Decomp5 r} {U : Submodule F4 GF5} (hD : D.ValidOn U) {p q : GF5}
    (hp : p ∈ U) (hq : q ∈ U) (hind : LinearIndependent F4 ![p, q]) :
    7 ≤ (alive2_5 D p q).card := by
  have hsum := sum_aliveAt_pt5 D p q
  have hm : ∀ m : Fin 5, 5 ≤ (aliveAt5 D (pt5 p q m)).card := fun m =>
    point_bound5 hD (U.add_mem (U.smul_mem _ hp) (U.smul_mem _ hq)) (pt_ne_zero5 hind m)
  have : 25 ≤ ∑ m : Fin 5, (aliveAt5 D (pt5 p q m)).card := by
    calc 25 = ∑ _m : Fin 5, 5 := by simp
      _ ≤ _ := Finset.sum_le_sum fun m _ => hm m
  omega

/-- L2, exact form: with at most 8 terms alive on the pencil, exactly 8 are, and at most 2 alive
terms vanish at each standard point. -/
theorem pencil_exact5 {D : Decomp5 r} {U : Submodule F4 GF5} (hD : D.ValidOn U) {p q : GF5}
    (hp : p ∈ U) (hq : q ∈ U) (hind : LinearIndependent F4 ![p, q])
    (h8 : (alive2_5 D p q).card ≤ 7) :
    (alive2_5 D p q).card = 7 ∧ ∀ m : Fin 5, 5 ≤ (aliveAt5 D (pt5 p q m)).card ∧
      ((alive2_5 D p q).filter fun i => D.a i (pt5 p q m) = 0).card ≤ 2 := by
  classical
  have h8' := pencil_count5 hD hp hq hind
  have hA : (alive2_5 D p q).card = 7 := le_antisymm h8 h8'
  have hsum := sum_aliveAt_pt5 D p q
  rw [hA] at hsum
  have hm : ∀ m : Fin 5, 5 ≤ (aliveAt5 D (pt5 p q m)).card := fun m =>
    point_bound5 hD (U.add_mem (U.smul_mem _ hp) (U.smul_mem _ hq)) (pt_ne_zero5 hind m)
  refine ⟨hA, fun m => ⟨hm m, ?_⟩⟩
  have hfilter : (alive2_5 D p q).filter (fun i => D.a i (pt5 p q m) = 0) =
      alive2_5 D p q \ aliveAt5 D (pt5 p q m) := by
    ext i; simp [mem_aliveAt5]
  rw [hfilter, Finset.card_sdiff_of_subset (aliveAt_pt_subset5 D p q m), hA]
  have := hm m
  omega

/-- Two independent vectors in a subspace of dimension at least 2. -/
lemma exists_pair_of_two_le5 {V : Submodule F4 GF5} (hV : 2 ≤ Module.finrank F4 V) :
    ∃ p q : GF5, p ∈ V ∧ q ∈ V ∧ LinearIndependent F4 ![p, q] := by
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank F4 V)
  obtain ⟨y, hy⟩ :=
    exists_linearIndependent_pair_of_one_lt_finrank (by omega : 1 < Module.finrank F4 V) hx
  refine ⟨x, y, x.2, y.2, ?_⟩
  have := hy.map' V.subtype (Submodule.ker_subtype V)
  convert this using 1
  ext i; fin_cases i <;> rfl

end Mu4.N5
