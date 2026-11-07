import Mu4.Lower.Basic

/-!
# Lower bound: the pencil count (L2) and the plane bound (L3)
-/

namespace Mu4.Lower
open Mu4 F4

variable {r : ℕ}

/-- Coefficients of the five standard points `x_m = ss_m p + tt_m q` of a pencil. -/
def ss : Fin 5 → F4 := ![1, 0, 1, w, w2]
def tt : Fin 5 → F4 := ![0, 1, 1, 1, 1]

/-- The standard points of `span(p, q)`. -/
def pt (p q : GF) (m : Fin 5) : GF := ss m • p + tt m • q

/-- A nonzero linear form on a 2-dim space vanishes at exactly one of the five points. -/
lemma vanish_count : ∀ α β : F4, (α ≠ 0 ∨ β ≠ 0) →
    (Finset.univ.filter fun m : Fin 5 => ss m * α + tt m * β ≠ 0).card = 4 := by decide

lemma vanish_exists : ∀ α β : F4, (α ≠ 0 ∨ β ≠ 0) → ∃ m : Fin 5, ss m * α + tt m * β = 0 := by
  decide

lemma vanish_unique : ∀ α β : F4, (α ≠ 0 ∨ β ≠ 0) → ∀ m m' : Fin 5,
    ss m * α + tt m * β = 0 → ss m' * α + tt m' * β = 0 → m = m' := by
  decide

/-- Every nonzero vector of `span(p, q)` is a nonzero multiple of a standard point. -/
lemma point_cover : ∀ s t : F4, (s ≠ 0 ∨ t ≠ 0) →
    ∃ m : Fin 5, ∃ c : F4, c ≠ 0 ∧ s = c * ss m ∧ t = c * tt m := by decide

lemma a_pt (D : Decomp r) (i : Fin r) (p q : GF) (m : Fin 5) :
    D.a i (pt p q m) = ss m * D.a i p + tt m * D.a i q := by
  simp [pt, map_add, map_smul, smul_eq_mul]

lemma sst_ne : ∀ m : Fin 5, ss m ≠ 0 ∨ tt m ≠ 0 := by decide

lemma pt_ne_zero {p q : GF} (h : LinearIndependent F4 ![p, q]) (m : Fin 5) : pt p q m ≠ 0 := by
  intro h0
  have := (LinearIndependent.pair_iff.mp h) (ss m) (tt m) h0
  rcases sst_ne m with h1 | h1
  · exact h1 this.1
  · exact h1 this.2

/-- The terms alive on `span(p, q)`. -/
noncomputable def alive2 (D : Decomp r) (p q : GF) : Finset (Fin r) :=
  by classical exact Finset.univ.filter fun i => D.a i p ≠ 0 ∨ D.a i q ≠ 0

lemma mem_alive2 {D : Decomp r} {p q : GF} {i : Fin r} :
    i ∈ alive2 D p q ↔ (D.a i p ≠ 0 ∨ D.a i q ≠ 0) := by
  classical simp [alive2]

lemma aliveAt_pt_subset (D : Decomp r) (p q : GF) (m : Fin 5) :
    aliveAt D (pt p q m) ⊆ alive2 D p q := by
  intro i hi
  rw [mem_aliveAt, a_pt] at hi
  rw [mem_alive2]
  by_contra h
  push_neg at h
  exact hi (by rw [h.1, h.2]; ring)

/-- Double counting: `∑_m |alive at x_m| = 4 |alive on P|`. -/
lemma sum_aliveAt_pt (D : Decomp r) (p q : GF) :
    ∑ m : Fin 5, (aliveAt D (pt p q m)).card = 4 * (alive2 D p q).card := by
  classical
  have key : ∀ m : Fin 5, (aliveAt D (pt p q m)).card =
      ∑ i : Fin r, if D.a i (pt p q m) ≠ 0 then 1 else 0 := by
    intro m
    rw [aliveAt, Finset.card_filter]
  simp only [key]
  rw [Finset.sum_comm]
  have inner : ∀ i : Fin r, (∑ m : Fin 5, if D.a i (pt p q m) ≠ 0 then 1 else 0) =
      if i ∈ alive2 D p q then 4 else 0 := by
    intro i
    rw [← Finset.card_filter]
    simp only [a_pt]
    by_cases hi : i ∈ alive2 D p q
    · rw [if_pos hi]
      exact vanish_count _ _ (mem_alive2.mp hi)
    · rw [if_neg hi]
      rw [mem_alive2] at hi
      push_neg at hi
      simp [hi.1, hi.2]
  simp only [inner]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_comm]

/-- L2: at least 8 terms are alive on a 2-dim subspace of `U`. -/
theorem pencil_count {D : Decomp r} {U : Submodule F4 GF} (hD : D.ValidOn U) {p q : GF}
    (hp : p ∈ U) (hq : q ∈ U) (hind : LinearIndependent F4 ![p, q]) :
    8 ≤ (alive2 D p q).card := by
  have hsum := sum_aliveAt_pt D p q
  have hm : ∀ m : Fin 5, 6 ≤ (aliveAt D (pt p q m)).card := fun m =>
    point_bound hD (U.add_mem (U.smul_mem _ hp) (U.smul_mem _ hq)) (pt_ne_zero hind m)
  have : 30 ≤ ∑ m : Fin 5, (aliveAt D (pt p q m)).card := by
    calc 30 = ∑ _m : Fin 5, 6 := by simp
      _ ≤ _ := Finset.sum_le_sum fun m _ => hm m
  omega

/-- L2, exact form: with at most 8 terms alive on the pencil, exactly 8 are, and at most 2 alive
terms vanish at each standard point. -/
theorem pencil_exact {D : Decomp r} {U : Submodule F4 GF} (hD : D.ValidOn U) {p q : GF}
    (hp : p ∈ U) (hq : q ∈ U) (hind : LinearIndependent F4 ![p, q])
    (h8 : (alive2 D p q).card ≤ 8) :
    (alive2 D p q).card = 8 ∧ ∀ m : Fin 5, 6 ≤ (aliveAt D (pt p q m)).card ∧
      ((alive2 D p q).filter fun i => D.a i (pt p q m) = 0).card ≤ 2 := by
  classical
  have h8' := pencil_count hD hp hq hind
  have hA : (alive2 D p q).card = 8 := le_antisymm h8 h8'
  have hsum := sum_aliveAt_pt D p q
  rw [hA] at hsum
  have hm : ∀ m : Fin 5, 6 ≤ (aliveAt D (pt p q m)).card := fun m =>
    point_bound hD (U.add_mem (U.smul_mem _ hp) (U.smul_mem _ hq)) (pt_ne_zero hind m)
  refine ⟨hA, fun m => ⟨hm m, ?_⟩⟩
  have hfilter : (alive2 D p q).filter (fun i => D.a i (pt p q m) = 0) =
      alive2 D p q \ aliveAt D (pt p q m) := by
    ext i; simp [mem_aliveAt]
  rw [hfilter, Finset.card_sdiff_of_subset (aliveAt_pt_subset D p q m), hA]
  have := hm m
  omega

/-! ### L3 -/

/-- The terms alive on a subspace. -/
noncomputable def aliveOn (D : Decomp r) (V : Submodule F4 GF) : Finset (Fin r) :=
  by classical exact Finset.univ.filter fun i => ∃ v ∈ V, D.a i v ≠ 0

lemma mem_aliveOn {D : Decomp r} {V : Submodule F4 GF} {i : Fin r} :
    i ∈ aliveOn D V ↔ ∃ v ∈ V, D.a i v ≠ 0 := by
  classical simp [aliveOn]

lemma finrank_ker_form {f : GF →ₗ[F4] F4} {x : GF} (hx : f x ≠ 0) :
    Module.finrank F4 (LinearMap.ker f) = 5 := by
  have hrange : LinearMap.range f = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ⟨(c / f x) • x, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hx]
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, Module.finrank_self, GF.finrank_eq] at this
  omega

/-- Two independent vectors in a subspace of dimension at least 2. -/
lemma exists_pair_of_two_le {V : Submodule F4 GF} (hV : 2 ≤ Module.finrank F4 V) :
    ∃ p q : GF, p ∈ V ∧ q ∈ V ∧ LinearIndependent F4 ![p, q] := by
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank F4 V)
  obtain ⟨y, hy⟩ :=
    exists_linearIndependent_pair_of_one_lt_finrank (by omega : 1 < Module.finrank F4 V) hx
  refine ⟨x, y, x.2, y.2, ?_⟩
  have := hy.map' V.subtype (Submodule.ker_subtype V)
  convert this using 1
  ext i; fin_cases i <;> rfl

/-- L3: at least 9 terms are alive on a 3-dim subspace of `U`. -/
theorem plane_bound {D : Decomp r} {U : Submodule F4 GF} (hD : D.ValidOn U) {V : Submodule F4 GF}
    (hVU : V ≤ U) (hV : 3 ≤ Module.finrank F4 V) : 9 ≤ (aliveOn D V).card := by
  classical
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank F4 V)
  have hx0 : (x : GF) ≠ 0 := by simpa using hx
  have h6 := point_bound hD (hVU x.2) hx0
  obtain ⟨i, hi⟩ : (aliveAt D x).Nonempty := Finset.card_pos.mp (by omega)
  have hix : D.a i x ≠ 0 := mem_aliveAt.mp hi
  have hK := finrank_ker_form hix
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V (LinearMap.ker (D.a i))
  have hle : Module.finrank F4 ↥(V ⊔ LinearMap.ker (D.a i)) ≤ 6 := by
    have := Submodule.finrank_le (V ⊔ LinearMap.ker (D.a i)); rwa [GF.finrank_eq] at this
  have h2 : 2 ≤ Module.finrank F4 ↥(V ⊓ LinearMap.ker (D.a i)) := by omega
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_pair_of_two_le h2
  have h8 := pencil_count hD (hVU hp.1) (hVU hq.1) hpq
  have hsub : alive2 D p q ⊆ (aliveOn D V).erase i := by
    intro j hj
    rw [Finset.mem_erase, mem_aliveOn]
    rw [mem_alive2] at hj
    constructor
    · rintro rfl
      have hpi : D.a j p = 0 := LinearMap.mem_ker.mp hp.2
      have hqi : D.a j q = 0 := LinearMap.mem_ker.mp hq.2
      rcases hj with h | h
      · exact h hpi
      · exact h hqi
    · rcases hj with h | h
      · exact ⟨p, hp.1, h⟩
      · exact ⟨q, hq.1, h⟩
  have hi' : i ∈ aliveOn D V := mem_aliveOn.mpr ⟨x, x.2, hix⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hi'] at this
  omega

end Mu4.Lower
