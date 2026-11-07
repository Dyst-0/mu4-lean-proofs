import Mu4.Lower.Step1

/-!
# The pencil structure lemma (`audit/PROOF.md`, L5)

On the pencil `P = span(p, q)` of step 1, with `x_1` a standard point where two alive terms `a, b`
vanish, put `Ŝ = span(x_1 g_a, x_1 g_b)`. Then `g_a, g_b` are independent (so `dim Ŝ = 2`) and
`x_m g_i ∈ Ŝ` for every alive `i` vanishing at `x_m`.
-/

namespace Mu4.Lower
open Mu4 F4

variable {D : Decomp 12} {H : Submodule F4 GF}

lemma W_van_pt (S : Step1Data D H) {i : Fin 12} (hi : i ∈ S.W) (m : Fin 5) :
    D.a i (pt S.p S.q m) = 0 := by
  rw [a_pt, (S.hWvan i hi).1, (S.hWvan i hi).2]; ring

lemma alive_of_not_W (S : Step1Data D H) {i : Fin 12} (hi : i ∉ S.W) :
    D.a i S.p ≠ 0 ∨ D.a i S.q ≠ 0 := by
  have : i ∈ alive2 D S.p S.q := by rw [S.halive]; simpa using hi
  exact mem_alive2.mp this

/-- An alive term vanishes at exactly one standard point. -/
lemma vanish_point_unique (S : Step1Data D H) {i : Fin 12} (hi : i ∉ S.W) {m m' : Fin 5}
    (h : D.a i (pt S.p S.q m) = 0) (h' : D.a i (pt S.p S.q m') = 0) : m = m' := by
  rw [a_pt] at h h'
  exact vanish_unique _ _ (alive_of_not_W S hi) m m' h h'

lemma vanish_point_exists (S : Step1Data D H) {i : Fin 12} (hi : i ∉ S.W) :
    ∃ m : Fin 5, D.a i (pt S.p S.q m) = 0 := by
  obtain ⟨m, hm⟩ := vanish_exists _ _ (alive_of_not_W S hi)
  exact ⟨m, by rw [a_pt]; exact hm⟩

/-- The alive terms vanishing at `x_m`. -/
noncomputable def vanAt (S : Step1Data D H) (m : Fin 5) : Finset (Fin 12) :=
  by classical exact S.Wᶜ.filter fun i => D.a i (pt S.p S.q m) = 0

lemma mem_vanAt (S : Step1Data D H) {m : Fin 5} {i : Fin 12} :
    i ∈ vanAt S m ↔ i ∉ S.W ∧ D.a i (pt S.p S.q m) = 0 := by
  classical simp [vanAt]

lemma aliveAt_pt_eq (S : Step1Data D H) (m : Fin 5) :
    aliveAt D (pt S.p S.q m) = S.Wᶜ \ vanAt S m := by
  ext i
  rw [mem_aliveAt, Finset.mem_sdiff, Finset.mem_compl, mem_vanAt]
  constructor
  · intro h
    refine ⟨fun hW => h (W_van_pt S hW m), fun h' => h h'.2⟩
  · rintro ⟨hW, h'⟩ h0
    exact h' ⟨hW, h0⟩

lemma vanAt_subset (S : Step1Data D H) (m : Fin 5) : vanAt S m ⊆ S.Wᶜ := by
  intro i hi; rw [Finset.mem_compl]; exact ((mem_vanAt S).mp hi).1

lemma card_Wc (S : Step1Data D H) : S.Wᶜ.card = 8 := by
  rw [Finset.card_compl, S.hW]; simp

lemma card_aliveAt_pt (S : Step1Data D H) (m : Fin 5) :
    (aliveAt D (pt S.p S.q m)).card + (vanAt S m).card = 8 := by
  rw [aliveAt_pt_eq, Finset.card_sdiff_of_subset (vanAt_subset S m), card_Wc]
  have := Finset.card_le_card (vanAt_subset S m)
  rw [card_Wc] at this
  omega

lemma pt_mem (S : Step1Data D H) (m : Fin 5) : pt S.p S.q m ∈ H :=
  H.add_mem (H.smul_mem _ S.hp) (H.smul_mem _ S.hq)

lemma vanAt_le_two (hD : D.ValidOn H) (S : Step1Data D H) (m : Fin 5) : (vanAt S m).card ≤ 2 := by
  have h6 : 6 ≤ (aliveAt D (pt S.p S.q m)).card := point_bound hD (pt_mem S m) (pt_ne_zero S.hind m)
  have := card_aliveAt_pt S m
  omega

lemma sum_vanAt (S : Step1Data D H) : ∑ m : Fin 5, (vanAt S m).card = 8 := by
  have h1 := sum_aliveAt_pt D S.p S.q
  rw [S.halive, card_Wc] at h1
  have h2 : ∑ m : Fin 5, ((aliveAt D (pt S.p S.q m)).card + (vanAt S m).card) = 40 := by
    simp [card_aliveAt_pt]
  rw [Finset.sum_add_distrib, h1] at h2
  omega

/-- Two independent vectors inside the span of two dependent ones: impossible. -/
lemma not_indep_in_span_dep {u v x y : GF} (huv : ¬ LinearIndependent F4 ![u, v])
    (hx : x ∈ Submodule.span F4 {u, v}) (hy : y ∈ Submodule.span F4 {u, v})
    (hxy : LinearIndependent F4 ![x, y]) : False := by
  have h1 : Module.finrank F4 (Submodule.span F4 ({u, v} : Set GF)) ≤ 1 := by
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp huv
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hg
    -- one of u, v is a multiple of the other
    have hsub : ∃ z : GF, Submodule.span F4 ({u, v} : Set GF) ≤ Submodule.span F4 {z} := by
      have hi' : g 0 ≠ 0 ∨ g 1 ≠ 0 := by
        rcases (Fin.exists_fin_two (p := fun i => g i ≠ 0)).mp ⟨i, hi⟩ with h | h
        · exact Or.inl h
        · exact Or.inr h
      rcases hi' with h0 | h1
      · refine ⟨v, Submodule.span_le.mpr ?_⟩
        intro z hz
        rcases hz with rfl | rfl
        · have hu : g 0 • z = -(g 1 • v) := eq_neg_of_add_eq_zero_left hg
          have : z = (g 0)⁻¹ • (-(g 1 • v)) := by
            rw [← hu, smul_smul, inv_mul_cancel₀ h0, one_smul]
          rw [this, smul_neg, smul_smul]
          exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
        · exact Submodule.subset_span rfl
      · refine ⟨u, Submodule.span_le.mpr ?_⟩
        intro z hz
        rcases hz with rfl | rfl
        · exact Submodule.subset_span rfl
        · have hv : g 1 • z = -(g 0 • u) := eq_neg_of_add_eq_zero_right hg
          have : z = (g 1)⁻¹ • (-(g 0 • u)) := by
            rw [← hv, smul_smul, inv_mul_cancel₀ h1, one_smul]
          rw [this, smul_neg, smul_smul]
          exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    obtain ⟨z, hz⟩ := hsub
    calc Module.finrank F4 (Submodule.span F4 ({u, v} : Set GF))
        ≤ Module.finrank F4 (Submodule.span F4 ({z} : Set GF)) := Submodule.finrank_mono hz
      _ ≤ 1 := by simpa using finrank_span_le_card (R := F4) ({z} : Set GF)
  have h2 : Module.finrank F4 (Submodule.span F4 (Set.range ![x, y])) = 2 := by
    simpa using finrank_span_eq_card hxy
  have h3 : Submodule.span F4 (Set.range ![x, y]) ≤ Submodule.span F4 {u, v} := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hx
    · exact hy
  have := Submodule.finrank_mono h3
  omega

/-- L5: the pencil structure lemma. -/
theorem pencil_structure (hD : D.ValidOn H) (S : Step1Data D H) {m1 : Fin 5} {a b : Fin 12}
    (hab : a ≠ b) (ha : a ∈ vanAt S m1) (hb : b ∈ vanAt S m1) :
    (∀ i, i ∉ S.W → ∀ m : Fin 5, D.a i (pt S.p S.q m) = 0 →
      pt S.p S.q m * D.g i ∈ Submodule.span F4 {pt S.p S.q m1 * D.g a, pt S.p S.q m1 * D.g b}) ∧
    LinearIndependent F4 ![D.g a, D.g b] := by
  classical
  set x1 := pt S.p S.q m1 with hx1def
  have hx1H : x1 ∈ H := pt_mem S m1
  have hx1 : x1 ≠ 0 := pt_ne_zero S.hind m1
  -- vanAt m1 = {a, b}
  have hvan : vanAt S m1 = {a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ha
      · rw [Finset.mem_singleton] at hz; rw [hz]; exact hb
    · rw [Finset.card_pair hab]; exact vanAt_le_two hD S m1
  have h6 : (aliveAt D x1).card = 6 := by
    have := card_aliveAt_pt S m1
    rw [hvan, Finset.card_pair hab, ← hx1def] at this
    omega
  have hbasis := point_basis hD hx1H hx1 h6
  -- off-pair alive terms are alive at x1
  have hoff : ∀ i, i ∉ S.W → i ∉ ({a, b} : Finset (Fin 12)) → i ∈ aliveAt D x1 := by
    intro i hiW hiab
    rw [aliveAt_pt_eq, Finset.mem_sdiff, Finset.mem_compl, hvan]
    exact ⟨hiW, hiab⟩
  have hspan_mem : ∀ i, i ∉ S.W → ∀ m : Fin 5, D.a i (pt S.p S.q m) = 0 →
      pt S.p S.q m * D.g i ∈ Submodule.span F4 {x1 * D.g a, x1 * D.g b} := by
    intro i hiW m hm
    by_cases hmm : m = m1
    · subst hmm
      have hi : i ∈ vanAt S m := (mem_vanAt S).mpr ⟨hiW, hm⟩
      rw [hvan] at hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · rw [Finset.mem_singleton] at hi; subst hi
        exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
    · have hiab : i ∉ ({a, b} : Finset (Fin 12)) := by
        intro hi
        rw [← hvan, mem_vanAt] at hi
        exact hmm (vanish_point_unique S hiW hm hi.2)
      have hi1 := hoff i hiW hiab
      obtain ⟨y0, hy0⟩ := point_dual hD hx1H hx1 h6 i hi1
      have hai : D.a i x1 ≠ 0 := mem_aliveAt.mp hi1
      -- x1 * y0 = a_i(x1) g_i
      have e1 : x1 * y0 = D.a i x1 • D.g i := by
        rw [mul_eq_sum_alive hD hx1H, Finset.sum_eq_single i]
        · rw [hy0 i hi1]; simp
        · intro j hj hji
          rw [hy0 j hj, if_neg hji]; simp
        · intro h; exact absurd hi1 h
      -- xm * y0 is a combination of g_a, g_b
      set xm := pt S.p S.q m
      have hxmH : xm ∈ H := pt_mem S m
      have e2 : xm * y0 = (D.a a xm * D.b a y0) • D.g a + (D.a b xm * D.b b y0) • D.g b := by
        rw [hD xm hxmH y0, ← Finset.sum_pair (f := fun j => (D.a j xm * D.b j y0) • D.g j) hab]
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        by_cases hjW : j ∈ S.W
        · rw [W_van_pt S hjW m]; simp
        · have hj1 := hoff j hjW hj
          rw [hy0 j hj1]
          by_cases hji : j = i
          · subst hji; rw [hm]; simp
          · rw [if_neg hji]; simp
      have : xm * D.g i = (D.a i x1)⁻¹ • (x1 * (xm * y0)) := by
        have hg : D.g i = (D.a i x1)⁻¹ • (x1 * y0) := by
          rw [e1, smul_smul, inv_mul_cancel₀ hai, one_smul]
        rw [hg, mul_smul_comm, ← mul_assoc, mul_comm xm x1, mul_assoc]
      rw [this, e2, mul_add, mul_smul_comm, mul_smul_comm]
      apply Submodule.smul_mem
      apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  refine ⟨hspan_mem, ?_⟩
  -- independence of g_a, g_b
  by_contra hdep
  -- a second point with two vanishing terms
  obtain ⟨m2, hm21, hm22⟩ : ∃ m2 : Fin 5, m2 ≠ m1 ∧ (vanAt S m2).card = 2 := by
    by_contra hno
    push_neg at hno
    have hle : ∀ m, m ≠ m1 → (vanAt S m).card ≤ 1 := by
      intro m hm
      have := vanAt_le_two hD S m
      have := hno m hm
      omega
    have hsum := sum_vanAt S
    have hm1 : (vanAt S m1).card = 2 := by rw [hvan, Finset.card_pair hab]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m1), hm1] at hsum
    have : ∑ m ∈ Finset.univ.erase m1, (vanAt S m).card ≤ ∑ m ∈ Finset.univ.erase m1, 1 :=
      Finset.sum_le_sum fun m hm => hle m (Finset.ne_of_mem_erase hm)
    simp at this
    omega
  obtain ⟨c, d, hcd, hvan2⟩ := Finset.card_eq_two.mp hm22
  have hc : c ∈ vanAt S m2 := by rw [hvan2]; simp
  have hd : d ∈ vanAt S m2 := by rw [hvan2]; simp
  have hcW := ((mem_vanAt S).mp hc).1
  have hdW := ((mem_vanAt S).mp hd).1
  have hcab : c ∉ ({a, b} : Finset (Fin 12)) := by
    intro h; rw [← hvan, mem_vanAt] at h
    exact hm21 (vanish_point_unique S hcW ((mem_vanAt S).mp hc).2 h.2)
  have hdab : d ∉ ({a, b} : Finset (Fin 12)) := by
    intro h; rw [← hvan, mem_vanAt] at h
    exact hm21 (vanish_point_unique S hdW ((mem_vanAt S).mp hd).2 h.2)
  have hc1 := hoff c hcW hcab
  have hd1 := hoff d hdW hdab
  -- g_c, g_d are independent (two of the basis at x1)
  have hgcd : LinearIndependent F4 ![D.g c, D.g d] := by
    have := hbasis.comp ![⟨c, hc1⟩, ⟨d, hd1⟩] (by
      intro u v huv
      fin_cases u <;> fin_cases v <;> simp_all [Subtype.ext_iff])
    convert this using 1
    ext u; fin_cases u <;> rfl
  -- x_{m2} g_c, x_{m2} g_d lie in the span of x1 g_a, x1 g_b, spanned by dependent vectors
  set x2 := pt S.p S.q m2
  have hx2 : x2 ≠ 0 := pt_ne_zero S.hind m2
  have hdep' : ¬ LinearIndependent F4 ![x1 * D.g a, x1 * D.g b] := by
    intro hli
    apply hdep
    have := hli.map' (LinearMap.mulLeft F4 x1⁻¹) (by
      rw [LinearMap.ker_eq_bot]
      intro u v huv
      simpa [LinearMap.mulLeft_apply, inv_ne_zero hx1] using huv)
    convert this using 1
    ext u; fin_cases u <;> simp [LinearMap.mulLeft_apply, ← mul_assoc, inv_mul_cancel₀ hx1]
  have hxc := hspan_mem c hcW m2 ((mem_vanAt S).mp hc).2
  have hxd := hspan_mem d hdW m2 ((mem_vanAt S).mp hd).2
  apply not_indep_in_span_dep hdep' hxc hxd
  have := hgcd.map' (LinearMap.mulLeft F4 x2) (by
    rw [LinearMap.ker_eq_bot]
    intro u v huv
    simpa [LinearMap.mulLeft_apply, hx2] using huv)
  convert this using 1
  ext u; fin_cases u <;> rfl

end Mu4.Lower
