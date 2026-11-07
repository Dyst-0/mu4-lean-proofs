import Mu4.N5.Transport5
import Mu4.N5.CoverCheck5
import Mu4.Normal.Cover

/-!
# The coverage facts C1(5), C2(5) in the field (`audit/PROOF.md`, mu_4(5))

Every 2-dim subspace of `A5` is `x · span(1, z)` with `z ∉ GF(4)`; for each such `z` the kernel-checked tables give
C1(5) (`cover1_5`) and C2(5) (`cover2_5`).
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Lower Mu4.Normal

lemma c1Ok5_all (x : Nat) (hx4 : 4 ≤ x) (hx : x < 1024) : c1Ok5 x = true :=
  List.all_eq_true.mp c1_ok5 x (List.mem_range'_1.mpr ⟨hx4, by omega⟩)

lemma c2Ok5_all (x : Nat) (hx4 : 4 ≤ x) (hx : x < 1024) : c2Ok5 x = true :=
  List.all_eq_true.mp c2_ok5 x (List.mem_range'_1.mpr ⟨hx4, by omega⟩)

lemma decode5_lin2 (ab z : Nat) : decode5 (lin2 ab z) = coordC ab 0 • (1 : GF5) + coordC ab 1 • decode5 z := by
  rw [lin2, decode5_xor, decode5_smulC, decode5_smulC, decode5_one]

lemma ftab5_spec (k : Nat) (hk : k < 3) :
    ftab5 k 0 = (pList5.getD k (0, 0)).2 ∧ ∀ s < 9, ftab5 k (s + 1) = mulK5 (ftab5 k s) (ftab5 k s) := by
  have h := ftab_ok5
  simp only [ftabOk5, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨(h k hk).1, (h k hk).2⟩

lemma decode5_ftab5 (k : Nat) (hk : k < 3) (s : Nat) (hs : s < 10) :
    decode5 (ftab5 k s) = frob5^[s] (decode5 (pList5.getD k (0, 0)).2) := by
  induction s with
  | zero => rw [(ftab5_spec k hk).1]; rfl
  | succ s ih =>
    rw [(ftab5_spec k hk).2 s (by omega), decode5_mulK5, ih (by omega), Function.iterate_succ_apply']
    rfl

lemma decode5_small : ∀ x < 4, ∀ l : Fin 5, coordC x l.val = (coordC x 0 • (1 : GF5)).v l := by
  decide

lemma code_ge_four5 {z : GF5} (hz : ∀ c : F4, z ≠ c • 1) : 4 ≤ encode5 z := by
  by_contra h
  push_neg at h
  apply hz (coordC (encode5 z) 0)
  rw [← decode5_encode5 z]
  ext l
  rw [decode5_v, decode5_encode5, ← decode5_v, decode5_encode5]
  have := decode5_small (encode5 z) h l
  rw [← this, ← decode5_v, decode5_encode5]

/-- C1(5) in the field. -/
theorem cover1_5 (z : GF5) (hz : ∀ c : F4, z ≠ c • 1) :
    ∃ k < 3, ∃ s < 10, ∃ a b c d : F4, (a ≠ 0 ∨ b ≠ 0) ∧
      (a • 1 + b • z) * frob5^[s] (decode5 (pList5.getD k (0, 0)).2) = c • 1 + d • z := by
  have h := c1Ok5_all (encode5 z) (code_ge_four5 hz) (encode5_lt z)
  unfold c1Ok5 at h
  generalize (c1Tab5 >>> (16 * encode5 z)) % 65536 = e at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hk, hs⟩, hab⟩, heq⟩ := h
  refine ⟨e / 4096, hk, e / 256 % 16, hs, coordC (e / 16 % 16) 0, coordC (e / 16 % 16) 1,
    coordC (e % 16) 0, coordC (e % 16) 1, ab_ne _ (Nat.mod_lt _ (by norm_num)) hab, ?_⟩
  have := congrArg decode5 heq
  rw [decode5_mulK5, decode5_lin2, decode5_lin2, decode5_ftab5 _ hk _ hs, decode5_encode5] at this
  exact this

/-- C2(5) in the field. -/
theorem cover2_5 (z : GF5) (hz : ∀ c : F4, z ≠ c • 1) :
    ∃ j < 17, ∃ a b c d : F4, (a ≠ 0 ∨ b ≠ 0) ∧
      (a • 1 + b • z) * decode5 (sList5.getD j (0, 0)).2 = c • 1 + d • z := by
  have h := c2Ok5_all (encode5 z) (code_ge_four5 hz) (encode5_lt z)
  unfold c2Ok5 at h
  generalize (c2Tab5 >>> (16 * encode5 z)) % 65536 = e at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨hj, hab⟩, heq⟩ := h
  refine ⟨e / 256, hj, coordC (e / 16 % 16) 0, coordC (e / 16 % 16) 1,
    coordC (e % 16) 0, coordC (e % 16) 1, ab_ne _ (Nat.mod_lt _ (by norm_num)) hab, ?_⟩
  have := congrArg decode5 heq
  rw [decode5_mulK5, decode5_lin2, decode5_lin2, decode5_encode5] at this
  exact this

/-! ### The representatives -/

lemma pList5_spec : ∀ k < 3, (pList5.getD k (0, 0)).1 = 1 ∧ 4 ≤ (pList5.getD k (0, 0)).2 ∧
    (pList5.getD k (0, 0)).2 < 1024 := by decide

lemma sList5_spec : ∀ j < 17, (sList5.getD j (0, 0)).1 = 1 ∧ 4 ≤ (sList5.getD j (0, 0)).2 ∧
    (sList5.getD j (0, 0)).2 < 1024 := by decide

lemma pList5_mem (k : Nat) (hk : k < 3) : pList5.getD k (0, 0) ∈ pList5 := by
  rw [List.getD_eq_getElem _ _ (by simp [pList5]; omega)]; exact List.getElem_mem _

lemma sList5_mem (j : Nat) (hj : j < 17) : sList5.getD j (0, 0) ∈ sList5 := by
  rw [List.getD_eq_getElem _ _ (by simp [sList5]; omega)]; exact List.getElem_mem _

/-- A code below `1024` whose coordinates `1..4` vanish is below `4`. -/
lemma lt_four_of_coord5 {x : Nat} (hx : x < 1024) (hc : ∀ l, 1 ≤ l → l < 5 → coordC x l = 0) :
    x < 4 := by
  have key : ∀ a b : Bool, F4.ofBits a b = 0 → a = false ∧ b = false := by decide
  have hb : ∀ i, 2 ≤ i → x.testBit i = false := by
    intro i hi
    by_cases h10 : i < 10
    · have hcl := hc (i / 2) (by omega) (by omega)
      simp only [coordC] at hcl
      obtain ⟨h0, h1⟩ := key _ _ hcl
      rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
      · have : i = 2 * (i / 2) := by omega
        rw [this]; exact h0
      · have : i = 2 * (i / 2) + 1 := by omega
        rw [this]; exact h1
    · apply Nat.testBit_eq_false_of_lt
      calc x < 2 ^ 10 := by norm_num; exact hx
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := Nat.lt_pow_two_of_testBit x (n := 2) (fun i hi => hb i hi)
  simpa using this

lemma GF5_eq_of_add_eq_zero {x y : GF5} (h : x + y = 0) : x = y := by
  calc x = x + (y + y) := by rw [GF5_add_self', add_zero]
    _ = (x + y) + y := by rw [add_assoc]
    _ = y := by rw [h, zero_add]

/-- `1` and `decode5 x` are independent for a code `x ∉ {0, 1, 2, 3}`. -/
lemma indep_one_decode5 {x : Nat} (hx4 : 4 ≤ x) (hx : x < 1024) :
    LinearIndependent F4 ![(1 : GF5), decode5 x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    have := congrArg (fun y : GF5 => y.v 0) hst
    simpa [GF5.one_v, pw5] using this
  · exfalso
    have h1 : t • decode5 x = s • (1 : GF5) := (GF5_eq_of_add_eq_zero (by rw [add_comm]; exact hst))
    have hdx : decode5 x = (t⁻¹ * s) • (1 : GF5) := by
      calc decode5 x = t⁻¹ • (t • decode5 x) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = (t⁻¹ * s) • (1 : GF5) := by rw [h1, smul_smul]
    have hc : ∀ l : Nat, 1 ≤ l → l < 5 → coordC x l = 0 := by
      intro l hl1 hl5
      have := congrArg (fun y : GF5 => y.v ⟨l, hl5⟩) hdx
      simp only [decode5_v, GF5.smul_v, GF5.one_v, Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      interval_cases l <;> simp [pw5]
    have := lt_four_of_coord5 hx hc
    omega

end Mu4.N5
