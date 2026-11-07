import Mu4.N5.Vertex5
import Mu4.Normal.Transport
import Mu4Comp5.Data

/-!
# mu_4(5), N8: the triple of vertices, and the end of the bridge

The three W-forms of a 10-term decomposition valid on `A5` have common kernel `P`, so their joint map onto GF(4)^3 is
onto: there are `d_0, d_1, d_2` with `w_k(d_j) = δ_kj`. Each vertex `d_j` gives a solution of the search of rank ≤ 1
(only the W-term `j` is alive there); the three solutions are pairwise adjacent (distinct directions, commuting pair
operators by N7) with independent directions. So `tripleFree5` is false, and `caseOK5` is false for a case in normal
form (`bridge5_holds`).
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge Module

/-! ### The W-forms -/

section WForms

variable {D : Decomp5 10} {H : Submodule F4 GF5}

/-- An enumeration of the three W-indices. -/
noncomputable def wk5 (S : Step1Data5 D H) : Fin 3 → Fin 10 := S.W.orderEmbOfFin S.hW

lemma wk5_mem (S : Step1Data5 D H) (l : Fin 3) : wk5 S l ∈ S.W := Finset.orderEmbOfFin_mem _ _ _

lemma wk5_inj (S : Step1Data5 D H) : Function.Injective (wk5 S) := (S.W.orderEmbOfFin S.hW).injective

lemma wk5_surj (S : Step1Data5 D H) {k : Fin 10} (hk : k ∈ S.W) : ∃ l, wk5 S l = k := by
  have : k ∈ Set.range (S.W.orderEmbOfFin S.hW) := by rw [Finset.range_orderEmbOfFin]; exact hk
  exact this

lemma W5_zero_on_P (S : Step1Data5 D H) {k : Fin 10} (hk : k ∈ S.W) {x : GF5}
    (hx : x ∈ Submodule.span F4 {S.p, S.q}) : D.a k x = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp [(S.hWvan k hk).1, (S.hWvan k hk).2]

lemma finrank_span_pair5 {u v : GF5} (h : LinearIndependent F4 ![u, v]) :
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

/-- The W-forms on `A5` have dual vectors: their joint map onto GF(4)^3 is onto. -/
lemma wforms_dual (S : Step1Data5 D ⊤) :
    ∃ dd : Fin 3 → GF5, ∀ l j : Fin 3, D.a (wk5 S l) (dd j) = if l = j then 1 else 0 := by
  classical
  set Φ : GF5 →ₗ[F4] (Fin 3 → F4) := LinearMap.pi fun l => D.a (wk5 S l)
  have hker : LinearMap.ker Φ = Submodule.span F4 {S.p, S.q} := by
    ext x
    constructor
    · intro hx
      apply S.hker x Submodule.mem_top
      intro k hk
      obtain ⟨l, rfl⟩ := wk5_surj S hk
      have := congrFun (LinearMap.mem_ker.mp hx) l
      simpa [Φ] using this
    · intro hx
      rw [LinearMap.mem_ker]
      funext l
      simp only [Φ, LinearMap.pi_apply, Pi.zero_apply]
      exact W5_zero_on_P S (wk5_mem S l) hx
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hker, finrank_span_pair5 S.hind, GF5.finrank_eq] at hrn
  have htop : LinearMap.range Φ = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [Module.finrank_fin_fun]; omega)
  have hsurj : ∀ j : Fin 3, ∃ x, Φ x = Pi.single j 1 := fun j => by
    have : Pi.single j (1 : F4) ∈ LinearMap.range Φ := by rw [htop]; trivial
    exact this
  choose dd hdd using hsurj
  refine ⟨dd, fun l j => ?_⟩
  have := congrFun (hdd j) l
  simp only [Φ, LinearMap.pi_apply] at this
  rw [this, Pi.single_apply]

end WForms

/-! ### Ranks -/

section Ranks

variable {D : Decomp5 10} {H : Submodule F4 GF5}

/-- The W-part `E_x(y) = ∑_{i ∈ W} a_i(x) b_i(y) g_i`. -/
noncomputable def Ex5 (S : Step1Data5 D H) (x y : GF5) : GF5 := ∑ k ∈ S.W, D.a k x • (D.b k y • D.g k)

/-- The W-indices alive at `x`. -/
noncomputable def Wset5 (S : Step1Data5 D H) (x : GF5) : Finset (Fin 10) :=
  by classical exact S.W.filter fun k => D.a k x ≠ 0

/-- The span of their `g`'s. -/
noncomputable def Wspan5 (S : Step1Data5 D H) (x : GF5) : Submodule F4 GF5 :=
  by classical exact Submodule.span F4 (((Wset5 S x).image D.g : Finset GF5) : Set GF5)

lemma Ex5_mem (S : Step1Data5 D H) (x y : GF5) : Ex5 S x y ∈ Wspan5 S x := by
  classical
  unfold Ex5 Wspan5
  apply Submodule.sum_mem
  intro k hk
  by_cases h0 : D.a k x = 0
  · rw [h0, zero_smul]; exact Submodule.zero_mem _
  · apply Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span _))
    simp only [Finset.coe_image]
    refine Set.mem_image_of_mem _ ?_
    simp [Wset5, hk, h0]

lemma finrank_Wspan5 (S : Step1Data5 D H) (x : GF5) : finrank F4 (Wspan5 S x) ≤ (Wset5 S x).card := by
  classical
  unfold Wspan5
  have h1 := finrank_span_finset_le_card (R := F4) ((Wset5 S x).image D.g)
  exact h1.trans Finset.card_image_le

lemma Wset5_card_le (S : Step1Data5 D H) (x : GF5) {Z : Finset (Fin 10)} (hZ : Z ⊆ S.W)
    (hz : ∀ k ∈ Z, D.a k x = 0) : (Wset5 S x).card + Z.card ≤ 3 := by
  classical
  have hsub : Wset5 S x ⊆ S.W \ Z := by
    intro k hk
    simp only [Wset5, Finset.mem_filter] at hk
    rw [Finset.mem_sdiff]
    exact ⟨hk.1, fun hkZ => hk.2 (hz k hkZ)⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hZ, S.hW] at this
  have := Finset.card_le_card hZ
  rw [S.hW] at this
  omega

end Ranks

lemma rk5_le (X : PCtx5) (hX : PCtx5WF X) (d : CaseData) (s : Sol) {W : Submodule F4 GF5}
    (hE : ∀ y, Esem5 X d s y ∈ W) : (withE5 X d s).rk ≤ finrank F4 W := by
  apply rankC_le5
  intro v hv
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hv
  rw [decode_Eval5 X hX]
  exact hE _

/-! ### Directions -/

lemma normalize_dir3 : ∀ g < 64, g ≠ 0 → ∃ μ : F4, μ ≠ 0 ∧ smulC μ g < 64 ∧ normalized3 (smulC μ g) = true := by
  decide +kernel

/-- A nonzero vector of `GF(4)^3` has a normalized multiple in `dirs3`. -/
lemma dir3_of_ne_zero {γ : Fin 3 → F4} (hγ : γ ≠ 0) :
    ∃ μ : F4, μ ≠ 0 ∧ smulC μ (encode3 γ) ∈ dirs3 ∧ vec3 (smulC μ (encode3 γ)) = μ • γ := by
  have hne : encode3 γ ≠ 0 := by
    intro h0; apply hγ; rw [← vec3_encode3 γ, h0]; funext k; simp [vec3]
  obtain ⟨μ, hμ, hlt, hn⟩ := normalize_dir3 _ (encode3_lt γ) hne
  refine ⟨μ, hμ, ?_, by rw [vec3_smulC, vec3_encode3]⟩
  rw [dirs3, List.mem_filter, List.mem_range]
  exact ⟨hlt, hn⟩

/-- `p0, p1` and the complement `tv` span `A5`. -/
lemma decompose5 {D : Decomp5 10} {H : Submodule F4 GF5} (S : Step1Data5 D H) {p0 p1 : Nat}
    (hp : S.p = decode5 p0) (hq : S.q = decode5 p1) (hX : (mkPCtx5 p0 p1).ok = true) (v : GF5) :
    ∃ π ∈ Submodule.span F4 {S.p, S.q}, ∃ γ : Fin 3 → F4,
      v = π + ∑ k : Fin 3, γ k • decode5 ((mkPCtx5 p0 p1).tv.getD k 0) := by
  have hok := hX
  simp only [PCtx5.ok, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨htv3, hrank⟩ := hok
  obtain ⟨t0, t1, t2, htv⟩ : ∃ t0 t1 t2, (mkPCtx5 p0 p1).tv = [t0, t1, t2] := by
    match h : (mkPCtx5 p0 p1).tv, htv3 with
    | [t0, t1, t2], _ => exact ⟨t0, t1, t2, rfl⟩
  have hp0 : (mkPCtx5 p0 p1).p0 = p0 := rfl
  have hp1 : (mkPCtx5 p0 p1).p1 = p1 := rfl
  rw [htv, hp0, hp1] at hrank
  set W5 := Submodule.span F4 ({decode5 p0, decode5 p1, decode5 t0, decode5 t1, decode5 t2} : Set GF5)
  have h5 : 5 ≤ finrank F4 W5 := by
    rw [← hrank]
    apply rankC_le5
    intro x hx
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact Submodule.subset_span (by simp)
  have htop : W5 = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _)
    (by rw [GF5.finrank_eq]; exact h5))
  have hv : v ∈ W5 := by rw [htop]; trivial
  simp only [W5] at hv
  rw [Submodule.mem_span_insert] at hv
  obtain ⟨c0, z0, hz0, rfl⟩ := hv
  rw [Submodule.mem_span_insert] at hz0
  obtain ⟨c1, z1, hz1, rfl⟩ := hz0
  rw [Submodule.mem_span_insert] at hz1
  obtain ⟨c2, z2, hz2, rfl⟩ := hz1
  rw [Submodule.mem_span_insert] at hz2
  obtain ⟨c3, z3, hz3, rfl⟩ := hz2
  rw [Submodule.mem_span_singleton] at hz3
  obtain ⟨c4, rfl⟩ := hz3
  refine ⟨c0 • S.p + c1 • S.q, Submodule.mem_span_pair.mpr ⟨c0, c1, rfl⟩, ![c2, c3, c4], ?_⟩
  rw [htv, Fin.sum_univ_three, hp, hq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero, List.getD_cons_succ]
  abel

/-! ### A triple makes `tripleFree5` false -/

lemma toArray_getD5 {α : Type*} [Inhabited α] (l : List α) (i : Nat) (hi : i < l.length) :
    l.toArray.getD i default = l[i] := by
  rw [Array.getD_eq_getD_getElem?]
  simp [hi]

lemma tripleFree5_false_core (d : CaseData) (sols : List SolE) {i j k : Nat} (hij : i < j) (hjk : j < k)
    (hk : k < sols.length) (h12 : adj5 d sols[i] sols[j] = true) (h13 : adj5 d sols[i] sols[k] = true)
    (h23 : adj5 d sols[j] sols[k] = true) (hspan : inSpan2 sols[i].s.c sols[j].s.c sols[k].s.c = false) :
    tripleFree5 d sols = false := by
  have hi : i < sols.length := by omega
  have hj : j < sols.length := by omega
  unfold tripleFree5
  simp only
  rw [List.all_eq_false]
  refine ⟨i, List.mem_range.mpr (by simp; omega), ?_⟩
  rw [Bool.not_eq_true, List.all_eq_false]
  refine ⟨j, List.mem_range.mpr (by simp; omega), ?_⟩
  rw [toArray_getD5 sols i hi, toArray_getD5 sols j hj, h12]
  simp only [decide_eq_true hij, Bool.not_true, Bool.false_or, Bool.not_eq_true]
  rw [List.all_eq_false]
  refine ⟨k, List.mem_range.mpr (by simp; omega), ?_⟩
  rw [toArray_getD5 sols k hk, h13, h23, hspan]
  simp [hjk]

/-- Three solutions, pairwise adjacent with independent directions, in any order of positions. -/
lemma tripleFree5_false_of_three (d : CaseData) (sols : List SolE) (e : Fin 3 → SolE)
    (hmem : ∀ a, e a ∈ sols) (hc : ∀ a b, a ≠ b → (e a).s.c ≠ (e b).s.c)
    (hadj : ∀ a b, a ≠ b → adj5 d (e a) (e b) = true)
    (hspan : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → inSpan2 (e a).s.c (e b).s.c (e c).s.c = false) :
    tripleFree5 d sols = false := by
  have hidx : ∀ a, ∃ i, ∃ h : i < sols.length, sols[i] = e a := fun a => List.mem_iff_getElem.mp (hmem a)
  choose idx hlt hget using hidx
  have hinj : ∀ a b, idx a = idx b → a = b := by
    intro a b h
    by_contra hab
    apply hc a b hab
    have : sols[idx a]'(hlt a) = sols[idx b]'(hlt b) := by simp only [h]
    rw [hget a, hget b] at this
    rw [this]
  have key : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → idx a < idx b → idx b < idx c →
      tripleFree5 d sols = false := by
    intro a b c hab hac hbc h1 h2
    have hget' : ∀ a' (h : idx a' < sols.length), sols[idx a'] = e a' := fun a' _ => hget a'
    apply tripleFree5_false_core d sols h1 h2 (hlt c)
    · rw [hget' a, hget' b]; exact hadj a b hab
    · rw [hget' a, hget' c]; exact hadj a c hac
    · rw [hget' b, hget' c]; exact hadj b c hbc
    · rw [hget' a, hget' b, hget' c]; exact hspan a b c hab hac hbc
  have h01 : idx 0 ≠ idx 1 := fun h => absurd (hinj 0 1 h) (by decide)
  have h02 : idx 0 ≠ idx 2 := fun h => absurd (hinj 0 2 h) (by decide)
  have h12 : idx 1 ≠ idx 2 := fun h => absurd (hinj 1 2 h) (by decide)
  rcases Nat.lt_or_gt_of_ne h01 with a | a <;> rcases Nat.lt_or_gt_of_ne h02 with b | b <;>
    rcases Nat.lt_or_gt_of_ne h12 with c | c
  · exact key 0 1 2 (by decide) (by decide) (by decide) a c
  · exact key 0 2 1 (by decide) (by decide) (by decide) b c
  · omega
  · exact key 2 0 1 (by decide) (by decide) (by decide) b a
  · exact key 1 0 2 (by decide) (by decide) (by decide) a b
  · omega
  · exact key 1 2 0 (by decide) (by decide) (by decide) c b
  · exact key 2 1 0 (by decide) (by decide) (by decide) c a

/-! ### The valid case -/

lemma sum_three5 {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ∑ i, f i = f a + f b + f c := by
  rw [Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all <;> abel

lemma vec3_add_self (v : Fin 3 → F4) : v + v = 0 := by
  funext k; simp only [Pi.add_apply, Pi.zero_apply]; exact F4.add_self _

lemma third_exists5 : ∀ a b : Fin 3, a ≠ b → ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide

lemma other_two5 : ∀ j : Fin 3, ∃ k1 k2 : Fin 3, k1 ≠ k2 ∧ k1 ≠ j ∧ k2 ≠ j := by decide

/-- The valid case: a decomposition in normal form gives an adjacent independent triple, so `tripleFree5` is false. -/
theorem tripleFree5_false_valid {p0 p1 s0 s1 : Nat} {mult ws : List Nat} {D : Decomp5 10}
    {d : CaseData} (V : VCtx5 p0 p1 s0 s1 mult ws D ⊤ d) (hX : (mkPCtx5 p0 p1).ok = true)
    (hwf : wfCheck5 d = true) :
    tripleFree5 d (allSols5 (mkPCtx5 p0 p1) d) = false := by
  classical
  have hXWF := mkPCtx5_WF p0 p1 hX
  have hd := caseWF_of_check5 d hwf
  set S := V.nf.S with hS
  obtain ⟨F, G0, hF1, hF2, hF3, hF4, hF5⟩ := V.ops_exist
  obtain ⟨dd, hδ⟩ := wforms_dual S
  have hdec := fun j : Fin 3 => decompose5 S V.nf.hp V.nf.hq hX (dd j)
  choose π hπ γ hγ using hdec
  set ψ : (Fin 3 → F4) → GF5 := fun g => ∑ k : Fin 3, g k • decode5 ((mkPCtx5 p0 p1).tv.getD k 0) with hψ
  have hψd : ∀ j, ψ (γ j) = dd j - π j := fun j => by rw [hγ j]; abel
  have hWψ : ∀ j l, D.a (wk5 S l) (ψ (γ j)) = D.a (wk5 S l) (dd j) := by
    intro j l
    rw [hψd, map_sub, W5_zero_on_P S (wk5_mem S l) (hπ j), sub_zero]
  have hψlin : ∀ ν : Fin 3 → F4, ψ (∑ j, ν j • γ j) = ∑ j, ν j • ψ (γ j) := by
    intro ν
    simp only [hψ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  have hind : ∀ ν : Fin 3 → F4, ∑ j, ν j • γ j = 0 → ∀ j, ν j = 0 := by
    intro ν hν j
    have h0 : ∑ i, ν i • ψ (γ i) = 0 := by
      rw [← hψlin, hν]; simp [hψ]
    have := congrArg (D.a (wk5 S j)) h0
    rw [map_sum, map_zero] at this
    simp only [map_smul, smul_eq_mul, hWψ, hδ, mul_ite, mul_one, mul_zero] at this
    rw [Finset.sum_ite_eq] at this
    simpa using this
  have hγ0 : ∀ j, γ j ≠ 0 := by
    intro j h0
    have := hind (fun i => if i = j then 1 else 0) (by simp [h0]) j
    simp at this
  choose μ hμ hdir hvec using fun j => dir3_of_ne_zero (hγ0 j)
  set c : Fin 3 → Nat := fun j => smulC (μ j) (encode3 (γ j)) with hc
  set x : Fin 3 → GF5 := fun j => xcG5 (mkPCtx5 p0 p1) (c j) with hx
  have hxe : ∀ j, x j = μ j • ψ (γ j) := by
    intro j
    simp only [hx, hψ, hc]
    rw [xcG_eq5 _ hXWF, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coordC_smulC _ _ _ (by omega), smul_smul]
    have : coordC (encode3 (γ j)) k = γ j k := congrFun (vec3_encode3 (γ j)) k
    rw [this]
  have hWx : ∀ j l, D.a (wk5 S l) (x j) = μ j * D.a (wk5 S l) (dd j) := by
    intro j l; rw [hxe, map_smul, smul_eq_mul, hWψ]
  have hzero : ∀ j l, l ≠ j → D.a (wk5 S l) (x j) = 0 := by
    intro j l hlj; rw [hWx, hδ, if_neg hlj, mul_zero]
  -- the solutions
  set lamOf : Fin 3 → Fin 10 → F4 := fun j k => D.a k (x j) with hlam
  set sol : Fin 3 → Sol := fun j => ⟨c j, F (lamOf j), G0 (lamOf j)⟩ with hsol
  have hE : ∀ j y, Esem5 (mkPCtx5 p0 p1) d (sol j) y = Ex5 S (x j) y := by
    intro j y
    show xcG5 (mkPCtx5 p0 p1) (c j) * y + offSem5 d.off (F (lamOf j)) y +
      blockSem5 (G0 (lamOf j)) [(d.ga, d.fa), (d.gb, d.fb)] y = _
    rw [add_assoc, hF4, show xcG5 (mkPCtx5 p0 p1) (c j) = x j from rfl, V.hD _ Submodule.mem_top y,
      ← Finset.sum_add_sum_compl S.W]
    unfold Ex5
    simp only [mul_smul, hlam]
    rw [add_assoc, GF5_add_self, add_zero]
  set es : Fin 3 → SolE := fun j => withE5 (mkPCtx5 p0 p1) d (sol j) with hes
  have hvert : ∀ j, (Wset5 S (x j)).card ≤ 1 := by
    intro j
    obtain ⟨k1, k2, hk12, hk1, hk2⟩ := other_two5 j
    have hsub : ({wk5 S k1, wk5 S k2} : Finset (Fin 10)) ⊆ S.W := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact wk5_mem S k1
      · rw [Finset.mem_singleton] at hk; rw [hk]; exact wk5_mem S k2
    have h1 := Wset5_card_le S (x j) hsub (by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hzero j k1 hk1
      · rw [Finset.mem_singleton] at hk; rw [hk]; exact hzero j k2 hk2)
    rw [Finset.card_pair (fun h => hk12 (wk5_inj S h))] at h1
    omega
  have hmem : ∀ j, es j ∈ allSols5 (mkPCtx5 p0 p1) d := by
    intro j
    exact sol_complete5 (mkPCtx5 p0 p1) hXWF d hd (sol j) (hdir j) (hF1 _) (hF2 _) (hF3 _).1 (hF3 _).2
      (W := Wspan5 S (x j)) ((finrank_Wspan5 S (x j)).trans (hvert j))
      (fun y => by rw [hE]; exact Ex5_mem S _ y)
  -- the directions are independent
  have hvc : ∀ j, vec3 (c j) = μ j • γ j := hvec
  have hcne : ∀ a b, a ≠ b → (es a).s.c ≠ (es b).s.c := by
    intro a b hab heq
    obtain ⟨k, hka, hkb⟩ := third_exists5 a b hab
    have hv := congrArg vec3 heq
    change vec3 (c a) = vec3 (c b) at hv
    rw [hvc, hvc] at hv
    have := hind (fun i => if i = a then μ a else if i = b then μ b else 0) (by
      rw [sum_three5 _ hab (Ne.symm hka) (Ne.symm hkb)]
      simp only [↓reduceIte, if_neg hab.symm, if_neg hka, if_neg hkb, zero_smul, add_zero]
      rw [hv, vec3_add_self]) a
    simp only [↓reduceIte] at this
    exact hμ a this
  have hspan : ∀ a b k, a ≠ b → a ≠ k → b ≠ k → inSpan2 (es a).s.c (es b).s.c (es k).s.c = false := by
    intro a b k hab hak hbk
    rw [← Bool.not_eq_true]
    intro h
    unfold inSpan2 at h
    rw [List.any_eq_true] at h
    obtain ⟨ab, -, hab'⟩ := h
    rw [beq_iff_eq] at hab'
    have hv := congrArg vec3 hab'
    rw [vec3_xor_smul] at hv
    change coordC ab 0 • vec3 (c a) + coordC ab 1 • vec3 (c b) = vec3 (c k) at hv
    rw [hvc, hvc, hvc] at hv
    have := hind (fun i => if i = a then coordC ab 0 * μ a else if i = b then coordC ab 1 * μ b else μ k)
      (by
        rw [sum_three5 _ hab hak hbk]
        simp only [↓reduceIte, if_neg hab.symm, if_neg hak.symm, if_neg hbk.symm]
        rw [mul_smul, mul_smul, hv, vec3_add_self]) k
    simp only [if_neg hak.symm, if_neg hbk.symm] at this
    exact hμ k this
  have hadj : ∀ a b, a ≠ b → adj5 d (es a) (es b) = true := by
    intro a b hab
    unfold adj5
    rw [Bool.and_eq_true, bne_iff_ne]
    exact ⟨hcne a b hab, hF5 (lamOf a) (lamOf b) (c a) (c b)⟩
  exact tripleFree5_false_of_three d _ es hmem hcne hadj hspan

/-! ### The bridge -/

lemma pList5_lt : ∀ P : Nat × Nat, P ∈ pList5 → P.1 < 1024 ∧ P.2 < 1024 := by decide

lemma sList5_lt : ∀ S : Nat × Nat, S ∈ sList5 → S.1 < 1024 ∧ S.2 < 1024 := by decide

/-- N6-N9: a 10-term decomposition in normal form makes its case's check fail. -/
theorem bridge5_holds : ∀ P : Nat × Nat, P ∈ pList5 → ∀ S : Nat × Nat, S ∈ sList5 →
    ∀ mult ws : List Nat, (mkPCtx5 P.1 P.2).ok = true →
    ∀ D : Decomp5 10, D.ValidOn ⊤ →
      NF5 P.1 P.2 S.1 S.2 mult ws D ⊤ → caseOK5 (mkPCtx5 P.1 P.2) S.1 S.2 mult ws = false := by
  intro P hP S hS mult ws hok D hD nf
  have hPb := pList5_lt P hP
  have hSb := sList5_lt S hS
  unfold caseOK5
  cases hsc : setupCase5 (mkPCtx5 P.1 P.2) S.1 S.2 mult ws with
  | invalid => exact absurd hsc (setupCase_ne_invalid5 nf hD hPb.1 hPb.2 hSb.1 hSb.2)
  | error => rfl
  | valid d =>
    simp only
    cases hwf : wfCheck5 d with
    | false => rfl
    | true =>
      obtain ⟨V⟩ := vctx_of5 nf hD hPb.1 hPb.2 hSb.1 hSb.2 hsc
      rw [tripleFree5_false_valid V hok hwf]
      rfl

end Mu4.N5
