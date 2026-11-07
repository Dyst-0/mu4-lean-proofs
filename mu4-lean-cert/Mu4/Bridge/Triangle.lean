import Mu4.Bridge.Vertex
import Mu4Comp.Data
import Mu4.Normal.Transport
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# L9: the triangle, and the end of the bridge (`audit/PROOF.md`)

`triangle_abstract` (L9 in abstract form, first proved in `lean/wip/Triangle.lean`): four forms on a space with a
joint map of rank 3; one of them, `w e`, is a combination of the other three, and there are `d_0, d_1, d_2` dual to
those three, so that either `w e` vanishes at a vertex `d_j`, or every edge `d_i, d_j` has an interior point
`d_i + c d_j`, `c ≠ 0`, where `w e` vanishes.

Applied to the four W-forms on `H` (common kernel `P`, so rank 3), the vertices give three solutions of the search
(L8, `ops_exist`; completeness `sol_complete`), pairwise edges, with independent directions, passing the final test.
So `triFree` is false, and `caseOK` is false for a case in normal form (`bridgeMath_holds`).
-/

set_option autoImplicit false

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower Module

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- L9 (abstract). -/
theorem triangle_abstract (w : Fin 4 → V →ₗ[K] K)
    (h3 : finrank K (LinearMap.range (LinearMap.pi w)) = 3) :
    ∃ e : Fin 4, ∃ d : Fin 3 → V,
      (∀ k j : Fin 3, w (e.succAbove k) (d j) = if k = j then 1 else 0) ∧
      ((∃ j, w e (d j) = 0) ∨
        (∀ i j : Fin 3, i ≠ j → ∃ c : K, c ≠ 0 ∧ w e (d i + c • d j) = 0)) := by
  classical
  set Φ := LinearMap.pi w with hΦ
  set R := LinearMap.range Φ with hRdef
  have hR : R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => ?_
    have := h3
    rw [h, finrank_top, finrank_fin_fun] at this
    norm_num at this
  obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top R hR
  set c : Fin 4 → K := fun k => φ (Pi.single k 1) with hc
  have hφ : ∀ v : Fin 4 → K, φ v = ∑ k, c k * v k := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hs : (Pi.single k (v k) : Fin 4 → K) = v k • (Pi.single k (1 : K) : Fin 4 → K) := by
      ext j; by_cases hj : j = k <;> simp [Pi.single_apply, hj]
    rw [hs, map_smul, smul_eq_mul, mul_comm]
  have hce : ∃ e, c e ≠ 0 := by
    by_contra h
    push_neg at h
    apply hφ0
    ext v
    simp [hφ, h]
  obtain ⟨e, he⟩ := hce
  have hrel : ∀ x : V, ∑ k, c k * w k x = 0 := by
    intro x
    have hx := hle (LinearMap.mem_range_self Φ x)
    rw [LinearMap.mem_ker, hφ] at hx
    simpa [Φ] using hx
  -- the coordinates other than `e` are injective on `R`
  let ψ : R →ₗ[K] (Fin 3 → K) :=
    (LinearMap.pi fun k : Fin 3 => LinearMap.proj (e.succAbove k)).comp R.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h0 : ∀ k : Fin 3, (r : Fin 4 → K) (e.succAbove k) = 0 := fun k =>
      congrFun hr k
    have hrφ : φ r = 0 := hle r.2
    rw [hφ, Fin.sum_univ_succAbove _ e] at hrφ
    simp only [h0, mul_zero, Finset.sum_const_zero, add_zero] at hrφ
    have hre : (r : Fin 4 → K) e = 0 := by
      rcases mul_eq_zero.mp hrφ with h | h
      · exact absurd h he
      · exact h
    apply Subtype.ext
    funext k
    by_cases hk : k = e
    · subst hk; simpa using hre
    · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
      simpa using h0 k'
  have hsurj : Function.Surjective ψ := by
    have hdim : finrank K R = finrank K (Fin 3 → K) := by rw [h3, finrank_fin_fun]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  choose r hr using fun j : Fin 3 => hsurj (Pi.single j 1)
  choose d hd using fun j : Fin 3 => (LinearMap.mem_range.mp (r j).2)
  have hdk : ∀ k j : Fin 3, w (e.succAbove k) (d j) = if k = j then 1 else 0 := by
    intro k j
    have h1 := congrFun (hr j) k
    have h2 : w (e.succAbove k) (d j) = ((r j : R) : Fin 4 → K) (e.succAbove k) := by
      rw [← hd j]; rfl
    rw [h2]
    simp only [ψ, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.pi_apply, LinearMap.coe_proj, Function.eval] at h1
    rw [h1, Pi.single_apply]
  -- the value of `w e` at the vertices
  have hwe : ∀ j : Fin 3, c e * w e (d j) = - c (e.succAbove j) := by
    intro j
    have h := hrel (d j)
    rw [Fin.sum_univ_succAbove _ e] at h
    simp only [hdk, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    linear_combination h
  refine ⟨e, d, hdk, ?_⟩
  by_cases hz : ∃ j, c (e.succAbove j) = 0
  · obtain ⟨j, hj⟩ := hz
    left
    refine ⟨j, ?_⟩
    have := hwe j
    rw [hj, neg_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h he
    · exact h
  · push_neg at hz
    right
    intro i j _
    refine ⟨- c (e.succAbove i) / c (e.succAbove j), ?_, ?_⟩
    · exact div_ne_zero (neg_ne_zero.mpr (hz i)) (hz j)
    · have hi := hwe i
      have hj := hwe j
      have hval : w e (d i + (- c (e.succAbove i) / c (e.succAbove j)) • d j) =
          w e (d i) + (- c (e.succAbove i) / c (e.succAbove j)) * w e (d j) := by
        rw [map_add, map_smul, smul_eq_mul]
      rw [hval]
      have hcj := hz j
      apply mul_left_cancel₀ he
      rw [mul_zero, mul_add, hi, mul_left_comm, hj]
      field_simp
      ring


end Abstract

/-! ### The W-forms on `H` -/

section WForms

variable {D : Decomp 12} {H : Submodule F4 GF}

/-- An enumeration of the four W-indices. -/
noncomputable def wk (S : Step1Data D H) : Fin 4 → Fin 12 := S.W.orderEmbOfFin S.hW

lemma wk_mem (S : Step1Data D H) (l : Fin 4) : wk S l ∈ S.W := Finset.orderEmbOfFin_mem _ _ _

lemma wk_inj (S : Step1Data D H) : Function.Injective (wk S) := (S.W.orderEmbOfFin S.hW).injective

lemma wk_surj (S : Step1Data D H) {k : Fin 12} (hk : k ∈ S.W) : ∃ l, wk S l = k := by
  have : k ∈ Set.range (S.W.orderEmbOfFin S.hW) := by rw [Finset.range_orderEmbOfFin]; exact hk
  exact this

/-- The W-forms on `H`. -/
noncomputable def wform (S : Step1Data D H) (l : Fin 4) : H →ₗ[F4] F4 := (D.a (wk S l)).comp H.subtype

lemma span_pq_le (S : Step1Data D H) : Submodule.span F4 {S.p, S.q} ≤ H := by
  rw [Submodule.span_le]
  intro x hx
  rcases hx with rfl | hx
  · exact S.hp
  · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact S.hq

lemma W_zero_on_P (S : Step1Data D H) {k : Fin 12} (hk : k ∈ S.W) {x : GF}
    (hx : x ∈ Submodule.span F4 {S.p, S.q}) : D.a k x = 0 :=
  Mu4.Lower.form_zero_on_span _ (S.hWvan k hk).1 (S.hWvan k hk).2 hx

/-- The joint map of the W-forms on `H` has rank 3 (its kernel is `P`). -/
lemma finrank_range_wforms (hH : finrank F4 H = 5) (S : Step1Data D H) :
    finrank F4 (LinearMap.range (LinearMap.pi (wform S))) = 3 := by
  classical
  set Φ := LinearMap.pi (wform S)
  have hmap : (LinearMap.ker Φ).map H.subtype = Submodule.span F4 {S.p, S.q} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply S.hker y.1 y.2
      intro k hk
      obtain ⟨l, rfl⟩ := wk_surj S hk
      have := congrFun (LinearMap.mem_ker.mp hy) l
      simpa [Φ, wform] using this
    · intro hx
      refine ⟨⟨x, span_pq_le S hx⟩, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      funext l
      simp only [Φ, LinearMap.pi_apply, wform, LinearMap.comp_apply, Submodule.subtype_apply,
        Pi.zero_apply]
      exact W_zero_on_P S (wk_mem S l) hx
  have hker : finrank F4 (LinearMap.ker Φ) = 2 := by
    have e := (Submodule.equivMapOfInjective _ (Submodule.injective_subtype H) (LinearMap.ker Φ)).finrank_eq
    rw [e, hmap, Mu4.Lower.finrank_span_pair S.hind]
  have := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hH, hker] at this
  omega

end WForms

/-! ### Directions -/

lemma normalize_dir : ∀ g < 256, g ≠ 0 → ∃ μ : F4, μ ≠ 0 ∧ smulC μ g < 256 ∧ normalized4 (smulC μ g) = true := by
  decide +kernel

lemma vec4_smulC (μ : F4) (x : Nat) : vec4 (smulC μ x) = μ • vec4 x := by
  funext k
  simp [vec4, coordC_smulC _ _ _ (show k.val < 32 by omega)]

lemma vec4_inj_of_lt {x y : Nat} (hx : x < 256) (hy : y < 256) (h : vec4 x = vec4 y) : x = y := by
  apply code_ext (n := 4) (by norm_num; exact hx) (by norm_num; exact hy)
  intro l hl
  exact congrFun h ⟨l, hl⟩

/-- A nonzero vector of `GF(4)^4` has a normalized multiple in `dirs`. -/
lemma dir_of_ne_zero {γ : Fin 4 → F4} (hγ : γ ≠ 0) :
    ∃ μ : F4, μ ≠ 0 ∧ smulC μ (encode4 γ) ∈ dirs ∧ vec4 (smulC μ (encode4 γ)) = μ • γ := by
  have hne : encode4 γ ≠ 0 := by
    intro h0; apply hγ; rw [← vec4_encode4 γ, h0]; funext k; simp [vec4]
  obtain ⟨μ, hμ, hlt, hn⟩ := normalize_dir _ (encode4_lt γ) hne
  refine ⟨μ, hμ, ?_, by rw [vec4_smulC, vec4_encode4]⟩
  rw [dirs, List.mem_filter, List.mem_range]
  exact ⟨hlt, hn⟩

/-! ### A passing triangle makes `triFree` false -/

lemma toArray_getD {α : Type*} [Inhabited α] (l : List α) (i : Nat) (hi : i < l.length) :
    l.toArray.getD i default = l[i] := by
  rw [Array.getD_eq_getD_getElem?]
  simp [hi]

lemma adj_getD (d : CaseData) (l : List SolE) (a b : Nat) (ha : a < l.length) (hb : b < l.length) :
    ((Array.ofFn (n := l.toArray.size) fun i => Array.ofFn (n := l.toArray.size) fun j =>
        if i.val < j.val then edge d l.toArray[i] l.toArray[j] else none).getD a #[]).getD b none =
      if a < b then edge d l[a] l[b] else none := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, List.size_toArray, ha, hb, dite_true,
    Option.getD_some, Fin.getElem_fin, List.getElem_toArray]

/-- `triFree` is false as soon as three solutions at `i < j < k` form a passing triangle. -/
lemma triFree_false_core (d : CaseData) (sols : List SolE) {i j k : Nat} (hij : i < j) (hjk : j < k)
    (hk : k < sols.length) {f12 f13 f23 : Bool}
    (h12 : edge d sols[i] sols[j] = some f12) (h13 : edge d sols[i] sols[k] = some f13)
    (h23 : edge d sols[j] sols[k] = some f23)
    (hspan : inSpan2 sols[i].s.c sols[j].s.c sols[k].s.c = false)
    (hpass : triPass sols[i] sols[j] sols[k] f12 f13 f23 = true) : triFree d sols = false := by
  have hi : i < sols.length := by omega
  have hj : j < sols.length := by omega
  unfold triFree
  simp only
  rw [List.all_eq_false]
  refine ⟨i, List.mem_range.mpr (by simp; omega), ?_⟩
  rw [Bool.not_eq_true, List.all_eq_false]
  refine ⟨j, List.mem_range.mpr (by simp; omega), ?_⟩
  rw [adj_getD d sols i j hi hj, if_pos hij, h12]
  simp only
  rw [Bool.not_eq_true, List.all_eq_false]
  refine ⟨k, List.mem_range.mpr (by simp; omega), ?_⟩
  rw [adj_getD d sols i k hi hk, if_pos (by omega), h13, adj_getD d sols j k hj hk, if_pos hjk, h23]
  simp only [toArray_getD sols i hi, toArray_getD sols j hj, toArray_getD sols k hk, hspan, hpass,
    decide_eq_true hjk, Bool.not_true, Bool.or_false]
  simp

/-- Three solutions, in any order of their positions, forming a passing triangle make `triFree` false. -/
lemma triFree_false_of_three (d : CaseData) (sols : List SolE) (e : Fin 3 → SolE) (hmem : ∀ a, e a ∈ sols)
    (hc : ∀ a b, a ≠ b → (e a).s.c ≠ (e b).s.c) (fl : Fin 3 → Fin 3 → Bool)
    (hedge : ∀ a b, a ≠ b → edge d (e a) (e b) = some (fl a b))
    (hspan : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → inSpan2 (e a).s.c (e b).s.c (e c).s.c = false)
    (hpass : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → triPass (e a) (e b) (e c) (fl a b) (fl a c) (fl b c) = true) :
    triFree d sols = false := by
  have hidx : ∀ a, ∃ i, ∃ h : i < sols.length, sols[i] = e a := fun a => List.mem_iff_getElem.mp (hmem a)
  choose idx hlt hget using hidx
  have hinj : ∀ a b, idx a = idx b → a = b := by
    intro a b h
    by_contra hab
    apply hc a b hab
    have e1 := hget a
    have e2 := hget b
    have : sols[idx a]'(hlt a) = sols[idx b]'(hlt b) := by simp only [h]
    rw [e1, e2] at this
    rw [this]
  have key : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → idx a < idx b → idx b < idx c →
      triFree d sols = false := by
    intro a b c hab hac hbc h1 h2
    have hget' : ∀ a' (h : idx a' < sols.length), sols[idx a'] = e a' := fun a' _ => hget a'
    apply triFree_false_core d sols h1 h2 (hlt c) (f12 := fl a b) (f13 := fl a c) (f23 := fl b c)
    · rw [hget' a, hget' b]; exact hedge a b hab
    · rw [hget' a, hget' c]; exact hedge a c hac
    · rw [hget' b, hget' c]; exact hedge b c hbc
    · rw [hget' a, hget' b, hget' c]; exact hspan a b c hab hac hbc
    · rw [hget' a, hget' b, hget' c]; exact hpass a b c hab hac hbc
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

/-! ### Ranks of the solutions' operators -/

section Ranks

variable {D : Decomp 12} {H : Submodule F4 GF}

/-- The W-part `E_x(y) = ∑_{i ∈ W} a_i(x) b_i(y) g_i`. -/
noncomputable def Ex (S : Step1Data D H) (x y : GF) : GF := ∑ k ∈ S.W, D.a k x • (D.b k y • D.g k)

/-- The W-indices alive at `x`. -/
noncomputable def Wset (S : Step1Data D H) (x : GF) : Finset (Fin 12) :=
  by classical exact S.W.filter fun k => D.a k x ≠ 0

/-- The span of their `g`'s. -/
noncomputable def Wspan (S : Step1Data D H) (x : GF) : Submodule F4 GF :=
  by classical exact Submodule.span F4 (((Wset S x).image D.g : Finset GF) : Set GF)

lemma Ex_mem (S : Step1Data D H) (x y : GF) : Ex S x y ∈ Wspan S x := by
  classical
  unfold Ex Wspan
  apply Submodule.sum_mem
  intro k hk
  by_cases h0 : D.a k x = 0
  · rw [h0, zero_smul]; exact Submodule.zero_mem _
  · apply Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span _))
    simp only [Finset.coe_image]
    refine Set.mem_image_of_mem _ ?_
    simp [Wset, hk, h0]

lemma finrank_Wspan (S : Step1Data D H) (x : GF) : finrank F4 (Wspan S x) ≤ (Wset S x).card := by
  classical
  unfold Wspan
  have h1 := finrank_span_finset_le_card (R := F4) ((Wset S x).image D.g)
  exact h1.trans Finset.card_image_le

lemma Wset_card_le (S : Step1Data D H) (x : GF) {Z : Finset (Fin 12)} (hZ : Z ⊆ S.W)
    (hz : ∀ k ∈ Z, D.a k x = 0) : (Wset S x).card + Z.card ≤ 4 := by
  classical
  have hsub : Wset S x ⊆ S.W \ Z := by
    intro k hk
    simp only [Wset, Finset.mem_filter] at hk
    rw [Finset.mem_sdiff]
    exact ⟨hk.1, fun hkZ => hk.2 (hz k hkZ)⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hZ, S.hW] at this
  have := Finset.card_le_card hZ
  rw [S.hW] at this
  omega

lemma Ex_add_smul (S : Step1Data D H) (x x' : GF) (lam : F4) (y : GF) :
    lam • Ex S x' y + Ex S x y = Ex S (x + lam • x') y := by
  unfold Ex
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_add, map_smul, smul_eq_mul, add_smul, mul_smul]
  abel

end Ranks

lemma rk_le (X : PCtx) (hX : PCtxWF X) (d : CaseData) (s : Sol) {W : Submodule F4 GF}
    (hE : ∀ y, Esem X d s y ∈ W) : (withE X d s).rk ≤ finrank F4 W := by
  apply rankC_le
  intro v hv
  simp only [withE] at hv
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hv
  rw [decode_Eval X hX]
  exact hE _

lemma rk_addCols_le (X : PCtx) (hX : PCtxWF X) (d : CaseData) (sa sb : Sol) (lam : F4)
    {W : Submodule F4 GF} (hE : ∀ y, lam • Esem X d sb y + Esem X d sa y ∈ W) :
    rankC (addCols lam (withE X d sb).cols (withE X d sa).cols) ≤ finrank F4 W := by
  apply rankC_le
  intro v hv
  simp only [withE, addCols] at hv
  rw [zip_map_map, List.map_map] at hv
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hv
  simp only [Function.comp_apply, decode_xor, decode_smulC, decode_Eval X hX]
  exact hE _

/-! ### The vertices -/

/-- `p0, p1` and the complement `tv` span `A`. -/
lemma decompose {D : Decomp 12} {H : Submodule F4 GF} (S : Step1Data D H) {p0 p1 : Nat} (hp : S.p = decode p0) (hq : S.q = decode p1)
    (hX : (mkPCtx p0 p1).ok = true) (v : GF) :
    ∃ π ∈ Submodule.span F4 {S.p, S.q}, ∃ γ : Fin 4 → F4,
      v = π + ∑ k : Fin 4, γ k • decode ((mkPCtx p0 p1).tv.getD k 0) := by
  have hok := hX
  simp only [PCtx.ok, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨htv4, hrank⟩ := hok
  obtain ⟨t0, t1, t2, t3, htv⟩ : ∃ t0 t1 t2 t3, (mkPCtx p0 p1).tv = [t0, t1, t2, t3] := by
    match h : (mkPCtx p0 p1).tv, htv4 with
    | [t0, t1, t2, t3], _ => exact ⟨t0, t1, t2, t3, rfl⟩
  have hp0 : (mkPCtx p0 p1).p0 = p0 := rfl
  have hp1 : (mkPCtx p0 p1).p1 = p1 := rfl
  rw [htv, hp0, hp1] at hrank
  set W6 := Submodule.span F4 ({decode p0, decode p1, decode t0, decode t1, decode t2, decode t3} : Set GF)
  have h6 : 6 ≤ finrank F4 W6 := by
    rw [← hrank]
    apply rankC_le
    intro x hx
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Submodule.subset_span (by simp)
  have htop : W6 = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _)
    (by rw [GF.finrank_eq]; exact h6))
  have hv : v ∈ W6 := by rw [htop]; trivial
  simp only [W6] at hv
  rw [Submodule.mem_span_insert] at hv
  obtain ⟨c0, z0, hz0, rfl⟩ := hv
  rw [Submodule.mem_span_insert] at hz0
  obtain ⟨c1, z1, hz1, rfl⟩ := hz0
  rw [Submodule.mem_span_insert] at hz1
  obtain ⟨c2, z2, hz2, rfl⟩ := hz1
  rw [Submodule.mem_span_insert] at hz2
  obtain ⟨c3, z3, hz3, rfl⟩ := hz2
  rw [Submodule.mem_span_insert] at hz3
  obtain ⟨c4, z4, hz4, rfl⟩ := hz3
  rw [Submodule.mem_span_singleton] at hz4
  obtain ⟨c5, rfl⟩ := hz4
  refine ⟨c0 • S.p + c1 • S.q, Submodule.mem_span_pair.mpr ⟨c0, c1, rfl⟩, ![c2, c3, c4, c5], ?_⟩
  rw [htv, Fin.sum_univ_four, hp, hq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero, List.getD_cons_succ]
  have e3 : ((3 : Fin 4) : Nat) = 3 := rfl
  rw [e3]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  abel

lemma sum_three {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ∑ i, f i = f a + f b + f c := by
  rw [Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all <;> abel

lemma vec4_add_self (v : Fin 4 → F4) : v + v = 0 := by
  funext k; simp only [Pi.add_apply, Pi.zero_apply]; exact F4.add_self _

lemma third_exists : ∀ a b : Fin 3, a ≠ b → ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide

lemma other_two : ∀ j : Fin 3, ∃ k1 k2 : Fin 3, k1 ≠ k2 ∧ k1 ≠ j ∧ k2 ≠ j := by decide

lemma one_of_three : ∀ a b c j : Fin 3, a ≠ b → a ≠ c → b ≠ c → j = a ∨ j = b ∨ j = c := by decide

lemma F4_ne_zero_mem : ∀ l : F4, l ≠ 0 → l ∈ [o, w, w2] := by decide

/-- The valid case: a decomposition in normal form gives a passing triangle, so `triFree` is false. -/
theorem triFree_false_valid {p0 p1 s0 s1 : Nat} {mult ws : List Nat} {D : Decomp 12} {H : Submodule F4 GF}
    {d : CaseData} (V : VCtx p0 p1 s0 s1 mult ws D H d) (hH : finrank F4 H = 5)
    (hX : (mkPCtx p0 p1).ok = true) (hwf : wfCheck d = true) :
    triFree d (allSols (mkPCtx p0 p1) d) = false := by
  classical
  have hXWF := mkPCtx_WF p0 p1 hX
  have hd := caseWF_of_check d hwf
  set S := V.nf.S with hS
  obtain ⟨F, G0, hF1, hF2, hF3, hF4, hF5⟩ := V.ops_exist
  obtain ⟨e, dd, hδ, halt⟩ := triangle_abstract (wform S) (finrank_range_wforms hH S)
  have hdec := fun j : Fin 3 => decompose S V.nf.hp V.nf.hq hX (dd j : GF)
  choose π hπ γ hγ using hdec
  set ψ : (Fin 4 → F4) → GF := fun g => ∑ k : Fin 4, g k • decode ((mkPCtx p0 p1).tv.getD k 0) with hψ
  have hψd : ∀ j, ψ (γ j) = (dd j : GF) - π j := fun j => by rw [hγ j]; abel
  have hWψ : ∀ j l, D.a (wk S l) (ψ (γ j)) = wform S l (dd j) := by
    intro j l
    rw [hψd, map_sub, W_zero_on_P S (wk_mem S l) (hπ j), sub_zero]; rfl
  have hψlin : ∀ ν : Fin 3 → F4, ψ (∑ j, ν j • γ j) = ∑ j, ν j • ψ (γ j) := by
    intro ν
    simp only [hψ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  have hind : ∀ ν : Fin 3 → F4, ∑ j, ν j • γ j = 0 → ∀ j, ν j = 0 := by
    intro ν hν j
    have h0 : ∑ i, ν i • ψ (γ i) = 0 := by
      rw [← hψlin, hν]; simp [hψ]
    have := congrArg (D.a (wk S (e.succAbove j))) h0
    rw [map_sum, map_zero] at this
    simp only [map_smul, smul_eq_mul, hWψ, hδ, mul_ite, mul_one, mul_zero] at this
    rw [Finset.sum_ite_eq] at this
    simpa using this
  have hγ0 : ∀ j, γ j ≠ 0 := by
    intro j h0
    have := hind (fun i => if i = j then 1 else 0) (by simp [h0]) j
    simp at this
  choose μ hμ hdir hvec using fun j => dir_of_ne_zero (hγ0 j)
  set c : Fin 3 → Nat := fun j => smulC (μ j) (encode4 (γ j)) with hc
  set x : Fin 3 → GF := fun j => xcG (mkPCtx p0 p1) (c j) with hx
  have hxe : ∀ j, x j = μ j • ψ (γ j) := by
    intro j
    simp only [hx, hψ, hc]
    rw [xcG_eq _ hXWF, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coordC_smulC _ _ _ (by omega), smul_smul]
    have : coordC (encode4 (γ j)) k = γ j k := congrFun (vec4_encode4 (γ j)) k
    rw [this]
  have hxH : ∀ j, x j ∈ H := by
    intro j
    rw [hxe, hψd]
    exact H.smul_mem _ (H.sub_mem (dd j).2 (span_pq_le S (hπ j)))
  have hWx : ∀ j l, D.a (wk S l) (x j) = μ j * wform S l (dd j) := by
    intro j l; rw [hxe, map_smul, smul_eq_mul, hWψ]
  have hzero : ∀ j k, k ≠ j → D.a (wk S (e.succAbove k)) (x j) = 0 := by
    intro j k hkj; rw [hWx, hδ, if_neg hkj, mul_zero]
  have hcard2 : ∀ l l' : Fin 4, l ≠ l' → ({wk S l, wk S l'} : Finset (Fin 12)).card = 2 :=
    fun l l' h => Finset.card_pair (fun h' => h (wk_inj S h'))
  have hsub2 : ∀ l l' : Fin 4, ({wk S l, wk S l'} : Finset (Fin 12)) ⊆ S.W := by
    intro l l' k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact wk_mem S l
    · rw [Finset.mem_singleton] at hk; rw [hk]; exact wk_mem S l'
  -- the solutions
  set lamOf : Fin 3 → Fin 12 → F4 := fun j k => D.a k (x j) with hlam
  set sol : Fin 3 → Sol := fun j => ⟨c j, F (lamOf j), G0 (lamOf j)⟩ with hsol
  have hE : ∀ j y, Esem (mkPCtx p0 p1) d (sol j) y = Ex S (x j) y := by
    intro j y
    show xcG (mkPCtx p0 p1) (c j) * y + offSem d.off (F (lamOf j)) y +
      blockSem (G0 (lamOf j)) [(d.ga, d.fa), (d.gb, d.fb)] y = _
    rw [add_assoc, hF4, show xcG (mkPCtx p0 p1) (c j) = x j from rfl, V.hD _ (hxH j) y,
      ← Finset.sum_add_sum_compl S.W]
    unfold Ex
    simp only [mul_smul, hlam]
    rw [add_assoc, GF_add_self, add_zero]
  set es : Fin 3 → SolE := fun j => withE (mkPCtx p0 p1) d (sol j) with hes
  have hvert : ∀ j, (Wset S (x j)).card ≤ 2 := by
    intro j
    obtain ⟨k1, k2, hk12, hk1, hk2⟩ := other_two j
    have h1 := Wset_card_le S (x j) (hsub2 (e.succAbove k1) (e.succAbove k2)) (by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hzero j k1 hk1
      · rw [Finset.mem_singleton] at hk; rw [hk]; exact hzero j k2 hk2)
    rw [hcard2 _ _ (fun h => hk12 (Fin.succAbove_right_injective h))] at h1
    omega
  have hmem : ∀ j, es j ∈ allSols (mkPCtx p0 p1) d := by
    intro j
    exact sol_complete (mkPCtx p0 p1) hXWF d hd (sol j) (hdir j) (hF1 _) (hF2 _) (hF3 _).1 (hF3 _).2
      (W := Wspan S (x j)) ((finrank_Wspan S (x j)).trans (hvert j)) (fun y => by rw [hE]; exact Ex_mem S _ y)
  -- the directions are independent
  have hvc : ∀ j, vec4 (c j) = μ j • γ j := hvec
  have hcne : ∀ a b, a ≠ b → (es a).s.c ≠ (es b).s.c := by
    intro a b hab heq
    obtain ⟨k, hka, hkb⟩ := third_exists a b hab
    have hv := congrArg vec4 heq
    change vec4 (c a) = vec4 (c b) at hv
    rw [hvc, hvc] at hv
    have := hind (fun i => if i = a then μ a else if i = b then μ b else 0) (by
      rw [sum_three _ hab (Ne.symm hka) (Ne.symm hkb)]
      simp only [↓reduceIte, if_neg hab.symm, if_neg hka, if_neg hkb, zero_smul, add_zero]
      rw [hv, vec4_add_self] ) a
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
    have hv := congrArg vec4 hab'
    rw [vec4_xor_smul] at hv
    change coordC ab 0 • vec4 (c a) + coordC ab 1 • vec4 (c b) = vec4 (c k) at hv
    rw [hvc, hvc, hvc] at hv
    have := hind (fun i => if i = a then coordC ab 0 * μ a else if i = b then coordC ab 1 * μ b else μ k)
      (by
        rw [sum_three _ hab hak hbk]
        simp only [↓reduceIte, if_neg hab.symm, if_neg hak.symm, if_neg hbk.symm]
        rw [mul_smul, mul_smul, hv, vec4_add_self]) k
    simp only [if_neg hak.symm, if_neg hbk.symm] at this
    exact hμ k this
  -- the edges
  set fl : Fin 3 → Fin 3 → Bool := fun a b =>
    ([o, w, w2].map fun lam => rankC (addCols lam (es b).cols (es a).cols)).any (· ≤ 2) with hfl
  have hrank : ∀ (a b : Fin 3) (lam : F4), rankC (addCols lam (es b).cols (es a).cols) ≤ (Wset S (x a + lam • x b)).card :=
    fun a b lam => (rk_addCols_le (mkPCtx p0 p1) hXWF d (sol a) (sol b) lam (W := Wspan S (x a + lam • x b))
      (fun y => by rw [hE, hE, Ex_add_smul]; exact Ex_mem S _ y)).trans (finrank_Wspan S _)
  have hzero_line : ∀ (a b k : Fin 3) (lam : F4), k ≠ a → k ≠ b → D.a (wk S (e.succAbove k)) (x a + lam • x b) = 0 := by
    intro a b k lam hka hkb
    rw [map_add, map_smul, smul_eq_mul, hzero a k hka, hzero b k hkb, mul_zero, add_zero]
  have hedge : ∀ a b, a ≠ b → edge d (es a) (es b) = some (fl a b) := by
    intro a b hab
    unfold edge
    rw [if_neg (by rw [beq_iff_eq]; exact hcne a b hab)]
    have hcomm := hF5 (lamOf a) (lamOf b) (c a) (c b)
    rw [if_neg (by
      show ¬ ((!((pairOps d (sol a)).zip (pairOps d (sol b))).all fun (G, H) => comm2 G H) = true)
      rw [hcomm]; simp)]
    simp only
    rw [if_pos]
    rw [List.all_eq_true]
    intro r hr
    obtain ⟨lam, -, rfl⟩ := List.mem_map.mp hr
    obtain ⟨k, hka, hkb⟩ := third_exists a b hab
    have h1 := Wset_card_le S (x a + lam • x b) (Z := {wk S (e.succAbove k)})
      (Finset.singleton_subset_iff.mpr (wk_mem S _)) (by
        intro k' hk'; rw [Finset.mem_singleton] at hk'; rw [hk']; exact hzero_line a b k lam hka hkb)
    rw [Finset.card_singleton] at h1
    have := hrank a b lam
    simp only [decide_eq_true_eq]
    omega
  have hpass : ∀ a b k, a ≠ b → a ≠ k → b ≠ k →
      triPass (es a) (es b) (es k) (fl a b) (fl a k) (fl b k) = true := by
    intro a b k hab hak hbk
    rcases halt with ⟨j0, hj0⟩ | hB
    · -- a vertex of rank ≤ 1
      have hrk : (es j0).rk ≤ 1 := by
        obtain ⟨k1, k2, hk12, hk1, hk2⟩ := other_two j0
        have hne1 : e.succAbove k1 ≠ e.succAbove k2 := fun h => hk12 (Fin.succAbove_right_injective h)
        have h1 := Wset_card_le S (x j0)
          (Z := {wk S (e.succAbove k1), wk S (e.succAbove k2), wk S e}) (by
            intro k' hk'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
            rcases hk' with rfl | rfl | rfl <;> exact wk_mem S _) (by
            intro k' hk'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
            rcases hk' with rfl | rfl | rfl
            · exact hzero j0 k1 hk1
            · exact hzero j0 k2 hk2
            · rw [hWx, hj0, mul_zero])
        have hc3 : ({wk S (e.succAbove k1), wk S (e.succAbove k2), wk S e} : Finset (Fin 12)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair]
          · exact fun h => (Fin.succAbove_ne e k2) (wk_inj S h)
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => hne1 (wk_inj S h), fun h => (Fin.succAbove_ne e k1) (wk_inj S h)⟩
        rw [hc3] at h1
        exact (rk_le (mkPCtx p0 p1) hXWF d (sol j0) (W := Wspan S (x j0))
          (fun y => by rw [hE]; exact Ex_mem S _ y)).trans ((finrank_Wspan S _).trans (by omega))
      unfold triPass
      rcases one_of_three a b k j0 hab hak hbk with rfl | rfl | rfl <;> simp [hrk]
    · -- every edge has an interior point of rank ≤ 2
      have hint : ∀ a b, a ≠ b → fl a b = true := by
        intro a b hab
        obtain ⟨cc, hcc, hw0⟩ := hB a b hab
        obtain ⟨k, hka, hkb⟩ := third_exists a b hab
        set lam := cc * μ a * (μ b)⁻¹ with hlamdef
        have hlam0 : lam ≠ 0 := mul_ne_zero (mul_ne_zero hcc (hμ a)) (inv_ne_zero (hμ b))
        have hze : D.a (wk S e) (x a + lam • x b) = 0 := by
          rw [map_add, map_smul, smul_eq_mul, hWx, hWx]
          have : wform S e (dd a + cc • dd b) = wform S e (dd a) + cc * wform S e (dd b) := by
            rw [map_add, map_smul, smul_eq_mul]
          rw [this] at hw0
          have hlm : lam * μ b = cc * μ a := by
            rw [hlamdef, mul_assoc, inv_mul_cancel₀ (hμ b), mul_one]
          calc μ a * wform S e (dd a) + lam * (μ b * wform S e (dd b))
              = μ a * wform S e (dd a) + (lam * μ b) * wform S e (dd b) := by ring
            _ = μ a * (wform S e (dd a) + cc * wform S e (dd b)) := by rw [hlm]; ring
            _ = 0 := by rw [hw0, mul_zero]
        have hne : e.succAbove k ≠ e := Fin.succAbove_ne e k
        have h1 := Wset_card_le S (x a + lam • x b) (hsub2 (e.succAbove k) e) (by
          intro k' hk'
          rcases Finset.mem_insert.mp hk' with rfl | hk'
          · exact hzero_line a b k lam hka hkb
          · rw [Finset.mem_singleton] at hk'; rw [hk']; exact hze)
        rw [hcard2 _ _ hne] at h1
        have := hrank a b lam
        simp only [hfl, List.any_eq_true, List.mem_map, decide_eq_true_eq]
        exact ⟨_, ⟨lam, F4_ne_zero_mem lam hlam0, rfl⟩, by omega⟩
      unfold triPass
      simp [hint a b hab, hint a k hak, hint b k hbk]
  exact triFree_false_of_three d _ es hmem hcne fl hedge hspan hpass

/-! ### The bridge -/

lemma pList_lt : ∀ P : Nat × Nat, P ∈ pList → P.1 < 4096 ∧ P.2 < 4096 := by decide

lemma sList_lt : ∀ S : Nat × Nat, S ∈ sList → S.1 < 4096 ∧ S.2 < 4096 := by decide

/-- L7-L10: a decomposition in normal form makes its case's check fail. This is `Mu4.Final.BridgeMath`. -/
theorem bridgeMath_holds : ∀ P : Nat × Nat, P ∈ pList → ∀ S : Nat × Nat, S ∈ sList →
    ∀ mult ws : List Nat, (mkPCtx P.1 P.2).ok = true →
    ∀ H : Submodule F4 GF, finrank F4 H = 5 → ∀ D : Decomp 12, D.ValidOn H →
      NF P.1 P.2 S.1 S.2 mult ws D H → caseOK (mkPCtx P.1 P.2) S.1 S.2 mult ws = false := by
  intro P hP S hS mult ws hok H hH D hD nf
  have hPb := pList_lt P hP
  have hSb := sList_lt S hS
  unfold caseOK
  cases hsc : setupCase (mkPCtx P.1 P.2) S.1 S.2 mult ws with
  | invalid => exact absurd hsc (setupCase_ne_invalid nf hD hPb.1 hPb.2 hSb.1 hSb.2)
  | error => rfl
  | valid d =>
    simp only
    cases hwf : wfCheck d with
    | false => rfl
    | true =>
      obtain ⟨V⟩ := vctx_of nf hD hPb.1 hPb.2 hSb.1 hSb.2 hsc
      rw [triFree_false_valid V hH hok hwf]
      rfl

end Mu4.Bridge
