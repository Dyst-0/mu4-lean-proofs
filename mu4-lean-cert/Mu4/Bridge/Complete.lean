import Mu4.Bridge.Coef

/-!
# Completeness of the direction search (`audit/PROOF.md`, L10, first half)

For a valid case `d` and a solution `s` (normalized direction, diagonalizable operators, and
`rank E ≤ 2`), `s` appears in `allSols X d`.
-/

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower

/-! ### The direction element and the columns of the `t_k` -/

lemma tcols_getD (X : PCtx) (hX : PCtxWF X) (k : Nat) (hk : k < 4) :
    X.tcols.getD k [] = (List.range 6).map fun l => mulK (X.tv.getD k 0) (eC l) := by
  rw [hX.tcols]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, show k < X.tv.length by rw [hX.tv4]; exact hk]

lemma decode_applyCols_t (X : PCtx) (hX : PCtxWF X) (k : Nat) (hk : k < 4) (y : Nat) :
    decode (applyCols (X.tcols.getD k []) y) = decode (X.tv.getD k 0) * decode y := by
  rw [tcols_getD X hX k hk]
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil]
  rw [decode_applyCols6, decode_eq_sum_eC y, Finset.mul_sum, Fin.sum_univ_six]
  simp only [decode_mulK, mul_smul_comm]
  rfl

lemma xcG_eq (X : PCtx) (hX : PCtxWF X) (c : Nat) :
    xcG X c = ∑ k : Fin 4, coordC c k • decode (X.tv.getD k 0) := by
  rw [xcG, PCtx.xc, decode_combo]
  have h4 := hX.tv4
  rw [Fintype.sum_equiv (finCongr h4) _ (fun k : Fin 4 => coordC c k • decode (X.tv.getD k 0))]
  intro k
  simp [List.getD_eq_getElem?_getD, List.get_eq_getElem]

/-! ### The subspace `Y1 = span(bY)` -/

/-- `ψ u = ∑_k u_k bY_k`. -/
def psiLin (d : CaseData) : (Fin 4 → F4) →ₗ[F4] GF where
  toFun u := ∑ k : Fin 4, u k • decode (d.bY.getD k 0)
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.smul_sum, mul_smul]

lemma decode_combo4_bY (d : CaseData) (hd : CaseWF d) (K : Nat) :
    decode (combo4 K d.bY) = psiLin d (vec4 K) := by
  have h4 := hd.bY4
  match hb : d.bY, h4 with
  | [b0, b1, b2, b3], _ =>
    rw [decode_combo4]
    simp [psiLin, vec4, Fin.sum_univ_four, hb]

lemma bY_getD_mem (d : CaseData) (hd : CaseWF d) (k : Fin 4) : d.bY.getD k 0 ∈ d.bY := by
  rw [List.getD_eq_getElem _ _ (by rw [hd.bY4]; exact k.isLt)]
  exact List.getElem_mem _

lemma fa_psi (d : CaseData) (hd : CaseWF d) (u : Fin 4 → F4) :
    formC d.fa (psiLin d u) = 0 ∧ formC d.fb (psiLin d u) = 0 := by
  simp only [psiLin, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, smul_eq_mul]
  constructor
  · apply Finset.sum_eq_zero; intro k _
    rw [← dotC_eq, (hd.bYker _ (bY_getD_mem d hd k)).1, mul_zero]
  · apply Finset.sum_eq_zero; intro k _
    rw [← dotC_eq, (hd.bYker _ (bY_getD_mem d hd k)).2, mul_zero]

/-- The block at `m0` vanishes on `Y1`. -/
lemma blockSem_m0_psi (d : CaseData) (hd : CaseWF d) (G : Nat) (u : Fin 4 → F4) :
    blockSem G [(d.ga, d.fa), (d.gb, d.fb)] (psiLin d u) = 0 := by
  obtain ⟨h1, h2⟩ := fa_psi d hd u
  simp [blockSem, h1, h2]

lemma blockSem_m0_ea (d : CaseData) (hd : CaseWF d) (G : Nat) :
    blockSem G [(d.ga, d.fa), (d.gb, d.fb)] (decode d.ea) =
      m00 G • decode d.ga + m10 G • decode d.gb := by
  have h1 : formC d.fa (decode d.ea) = 1 := by rw [← dotC_eq]; exact hd.eaf.1
  have h2 : formC d.fb (decode d.ea) = 0 := by rw [← dotC_eq]; exact hd.eaf.2
  simp [blockSem, h1, h2]

lemma blockSem_m0_eb (d : CaseData) (hd : CaseWF d) (G : Nat) :
    blockSem G [(d.ga, d.fa), (d.gb, d.fb)] (decode d.eb) =
      m01 G • decode d.ga + m11 G • decode d.gb := by
  have h1 : formC d.fa (decode d.eb) = 0 := by rw [← dotC_eq]; exact hd.ebf.1
  have h2 : formC d.fb (decode d.eb) = 1 := by rw [← dotC_eq]; exact hd.ebf.2
  simp [blockSem, h1, h2]

/-! ### GF(4)^4 codes -/

lemma encode4_lt (v : Fin 4 → F4) : encode4 v < 256 := by
  have e : (256 : Nat) = 2 ^ 8 := by norm_num
  rw [e]
  apply xorFin_lt
  intro k
  have := unitC_lt (v k) k
  have hk := k.isLt
  have : 4 ^ (k.val + 1) ≤ 2 ^ 8 := by
    calc 4 ^ (k.val + 1) ≤ 4 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ 8 := by norm_num
  show unitC (v k) k < 2 ^ 8
  omega

lemma coordC_mod256 (x k : Nat) (hk : k < 4) : coordC (x % 256) k = coordC x k := by
  have e : (256 : Nat) = 2 ^ 8 := by norm_num
  simp only [coordC, e, Nat.testBit_mod_two_pow]
  simp [show 2 * k < 8 by omega, show 2 * k + 1 < 8 by omega]

lemma ab_mat2 : ∀ ab < 16, ab = mat2 (coordC ab 0) (coordC ab 1) 0 0 := by decide

lemma indep4_of_li {u u' : Fin 4 → F4} (h : LinearIndependent F4 ![u, u']) :
    indep4 (encode4 u) (encode4 u') = true := by
  unfold indep4
  rw [List.all_eq_true]
  intro ab hab
  rw [List.mem_range] at hab
  by_cases h0 : ab = 0
  · simp [h0]
  · rw [beq_false_of_ne h0, Bool.false_or, bne_iff_ne, ne_eq]
    intro hw
    have hv : vec4 (smulC (coordC ab 0) (encode4 u) ^^^ smulC (coordC ab 1) (encode4 u')) = 0 := by
      funext k
      rw [show vec4 _ k = coordC _ k.val from rfl, ← coordC_mod256 _ _ k.isLt, hw]
      simp
    rw [vec4_xor_smul, vec4_encode4, vec4_encode4] at hv
    obtain ⟨ha, hb⟩ := (LinearIndependent.pair_iff.mp h) _ _ hv
    apply h0
    rw [ab_mat2 ab hab, ha, hb]; rfl

/-! ### The kernel step: a reduced echelon pair inside `ker E ∩ Y1` -/

theorem exists_K (X : PCtx) (d : CaseData) (hd : CaseWF d) (s : Sol) {W : Submodule F4 GF}
    (hW : Module.finrank F4 W ≤ 2) (hE : ∀ y, Esem X d s y ∈ W) :
    ∃ K ∈ rrefPairs, Esem X d s (decode (combo4 K.1 d.bY)) = 0 ∧
      Esem X d s (decode (combo4 K.2 d.bY)) = 0 := by
  let φ := (Elin X d s).comp (psiLin d)
  have hr : Module.finrank F4 (LinearMap.range φ) ≤ 2 := by
    have : LinearMap.range φ ≤ W := by rintro _ ⟨u, rfl⟩; exact hE _
    exact (Submodule.finrank_mono this).trans hW
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [Module.finrank_fin_fun] at hrn
  obtain ⟨u, u', hu, hu', hind⟩ := exists_pair_of_two_le' (V := LinearMap.ker φ) (by omega)
  have hcov := rref_cover
  unfold rrefCoverOK at hcov
  rw [List.all_eq_true] at hcov
  have h1 := hcov (encode4 u) (List.mem_range.mpr (encode4_lt u))
  rw [List.all_eq_true] at h1
  have h2 := h1 (encode4 u') (List.mem_range.mpr (encode4_lt u'))
  rw [indep4_of_li hind, Bool.not_true, Bool.false_or, List.any_eq_true] at h2
  obtain ⟨K, hK, hKs⟩ := h2
  rw [Bool.and_eq_true] at hKs
  have inker : ∀ c, inSpan2 (encode4 u) (encode4 u') c = true → Esem X d s (psiLin d (vec4 c)) = 0 := by
    intro c hc
    unfold inSpan2 at hc
    rw [List.any_eq_true] at hc
    obtain ⟨ab, -, hab⟩ := hc
    rw [beq_iff_eq] at hab
    rw [← hab, vec4_xor_smul, vec4_encode4, vec4_encode4]
    have : coordC ab 0 • u + coordC ab 1 • u' ∈ LinearMap.ker φ :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hu')
    exact LinearMap.mem_ker.mp this
  refine ⟨K, hK, ?_, ?_⟩
  · rw [decode_combo4_bY d hd]; exact inker _ hKs.1
  · rw [decode_combo4_bY d hd]; exact inker _ hKs.2

/-! ### Keys and tables -/

lemma GF_add_self (x : GF) : x + x = 0 := by
  ext l; simp only [GF.add_v, Pi.add_apply, GF.zero_v, Pi.zero_apply]; exact F4.add_self _

lemma eq_of_add_eq_zero' {x y : GF} (h : x + y = 0) : x = y := by
  have := congrArg (· + y) h
  simpa [add_assoc, GF_add_self] using this

lemma sum_c_ty (X : PCtx) (hX : PCtxWF X) (c y : Nat) :
    ∑ k : Fin 4, coordC c k • decode (applyCols (X.tcols.getD k []) y) = xcG X c * decode y := by
  rw [xcG_eq X hX c, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [decode_applyCols_t X hX k k.isLt, smul_mul_assoc]

/-- The values `t_k y` computed by `solsK`. -/
def tyList (X : PCtx) (y1 y2 : Nat) : List (Nat × Nat) :=
  X.tcols.map fun tc => (applyCols tc y1, applyCols tc y2)

lemma tyList_eq (X : PCtx) (hX : PCtxWF X) (y1 y2 : Nat) :
    tyList X y1 y2 = (List.range 4).map fun k =>
      (applyCols (X.tcols.getD k []) y1, applyCols (X.tcols.getD k []) y2) := by
  have h4 : X.tcols.length = 4 := by rw [hX.tcols, List.length_map, hX.tv4]
  apply List.ext_getElem
  · simp [tyList, h4]
  · intro n h1 h2
    simp [tyList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < X.tcols.length by
      simp [tyList] at h1; omega)]

/-- Coordinate `l` of `combo4 c` of four keys. -/
lemma coordC_combo4_keys (c : Nat) (f : Nat → Nat) (l : Nat) (hl : l < 32) :
    coordC (combo4 c ((List.range 4).map f)) l = ∑ k : Fin 4, coordC c k * coordC (f k) l := by
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, combo4, coordC_xor,
    coordC_smulC _ _ _ hl, Fin.sum_univ_four]
  rfl

/-- The key of the right-hand side equals the key of `G B` (pair block). -/
lemma key_eq_pair (X : PCtx) (hX : PCtxWF X) (d : CaseData) (hd : CaseWF d) (c : Nat)
    (goff : List Nat) (hg : goff.length = d.off.length) (y1 y2 : Nat)
    (h1 : E0sem X d c goff (decode y1) = 0) (h2 : E0sem X d c goff (decode y2) = 0)
    {i : Nat} (hi : i < d.off.length) {g0 f0 g1 f1 : Nat} (hb : blkOf d i = [(g0, f0), (g1, f1)])
    {r0 r1 : Nat} (hr : d.rhoOff.getD i [] = [r0, r1]) :
    combo4 c ((tyList X y1 y2).map fun x => keyR [r0, r1] x.1 x.2) =
      keyGB true (dotC f0 y1) (dotC f0 y2) (dotC f1 y1) (dotC f1 y2) (goff.getD i 0) := by
  have e1 := eq_of_add_eq_zero' h1
  have e2 := eq_of_add_eq_zero' h2
  have hu0 : (0 : Nat) < (blkOf d i).length := by rw [hb]; simp
  have hu1 : (1 : Nat) < (blkOf d i).length := by rw [hb]; simp
  have c00 := rho_offSem d hd goff hg (decode y1) hi hu0
  have c01 := rho_offSem d hd goff hg (decode y2) hi hu0
  have c10 := rho_offSem d hd goff hg (decode y1) hi hu1
  have c11 := rho_offSem d hd goff hg (decode y2) hi hu1
  simp only [rhoOf, hr, List.getD_cons_zero, List.getD_cons_succ, hb, coefS, if_true,
    show (1 : Nat) ≠ 0 by omega, if_false] at c00 c01 c10 c11
  rw [← e1] at c00 c10
  rw [← e2] at c01 c11
  rw [← sum_c_ty X hX c y1, map_sum] at c00 c10
  rw [← sum_c_ty X hX c y2, map_sum] at c01 c11
  apply code_ext (n := 4) (combo4_lt _ _ (fun (k : Nat)
      (hk : k ∈ (tyList X y1 y2).map fun x => keyR [r0, r1] x.1 x.2) => by
        rw [List.mem_map] at hk; obtain ⟨x, -, rfl⟩ := hk; exact keyR_lt _ _ _))
    (by have := keyGB_lt true (dotC f0 y1) (dotC f0 y2) (dotC f1 y1) (dotC f1 y2) (goff.getD i 0)
        norm_num at this ⊢; exact this)
  intro l hl
  rw [tyList_eq X hX, List.map_map, coordC_combo4_keys _ _ _ (by omega)]
  simp only [Function.comp_def]
  simp only [map_smul, smul_eq_mul] at c00 c01 c10 c11
  interval_cases l
  · simp only [(coordC_keyR_pair _ _ _ _).1, keyGB, if_true, coordC_mat2_0, dotC_eq]
    rw [← c00]
  · simp only [(coordC_keyR_pair _ _ _ _).2.1, keyGB, if_true, coordC_mat2_1, dotC_eq]
    rw [← c01]
  · simp only [(coordC_keyR_pair _ _ _ _).2.2.1, keyGB, if_true, coordC_mat2_2, dotC_eq]
    rw [← c10]
  · simp only [(coordC_keyR_pair _ _ _ _).2.2.2, keyGB, if_true, coordC_mat2_3, dotC_eq]
    rw [← c11]

/-- The key of the right-hand side equals the key of `G B` (single block). -/
lemma key_eq_single (X : PCtx) (hX : PCtxWF X) (d : CaseData) (hd : CaseWF d) (c : Nat)
    (goff : List Nat) (hg : goff.length = d.off.length) (y1 y2 : Nat)
    (h1 : E0sem X d c goff (decode y1) = 0) (h2 : E0sem X d c goff (decode y2) = 0)
    {i : Nat} (hi : i < d.off.length) {g0 f0 : Nat} (hb : blkOf d i = [(g0, f0)])
    {r0 : Nat} (hr : d.rhoOff.getD i [] = [r0]) :
    combo4 c ((tyList X y1 y2).map fun x => keyR [r0] x.1 x.2) =
      keyGB false (dotC f0 y1) (dotC f0 y2) 0 0 (goff.getD i 0) := by
  have e1 := eq_of_add_eq_zero' h1
  have e2 := eq_of_add_eq_zero' h2
  have hu0 : (0 : Nat) < (blkOf d i).length := by rw [hb]; simp
  have c00 := rho_offSem d hd goff hg (decode y1) hi hu0
  have c01 := rho_offSem d hd goff hg (decode y2) hi hu0
  simp only [rhoOf, hr, List.getD_cons_zero, hb, coefS] at c00 c01
  rw [← e1, ← sum_c_ty X hX c y1, map_sum] at c00
  rw [← e2, ← sum_c_ty X hX c y2, map_sum] at c01
  apply code_ext (n := 4) (combo4_lt _ _ (fun (k : Nat)
      (hk : k ∈ (tyList X y1 y2).map fun x => keyR [r0] x.1 x.2) => by
        rw [List.mem_map] at hk; obtain ⟨x, -, rfl⟩ := hk; exact keyR_lt _ _ _))
    (by have := keyGB_lt false (dotC f0 y1) (dotC f0 y2) 0 0 (goff.getD i 0)
        norm_num at this ⊢; exact this)
  intro l hl
  simp only [map_smul, smul_eq_mul] at c00 c01
  have hL : coordC (combo4 c ((tyList X y1 y2).map fun x => keyR [r0] x.1 x.2)) l =
      (if l = 0 then ∑ k : Fin 4, coordC c k * formC r0 (decode (applyCols (X.tcols.getD k []) y1))
        else 0) +
      (if l = 1 then ∑ k : Fin 4, coordC c k * formC r0 (decode (applyCols (X.tcols.getD k []) y2))
        else 0) := by
    rw [tyList_eq X hX, List.map_map, coordC_combo4_keys _ _ _ (by omega)]
    simp only [Function.comp_def, coordC_keyR_single, dotC_eq, mul_add, Finset.sum_add_distrib]
    by_cases h0 : l = 0
    · subst h0; simp
    · by_cases h1 : l = 1
      · subst h1; simp
      · simp [h0, h1]
  have hR : coordC (keyGB false (dotC f0 y1) (dotC f0 y2) 0 0 (goff.getD i 0)) l =
      (if l = 0 then coordC (goff.getD i 0) 0 * formC f0 (decode y1) else 0) +
      (if l = 1 then coordC (goff.getD i 0) 0 * formC f0 (decode y2) else 0) := by
    simp only [keyGB, Bool.false_eq_true, if_false, coordC_xor, coordC_unitC, dotC_eq]
    by_cases h0 : l = 0
    · subst h0; simp
    · by_cases h1 : l = 1
      · subst h1; simp
      · simp [h0, h1, Ne.symm h0, Ne.symm h1]
  rw [hL, hR, c00, c01]

/-! ### Candidates and choices -/

lemma mem_choices (cands : List (List Nat)) (goff : List Nat) (hlen : goff.length = cands.length)
    (h : ∀ i < goff.length, goff.getD i 0 ∈ cands.getD i []) : goff ∈ choices cands := by
  induction cands generalizing goff with
  | nil =>
    match goff with
    | [] => simp [choices]
    | _ :: _ => simp at hlen
  | cons l ls ih =>
    match goff with
    | [] => simp at hlen
    | x :: xs =>
      simp only [choices, List.mem_flatMap, List.mem_map]
      refine ⟨x, ?_, xs, ih xs (by simpa using hlen) (fun i hi => ?_), rfl⟩
      · have := h 0 (by simp); simpa using this
      · have := h (i + 1) (by simp; omega); simpa using this

lemma candsAt_spec (tbls : List (Array (List Nat))) (keysT : List (List Nat)) (c : Nat)
    (goff : List Nat) (h1 : tbls.length = goff.length) (h2 : keysT.length = goff.length)
    (hmem : ∀ i < goff.length,
      goff.getD i 0 ∈ (tbls.getD i #[]).getD (combo4 c (keysT.getD i [])) []) :
    ∃ cands, candsAt tbls keysT c = some cands ∧ goff ∈ choices cands := by
  induction goff generalizing tbls keysT with
  | nil =>
    match tbls, keysT, h1, h2 with
    | [], [], _, _ => exact ⟨[], rfl, by simp [choices]⟩
  | cons x xs ih =>
    match tbls, keysT, h1, h2 with
    | tb :: tbls, ks :: keysT, h1, h2 =>
      have hx : x ∈ tb.getD (combo4 c ks) [] := by have := hmem 0 (by simp); simpa using this
      obtain ⟨cs, hcs, hxs⟩ := ih tbls keysT (by simpa using h1) (by simpa using h2)
        (fun i hi => by have := hmem (i + 1) (by simp; omega); simpa using this)
      refine ⟨tb.getD (combo4 c ks) [] :: cs, ?_, ?_⟩
      · have hne : (tb.getD (combo4 c ks) []).isEmpty = false := by
          cases hl : tb.getD (combo4 c ks) [] with
          | nil => rw [hl] at hx; simp at hx
          | cons _ _ => rfl
        simp only [candsAt, hne, hcs]
        rfl
      · simp only [choices, List.mem_flatMap, List.mem_map]
        exact ⟨x, hx, xs, hxs, rfl⟩

lemma blk_shape (d : CaseData) (hd : CaseWF d) {i : Nat} (hi : i < d.off.length) :
    (∃ g0 f0 g1 f1 r0 r1, blkOf d i = [(g0, f0), (g1, f1)] ∧ d.rhoOff.getD i [] = [r0, r1]) ∨
    (∃ g0 f0 r0, blkOf d i = [(g0, f0)] ∧ d.rhoOff.getD i [] = [r0]) := by
  have hs := hd.shape i hi
  have hr := hd.rhoShape i hi
  rcases hs with h1 | h2
  · right
    match hb : blkOf d i, h1, hrr : d.rhoOff.getD i [], hr with
    | [(g0, f0)], _, [r0], _ => exact ⟨g0, f0, r0, rfl, rfl⟩
  · left
    match hb : blkOf d i, h2, hrr : d.rhoOff.getD i [], hr with
    | [(g0, f0), (g1, f1)], _, [r0, r1], _ => exact ⟨g0, f0, g1, f1, r0, r1, rfl, rfl⟩

/-- Each off-block operator of a solution is found in its table. -/
lemma goff_mem_table (X : PCtx) (hX : PCtxWF X) (d : CaseData) (hd : CaseWF d) (c : Nat)
    (goff : List Nat) (hg : goff.length = d.off.length) (y1 y2 : Nat)
    (h1 : E0sem X d c goff (decode y1) = 0) (h2 : E0sem X d c goff (decode y2) = 0)
    {i : Nat} (hi : i < d.off.length) (hcand : goff.getD i 0 ∈ candOps (blkOf d i)) :
    goff.getD i 0 ∈ (mkTable (blkOf d i) y1 y2).getD
      (combo4 c ((tyList X y1 y2).map fun x => keyR (d.rhoOff.getD i []) x.1 x.2)) [] := by
  rcases blk_shape d hd hi with ⟨g0, f0, g1, f1, r0, r1, hb, hr⟩ | ⟨g0, f0, r0, hb, hr⟩
  · rw [hr, key_eq_pair X hX d hd c goff hg y1 y2 h1 h2 hi hb hr, hb, mkTable_pair]
    rw [hb] at hcand
    exact mem_tableOf true _ _ _ _ (by simpa [candOps] using hcand)
  · rw [hr, key_eq_single X hX d hd c goff hg y1 y2 h1 h2 hi hb hr, hb, mkTable_single]
    rw [hb] at hcand
    exact mem_tableOf false _ _ _ _ (by simpa [candOps] using hcand)

/-! ### Decoding the vectors of the search -/

lemma decode_offContrib (off : List (Nat × List Term)) (goff : List Nat)
    (hg : goff.length = off.length) (y : Nat) :
    decode (offContrib (off.map (·.2)) goff ((off.map (·.2)).map fun ts => entriesAt ts y)) =
      offSem off goff (decode y) := by
  induction off generalizing goff with
  | nil => simp [offContrib, offSem]
  | cons b off ih =>
    match goff, hg with
    | G :: goff, hg =>
      simp only [List.map_cons, offContrib, decode_xor, applyGE_entriesAt, decode_applyG]
      rw [ih goff (by simpa using hg)]
      simp [offSem]

/-- The `E0` value computed by `solsGoff` at a vector `y`. -/
def e0Code (X : PCtx) (d : CaseData) (c : Nat) (goff : List Nat) (y : Nat) : Nat :=
  applyCols (X.xcCols c) y ^^^ offContrib (d.off.map (·.2)) goff
    ((d.off.map (·.2)).map fun ts => entriesAt ts y)

lemma decode_e0Code (X : PCtx) (hX : PCtxWF X) (d : CaseData) (c : Nat) (goff : List Nat)
    (hg : goff.length = d.off.length) (y : Nat) :
    decode (e0Code X d c goff y) = E0sem X d c goff (decode y) := by
  rw [e0Code, decode_xor, decode_applyCols_xc X hX, decode_offContrib _ _ hg]
  rfl

lemma Esem_eq (X : PCtx) (d : CaseData) (s : Sol) (y : GF) :
    Esem X d s y = E0sem X d s.c s.goff y + blockSem s.g0 [(d.ga, d.fa), (d.gb, d.fb)] y := rfl

lemma blockSem_m0_mem (d : CaseData) (G : Nat) (y : GF) :
    ∃ α β : F4, blockSem G [(d.ga, d.fa), (d.gb, d.fb)] y = α • decode d.ga + β • decode d.gb :=
  ⟨_, _, rfl⟩

lemma pivW_echelon (d : CaseData) : Echelon (pivW d) :=
  foldl_insertPivot_echelon [d.ga, d.gb] [] trivial

lemma redLin_kills_m0 (d : CaseData) (G : Nat) (y : GF) :
    redLin (pivW d) (blockSem G [(d.ga, d.fa), (d.gb, d.fb)] y) = 0 := by
  obtain ⟨α, β, h⟩ := blockSem_m0_mem d G y
  have hpos := echelon_pos _ (pivW_echelon d)
  obtain ⟨ka, kb⟩ := pivW_kills d
  rw [decode_reduceBy _ hpos] at ka kb
  rw [h, map_add, map_smul, map_smul, ka, kb, smul_zero, smul_zero, add_zero]

/-- The pivot positions of an RREF pair are distinct and `< 4`. -/
lemma pivots_rref {K : Nat × Nat} (hK : K ∈ rrefPairs) :
    (pivots K).1 < (pivots K).2 ∧ (pivots K).2 < 4 := by
  simp only [rrefPairs, List.mem_flatMap, List.mem_filterMap, List.mem_range] at hK
  obtain ⟨r0, -, r1, -, hr⟩ := hK
  split at hr
  · rename_i p q hp hq
    split_ifs at hr with hc
    simp only [Option.some.injEq] at hr
    subst hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    simp only [pivots, hp, hq, Option.getD_some]
    exact ⟨hc.1.1.1, (firstNZ_some hq).2.1⟩
  · simp at hr

/-- The vectors `es` of `solsK`: two vectors of `bY`, then `ea`, `eb`. -/
lemma es_shape (d : CaseData) (hd : CaseWF d) {K : Nat × Nat} (hK : K ∈ rrefPairs) :
    ∃ a b, a ∈ d.bY ∧ b ∈ d.bY ∧
      ((List.range 4).filter fun i => i != (pivots K).1 && i != (pivots K).2).map
        (fun i => d.bY.getD i 0) ++ [d.ea, d.eb] = [a, b, d.ea, d.eb] := by
  obtain ⟨hpq, hq4⟩ := pivots_rref hK
  generalize (pivots K).1 = p at hpq
  generalize (pivots K).2 = q at hpq hq4
  have mem : ∀ i < 4, d.bY.getD i 0 ∈ d.bY := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by rw [hd.bY4]; exact hi)]; exact List.getElem_mem _
  have hf : ∃ a b, a < 4 ∧ b < 4 ∧
      ((List.range 4).filter fun i => i != p && i != q) = [a, b] := by
    interval_cases q <;> interval_cases p <;> exact ⟨_, _, by norm_num, by norm_num, rfl⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hf
  exact ⟨d.bY.getD a 0, d.bY.getD b 0, mem a ha, mem b hb, by rw [hab]; rfl⟩

/-! ### Membership, from the inside out -/

lemma mat2_0_0_lt (a b : F4) : mat2 a b 0 0 < 16 := by
  have h0 := unitC_lt a 0
  have h1 := unitC_lt b 1
  have hz : ∀ l, unitC 0 l = 0 := fun l => by simp [unitC, F4.code]
  simp only [mat2, hz, Nat.xor_zero]
  have e : (16 : Nat) = 2 ^ 4 := by norm_num
  rw [e]; exact Nat.xor_lt_two_pow (by omega) (by omega)

lemma mat2_self {G : Nat} (hG : G < 256) : mat2 (m00 G) (m01 G) (m10 G) (m11 G) = G :=
  mat2_ext (mat2_lt _ _ _ _) hG (by simp) (by simp) (by simp) (by simp)

lemma mem_solsColA (d : CaseData) (s : Sol) {pbase : List (Nat × Nat)} (hpb : Echelon pbase)
    {W : Submodule F4 GF} (hW2 : Module.finrank F4 W ≤ 2) (hpbW : pivSpan pbase ≤ W)
    (vea veb : Nat)
    (hvA : decode (vea ^^^ smulC (m00 s.g0) d.ga ^^^ smulC (m10 s.g0) d.gb) ∈ W)
    (hvC : decode (veb ^^^ smulC (m01 s.g0) d.ga ^^^ smulC (m11 s.g0) d.gb) ∈ W)
    (hg0 : s.g0 < 256) (hdiag : diagPred s.g0 = true) :
    s ∈ solsColA d s.c s.goff pbase vea veb (mat2 (m00 s.g0) (m10 s.g0) 0 0) := by
  unfold solsColA
  simp only [coordC_mat2_0, coordC_mat2_1]
  obtain ⟨pA, hpA, rfl⟩ := push2_isSome pbase hpb _ hW2 hpbW hvA
  rw [hpA]
  simp only
  rw [List.mem_filterMap]
  refine ⟨mat2 (m01 s.g0) (m11 s.g0) 0 0, List.mem_range.mpr (mat2_0_0_lt _ _), ?_⟩
  simp only [coordC_mat2_0, coordC_mat2_1]
  have hspan : pivSpan (insertPivot 6 pbase (vea ^^^ smulC (m00 s.g0) d.ga ^^^
      smulC (m10 s.g0) d.gb)) ≤ W := by
    refine (insertPivot_span _ _).trans (sup_le hpbW ?_)
    rw [Submodule.span_le]; rintro _ rfl; exact hvA
  obtain ⟨_, hC, _⟩ := push2_isSome _ (insertPivot_echelon _ hpb _) _ hW2 hspan hvC
  rw [hC, mat2_self hg0, hdiag]
  rfl

lemma zip_map_map {α β γ : Type*} (L : List α) (f : α → β) (g : α → γ) :
    (L.map f).zip (L.map g) = L.map fun y => (f y, g y) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

lemma mem_dedupSols (l : List Sol) (s : Sol) (h : s ∈ l) : s ∈ dedupSols l := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [dedupSols]
    split_ifs with hc
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.contains_iff_mem.mp hc
      · exact ih h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

lemma E0sem_eq (X : PCtx) (d : CaseData) (s : Sol) (y : GF) :
    E0sem X d s.c s.goff y = Esem X d s y + blockSem s.g0 [(d.ga, d.fa), (d.gb, d.fb)] y := by
  rw [Esem_eq, add_assoc, GF_add_self, add_zero]

/-- `solsGoff` finds the solution (for the vectors `es = [a, b, ea, eb]` of `solsK`). -/
lemma mem_solsGoff (X : PCtx) (hX : PCtxWF X) (d : CaseData) (hd : CaseWF d) (s : Sol)
    (hlen : s.goff.length = d.off.length) (hg0 : s.g0 < 256) (hdiag : diagPred s.g0 = true)
    {W : Submodule F4 GF} (hW2 : Module.finrank F4 W ≤ 2) (hE : ∀ y, Esem X d s y ∈ W)
    {a b : Nat} (ha : a ∈ d.bY) (hb : b ∈ d.bY) :
    s ∈ solsGoff d (d.off.map (·.2))
      { es := [a, b, d.ea, d.eb],
        entEs := [a, b, d.ea, d.eb].map fun y => (d.off.map (·.2)).map fun ts => entriesAt ts y,
        entA := (d.off.map (·.2)).map fun ts => entriesAt ts d.ea,
        entB := (d.off.map (·.2)).map fun ts => entriesAt ts d.eb }
      s.c ([a, b, d.ea, d.eb].map (applyCols (X.xcCols s.c))) (applyCols (X.xcCols s.c) d.ea)
      (applyCols (X.xcCols s.c) d.eb) s.goff := by
  have hY : ∀ y ∈ d.bY, E0sem X d s.c s.goff (decode y) = Esem X d s (decode y) := by
    intro y hy
    rw [E0sem_eq]
    have h1 : formC d.fa (decode y) = 0 := by rw [← dotC_eq]; exact (hd.bYker y hy).1
    have h2 : formC d.fb (decode y) = 0 := by rw [← dotC_eq]; exact (hd.bYker y hy).2
    simp [blockSem, h1, h2]
  have he : ∀ y, decode (e0Code X d s.c s.goff y) = E0sem X d s.c s.goff (decode y) :=
    decode_e0Code X hX d s.c s.goff hlen
  have he0 : (([a, b, d.ea, d.eb].map (applyCols (X.xcCols s.c))).zip
      ([a, b, d.ea, d.eb].map fun y => (d.off.map (·.2)).map fun ts => entriesAt ts y)).map
        (fun x => x.1 ^^^ offContrib (d.off.map (·.2)) s.goff x.2) =
      [e0Code X d s.c s.goff a, e0Code X d s.c s.goff b, e0Code X d s.c s.goff d.ea,
        e0Code X d s.c s.goff d.eb] := rfl
  simp only [solsGoff]
  rw [he0]
  -- the reduction filter
  have hpos := echelon_pos _ (pivW_echelon d)
  have hred : ∀ y, decode (reduceBy (pivW d) (e0Code X d s.c s.goff y)) ∈
      W.map (redLin (pivW d)) := by
    intro y
    rw [decode_reduceBy _ hpos, he, E0sem_eq, map_add, redLin_kills_m0, add_zero]
    exact Submodule.mem_map_of_mem (hE _)
  have hW2' : Module.finrank F4 (W.map (redLin (pivW d))) ≤ 2 :=
    (Submodule.finrank_map_le _ _).trans hW2
  obtain ⟨p1, hp1, -, -⟩ := pushAll2_isSome
    ([e0Code X d s.c s.goff a, e0Code X d s.c s.goff b, e0Code X d s.c s.goff d.ea,
      e0Code X d s.c s.goff d.eb].map (reduceBy (pivW d))) [] trivial hW2'
    (by rw [pivSpan, Submodule.span_le]; rintro _ ⟨q, hq, -⟩; simp at hq)
    (by intro v hv
        rw [List.mem_map] at hv
        obtain ⟨y, hy, rfl⟩ := hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl <;> exact hred _)
  rw [hp1]
  -- the base pivots
  obtain ⟨pb, hpb, hech, hspan⟩ := pushAll2_isSome
    [e0Code X d s.c s.goff a, e0Code X d s.c s.goff b] [] trivial hW2
    (by rw [pivSpan, Submodule.span_le]; rintro _ ⟨q, hq, -⟩; simp at hq)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · rw [he, hY a ha]; exact hE _
        · rw [he, hY b hb]; exact hE _)
  rw [show [e0Code X d s.c s.goff a, e0Code X d s.c s.goff b, e0Code X d s.c s.goff d.ea,
      e0Code X d s.c s.goff d.eb].take 2 = [e0Code X d s.c s.goff a, e0Code X d s.c s.goff b]
      from rfl, hpb]
  rw [List.mem_flatMap]
  refine ⟨mat2 (m00 s.g0) (m10 s.g0) 0 0, List.mem_range.mpr (mat2_0_0_lt _ _), ?_⟩
  have hvA : decode (e0Code X d s.c s.goff d.ea ^^^ smulC (m00 s.g0) d.ga ^^^
      smulC (m10 s.g0) d.gb) ∈ W := by
    rw [decode_xor, decode_xor, decode_smulC, decode_smulC, he, add_assoc,
      ← blockSem_m0_ea d hd s.g0, ← Esem_eq]
    exact hE _
  have hvC : decode (e0Code X d s.c s.goff d.eb ^^^ smulC (m01 s.g0) d.ga ^^^
      smulC (m11 s.g0) d.gb) ∈ W := by
    rw [decode_xor, decode_xor, decode_smulC, decode_smulC, he, add_assoc,
      ← blockSem_m0_eb d hd s.g0, ← Esem_eq]
    exact hE _
  exact mem_solsColA d s hech hW2 hspan (e0Code X d s.c s.goff d.ea) (e0Code X d s.c s.goff d.eb)
    hvA hvC hg0 hdiag

/-- The completeness theorem of the direction search. -/
theorem sol_complete (X : PCtx) (hX : PCtxWF X) (d : CaseData) (hd : CaseWF d) (s : Sol)
    (hc : s.c ∈ dirs) (hlen : s.goff.length = d.off.length)
    (hcand : ∀ i < d.off.length, s.goff.getD i 0 ∈ candOps (blkOf d i))
    (hg0 : s.g0 < 256) (hdiag : diagPred s.g0 = true)
    {W : Submodule F4 GF} (hW2 : Module.finrank F4 W ≤ 2) (hE : ∀ y, Esem X d s y ∈ W) :
    withE X d s ∈ allSols X d := by
  obtain ⟨K, hK, hK1, hK2⟩ := exists_K X d hd s hW2 hE
  have hE0y : ∀ K' : Nat, Esem X d s (decode (combo4 K' d.bY)) = 0 →
      E0sem X d s.c s.goff (decode (combo4 K' d.bY)) = 0 := by
    intro K' h
    rw [E0sem_eq, h, decode_combo4_bY d hd, blockSem_m0_psi d hd, add_zero]
  have h1 := hE0y K.1 hK1
  have h2 := hE0y K.2 hK2
  have hsK : s ∈ solsK X d K := by
    obtain ⟨a, b, ha, hb, hes⟩ := es_shape d hd hK
    unfold solsK
    simp only [hes]
    rw [List.mem_flatMap]
    refine ⟨s.c, hc, ?_⟩
    unfold solsKc
    obtain ⟨cands, hcands, hch⟩ := candsAt_spec
      ((d.off.map (·.2)).map fun ts => mkTable ts (combo4 K.1 d.bY) (combo4 K.2 d.bY))
      (d.rhoOff.map fun rhos => (tyList X (combo4 K.1 d.bY) (combo4 K.2 d.bY)).map
        fun x => keyR rhos x.1 x.2) s.c s.goff
      (by simp [hlen]) (by simp [hd.rhoLen, hlen]) (fun i hi => by
        have hi' : i < d.off.length := by omega
        have := goff_mem_table X hX d hd s.c s.goff hlen _ _ h1 h2 hi' (hcand i hi')
        rw [List.getD_eq_getElem _ _ (by simp; exact hi'),
          List.getD_eq_getElem _ _ (by simp [hd.rhoLen]; exact hi')]
        simp only [List.getElem_map]
        rw [List.getD_eq_getElem _ _ (by rw [hd.rhoLen]; exact hi')] at this
        have hblk : blkOf d i = d.off[i].2 := by
          simp only [blkOf, List.getD_eq_getElem _ _ hi']
        rw [hblk] at this
        exact this)
    simp only [tyList] at hcands
    rw [hcands]
    simp only
    rw [List.mem_flatMap]
    exact ⟨s.goff, hch, mem_solsGoff X hX d hd s hlen hg0 hdiag hW2 hE ha hb⟩
  unfold allSols
  rw [List.mem_filter, List.mem_map]
  refine ⟨⟨s, mem_dedupSols _ s (List.mem_flatMap.mpr ⟨K, hK, hsK⟩), rfl⟩, ?_⟩
  simp only [withE, decide_eq_true_eq]
  refine (rankC_le _ (W := W) ?_).trans hW2
  intro v hv
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hv
  rw [decode_Eval X hX]
  exact hE _

end Mu4.Bridge
