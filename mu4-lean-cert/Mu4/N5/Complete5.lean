import Mu4.N5.Coef5
import Mu4.Bridge.Complete

/-!
# mu_4(5): completeness of the direction search (`audit/PROOF.md`, N9)

For a valid case `d` and a solution `s` (normalized direction of `A5/P`, diagonalizable operators, and
`rank E ≤ 1`), `withE5 X d s` appears in `allSols5 X d` (`sol_complete5`). As `Mu4/Bridge/Complete.lean`, with
`K` a 2-dim subspace of the 3-dim `Y` and the echelon pairs of GF(4)^3.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge


/-! ### The direction element and the columns of the `t_k` -/

lemma tcols_getD5 (X : PCtx5) (hX : PCtx5WF X) (k : Nat) (hk : k < 3) :
    X.tcols.getD k [] = (List.range 5).map fun l => mulK5 (X.tv.getD k 0) (eC l) := by
  rw [hX.tcols]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, show k < X.tv.length by rw [hX.tv3]; exact hk]

lemma decode_applyCols_t5 (X : PCtx5) (hX : PCtx5WF X) (k : Nat) (hk : k < 3) (y : Nat) :
    decode5 (applyCols5 (X.tcols.getD k []) y) = decode5 (X.tv.getD k 0) * decode5 y := by
  rw [tcols_getD5 X hX k hk]
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil]
  rw [decode5_applyCols5, decode_eq_sum_eC5 y, Finset.mul_sum, Fin.sum_univ_five]
  simp only [decode5_mulK5, mul_smul_comm]
  rfl

lemma xcG_eq5 (X : PCtx5) (hX : PCtx5WF X) (c : Nat) :
    xcG5 X c = ∑ k : Fin 3, coordC c k • decode5 (X.tv.getD k 0) := by
  rw [xcG5, PCtx5.xc, decode5_combo]
  have h4 := hX.tv3
  rw [Fintype.sum_equiv (finCongr h4) _ (fun k : Fin 3 => coordC c k • decode5 (X.tv.getD k 0))]
  intro k
  simp [List.getD_eq_getElem?_getD, List.get_eq_getElem]

/-! ### The subspace `Y1 = span(bY)` -/

/-- `ψ u = ∑_k u_k bY_k`. -/
def psiLin5 (d : CaseData) : (Fin 3 → F4) →ₗ[F4] GF5 where
  toFun u := ∑ k : Fin 3, u k • decode5 (d.bY.getD k 0)
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.smul_sum, mul_smul]

lemma decode5_combo3_bY (d : CaseData) (hd : CaseWF5 d) (K : Nat) :
    decode5 (combo3 K d.bY) = psiLin5 d (vec3 K) := by
  have h4 := hd.bY3
  match hb : d.bY, h4 with
  | [b0, b1, b2], _ =>
    rw [decode5_combo3]
    simp [psiLin5, vec3, Fin.sum_univ_three, hb]

lemma bY_getD_mem5 (d : CaseData) (hd : CaseWF5 d) (k : Fin 3) : d.bY.getD k 0 ∈ d.bY := by
  rw [List.getD_eq_getElem _ _ (by rw [hd.bY3]; exact k.isLt)]
  exact List.getElem_mem _

lemma fa_psi5 (d : CaseData) (hd : CaseWF5 d) (u : Fin 3 → F4) :
    formC5 d.fa (psiLin5 d u) = 0 ∧ formC5 d.fb (psiLin5 d u) = 0 := by
  simp only [psiLin5, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, smul_eq_mul]
  constructor
  · apply Finset.sum_eq_zero; intro k _
    rw [← dotC_eq5, (hd.bYker _ (bY_getD_mem5 d hd k)).1, mul_zero]
  · apply Finset.sum_eq_zero; intro k _
    rw [← dotC_eq5, (hd.bYker _ (bY_getD_mem5 d hd k)).2, mul_zero]

/-- The block at `m0` vanishes on `Y1`. -/
lemma blockSem_m0_psi5 (d : CaseData) (hd : CaseWF5 d) (G : Nat) (u : Fin 3 → F4) :
    blockSem5 G [(d.ga, d.fa), (d.gb, d.fb)] (psiLin5 d u) = 0 := by
  obtain ⟨h1, h2⟩ := fa_psi5 d hd u
  simp [blockSem5, h1, h2]

lemma blockSem_m0_ea5 (d : CaseData) (hd : CaseWF5 d) (G : Nat) :
    blockSem5 G [(d.ga, d.fa), (d.gb, d.fb)] (decode5 d.ea) =
      m00 G • decode5 d.ga + m10 G • decode5 d.gb := by
  have h1 : formC5 d.fa (decode5 d.ea) = 1 := by rw [← dotC_eq5]; exact hd.eaf.1
  have h2 : formC5 d.fb (decode5 d.ea) = 0 := by rw [← dotC_eq5]; exact hd.eaf.2
  simp [blockSem5, h1, h2]

lemma blockSem_m0_eb5 (d : CaseData) (hd : CaseWF5 d) (G : Nat) :
    blockSem5 G [(d.ga, d.fa), (d.gb, d.fb)] (decode5 d.eb) =
      m01 G • decode5 d.ga + m11 G • decode5 d.gb := by
  have h1 : formC5 d.fa (decode5 d.eb) = 0 := by rw [← dotC_eq5]; exact hd.ebf.1
  have h2 : formC5 d.fb (decode5 d.eb) = 1 := by rw [← dotC_eq5]; exact hd.ebf.2
  simp [blockSem5, h1, h2]

/-! ### GF5(4)^4 codes -/

lemma encode3_lt (v : Fin 3 → F4) : encode3 v < 64 := by
  have e : (64 : Nat) = 2 ^ 6 := by norm_num
  rw [e]
  apply xorFin_lt
  intro k
  have := unitC_lt (v k) k
  have hk := k.isLt
  have : 4 ^ (k.val + 1) ≤ 2 ^ 6 := by
    calc 4 ^ (k.val + 1) ≤ 4 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ 6 := by norm_num
  show unitC (v k) k < 2 ^ 6
  omega

lemma coordC_mod64 (x k : Nat) (hk : k < 3) : coordC (x % 64) k = coordC x k := by
  have e : (64 : Nat) = 2 ^ 6 := by norm_num
  simp only [coordC, e, Nat.testBit_mod_two_pow]
  simp [show 2 * k < 6 by omega, show 2 * k + 1 < 6 by omega]

lemma indep3_of_li {u u' : Fin 3 → F4} (h : LinearIndependent F4 ![u, u']) :
    indep3 (encode3 u) (encode3 u') = true := by
  unfold indep3
  rw [List.all_eq_true]
  intro ab hab
  rw [List.mem_range] at hab
  by_cases h0 : ab = 0
  · simp [h0]
  · rw [beq_false_of_ne h0, Bool.false_or, bne_iff_ne, ne_eq]
    intro hw
    have hv : vec3 (smulC (coordC ab 0) (encode3 u) ^^^ smulC (coordC ab 1) (encode3 u')) = 0 := by
      funext k
      rw [show vec3 _ k = coordC _ k.val from rfl, ← coordC_mod64 _ _ k.isLt, hw]
      simp
    rw [vec3_xor_smul, vec3_encode3, vec3_encode3] at hv
    obtain ⟨ha, hb⟩ := (LinearIndependent.pair_iff.mp h) _ _ hv
    apply h0
    rw [ab_mat2 ab hab, ha, hb]; rfl

/-! ### The kernel step: a reduced echelon pair inside `ker E ∩ Y1` -/

theorem exists_K5 (X : PCtx5) (d : CaseData) (hd : CaseWF5 d) (s : Sol) {W : Submodule F4 GF5}
    (hW : Module.finrank F4 W ≤ 1) (hE : ∀ y, Esem5 X d s y ∈ W) :
    ∃ K ∈ rrefPairs3, Esem5 X d s (decode5 (combo3 K.1 d.bY)) = 0 ∧
      Esem5 X d s (decode5 (combo3 K.2 d.bY)) = 0 := by
  let φ := (Elin5 X d s).comp (psiLin5 d)
  have hr : Module.finrank F4 (LinearMap.range φ) ≤ 1 := by
    have : LinearMap.range φ ≤ W := by rintro _ ⟨u, rfl⟩; exact hE _
    exact (Submodule.finrank_mono this).trans hW
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [Module.finrank_fin_fun] at hrn
  obtain ⟨u, u', hu, hu', hind⟩ := exists_pair_of_two_le' (V := LinearMap.ker φ) (by omega)
  obtain ⟨K, hK, ⟨ab, -, hab⟩, ⟨cd, -, hcd⟩⟩ :=
    rref_cover3 (encode3 u) (encode3 u') (encode3_lt u) (encode3_lt u') (indep3_of_li hind)
  have inker : ∀ e, Esem5 X d s (psiLin5 d (vec3 (lin2u e (encode3 u) (encode3 u')))) = 0 := by
    intro e
    rw [lin2u, vec3_xor_smul, vec3_encode3, vec3_encode3]
    have : coordC e 0 • u + coordC e 1 • u' ∈ LinearMap.ker φ :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hu')
    exact LinearMap.mem_ker.mp this
  refine ⟨K, hK, ?_, ?_⟩
  · rw [decode5_combo3_bY d hd, ← hab]; exact inker ab
  · rw [decode5_combo3_bY d hd, ← hcd]; exact inker cd

/-! ### Keys and tables -/

lemma GF5_add_self (x : GF5) : x + x = 0 := by
  ext l; simp only [GF5.add_v, Pi.add_apply, GF5.zero_v, Pi.zero_apply]; exact F4.add_self _

lemma eq_of_add_eq_zero'5 {x y : GF5} (h : x + y = 0) : x = y := by
  have := congrArg (· + y) h
  simpa [add_assoc, GF5_add_self] using this

lemma sum_c_ty5 (X : PCtx5) (hX : PCtx5WF X) (c y : Nat) :
    ∑ k : Fin 3, coordC c k • decode5 (applyCols5 (X.tcols.getD k []) y) = xcG5 X c * decode5 y := by
  rw [xcG_eq5 X hX c, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [decode_applyCols_t5 X hX k k.isLt, smul_mul_assoc]

/-- The values `t_k y` computed by `solsK5`. -/
def tyList5 (X : PCtx5) (y1 y2 : Nat) : List (Nat × Nat) :=
  X.tcols.map fun tc => (applyCols5 tc y1, applyCols5 tc y2)

lemma tyList_eq5 (X : PCtx5) (hX : PCtx5WF X) (y1 y2 : Nat) :
    tyList5 X y1 y2 = (List.range 3).map fun k =>
      (applyCols5 (X.tcols.getD k []) y1, applyCols5 (X.tcols.getD k []) y2) := by
  have h4 : X.tcols.length = 3 := by rw [hX.tcols, List.length_map, hX.tv3]
  apply List.ext_getElem
  · simp [tyList5, h4]
  · intro n h1 h2
    simp [tyList5, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < X.tcols.length by
      simp [tyList5] at h1; omega)]

/-- Coordinate `l` of `combo3 c` of three keys. -/
lemma coordC_combo4_keys5 (c : Nat) (f : Nat → Nat) (l : Nat) (hl : l < 32) :
    coordC (combo3 c ((List.range 3).map f)) l = ∑ k : Fin 3, coordC c k * coordC (f k) l := by
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, combo3, coordC_xor,
    coordC_smulC _ _ _ hl, Fin.sum_univ_three]
  rfl

/-- The key of the right-hand side equals the key of `G B` (pair block). -/
lemma key_eq_pair5 (X : PCtx5) (hX : PCtx5WF X) (d : CaseData) (hd : CaseWF5 d) (c : Nat)
    (goff : List Nat) (hg : goff.length = d.off.length) (y1 y2 : Nat)
    (h1 : E0sem5 X d c goff (decode5 y1) = 0) (h2 : E0sem5 X d c goff (decode5 y2) = 0)
    {i : Nat} (hi : i < d.off.length) {g0 f0 g1 f1 : Nat} (hb : blkOf d i = [(g0, f0), (g1, f1)])
    {r0 r1 : Nat} (hr : d.rhoOff.getD i [] = [r0, r1]) :
    combo3 c ((tyList5 X y1 y2).map fun x => keyR5 [r0, r1] x.1 x.2) =
      keyGB true (dotC5 f0 y1) (dotC5 f0 y2) (dotC5 f1 y1) (dotC5 f1 y2) (goff.getD i 0) := by
  have e1 := eq_of_add_eq_zero'5 h1
  have e2 := eq_of_add_eq_zero'5 h2
  have hu0 : (0 : Nat) < (blkOf d i).length := by rw [hb]; simp
  have hu1 : (1 : Nat) < (blkOf d i).length := by rw [hb]; simp
  have c00 := rho_offSem5 d hd goff hg (decode5 y1) hi hu0
  have c01 := rho_offSem5 d hd goff hg (decode5 y2) hi hu0
  have c10 := rho_offSem5 d hd goff hg (decode5 y1) hi hu1
  have c11 := rho_offSem5 d hd goff hg (decode5 y2) hi hu1
  simp only [rhoOf, hr, List.getD_cons_zero, List.getD_cons_succ, hb, coefS5, if_true,
    show (1 : Nat) ≠ 0 by omega, if_false] at c00 c01 c10 c11
  rw [← e1] at c00 c10
  rw [← e2] at c01 c11
  rw [← sum_c_ty5 X hX c y1, map_sum] at c00 c10
  rw [← sum_c_ty5 X hX c y2, map_sum] at c01 c11
  apply code_ext (n := 4) (combo3_lt _ _ (fun (k : Nat)
      (hk : k ∈ (tyList5 X y1 y2).map fun x => keyR5 [r0, r1] x.1 x.2) => by
        rw [List.mem_map] at hk; obtain ⟨x, -, rfl⟩ := hk; exact keyR5_lt _ _ _))
    (by have := keyGB_lt true (dotC5 f0 y1) (dotC5 f0 y2) (dotC5 f1 y1) (dotC5 f1 y2) (goff.getD i 0)
        norm_num at this ⊢; exact this)
  intro l hl
  rw [tyList_eq5 X hX, List.map_map, coordC_combo4_keys5 _ _ _ (by omega)]
  simp only [Function.comp_def]
  simp only [map_smul, smul_eq_mul] at c00 c01 c10 c11
  interval_cases l
  · simp only [(coordC_keyR5_pair _ _ _ _).1, keyGB, if_true, coordC_mat2_0, dotC_eq5]
    rw [← c00]
  · simp only [(coordC_keyR5_pair _ _ _ _).2.1, keyGB, if_true, coordC_mat2_1, dotC_eq5]
    rw [← c01]
  · simp only [(coordC_keyR5_pair _ _ _ _).2.2.1, keyGB, if_true, coordC_mat2_2, dotC_eq5]
    rw [← c10]
  · simp only [(coordC_keyR5_pair _ _ _ _).2.2.2, keyGB, if_true, coordC_mat2_3, dotC_eq5]
    rw [← c11]

/-- The key of the right-hand side equals the key of `G B` (single block). -/
lemma key_eq_single5 (X : PCtx5) (hX : PCtx5WF X) (d : CaseData) (hd : CaseWF5 d) (c : Nat)
    (goff : List Nat) (hg : goff.length = d.off.length) (y1 y2 : Nat)
    (h1 : E0sem5 X d c goff (decode5 y1) = 0) (h2 : E0sem5 X d c goff (decode5 y2) = 0)
    {i : Nat} (hi : i < d.off.length) {g0 f0 : Nat} (hb : blkOf d i = [(g0, f0)])
    {r0 : Nat} (hr : d.rhoOff.getD i [] = [r0]) :
    combo3 c ((tyList5 X y1 y2).map fun x => keyR5 [r0] x.1 x.2) =
      keyGB false (dotC5 f0 y1) (dotC5 f0 y2) 0 0 (goff.getD i 0) := by
  have e1 := eq_of_add_eq_zero'5 h1
  have e2 := eq_of_add_eq_zero'5 h2
  have hu0 : (0 : Nat) < (blkOf d i).length := by rw [hb]; simp
  have c00 := rho_offSem5 d hd goff hg (decode5 y1) hi hu0
  have c01 := rho_offSem5 d hd goff hg (decode5 y2) hi hu0
  simp only [rhoOf, hr, List.getD_cons_zero, hb, coefS5] at c00 c01
  rw [← e1, ← sum_c_ty5 X hX c y1, map_sum] at c00
  rw [← e2, ← sum_c_ty5 X hX c y2, map_sum] at c01
  apply code_ext (n := 4) (combo3_lt _ _ (fun (k : Nat)
      (hk : k ∈ (tyList5 X y1 y2).map fun x => keyR5 [r0] x.1 x.2) => by
        rw [List.mem_map] at hk; obtain ⟨x, -, rfl⟩ := hk; exact keyR5_lt _ _ _))
    (by have := keyGB_lt false (dotC5 f0 y1) (dotC5 f0 y2) 0 0 (goff.getD i 0)
        norm_num at this ⊢; exact this)
  intro l hl
  simp only [map_smul, smul_eq_mul] at c00 c01
  have hL : coordC (combo3 c ((tyList5 X y1 y2).map fun x => keyR5 [r0] x.1 x.2)) l =
      (if l = 0 then ∑ k : Fin 3, coordC c k * formC5 r0 (decode5 (applyCols5 (X.tcols.getD k []) y1))
        else 0) +
      (if l = 1 then ∑ k : Fin 3, coordC c k * formC5 r0 (decode5 (applyCols5 (X.tcols.getD k []) y2))
        else 0) := by
    rw [tyList_eq5 X hX, List.map_map, coordC_combo4_keys5 _ _ _ (by omega)]
    simp only [Function.comp_def, coordC_keyR5_single, dotC_eq5, mul_add, Finset.sum_add_distrib]
    by_cases h0 : l = 0
    · subst h0; simp
    · by_cases h1 : l = 1
      · subst h1; simp
      · simp [h0, h1]
  have hR : coordC (keyGB false (dotC5 f0 y1) (dotC5 f0 y2) 0 0 (goff.getD i 0)) l =
      (if l = 0 then coordC (goff.getD i 0) 0 * formC5 f0 (decode5 y1) else 0) +
      (if l = 1 then coordC (goff.getD i 0) 0 * formC5 f0 (decode5 y2) else 0) := by
    simp only [keyGB, Bool.false_eq_true, if_false, coordC_xor, coordC_unitC, dotC_eq5]
    by_cases h0 : l = 0
    · subst h0; simp
    · by_cases h1 : l = 1
      · subst h1; simp
      · simp [h0, h1, Ne.symm h0, Ne.symm h1]
  rw [hL, hR, c00, c01]

/-! ### Candidates and choices -/

lemma candsAt_spec5 (tbls : List (Array (List Nat))) (keysT : List (List Nat)) (c : Nat)
    (goff : List Nat) (h1 : tbls.length = goff.length) (h2 : keysT.length = goff.length)
    (hmem : ∀ i < goff.length,
      goff.getD i 0 ∈ (tbls.getD i #[]).getD (combo3 c (keysT.getD i [])) []) :
    ∃ cands, candsAt3 tbls keysT c = some cands ∧ goff ∈ choices cands := by
  induction goff generalizing tbls keysT with
  | nil =>
    match tbls, keysT, h1, h2 with
    | [], [], _, _ => exact ⟨[], rfl, by simp [choices]⟩
  | cons x xs ih =>
    match tbls, keysT, h1, h2 with
    | tb :: tbls, ks :: keysT, h1, h2 =>
      have hx : x ∈ tb.getD (combo3 c ks) [] := by have := hmem 0 (by simp); simpa using this
      obtain ⟨cs, hcs, hxs⟩ := ih tbls keysT (by simpa using h1) (by simpa using h2)
        (fun i hi => by have := hmem (i + 1) (by simp; omega); simpa using this)
      refine ⟨tb.getD (combo3 c ks) [] :: cs, ?_, ?_⟩
      · have hne : (tb.getD (combo3 c ks) []).isEmpty = false := by
          cases hl : tb.getD (combo3 c ks) [] with
          | nil => rw [hl] at hx; simp at hx
          | cons _ _ => rfl
        simp only [candsAt3, hne, hcs]
        rfl
      · simp only [choices, List.mem_flatMap, List.mem_map]
        exact ⟨x, hx, xs, hxs, rfl⟩

lemma blk_shape5 (d : CaseData) (hd : CaseWF5 d) {i : Nat} (hi : i < d.off.length) :
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
lemma goff_mem_table5 (X : PCtx5) (hX : PCtx5WF X) (d : CaseData) (hd : CaseWF5 d) (c : Nat)
    (goff : List Nat) (hg : goff.length = d.off.length) (y1 y2 : Nat)
    (h1 : E0sem5 X d c goff (decode5 y1) = 0) (h2 : E0sem5 X d c goff (decode5 y2) = 0)
    {i : Nat} (hi : i < d.off.length) (hcand : goff.getD i 0 ∈ candOps (blkOf d i)) :
    goff.getD i 0 ∈ (mkTable5 (blkOf d i) y1 y2).getD
      (combo3 c ((tyList5 X y1 y2).map fun x => keyR5 (d.rhoOff.getD i []) x.1 x.2)) [] := by
  rcases blk_shape5 d hd hi with ⟨g0, f0, g1, f1, r0, r1, hb, hr⟩ | ⟨g0, f0, r0, hb, hr⟩
  · rw [hr, key_eq_pair5 X hX d hd c goff hg y1 y2 h1 h2 hi hb hr, hb, mkTable5_pair]
    rw [hb] at hcand
    exact mem_tableOf true _ _ _ _ (by simpa [candOps] using hcand)
  · rw [hr, key_eq_single5 X hX d hd c goff hg y1 y2 h1 h2 hi hb hr, hb, mkTable5_single]
    rw [hb] at hcand
    exact mem_tableOf false _ _ _ _ (by simpa [candOps] using hcand)

/-! ### Decoding the vectors of the search -/

lemma decode_offContrib5 (off : List (Nat × List Term)) (goff : List Nat)
    (hg : goff.length = off.length) (y : Nat) :
    decode5 (offContrib (off.map (·.2)) goff ((off.map (·.2)).map fun ts => entriesAt5 ts y)) =
      offSem5 off goff (decode5 y) := by
  induction off generalizing goff with
  | nil => simp [offContrib, offSem5]
  | cons b off ih =>
    match goff, hg with
    | G :: goff, hg =>
      simp only [List.map_cons, offContrib, decode5_xor, applyGE_entriesAt5, decode_applyG5]
      rw [ih goff (by simpa using hg)]
      simp [offSem5]

/-- The `E0` value computed by `solsGoff1` at a vector `y`. -/
def e0Code5 (X : PCtx5) (d : CaseData) (c : Nat) (goff : List Nat) (y : Nat) : Nat :=
  applyCols5 (X.xcCols c) y ^^^ offContrib (d.off.map (·.2)) goff
    ((d.off.map (·.2)).map fun ts => entriesAt5 ts y)

lemma decode_e0Code5 (X : PCtx5) (hX : PCtx5WF X) (d : CaseData) (c : Nat) (goff : List Nat)
    (hg : goff.length = d.off.length) (y : Nat) :
    decode5 (e0Code5 X d c goff y) = E0sem5 X d c goff (decode5 y) := by
  rw [e0Code5, decode5_xor, decode_applyCols_xc5 X hX, decode_offContrib5 _ _ hg]
  rfl

lemma Esem_eq5 (X : PCtx5) (d : CaseData) (s : Sol) (y : GF5) :
    Esem5 X d s y = E0sem5 X d s.c s.goff y + blockSem5 s.g0 [(d.ga, d.fa), (d.gb, d.fb)] y := rfl

lemma blockSem_m0_mem5 (d : CaseData) (G : Nat) (y : GF5) :
    ∃ α β : F4, blockSem5 G [(d.ga, d.fa), (d.gb, d.fb)] y = α • decode5 d.ga + β • decode5 d.gb :=
  ⟨_, _, rfl⟩

lemma pivW_echelon5 (d : CaseData) : Echelon5 (pivW5 d) :=
  foldl_insertPivot_echelon5 [d.ga, d.gb] [] trivial

lemma redLin_kills_m05 (d : CaseData) (G : Nat) (y : GF5) :
    redLin5 (pivW5 d) (blockSem5 G [(d.ga, d.fa), (d.gb, d.fb)] y) = 0 := by
  obtain ⟨α, β, h⟩ := blockSem_m0_mem5 d G y
  have hpos := echelon_pos5 _ (pivW_echelon5 d)
  obtain ⟨ka, kb⟩ := pivW_kills5 d
  rw [decode_reduceBy5 _ hpos] at ka kb
  rw [h, map_add, map_smul, map_smul, ka, kb, smul_zero, smul_zero, add_zero]

/-- The pivot positions of an RREF pair are distinct and `< 4`. -/
lemma pivots_rref5 {K : Nat × Nat} (hK : K ∈ rrefPairs3) :
    (pivots3 K).1 < (pivots3 K).2 ∧ (pivots3 K).2 < 3 := by
  simp only [rrefPairs3, List.mem_flatMap, List.mem_filterMap, List.mem_range] at hK
  obtain ⟨r0, -, r1, -, hr⟩ := hK
  split at hr
  · rename_i p q hp hq
    split_ifs at hr with hc
    simp only [Option.some.injEq] at hr
    subst hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    simp only [pivots3, hp, hq, Option.getD_some]
    exact ⟨hc.1.1.1, (firstNZ_some hq).2.1⟩
  · simp at hr

/-- The vectors `es` of `solsK5`: the vector of `bY` off the pivots, then `ea`, `eb`. -/
lemma es_shape5 (d : CaseData) (hd : CaseWF5 d) {K : Nat × Nat} (hK : K ∈ rrefPairs3) :
    ∃ a, a ∈ d.bY ∧
      ((List.range 3).filter fun i => i != (pivots3 K).1 && i != (pivots3 K).2).map
        (fun i => d.bY.getD i 0) ++ [d.ea, d.eb] = [a, d.ea, d.eb] := by
  obtain ⟨hpq, hq3⟩ := pivots_rref5 hK
  generalize (pivots3 K).1 = p at hpq
  generalize (pivots3 K).2 = q at hpq hq3
  have mem : ∀ i < 3, d.bY.getD i 0 ∈ d.bY := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by rw [hd.bY3]; exact hi)]; exact List.getElem_mem _
  have hf : ∃ a, a < 3 ∧ ((List.range 3).filter fun i => i != p && i != q) = [a] := by
    interval_cases q <;> interval_cases p <;> exact ⟨_, by norm_num, rfl⟩
  obtain ⟨a, ha, hab⟩ := hf
  exact ⟨d.bY.getD a 0, mem a ha, by rw [hab]; rfl⟩

/-! ### Membership, from the inside out -/

lemma mem_solsColA5 (d : CaseData) (s : Sol) {pbase : List (Nat × Nat)} (hpb : Echelon5 pbase)
    {W : Submodule F4 GF5} (hW2 : Module.finrank F4 W ≤ 1) (hpbW : pivSpan5 pbase ≤ W)
    (vea veb : Nat)
    (hvA : decode5 (vea ^^^ smulC (m00 s.g0) d.ga ^^^ smulC (m10 s.g0) d.gb) ∈ W)
    (hvC : decode5 (veb ^^^ smulC (m01 s.g0) d.ga ^^^ smulC (m11 s.g0) d.gb) ∈ W)
    (hg0 : s.g0 < 256) (hdiag : diagPred s.g0 = true) :
    s ∈ solsColA1 d s.c s.goff pbase vea veb (mat2 (m00 s.g0) (m10 s.g0) 0 0) := by
  unfold solsColA1
  simp only [coordC_mat2_0, coordC_mat2_1]
  obtain ⟨pA, hpA, rfl⟩ := push1_isSome pbase hpb _ hW2 hpbW hvA
  rw [hpA]
  simp only
  rw [List.mem_filterMap]
  refine ⟨mat2 (m01 s.g0) (m11 s.g0) 0 0, List.mem_range.mpr (mat2_0_0_lt _ _), ?_⟩
  simp only [coordC_mat2_0, coordC_mat2_1]
  have hspan : pivSpan5 (insertPivot 5 pbase (vea ^^^ smulC (m00 s.g0) d.ga ^^^
      smulC (m10 s.g0) d.gb)) ≤ W := by
    refine (insertPivot_span5 _ _).trans (sup_le hpbW ?_)
    rw [Submodule.span_le]; rintro _ rfl; exact hvA
  obtain ⟨_, hC, _⟩ := push1_isSome _ (insertPivot_echelon5 _ hpb _) _ hW2 hspan hvC
  rw [hC, mat2_self hg0, hdiag]
  rfl

lemma E0sem_eq5 (X : PCtx5) (d : CaseData) (s : Sol) (y : GF5) :
    E0sem5 X d s.c s.goff y = Esem5 X d s y + blockSem5 s.g0 [(d.ga, d.fa), (d.gb, d.fb)] y := by
  rw [Esem_eq5, add_assoc, GF5_add_self, add_zero]

/-- `solsGoff1` finds the solution (for the vectors `es = [a, ea, eb]` of `solsK5`). -/
lemma mem_solsGoff5 (X : PCtx5) (hX : PCtx5WF X) (d : CaseData) (hd : CaseWF5 d) (s : Sol)
    (hlen : s.goff.length = d.off.length) (hg0 : s.g0 < 256) (hdiag : diagPred s.g0 = true)
    {W : Submodule F4 GF5} (hW2 : Module.finrank F4 W ≤ 1) (hE : ∀ y, Esem5 X d s y ∈ W)
    {a : Nat} (ha : a ∈ d.bY) :
    s ∈ solsGoff1 d (d.off.map (·.2))
      { es := [a, d.ea, d.eb],
        entEs := [a, d.ea, d.eb].map fun y => (d.off.map (·.2)).map fun ts => entriesAt5 ts y,
        entA := (d.off.map (·.2)).map fun ts => entriesAt5 ts d.ea,
        entB := (d.off.map (·.2)).map fun ts => entriesAt5 ts d.eb }
      s.c ([a, d.ea, d.eb].map (applyCols5 (X.xcCols s.c))) (applyCols5 (X.xcCols s.c) d.ea)
      (applyCols5 (X.xcCols s.c) d.eb) s.goff := by
  have hY : ∀ y ∈ d.bY, E0sem5 X d s.c s.goff (decode5 y) = Esem5 X d s (decode5 y) := by
    intro y hy
    rw [E0sem_eq5]
    have h1 : formC5 d.fa (decode5 y) = 0 := by rw [← dotC_eq5]; exact (hd.bYker y hy).1
    have h2 : formC5 d.fb (decode5 y) = 0 := by rw [← dotC_eq5]; exact (hd.bYker y hy).2
    simp [blockSem5, h1, h2]
  have he : ∀ y, decode5 (e0Code5 X d s.c s.goff y) = E0sem5 X d s.c s.goff (decode5 y) :=
    decode_e0Code5 X hX d s.c s.goff hlen
  have he0 : (([a, d.ea, d.eb].map (applyCols5 (X.xcCols s.c))).zip
      ([a, d.ea, d.eb].map fun y => (d.off.map (·.2)).map fun ts => entriesAt5 ts y)).map
        (fun x => x.1 ^^^ offContrib (d.off.map (·.2)) s.goff x.2) =
      [e0Code5 X d s.c s.goff a, e0Code5 X d s.c s.goff d.ea, e0Code5 X d s.c s.goff d.eb] := rfl
  simp only [solsGoff1]
  rw [he0]
  -- the reduction filter
  have hpos := echelon_pos5 _ (pivW_echelon5 d)
  have hred : ∀ y, decode5 (reduceBy (pivW5 d) (e0Code5 X d s.c s.goff y)) ∈
      W.map (redLin5 (pivW5 d)) := by
    intro y
    rw [decode_reduceBy5 _ hpos, he, E0sem_eq5, map_add, redLin_kills_m05, add_zero]
    exact Submodule.mem_map_of_mem (hE _)
  have hW2' : Module.finrank F4 (W.map (redLin5 (pivW5 d))) ≤ 1 :=
    (Submodule.finrank_map_le _ _).trans hW2
  obtain ⟨p1, hp1, -, -⟩ := pushAll1_isSome
    ([e0Code5 X d s.c s.goff a, e0Code5 X d s.c s.goff d.ea,
      e0Code5 X d s.c s.goff d.eb].map (reduceBy (pivW5 d))) [] trivial hW2'
    (by rw [pivSpan5, Submodule.span_le]; rintro _ ⟨q, hq, -⟩; simp at hq)
    (by intro v hv
        rw [List.mem_map] at hv
        obtain ⟨y, hy, rfl⟩ := hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl <;> exact hred _)
  rw [hp1]
  -- the base pivot
  obtain ⟨pb, hpb, hech, hspan⟩ := pushAll1_isSome
    [e0Code5 X d s.c s.goff a] [] trivial hW2
    (by rw [pivSpan5, Submodule.span_le]; rintro _ ⟨q, hq, -⟩; simp at hq)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        subst hv
        rw [he, hY a ha]; exact hE _)
  rw [show [e0Code5 X d s.c s.goff a, e0Code5 X d s.c s.goff d.ea,
      e0Code5 X d s.c s.goff d.eb].take 1 = [e0Code5 X d s.c s.goff a] from rfl, hpb]
  rw [List.mem_flatMap]
  refine ⟨mat2 (m00 s.g0) (m10 s.g0) 0 0, List.mem_range.mpr (mat2_0_0_lt _ _), ?_⟩
  have hvA : decode5 (e0Code5 X d s.c s.goff d.ea ^^^ smulC (m00 s.g0) d.ga ^^^
      smulC (m10 s.g0) d.gb) ∈ W := by
    rw [decode5_xor, decode5_xor, decode5_smulC, decode5_smulC, he, add_assoc,
      ← blockSem_m0_ea5 d hd s.g0, ← Esem_eq5]
    exact hE _
  have hvC : decode5 (e0Code5 X d s.c s.goff d.eb ^^^ smulC (m01 s.g0) d.ga ^^^
      smulC (m11 s.g0) d.gb) ∈ W := by
    rw [decode5_xor, decode5_xor, decode5_smulC, decode5_smulC, he, add_assoc,
      ← blockSem_m0_eb5 d hd s.g0, ← Esem_eq5]
    exact hE _
  exact mem_solsColA5 d s hech hW2 hspan (e0Code5 X d s.c s.goff d.ea) (e0Code5 X d s.c s.goff d.eb)
    hvA hvC hg0 hdiag

/-- The completeness theorem of the direction search. -/
theorem sol_complete5 (X : PCtx5) (hX : PCtx5WF X) (d : CaseData) (hd : CaseWF5 d) (s : Sol)
    (hc : s.c ∈ dirs3) (hlen : s.goff.length = d.off.length)
    (hcand : ∀ i < d.off.length, s.goff.getD i 0 ∈ candOps (blkOf d i))
    (hg0 : s.g0 < 256) (hdiag : diagPred s.g0 = true)
    {W : Submodule F4 GF5} (hW2 : Module.finrank F4 W ≤ 1) (hE : ∀ y, Esem5 X d s y ∈ W) :
    withE5 X d s ∈ allSols5 X d := by
  obtain ⟨K, hK, hK1, hK2⟩ := exists_K5 X d hd s hW2 hE
  have hE0y : ∀ K' : Nat, Esem5 X d s (decode5 (combo3 K' d.bY)) = 0 →
      E0sem5 X d s.c s.goff (decode5 (combo3 K' d.bY)) = 0 := by
    intro K' h
    rw [E0sem_eq5, h, decode5_combo3_bY d hd, blockSem_m0_psi5 d hd, add_zero]
  have h1 := hE0y K.1 hK1
  have h2 := hE0y K.2 hK2
  have hsK : s ∈ solsK5 X d K := by
    obtain ⟨a, ha, hes⟩ := es_shape5 d hd hK
    unfold solsK5
    simp only [hes]
    rw [List.mem_flatMap]
    refine ⟨s.c, hc, ?_⟩
    unfold solsKc5
    obtain ⟨cands, hcands, hch⟩ := candsAt_spec5
      ((d.off.map (·.2)).map fun ts => mkTable5 ts (combo3 K.1 d.bY) (combo3 K.2 d.bY))
      (d.rhoOff.map fun rhos => (tyList5 X (combo3 K.1 d.bY) (combo3 K.2 d.bY)).map
        fun x => keyR5 rhos x.1 x.2) s.c s.goff
      (by simp [hlen]) (by simp [hd.rhoLen, hlen]) (fun i hi => by
        have hi' : i < d.off.length := by omega
        have := goff_mem_table5 X hX d hd s.c s.goff hlen _ _ h1 h2 hi' (hcand i hi')
        rw [List.getD_eq_getElem _ _ (by simp; exact hi'),
          List.getD_eq_getElem _ _ (by simp [hd.rhoLen]; exact hi')]
        simp only [List.getElem_map]
        rw [List.getD_eq_getElem _ _ (by rw [hd.rhoLen]; exact hi')] at this
        have hblk : blkOf d i = d.off[i].2 := by
          simp only [blkOf, List.getD_eq_getElem _ _ hi']
        rw [hblk] at this
        exact this)
    simp only [tyList5] at hcands
    rw [hcands]
    simp only
    rw [List.mem_flatMap]
    exact ⟨s.goff, hch, mem_solsGoff5 X hX d hd s hlen hg0 hdiag hW2 hE ha⟩
  unfold allSols5
  rw [List.mem_filter, List.mem_map]
  refine ⟨⟨s, mem_dedupSols _ s (List.mem_flatMap.mpr ⟨K, hK, hsK⟩), rfl⟩, ?_⟩
  simp only [withE5, decide_eq_true_eq]
  refine (rankC_le5 _ (W := W) ?_).trans hW2
  intro v hv
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hv
  rw [decode_Eval5 X hX]
  exact hE _

end Mu4.N5
