import Mu4.Lower.Step1
import Mu4.Field
import Mu4Geom

/-!
# G1 from the search (`audit/PROOF.md`, G1)

`geometry_of_check : geomCheck 7 = true → Geometry`.

Among 12 vectors spanning GF(4)^5, five form a basis; in the coordinates of that basis they are
`e_0, …, e_4`. If every 4 of the 12 vectors (distinct indices) were independent, the normalized
codes of the other 7 would extend the basis in the search of `Mu4Geom.lean`: each lies outside
the span of any 3 earlier points. `noExt_eq_false` (soundness of the search) turns that into
`geomCheck 7 = false`. The check `geomCheck 7 = true` is `Mu4.Check.geomCheck_ok`
(`native_decide`).
-/

namespace Mu4.Lower
open Mu4 F4 Mu4.Geom

/-! ### Codes of GF(4)^5 -/

/-- The vector of `GF(4)^5` with code `x`. -/
def dec5 (x : Nat) : Fin 5 → F4 := fun l => coordC x l.val

/-- The code of a vector of `GF(4)^5`. -/
def enc5 (a : Fin 5 → F4) : Nat := xorFin fun l : Fin 5 => (a l).code <<< (2 * l.val)

lemma coordC_xorFin5 {n : Nat} (f : Fin n → Nat) (l : Nat) :
    coordC (xorFin f) l = ∑ i : Fin n, coordC (f i) l := by
  have key : ∀ L : List Nat, coordC (L.foldr (· ^^^ ·) 0) l = (L.map fun x => coordC x l).sum := by
    intro L; induction L with
    | nil => simp
    | cons a L ih => simp [ih]
  rw [xorFin, key, List.map_ofFn, List.sum_ofFn]; rfl

@[simp] lemma dec5_enc5 (a : Fin 5 → F4) : dec5 (enc5 a) = a := by
  funext k
  simp only [dec5, enc5, coordC_xorFin5, coordC_shift]
  simp [Fin.val_inj]

lemma dec5_xor (x y : Nat) : dec5 (x ^^^ y) = dec5 x + dec5 y := by
  funext l; simp [dec5]

lemma dec5_smulC (c : F4) (x : Nat) : dec5 (smulC c x) = c • dec5 x := by
  funext l; simp [dec5, coordC_smulC _ _ _ (show l.val < 32 by omega)]

@[simp] lemma dec5_zero : dec5 0 = 0 := by funext l; simp [dec5]

lemma enc5_lt (a : Fin 5 → F4) : enc5 a < 1024 := by
  have term : ∀ l : Fin 5, (a l).code <<< (2 * l.val) < 2 ^ 10 := by
    intro l
    rw [Nat.shiftLeft_eq]
    have h1 := code_lt (a l)
    have h2 : 2 ^ (2 * l.val) * 4 ≤ 2 ^ 10 := by
      have : 2 * l.val + 2 ≤ 10 := by omega
      calc 2 ^ (2 * l.val) * 4 = 2 ^ (2 * l.val + 2) := by ring
        _ ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) this
    calc (a l).code * 2 ^ (2 * l.val) < 4 * 2 ^ (2 * l.val) :=
          Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ (2 * l.val) * 4 := by ring
      _ ≤ 2 ^ 10 := h2
  have hfold : ∀ L : List Nat, (∀ x ∈ L, x < 2 ^ 10) → L.foldr (· ^^^ ·) 0 < 2 ^ 10 := by
    intro L hL
    induction L with
    | nil => simp
    | cons x L ih =>
      simp only [List.foldr_cons]
      exact Nat.xor_lt_two_pow (hL x (by simp)) (ih fun y hy => hL y (by simp [hy]))
  have := hfold _ (by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨l, rfl⟩ := hx
    exact term l)
  simpa [enc5, xorFin] using this

/-- Normalization on codes (a finite check by the kernel). -/
lemma normC_spec : ∀ x < 1024, x ≠ 0 →
    normC x ≠ 0 ∧ normC (normC x) = normC x ∧ normC x < 1024 ∧ firstCoord x ≠ z := by
  decide +kernel

lemma inv_ne_zero' {c : F4} (h : c ≠ z) : F4.inv c ≠ 0 := by
  revert h; cases c <;> decide

lemma normC_mem_points {x : Nat} (hx : x < 1024) (h0 : x ≠ 0) : normC x ∈ points := by
  obtain ⟨h1, h2, h3, -⟩ := normC_spec x hx h0
  simp only [points, List.mem_filter, List.mem_range]
  exact ⟨h3, by simp [h1, h2]⟩

lemma points_nodup : points.Nodup := List.Nodup.filter _ List.nodup_range

/-- The basis vectors have the codes `4^k`. -/
lemma normC_enc5_single : ∀ k : Fin 5,
    normC (enc5 (fun j => if k = j then 1 else 0)) = 4 ^ k.val := by
  decide +kernel

/-! ### Marked codes -/

/-- `v` lies in the span of three codes of `S` (not necessarily distinct). -/
def InSpan3 (S : List Nat) (v : Nat) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ r s t : F4, dec5 v = r • dec5 a + s • dec5 b + t • dec5 c

/-- Every marked code lies in the span of three codes of `S`. -/
def Sound (S : List Nat) (f : Array Bool) : Prop := ∀ v, f.getD v false = true → InSpan3 S v

lemma InSpan3.mono {S S' : List Nat} (h : S ⊆ S') {v : Nat} (hv : InSpan3 S v) :
    InSpan3 S' v := by
  obtain ⟨a, ha, b, hb, c, hc, r, s, t, e⟩ := hv
  exact ⟨a, h ha, b, h hb, c, h hc, r, s, t, e⟩

lemma Sound.mono {S S' : List Nat} (h : S ⊆ S') {f : Array Bool} (hf : Sound S f) :
    Sound S' f :=
  fun v hv => (hf v hv).mono h

lemma getD_set_true {f : Array Bool} {i v : Nat}
    (h : (f.setIfInBounds i true).getD v false = true) : v = i ∨ f.getD v false = true := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at h
  rw [Array.getD_eq_getD_getElem?]
  by_cases hiv : i = v
  · exact Or.inl hiv.symm
  · rw [if_neg hiv] at h; exact Or.inr h

lemma foldl_pres {α : Type} (P : Array Bool → Prop) (g : Array Bool → α → Array Bool) :
    ∀ L : List α, (∀ f x, x ∈ L → P f → P (g f x)) → ∀ f, P f → P (L.foldl g f) := by
  intro L
  induction L with
  | nil => intro _ f hf; exact hf
  | cons x L ih =>
    intro hg f hf
    exact ih (fun f y hy hf => hg f y (List.mem_cons_of_mem _ hy) hf) _
      (hg f x List.mem_cons_self hf)

lemma mem_mults {x y : Nat} (h : y ∈ mults x) : ∃ r : F4, dec5 y = r • dec5 x := by
  simp only [mults, List.mem_map] at h
  obtain ⟨r, -, rfl⟩ := h
  exact ⟨r, dec5_smulC r x⟩

lemma sound_markPlane {S : List Nat} {a b c : Nat} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    {f : Array Bool} (hf : Sound S f) : Sound S (markPlane f a b c) := by
  unfold markPlane
  dsimp only
  refine foldl_pres _ _ (mults a) ?_ f hf
  intro f ra hra hf
  refine foldl_pres _ _ (mults b) ?_ f hf
  intro f sb hsb hf
  refine foldl_pres _ _ (mults c) ?_ f hf
  intro f tc htc hf v hv
  rcases getD_set_true hv with rfl | hv
  · obtain ⟨r, hr⟩ := mem_mults hra
    obtain ⟨s, hs⟩ := mem_mults hsb
    obtain ⟨t, ht⟩ := mem_mults htc
    exact ⟨a, ha, b, hb, c, hc, r, s, t, by rw [dec5_xor, dec5_xor, hr, hs, ht]⟩
  · exact hf v hv

lemma sound_addPoint {cur : List Nat} {f : Array Bool} (hf : Sound cur f) (p : Nat) :
    Sound (p :: cur) (addPoint f p cur) := by
  suffices h : ∀ L : List Nat, L ⊆ cur → ∀ f, Sound (p :: cur) f →
      Sound (p :: cur) (addPoint f p L) from
    h cur (fun _ h => h) f (hf.mono (List.subset_cons_self _ _))
  intro L
  induction L with
  | nil => intro _ f hf; exact hf
  | cons a rest ih =>
    intro hL f hf
    simp only [addPoint]
    apply ih (fun x hx => hL (List.mem_cons_of_mem _ hx))
    refine foldl_pres _ _ rest ?_ f hf
    intro f b hb hf
    exact sound_markPlane List.mem_cons_self
      (List.mem_cons_of_mem _ (hL List.mem_cons_self))
      (List.mem_cons_of_mem _ (hL (List.mem_cons_of_mem _ hb))) hf

lemma sound_addAll : ∀ (ps : List Nat) (f : Array Bool) (cur : List Nat), Sound cur f →
    Sound (addAll ps (f, cur)).2 (addAll ps (f, cur)).1 := by
  intro ps
  induction ps with
  | nil => intro f cur h; exact h
  | cons p ps ih => intro f cur h; exact ih _ _ (sound_addPoint h p)

lemma addAll_snd : ∀ (ps : List Nat) (f : Array Bool) (cur : List Nat),
    (addAll ps (f, cur)).2 = ps.reverse ++ cur := by
  intro ps
  induction ps with
  | nil => intro f cur; rfl
  | cons p ps ih => intro f cur; simp [addAll, ih]

lemma sound_start : Sound start.2 start.1 := by
  apply sound_addAll
  intro v hv
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hv
  split at hv <;> simp at hv

lemma start_snd : start.2 = [256, 64, 16, 4, 1] := by
  simp only [start, addAll_snd]; rfl

/-! ### Soundness of the search -/

/-- `M` extends `cur` point by point, each point outside the span of any 3 earlier ones. -/
def ValidSeq : List Nat → List Nat → Prop
  | _, [] => True
  | cur, m :: M => ¬ InSpan3 cur m ∧ ValidSeq (m :: cur) M

/-- Soundness of `noExt`: a valid extension by `k` points of `cands` makes it `false`. -/
theorem noExt_eq_false : ∀ (cands : List Nat) (k : Nat) (cur : List Nat) (f : Array Bool)
    (M : List Nat), Sound cur f → M.Sublist cands → M.length = k → ValidSeq cur M →
    noExt k cur f cands = false := by
  intro cands
  induction cands with
  | nil =>
    intro k cur f M _ hM hk _
    rw [List.sublist_nil] at hM
    subst hM; subst hk
    simp [noExt]
  | cons p rest ih =>
    intro k cur f M hf hM hk hV
    cases k with
    | zero => simp [noExt]
    | succ k =>
      cases hM with
      | cons _ hM' =>
        have := ih (k + 1) cur f M hf hM' hk hV
        simp [noExt, this]
      | cons₂ _ hM' =>
        rename_i M'
        obtain ⟨hnot, hV'⟩ := hV
        have hfp : f.getD p false = false := by
          cases h : f.getD p false
          · rfl
          · exact absurd (hf p h) hnot
        have := ih k (p :: cur) (addPoint f p cur) M' (sound_addPoint hf p) hM'
          (by simpa using hk) hV'
        simp [noExt, hfp, this]

/-- A list of codes is a valid extension when every code is outside the span of any 3 others. -/
lemma validSeq_of (A : Finset Nat)
    (hA : ∀ m ∈ A, ∀ S : List Nat, (∀ x ∈ S, x ∈ A ∧ x ≠ m) → ¬ InSpan3 S m) :
    ∀ (M cur : List Nat), M.Nodup → (∀ m ∈ M, m ∉ cur) → (∀ x ∈ cur, x ∈ A) →
      (∀ m ∈ M, m ∈ A) → ValidSeq cur M := by
  intro M
  induction M with
  | nil => intro _ _ _ _ _; trivial
  | cons m M ih =>
    intro cur hnd hdis hcur hM
    refine ⟨hA m (hM m List.mem_cons_self) cur
      (fun x hx => ⟨hcur x hx, fun h => hdis m List.mem_cons_self (h ▸ hx)⟩), ?_⟩
    apply ih (m :: cur) (List.nodup_cons.mp hnd).2
    · intro m' hm' hm'c
      rcases List.mem_cons.mp hm'c with h | h
      · exact (List.nodup_cons.mp hnd).1 (h ▸ hm')
      · exact hdis m' (List.mem_cons_of_mem _ hm') h
    · intro x hx
      rcases List.mem_cons.mp hx with h | h
      · exact h ▸ hM m List.mem_cons_self
      · exact hcur x h
    · intro m' hm'
      exact hM m' (List.mem_cons_of_mem _ hm')

/-! ### G1 -/

/-- G1, from the search check. -/
theorem geometry_of_check (hcheck : geomCheck 7 = true) : Geometry := by
  intro v hspan
  by_contra hcon
  have hind : ∀ i j k l : Fin 12, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      LinearIndependent F4 ![v i, v j, v k, v l] := by
    intro i j k l h1 h2 h3 h4 h5 h6
    by_contra h
    exact hcon ⟨i, j, k, l, h1, h2, h3, h4, h5, h6, h⟩
  -- five of the vectors form a basis: indices `ι5`, coordinates `φ` for that basis
  obtain ⟨ι5, hι5, φ, hφ⟩ : ∃ ι5 : Fin 5 → Fin 12, Function.Injective ι5 ∧
      ∃ φ : (Fin 5 → F4) ≃ₗ[F4] (Fin 5 → F4),
        ∀ k, φ (v (ι5 k)) = fun j => if k = j then 1 else 0 := by
    obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' F4 v
    haveI : Finite κ := Finite.of_injective a ha
    haveI : Fintype κ := Fintype.ofFinite κ
    have hsp' : ⊤ ≤ Submodule.span F4 (Set.range (v ∘ a)) := by rw [hsp, hspan]
    let b := Module.Basis.mk hli hsp'
    have hcard : Fintype.card κ = 5 := by
      have := Module.finrank_eq_card_basis b
      rw [Module.finrank_fin_fun] at this
      exact this.symm
    let e : κ ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
    let b5 : Module.Basis (Fin 5) F4 (Fin 5 → F4) := b.reindex e
    refine ⟨a ∘ e.symm, ha.comp e.symm.injective, b5.equivFun, fun k => ?_⟩
    have hb5 : b5 k = v ((a ∘ e.symm) k) := by
      simp only [b5, b, Module.Basis.reindex_apply, Module.Basis.mk_apply, Function.comp_apply]
    funext j
    rw [← hb5]
    exact b5.equivFun_self k j
  obtain ⟨w, hw⟩ : ∃ w : Fin 12 → (Fin 5 → F4), ∀ i, w i = φ (v i) := ⟨_, fun _ => rfl⟩
  have hwb : ∀ k, w (ι5 k) = fun j => if k = j then 1 else 0 := fun k => by rw [hw, hφ]
  have hindw : ∀ i j k l : Fin 12, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      LinearIndependent F4 ![w i, w j, w k, w l] := by
    intro i j k l h1 h2 h3 h4 h5 h6
    have h := (hind i j k l h1 h2 h3 h4 h5 h6).map' φ.toLinearMap φ.ker
    have e : ![w i, w j, w k, w l] = φ.toLinearMap ∘ ![v i, v j, v k, v l] := by
      funext x; fin_cases x <;> simp [hw]
    rw [e]; exact h
  -- no vector lies in the span of 3 others
  have span3 : ∀ (l : Fin 12) (s : Finset (Fin 12)), l ∉ s → s.card ≤ 3 →
      w l ∉ Submodule.span F4 (w '' (s : Set (Fin 12))) := by
    intro l s hl hs hmem
    have hst : s ⊆ Finset.univ.erase l := fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => hl (h ▸ hx), Finset.mem_univ _⟩
    obtain ⟨u, hsu, hut, hu⟩ := Finset.exists_subsuperset_card_eq hst hs
      (by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp)
    obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hu
    have hne : ∀ x ∈ ({i, j, k} : Finset (Fin 12)), x ≠ l := fun x hx h =>
      by have := hut hx; rw [h] at this; simp at this
    have hli4 := hindw l i j k (hne i (by simp)).symm (hne j (by simp)).symm
      (hne k (by simp)).symm hij hik hjk
    have hcons : (![w l, w i, w j, w k] : Fin 4 → (Fin 5 → F4)) =
        Fin.cons (w l) ![w i, w j, w k] := rfl
    rw [hcons, linearIndependent_fin_cons] at hli4
    apply hli4.2
    have hrange : Set.range ![w i, w j, w k] =
        w '' ((({i, j, k} : Finset (Fin 12))) : Set (Fin 12)) := by
      rw [Matrix.range_cons, Matrix.range_cons_cons_empty]
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
        Set.image_singleton, Set.singleton_union]
    rw [hrange]
    exact Submodule.span_mono (Set.image_mono (by exact_mod_cast hsu)) hmem
  -- the normalized codes `C i`, with `dec5 (C i) = lam i • w i`
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i h
    apply span3 i ∅ (by simp) (by simp)
    rw [h]; exact Submodule.zero_mem _
  have henc0 : ∀ i, enc5 (w i) ≠ 0 := by
    intro i h; apply hw0 i; rw [← dec5_enc5 (w i), h, dec5_zero]
  obtain ⟨C, hCdef⟩ : ∃ C : Fin 12 → Nat, ∀ i, C i = normC (enc5 (w i)) := ⟨_, fun _ => rfl⟩
  obtain ⟨lam, hlamdef⟩ : ∃ lam : Fin 12 → F4, ∀ i, lam i = F4.inv (firstCoord (enc5 (w i))) :=
    ⟨_, fun _ => rfl⟩
  have hC : ∀ i, dec5 (C i) = lam i • w i := by
    intro i; rw [hCdef, hlamdef, normC, dec5_smulC, dec5_enc5]
  have hlam : ∀ i, lam i ≠ 0 := fun i => by
    rw [hlamdef]; exact inv_ne_zero' (normC_spec _ (enc5_lt _) (henc0 i)).2.2.2
  have hCpt : ∀ i, C i ∈ points := fun i => by
    rw [hCdef]; exact normC_mem_points (enc5_lt _) (henc0 i)
  have Cinj : Function.Injective C := by
    intro i j hij
    by_contra hne
    apply span3 i {j} (by simpa using hne) (by simp)
    have e' : lam i • w i = lam j • w j := by rw [← hC, ← hC, hij]
    have hwi : w i = ((lam i)⁻¹ * lam j) • w j := by
      rw [mul_smul, ← e', smul_smul, inv_mul_cancel₀ (hlam i), one_smul]
    rw [hwi, Finset.coe_singleton, Set.image_singleton]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hbasis : ∀ k : Fin 5, C (ι5 k) = 4 ^ k.val := by
    intro k
    rw [hCdef, hwb k]
    exact normC_enc5_single k
  -- every code is outside the span of 3 other codes
  obtain ⟨A, hAdef⟩ : ∃ A : Finset Nat, A = Finset.univ.image C := ⟨_, rfl⟩
  have hA : ∀ m ∈ A, ∀ S : List Nat, (∀ x ∈ S, x ∈ A ∧ x ≠ m) → ¬ InSpan3 S m := by
    intro m hm S hS hspan'
    rw [hAdef] at hm
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨a', ha', b', hb', c', hc', r, s, t, e'⟩ := hspan'
    obtain ⟨hai, hal⟩ := hS a' ha'
    obtain ⟨hbi, hbl⟩ := hS b' hb'
    obtain ⟨hci, hcl⟩ := hS c' hc'
    rw [hAdef] at hai hbi hci
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hai
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hbi
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hci
    have hil : l ≠ i := fun h => hal (h ▸ rfl)
    have hjl : l ≠ j := fun h => hbl (h ▸ rfl)
    have hkl : l ≠ k := fun h => hcl (h ▸ rfl)
    apply span3 l {i, j, k} (by simp [hil, hjl, hkl]) Finset.card_le_three
    rw [hC, hC, hC, hC] at e'
    have hwl : w l = (lam l)⁻¹ • (r • lam i • w i + s • lam j • w j + t • lam k • w k) := by
      rw [← e', smul_smul, inv_mul_cancel₀ (hlam l), one_smul]
    rw [hwl]
    have mem : ∀ x ∈ ({i, j, k} : Finset (Fin 12)),
        w x ∈ Submodule.span F4 (w '' ((({i, j, k} : Finset (Fin 12))) : Set (Fin 12))) :=
      fun x hx => Submodule.subset_span (Set.mem_image_of_mem _ (by exact_mod_cast hx))
    refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) <;>
      refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (mem _ ?_)) <;> simp
  -- the codes of the other 7 vectors, increasing
  obtain ⟨T, hTdef⟩ : ∃ T : Finset Nat, T = ((Finset.univ.image ι5)ᶜ).image C := ⟨_, rfl⟩
  have hT : T.card = 7 := by
    rw [hTdef, Finset.card_image_of_injective _ Cinj, Finset.card_compl,
      Finset.card_image_of_injective _ hι5]
    simp
  obtain ⟨M, hMsub, hMmem⟩ : ∃ M : List Nat, M.Sublist points ∧ ∀ x, x ∈ M ↔ x ∈ T := by
    refine ⟨points.filter (fun x => decide (x ∈ T)), List.filter_sublist, fun x => ?_⟩
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [hTdef] at h
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
      exact hCpt i
  have hMnd : M.Nodup := points_nodup.sublist hMsub
  have hMlen : M.length = 7 := by
    rw [← List.toFinset_card_of_nodup hMnd, ← hT]
    rw [show M.toFinset = T from Finset.ext fun x => by rw [List.mem_toFinset, hMmem]]
  -- the basis codes
  have hstartA : ∀ x ∈ start.2, ∃ k, x = C (ι5 k) := by
    intro x hx
    rw [start_snd] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨4, by rw [hbasis]; rfl⟩
    · exact ⟨3, by rw [hbasis]; rfl⟩
    · exact ⟨2, by rw [hbasis]; rfl⟩
    · exact ⟨1, by rw [hbasis]; rfl⟩
    · exact ⟨0, by rw [hbasis]; rfl⟩
  have hV : ValidSeq start.2 M := by
    refine validSeq_of A hA M start.2 hMnd ?_ ?_ ?_
    · intro m hm hms
      obtain ⟨k, rfl⟩ := hstartA m hms
      have hT' := (hMmem _).mp hm
      rw [hTdef] at hT'
      obtain ⟨r, hr, hrk⟩ := Finset.mem_image.mp hT'
      have := Cinj hrk
      simp only [Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and,
        not_exists] at hr
      exact hr k this.symm
    · intro x hx
      obtain ⟨k, rfl⟩ := hstartA x hx
      rw [hAdef]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · intro m hm
      have hT' := (hMmem _).mp hm
      rw [hTdef] at hT'
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hT'
      rw [hAdef]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hfalse := noExt_eq_false points 7 start.2 start.1 M sound_start hMsub hMlen hV
  have htrue : noExt 7 start.2 start.1 points = true := hcheck
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

end Mu4.Lower
