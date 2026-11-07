import Mu4.Bridge.Complete
import Mu4.Bridge.Mat2
import Mu4.Lower.Pencil

/-!
# The normal form of a 12-term decomposition, and its blocks (`audit/PROOF.md`, L6-L7)

`NF p0 p1 s0 s1 mult ws D H`: the decomposition `D`, valid on the hyperplane `H`, has step-1 data
with pencil `P = span(p0, p1)` (codes of a representative), is normalized (`a_i|_P = l_{m(i)}`),
has multiplicities `mult` at the five standard points, `x_{m(i)} g_i ∈ Ŝ = span(s0, s1)`, and the
single terms at the points `ws` of `W_m = x_m⁻¹ Ŝ`.
-/

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower

/-- `l_m(x_q)` as in the search (`Mu4.Search.lval`), on `Fin 5`. -/
lemma lval_eq : ∀ m q : Fin 5, lval m.val q.val = tt m * ss q + ss m * tt q := by decide

/-- The normal form for the case `(p0, p1, s0, s1, mult, ws)`. -/
structure NF (p0 p1 s0 s1 : Nat) (mult ws : List Nat) (D : Decomp 12) (H : Submodule F4 GF) where
  S : Step1Data D H
  hp : S.p = decode p0
  hq : S.q = decode p1
  norm : ∀ i, i ∉ S.W → ∀ m : Fin 5, D.a i (pt S.p S.q m) = 0 →
    ∀ q : Fin 5, D.a i (pt S.p S.q q) = lval m q
  mult_eq : ∀ m : Fin 5, mult.getD m 0 = (vanAt S m).card
  shat : ∀ i, i ∉ S.W → ∀ m : Fin 5, D.a i (pt S.p S.q m) = 0 →
    pt S.p S.q m * D.g i ∈ Submodule.span F4 {decode s0, decode s1}
  single : ∀ m : Fin 5, (vanAt S m).card = 1 → ∀ i ∈ vanAt S m,
    D.g i ∈ Submodule.span F4 {pcA (ws.getD m 0) • ((pt S.p S.q m)⁻¹ * decode s0) +
      pcB (ws.getD m 0) • ((pt S.p S.q m)⁻¹ * decode s1)}

variable {p0 p1 s0 s1 : Nat} {mult ws : List Nat} {D : Decomp 12} {H : Submodule F4 GF}

/-- The true block at the point `m`: `Block_m y = ∑_{i alive, vanishing at x_m} b_i(y) g_i`. -/
noncomputable def trueBlock (S : Step1Data D H) (m : Fin 5) (y : GF) : GF :=
  ∑ i ∈ vanAt S m, D.b i y • D.g i

/-- The vanishing point of an alive term. -/
noncomputable def vpt (S : Step1Data D H) (i : Fin 12) : Fin 5 :=
  if h : i ∉ S.W then (vanish_point_exists S h).choose else 0

lemma vpt_spec (S : Step1Data D H) {i : Fin 12} (hi : i ∉ S.W) :
    D.a i (pt S.p S.q (vpt S i)) = 0 := by
  rw [vpt, dif_pos hi]; exact (vanish_point_exists S hi).choose_spec

lemma mem_vanAt_iff_vpt (S : Step1Data D H) {i : Fin 12} {m : Fin 5} :
    i ∈ vanAt S m ↔ i ∉ S.W ∧ vpt S i = m := by
  rw [mem_vanAt]
  constructor
  · rintro ⟨hW, h0⟩
    exact ⟨hW, vanish_point_unique S hW (vpt_spec S hW) h0⟩
  · rintro ⟨hW, rfl⟩
    exact ⟨hW, vpt_spec S hW⟩

/-- L7a: on the standard points, `x_q y = ∑_m l_m(x_q) Block_m(y)`. -/
theorem mul_pt_eq (nf : NF p0 p1 s0 s1 mult ws D H) (hD : D.ValidOn H) (q : Fin 5) (y : GF) :
    pt nf.S.p nf.S.q q * y = ∑ m : Fin 5, lval m q • trueBlock nf.S m y := by
  classical
  set S := nf.S
  rw [hD _ (pt_mem S q) y]
  -- split off the W-terms (they vanish at x_q)
  rw [← Finset.sum_compl_add_sum S.W]
  have hWz : ∑ i ∈ S.W, (D.a i (pt S.p S.q q) * D.b i y) • D.g i = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [W_van_pt S hi q]; simp
  rw [hWz, add_zero]
  -- regroup the alive terms by their vanishing point
  rw [← Finset.sum_fiberwise_of_maps_to (s := S.Wᶜ) (t := Finset.univ) (g := vpt S)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [trueBlock, Finset.smul_sum]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_compl, mem_vanAt_iff_vpt]
  · intro i hi
    obtain ⟨hW, hv⟩ := (mem_vanAt_iff_vpt S).mp hi
    rw [nf.norm i hW m (by rw [← hv]; exact vpt_spec S hW) q, smul_smul, mul_comm]

/-! ### Codes of the case: inverses, `W_m`, forms -/

lemma decode_invC (x : Nat) (hx : x < 4096) : decode (invC x) = (decode x)⁻¹ := by
  by_cases h0 : x = 0
  · subst h0; rw [invC_zero, decode_zero, inv_zero]
  · have h := mulK_invC x (Nat.one_le_iff_ne_zero.mpr h0) hx
    have h1 : decode x * decode (invC x) = 1 := by rw [← decode_mulK, h, decode_one]
    exact eq_inv_of_mul_eq_one_right h1

lemma smulC_lt_4096 (c : F4) {x : Nat} (hx : x < 4096) : smulC c x < 4096 := by
  have e : (4096 : Nat) = 2 ^ (2 * 6) := by norm_num
  rw [e] at hx ⊢; exact smulC_lt c hx

lemma ptC_lt {p0 p1 : Nat} (h0 : p0 < 4096) (h1 : p1 < 4096) (m : Nat) : ptC p0 p1 m < 4096 := by
  have e : (4096 : Nat) = 2 ^ 12 := by norm_num
  have a := smulC_lt_4096 (ssC m) h0
  have b := smulC_lt_4096 (ttC m) h1
  rw [e] at a b ⊢
  exact Nat.xor_lt_two_pow a b

lemma decode_Wv (p0 p1 s0 s1 : Nat) (h0 : p0 < 4096) (h1 : p1 < 4096) (m : Fin 5) (i : Nat) :
    decode (Wv (mkPCtx p0 p1) s0 s1 m i) =
      (pt (decode p0) (decode p1) m)⁻¹ * decode (if i = 0 then s0 else s1) := by
  rw [Wv, decode_mulK, mkPCtx_pts, decode_invC _ (ptC_lt h0 h1 m), decode_ptC]

/-- Every element of GF(4^6) in the basis `e_t = t^t`. -/
lemma GF_expand (y : GF) : y = ∑ t : Fin 6, y.v t • decode (eC t) := by
  ext k
  rw [GF.v_sum, Finset.sum_apply]
  simp only [GF.smul_v, Pi.smul_apply, smul_eq_mul, decode_eC, tG_pow, Fin.sum_univ_six]
  fin_cases k <;> simp [pw]

/-- `formOf xm0 l rho` is the form `y ↦ rho(x_{m0} y) / l`. -/
lemma formC_formOf (xm0 : Nat) (l : F4) (rho : Nat) (y : GF) :
    formC (formOf xm0 l rho) y = formC rho (decode xm0 * y) * l⁻¹ := by
  have key : ∀ t : Fin 6, coordC (formOf xm0 l rho) t = dotC rho (mulK xm0 (eC t)) * l⁻¹ := by
    intro t
    unfold formOf
    have h : ∀ (L : List Nat) (a : Nat), coordC (L.foldl (fun acc t => acc ^^^
        unitC (dotC rho (mulK xm0 (eC t)) * l⁻¹) t) a) t.val =
        coordC a t + ((L.filter (· = t.val)).map fun _ => dotC rho (mulK xm0 (eC t)) * l⁻¹).sum := by
      intro L; induction L with
      | nil => intro a; simp
      | cons k L ih =>
        intro a
        simp only [List.foldl_cons]
        rw [ih, coordC_xor, coordC_unitC]
        by_cases hk : k = t.val
        · subst hk; simp [add_assoc]
        · simp [hk, Ne.symm hk]
    rw [h, coordC_zero, zero_add]
    have : (List.range 6).filter (· = t.val) = [t.val] := by
      fin_cases t <;> decide
    rw [this]; simp
  calc formC (formOf xm0 l rho) y = ∑ t : Fin 6, coordC (formOf xm0 l rho) t * y.v t := rfl
    _ = ∑ t : Fin 6, (dotC rho (mulK xm0 (eC t)) * l⁻¹) * y.v t := by simp only [key]
    _ = (∑ t : Fin 6, y.v t * formC rho (decode xm0 * decode (eC t))) * l⁻¹ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [dotC_eq, decode_mulK]; ring
    _ = formC rho (decode xm0 * y) * l⁻¹ := by
        congr 1
        conv_rhs => rw [GF_expand y]
        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [mul_smul_comm, map_smul, smul_eq_mul]

end Mu4.Bridge
