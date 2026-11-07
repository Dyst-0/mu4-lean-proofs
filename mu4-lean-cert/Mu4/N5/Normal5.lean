import Mu4.N5.Complete5
import Mu4.Bridge.Normal

/-!
# mu_4(5): the normal form of a 10-term decomposition, and its blocks (`audit/PROOF.md`, N5-N6)

`NF5 p0 p1 s0 s1 mult ws D H`: the decomposition `D`, valid on `H` (here `⊤`), has step-1 data with pencil
`P = span(p0, p1)`, is normalized (`a_i|_P = l_{m(i)}`), has multiplicities `mult` at the five standard points,
`x_{m(i)} g_i ∈ Ŝ = span(s0, s1)`, and the single terms at the points `ws` of `W_m = x_m⁻¹ Ŝ`.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge


/-- The normal form for the case `(p0, p1, s0, s1, mult, ws)`. -/
structure NF5 (p0 p1 s0 s1 : Nat) (mult ws : List Nat) (D : Decomp5 10) (H : Submodule F4 GF5) where
  S : Step1Data5 D H
  hp : S.p = decode5 p0
  hq : S.q = decode5 p1
  norm : ∀ i, i ∉ S.W → ∀ m : Fin 5, D.a i (pt5 S.p S.q m) = 0 →
    ∀ q : Fin 5, D.a i (pt5 S.p S.q q) = lval m q
  mult_eq : ∀ m : Fin 5, mult.getD m 0 = (vanAt5 S m).card
  shat : ∀ i, i ∉ S.W → ∀ m : Fin 5, D.a i (pt5 S.p S.q m) = 0 →
    pt5 S.p S.q m * D.g i ∈ Submodule.span F4 {decode5 s0, decode5 s1}
  single : ∀ m : Fin 5, (vanAt5 S m).card = 1 → ∀ i ∈ vanAt5 S m,
    D.g i ∈ Submodule.span F4 {pcA (ws.getD m 0) • ((pt5 S.p S.q m)⁻¹ * decode5 s0) +
      pcB (ws.getD m 0) • ((pt5 S.p S.q m)⁻¹ * decode5 s1)}

variable {p0 p1 s0 s1 : Nat} {mult ws : List Nat} {D : Decomp5 10} {H : Submodule F4 GF5}

/-- The true block at the point `m`: `Block_m y = ∑_{i alive, vanishing at x_m} b_i(y) g_i`. -/
noncomputable def trueBlock5 (S : Step1Data5 D H) (m : Fin 5) (y : GF5) : GF5 :=
  ∑ i ∈ vanAt5 S m, D.b i y • D.g i

/-- The vanishing point of an alive term. -/
noncomputable def vpt5 (S : Step1Data5 D H) (i : Fin 10) : Fin 5 :=
  if h : i ∉ S.W then (vanish_point_exists5 S h).choose else 0

lemma vpt_spec5 (S : Step1Data5 D H) {i : Fin 10} (hi : i ∉ S.W) :
    D.a i (pt5 S.p S.q (vpt5 S i)) = 0 := by
  rw [vpt5, dif_pos hi]; exact (vanish_point_exists5 S hi).choose_spec

lemma mem_vanAt_iff_vpt5 (S : Step1Data5 D H) {i : Fin 10} {m : Fin 5} :
    i ∈ vanAt5 S m ↔ i ∉ S.W ∧ vpt5 S i = m := by
  rw [mem_vanAt5]
  constructor
  · rintro ⟨hW, h0⟩
    exact ⟨hW, vanish_point_unique5 S hW (vpt_spec5 S hW) h0⟩
  · rintro ⟨hW, rfl⟩
    exact ⟨hW, vpt_spec5 S hW⟩

/-- L7a: on the standard points, `x_q y = ∑_m l_m(x_q) Block_m(y)`. -/
theorem mul_pt_eq5 (nf : NF5 p0 p1 s0 s1 mult ws D H) (hD : D.ValidOn H) (q : Fin 5) (y : GF5) :
    pt5 nf.S.p nf.S.q q * y = ∑ m : Fin 5, lval m q • trueBlock5 nf.S m y := by
  classical
  set S := nf.S
  rw [hD _ (pt_mem5 S q) y]
  -- split off the W-terms (they vanish at x_q)
  rw [← Finset.sum_compl_add_sum S.W]
  have hWz : ∑ i ∈ S.W, (D.a i (pt5 S.p S.q q) * D.b i y) • D.g i = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [W_van_pt5 S hi q]; simp
  rw [hWz, add_zero]
  -- regroup the alive terms by their vanishing point
  rw [← Finset.sum_fiberwise_of_maps_to (s := S.Wᶜ) (t := Finset.univ) (g := vpt5 S)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [trueBlock5, Finset.smul_sum]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_compl, mem_vanAt_iff_vpt5]
  · intro i hi
    obtain ⟨hW, hv⟩ := (mem_vanAt_iff_vpt5 S).mp hi
    rw [nf.norm i hW m (by rw [← hv]; exact vpt_spec5 S hW) q, smul_smul, mul_comm]

/-! ### Codes of the case: inverses, `W_m`, forms -/

lemma decode5_invC5 (x : Nat) (hx : x < 1024) : decode5 (invC5 x) = (decode5 x)⁻¹ := by
  by_cases h0 : x = 0
  · subst h0; rw [invC5_zero, decode5_zero, inv_zero]
  · have h := mulK5_invC5 x (Nat.one_le_iff_ne_zero.mpr h0) hx
    have h1 : decode5 x * decode5 (invC5 x) = 1 := by rw [← decode5_mulK5, h, decode5_one]
    exact eq_inv_of_mul_eq_one_right h1

lemma smulC_lt_1024 (c : F4) {x : Nat} (hx : x < 1024) : smulC c x < 1024 := by
  have e : (1024 : Nat) = 2 ^ (2 * 5) := by norm_num
  rw [e] at hx ⊢; exact smulC_lt c hx

lemma ptC_lt5 {p0 p1 : Nat} (h0 : p0 < 1024) (h1 : p1 < 1024) (m : Nat) : ptC p0 p1 m < 1024 := by
  have e : (1024 : Nat) = 2 ^ 10 := by norm_num
  have a := smulC_lt_1024 (ssC m) h0
  have b := smulC_lt_1024 (ttC m) h1
  rw [e] at a b ⊢
  exact Nat.xor_lt_two_pow a b

lemma decode_Wv5 (p0 p1 s0 s1 : Nat) (h0 : p0 < 1024) (h1 : p1 < 1024) (m : Fin 5) (i : Nat) :
    decode5 (Wv5 (mkPCtx5 p0 p1) s0 s1 m i) =
      (pt5 (decode5 p0) (decode5 p1) m)⁻¹ * decode5 (if i = 0 then s0 else s1) := by
  rw [Wv5, decode5_mulK5, mkPCtx5_pts, decode5_invC5 _ (ptC_lt5 h0 h1 m), decode_ptC5]

/-- Every element of GF5(4^6) in the basis `e_t = t^t`. -/
lemma GF_expand5 (y : GF5) : y = ∑ t : Fin 5, y.v t • decode5 (eC t) := by
  ext k
  rw [GF5.v_sum, Finset.sum_apply]
  simp only [GF5.smul_v, Pi.smul_apply, smul_eq_mul, decode_eC5, tG5_pow, Fin.sum_univ_five]
  fin_cases k <;> simp [pw5]

/-- `formOf5 xm0 l rho` is the form `y ↦ rho(x_{m0} y) / l`. -/
lemma formC_formOf5 (xm0 : Nat) (l : F4) (rho : Nat) (y : GF5) :
    formC5 (formOf5 xm0 l rho) y = formC5 rho (decode5 xm0 * y) * l⁻¹ := by
  have key : ∀ t : Fin 5, coordC (formOf5 xm0 l rho) t = dotC5 rho (mulK5 xm0 (eC t)) * l⁻¹ := by
    intro t
    unfold formOf5
    have h : ∀ (L : List Nat) (a : Nat), coordC (L.foldl (fun acc t => acc ^^^
        unitC (dotC5 rho (mulK5 xm0 (eC t)) * l⁻¹) t) a) t.val =
        coordC a t + ((L.filter (· = t.val)).map fun _ => dotC5 rho (mulK5 xm0 (eC t)) * l⁻¹).sum := by
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
    have : (List.range 5).filter (· = t.val) = [t.val] := by
      fin_cases t <;> decide
    rw [this]; simp
  calc formC5 (formOf5 xm0 l rho) y = ∑ t : Fin 5, coordC (formOf5 xm0 l rho) t * y.v t := rfl
    _ = ∑ t : Fin 5, (dotC5 rho (mulK5 xm0 (eC t)) * l⁻¹) * y.v t := by simp only [key]
    _ = (∑ t : Fin 5, y.v t * formC5 rho (decode5 xm0 * decode5 (eC t))) * l⁻¹ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [dotC_eq5, decode5_mulK5]; ring
    _ = formC5 rho (decode5 xm0 * y) * l⁻¹ := by
        congr 1
        conv_rhs => rw [GF_expand5 y]
        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [mul_smul_comm, map_smul, smul_eq_mul]

end Mu4.N5
