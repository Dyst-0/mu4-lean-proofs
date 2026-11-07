import Mu4.N5.GFField5
import Mu4.Bridge.Codes
import Mu4Comp5.Search

/-!
# mu_4(5): semantics of the code primitives

The n = 5 versions of `Mu4/Bridge/Codes.lean`: decoding of linear combinations, and `rankC5` (elimination on five
coordinates) as a lower bound for the true rank in GF(4^5). Generic lemmas (2×2 matrix codes, `firstNZ`,
`coordC_unitC`) are those of `Mu4.Bridge`.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge


/-! ### Linear combinations -/

lemma decode5_combo (c : Nat) (vs : List Nat) :
    decode5 (combo c vs) = ∑ k : Fin vs.length, coordC c k • decode5 (vs.get k) := by
  simp [combo]

lemma decode5_combo3 (c : Nat) (k0 k1 k2 : Nat) :
    decode5 (combo3 c [k0, k1, k2]) = coordC c 0 • decode5 k0 + coordC c 1 • decode5 k1 + coordC c 2 • decode5 k2 := by
  simp [combo3]

lemma combo3_eq_combo (c : Nat) (ks : List Nat) : decode5 (combo3 c ks) = decode5 (combo c ks) := by
  match ks with
  | [k0, k1, k2] => rw [decode5_combo3, decode5_combo]; simp [Fin.sum_univ_three]
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ :: _ => rfl

lemma decode5_applyCols5 (a0 a1 a2 a3 a4 v : Nat) :
    decode5 (applyCols5 [a0, a1, a2, a3, a4] v) =
      coordC v 0 • decode5 a0 + coordC v 1 • decode5 a1 + coordC v 2 • decode5 a2 +
        coordC v 3 • decode5 a3 + coordC v 4 • decode5 a4 := by
  simp [applyCols5]

/-! ### Echelon5 pivot lists and the rank lower bound -/

/-- Echelon5 form: each pivot vector has a 1 at its position (`< 5`), and all later pivot vectors
vanish there. -/
def Echelon5 : List (Nat × Nat) → Prop
  | [] => True
  | (p, v) :: rest => p < 5 ∧ coordC v p = 1 ∧ (∀ q ∈ rest, coordC q.2 p = 0) ∧ Echelon5 rest

lemma echelon_append5 (piv : List (Nat × Nat)) (p v : Nat) (h : Echelon5 piv) (hp : p < 5)
    (hv : coordC v p = 1) (hz : ∀ q ∈ piv, coordC v q.1 = 0) : Echelon5 (piv ++ [(p, v)]) := by
  induction piv with
  | nil => exact ⟨hp, hv, by simp, trivial⟩
  | cons x rest ih =>
    obtain ⟨hx1, hx2, hx3, hx4⟩ := h
    refine ⟨hx1, hx2, ?_, ih hx4 fun q hq => hz q (List.mem_cons_of_mem _ hq)⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hx3 q hq
    · simp at hq; subst hq; exact hz x List.mem_cons_self

/-- `reduceBy` kills the pivot positions. -/
lemma reduceBy_zero_at5 (piv : List (Nat × Nat)) (h : Echelon5 piv) (v : Nat) :
    ∀ q ∈ piv, coordC (reduceBy piv v) q.1 = 0 := by
  induction piv generalizing v with
  | nil => simp
  | cons x rest ih =>
    obtain ⟨hx1, hx2, hx3, hx4⟩ := h
    intro q hq
    have hstep : reduceBy (x :: rest) v = reduceBy rest (v ^^^ smulC (coordC v x.1) x.2) := rfl
    rw [hstep]
    rcases List.mem_cons.mp hq with rfl | hq
    · -- the later pivots3 vanish at q.1, so the coordinate stays 0
      have key : ∀ (L : List (Nat × Nat)), (∀ r ∈ L, coordC r.2 q.1 = 0) → ∀ u, coordC u q.1 = 0 →
          coordC (reduceBy L u) q.1 = 0 := by
        intro L hL
        induction L with
        | nil => intro u hu; exact hu
        | cons y L ihL =>
          intro u hu
          show coordC (reduceBy L (u ^^^ smulC (coordC u y.1) y.2)) q.1 = 0
          apply ihL (fun r hr => hL r (List.mem_cons_of_mem _ hr))
          rw [coordC_reduce_step _ _ _ _ (by omega), hu, hL y List.mem_cons_self]
          simp
      apply key rest hx3
      rw [coordC_reduce_step _ _ _ _ (by omega), hx2]
      generalize coordC v q.1 = d; revert d; decide
    · exact ih hx4 _ q hq

/-- The decoded value of `reduceBy` differs from `v` by a combination of the pivot vectors. -/
lemma reduceBy_mem5 (piv : List (Nat × Nat)) (v : Nat) :
    decode5 (reduceBy piv v) - decode5 v ∈ Submodule.span F4 {x | ∃ q ∈ piv, x = decode5 q.2} := by
  induction piv generalizing v with
  | nil => simp [reduceBy]
  | cons x rest ih =>
    have hstep : reduceBy (x :: rest) v = reduceBy rest (v ^^^ smulC (coordC v x.1) x.2) := rfl
    rw [hstep]
    have h1 := ih (v ^^^ smulC (coordC v x.1) x.2)
    have : decode5 (reduceBy rest (v ^^^ smulC (coordC v x.1) x.2)) - decode5 v =
        (decode5 (reduceBy rest (v ^^^ smulC (coordC v x.1) x.2)) -
          decode5 (v ^^^ smulC (coordC v x.1) x.2)) + coordC v x.1 • decode5 x.2 := by
      rw [decode5_xor, decode5_smulC]; abel
    rw [this]
    refine Submodule.add_mem _ (Submodule.span_mono ?_ h1) ?_
    · rintro y ⟨q, hq, rfl⟩; exact ⟨q, List.mem_cons_of_mem _ hq, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, List.mem_cons_self, rfl⟩)

/-- Coordinates of a finite combination of decoded codes. -/
lemma v_lin5 {ι : Type*} [Fintype ι] (c : ι → F4) (w : ι → Nat) (l : Fin 5) :
    (∑ i, c i • decode5 (w i)).v l = ∑ i, c i * coordC (w i) l.val := by
  rw [GF5.v_sum, Finset.sum_apply]
  rfl

/-- Echelon5 pivot vectors are linearly independent. -/
lemma echelon_indep5 (piv : List (Nat × Nat)) (h : Echelon5 piv) :
    LinearIndependent F4 (fun i : Fin piv.length => decode5 (piv.get i).2) := by
  induction piv with
  | nil => exact linearIndependent_empty_type (ι := Fin 0)
  | cons x rest ih =>
    obtain ⟨hx1, hx2, hx3, hx4⟩ := h
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∑ i : Fin (rest.length + 1), g i • decode5 ((x :: rest).get i).2 = 0 := hg
    have h0 : g 0 = 0 := by
      have this := v_lin5 (ι := Fin (rest.length + 1)) (fun i => g i)
        (fun i => ((x :: rest).get i).2) ⟨x.1, hx1⟩
      rw [hg', GF5.zero_v, Pi.zero_apply, Fin.sum_univ_succ] at this
      symm at this
      have hrest : ∀ i : Fin rest.length, coordC ((x :: rest).get i.succ).2 x.1 = 0 :=
        fun i => hx3 _ (by simp)
      simp only [hrest, mul_zero, Finset.sum_const_zero, add_zero] at this
      simpa [hx2] using this
    have hrest := (Fintype.linearIndependent_iff.mp (ih hx4)) (fun i => g i.succ) (by
      rw [Fin.sum_univ_succ, h0, zero_smul, zero_add] at hg'
      simpa using hg')
    intro i
    exact Fin.cases h0 (fun j => hrest j) i

lemma echelon_pos5 (piv : List (Nat × Nat)) (h : Echelon5 piv) : ∀ q ∈ piv, q.1 < 5 := by
  induction piv with
  | nil => simp
  | cons x rest ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact ih h.2.2.2 q hq

/-- `insertPivot` keeps the echelon form. -/
lemma insertPivot_echelon5 (piv : List (Nat × Nat)) (h : Echelon5 piv) (v : Nat) :
    Echelon5 (insertPivot 5 piv v) := by
  cases hf : firstNZ (reduceBy piv v) 0 5 with
  | none => simpa [insertPivot, hf] using h
  | some p =>
    simp only [insertPivot, hf]
    obtain ⟨-, hp6, hcp⟩ := firstNZ_some hf
    apply echelon_append5 piv _ _ h (by omega)
    · rw [coordC_smulC _ _ _ (by omega), inv_mul_cancel₀ hcp]
    · intro q hq
      have hq6 := echelon_pos5 piv h q hq
      rw [coordC_smulC _ _ _ (by omega), reduceBy_zero_at5 piv h v q hq, mul_zero]

/-- The span of the decoded pivot vectors. -/
def pivSpan5 (piv : List (Nat × Nat)) : Submodule F4 GF5 :=
  Submodule.span F4 {x | ∃ q ∈ piv, x = decode5 q.2}

/-- The new pivot vectors lie in the span of the old ones and `v`. -/
lemma insertPivot_span5 (piv : List (Nat × Nat)) (v : Nat) :
    pivSpan5 (insertPivot 5 piv v) ≤ pivSpan5 piv ⊔ Submodule.span F4 {decode5 v} := by
  rw [pivSpan5, Submodule.span_le]
  rintro x ⟨q, hq, rfl⟩
  cases hf : firstNZ (reduceBy piv v) 0 5 with
  | none =>
    simp only [insertPivot, hf] at hq
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨q, hq, rfl⟩)
  | some p =>
    simp only [insertPivot, hf] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨q, hq, rfl⟩)
    · simp only [List.mem_singleton] at hq
      subst hq
      simp only [decode5_smulC]
      apply Submodule.smul_mem
      have h1 := reduceBy_mem5 piv v
      have : decode5 (reduceBy piv v) = (decode5 (reduceBy piv v) - decode5 v) + decode5 v := by abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left h1)
        (Submodule.mem_sup_right (Submodule.subset_span rfl))

/-- The length of an echelon list is the dimension of its span. -/
lemma echelon_length_le5 (piv : List (Nat × Nat)) (h : Echelon5 piv) {W : Submodule F4 GF5}
    (hW : pivSpan5 piv ≤ W) : piv.length ≤ Module.finrank F4 W := by
  have hli := echelon_indep5 piv h
  have hmem : ∀ i : Fin piv.length, decode5 (piv.get i).2 ∈ W := fun i =>
    hW (Submodule.subset_span ⟨piv.get i, List.get_mem _ _, rfl⟩)
  let f : Fin piv.length → W := fun i => ⟨decode5 (piv.get i).2, hmem i⟩
  have hf : LinearIndependent F4 f := by
    apply LinearIndependent.of_comp W.subtype
    exact hli
  simpa using hf.fintype_card_le_finrank

/-- `insertPivot` length bound. -/
lemma insertPivot_length_le5 (piv : List (Nat × Nat)) (h : Echelon5 piv) (v : Nat)
    {W : Submodule F4 GF5} (hW : pivSpan5 piv ≤ W) (hv : decode5 v ∈ W) :
    (insertPivot 5 piv v).length ≤ Module.finrank F4 W := by
  apply echelon_length_le5 _ (insertPivot_echelon5 piv h v)
  refine (insertPivot_span5 piv v).trans (sup_le hW ?_)
  rw [Submodule.span_le]; rintro _ rfl; exact hv

lemma foldl_insertPivot_echelon5 (vs : List Nat) (piv : List (Nat × Nat)) (h : Echelon5 piv) :
    Echelon5 (vs.foldl (insertPivot 5) piv) := by
  induction vs generalizing piv with
  | nil => exact h
  | cons v vs ih => exact ih _ (insertPivot_echelon5 piv h v)

lemma foldl_insertPivot_span5 (vs : List Nat) (piv : List (Nat × Nat)) {W : Submodule F4 GF5}
    (hW : pivSpan5 piv ≤ W) (hvs : ∀ v ∈ vs, decode5 v ∈ W) :
    pivSpan5 (vs.foldl (insertPivot 5) piv) ≤ W := by
  induction vs generalizing piv with
  | nil => exact hW
  | cons v vs ih =>
    apply ih _ _ (fun u hu => hvs u (List.mem_cons_of_mem _ hu))
    refine (insertPivot_span5 piv v).trans (sup_le hW ?_)
    rw [Submodule.span_le]; rintro _ rfl; exact hvs v List.mem_cons_self

/-- `rankC5` is a lower bound for the true rank: if all vectors lie in `W`, then
`rankC5 vs ≤ finrank W`. -/
theorem rankC_le5 (vs : List Nat) {W : Submodule F4 GF5} (hvs : ∀ v ∈ vs, decode5 v ∈ W) :
    rankC5 vs ≤ Module.finrank F4 W := by
  apply echelon_length_le5 _ (foldl_insertPivot_echelon5 vs [] trivial)
  apply foldl_insertPivot_span5 vs [] _ hvs
  rw [pivSpan5, Submodule.span_le]
  rintro x ⟨q, hq, -⟩
  simp at hq

/-- `push1` succeeds when the true rank stays at most 2. -/
lemma push1_isSome (piv : List (Nat × Nat)) (h : Echelon5 piv) (v : Nat) {W : Submodule F4 GF5}
    (hW2 : Module.finrank F4 W ≤ 1) (hpiv : pivSpan5 piv ≤ W) (hv : decode5 v ∈ W) :
    ∃ piv', push1 piv v = some piv' ∧ piv' = insertPivot 5 piv v := by
  have := insertPivot_length_le5 piv h v hpiv hv
  refine ⟨insertPivot 5 piv v, ?_, rfl⟩
  simp only [push1]
  rw [if_pos (by omega)]

/-- `pushAll1` succeeds when all vectors lie in a subspace of dimension at most 2. -/
lemma pushAll1_isSome (vs : List Nat) (piv : List (Nat × Nat)) (h : Echelon5 piv)
    {W : Submodule F4 GF5} (hW2 : Module.finrank F4 W ≤ 1) (hpiv : pivSpan5 piv ≤ W)
    (hvs : ∀ v ∈ vs, decode5 v ∈ W) :
    ∃ piv', pushAll1 piv vs = some piv' ∧ Echelon5 piv' ∧ pivSpan5 piv' ≤ W := by
  induction vs generalizing piv with
  | nil => exact ⟨piv, rfl, h, hpiv⟩
  | cons v vs ih =>
    obtain ⟨piv', hp, rfl⟩ := push1_isSome piv h v hW2 hpiv (hvs v List.mem_cons_self)
    have hsp : pivSpan5 (insertPivot 5 piv v) ≤ W := by
      refine (insertPivot_span5 piv v).trans (sup_le hpiv ?_)
      rw [Submodule.span_le]; rintro _ rfl; exact hvs v List.mem_cons_self
    obtain ⟨piv'', h1, h2, h3⟩ := ih (insertPivot 5 piv v) (insertPivot_echelon5 piv h v) hsp
      (fun u hu => hvs u (List.mem_cons_of_mem _ hu))
    exact ⟨piv'', by simp [pushAll1, hp, h1], h2, h3⟩

end Mu4.N5
