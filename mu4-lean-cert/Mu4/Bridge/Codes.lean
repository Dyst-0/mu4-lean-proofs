import Mu4.Lower.Count
import Mu4Comp.Search.Dir

/-!
# Semantics of the search's code primitives

Decoding lemmas for the linear-algebra primitives of `Mu4Comp.Search` (linear combinations, unit
vectors, 2×2 matrix codes, `firstNZ`) and the fact that `rankC` is a lower bound for the true
rank (pivot lists in echelon form decode to independent vectors in the span of the input).
-/

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower

/-! ### Linear combinations -/

lemma decode_combo (c : Nat) (vs : List Nat) :
    decode (combo c vs) = ∑ k : Fin vs.length, coordC c k • decode (vs.get k) := by
  simp [combo]

lemma decode_combo4 (c : Nat) (k0 k1 k2 k3 : Nat) :
    decode (combo4 c [k0, k1, k2, k3]) =
      coordC c 0 • decode k0 + coordC c 1 • decode k1 + coordC c 2 • decode k2 +
        coordC c 3 • decode k3 := by
  simp [combo4]

lemma combo4_eq_combo (c : Nat) (ks : List Nat) : decode (combo4 c ks) = decode (combo c ks) := by
  match ks with
  | [k0, k1, k2, k3] => rw [decode_combo4, decode_combo]; simp [Fin.sum_univ_four]
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ => rfl

lemma decode_applyCols6 (a0 a1 a2 a3 a4 a5 v : Nat) :
    decode (applyCols [a0, a1, a2, a3, a4, a5] v) =
      coordC v 0 • decode a0 + coordC v 1 • decode a1 + coordC v 2 • decode a2 +
        coordC v 3 • decode a3 + coordC v 4 • decode a4 + coordC v 5 • decode a5 := by
  simp [applyCols]

/-! ### Unit codes and 2×2 matrices -/

lemma coordC_unitC (c : F4) (l l' : Nat) : coordC (unitC c l) l' = if l = l' then c else 0 :=
  coordC_shift c l l'

@[simp] lemma m00_mat2 (a b c d : F4) : m00 (mat2 a b c d) = a := by
  simp [m00, mat2, coordC_unitC]
@[simp] lemma m01_mat2 (a b c d : F4) : m01 (mat2 a b c d) = b := by
  simp [m01, mat2, coordC_unitC]
@[simp] lemma m10_mat2 (a b c d : F4) : m10 (mat2 a b c d) = c := by
  simp [m10, mat2, coordC_unitC]
@[simp] lemma m11_mat2 (a b c d : F4) : m11 (mat2 a b c d) = d := by
  simp [m11, mat2, coordC_unitC]

/-- A matrix code is determined by its four entries. -/
lemma mat2_ext {G H : Nat} (hG : G < 256) (hH : H < 256) (h00 : m00 G = m00 H) (h01 : m01 G = m01 H)
    (h10 : m10 G = m10 H) (h11 : m11 G = m11 H) : G = H := by
  have key : ∀ x < 256, x = mat2 (m00 x) (m01 x) (m10 x) (m11 x) := by decide +kernel
  rw [key G hG, key H hH, h00, h01, h10, h11]

/-! ### `firstNZ` -/

lemma firstNZ_some {v i k p : Nat} (h : firstNZ v i k = some p) :
    i ≤ p ∧ p < i + k ∧ coordC v p ≠ 0 := by
  induction k generalizing i with
  | zero => simp [firstNZ] at h
  | succ k ih =>
    unfold firstNZ at h
    split_ifs at h with hc
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨le_refl _, by omega, by simpa using hc⟩
    · obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨by omega, by omega, h3⟩

lemma firstNZ_none {v i k : Nat} (h : firstNZ v i k = none) : ∀ l, i ≤ l → l < i + k → coordC v l = 0 := by
  induction k generalizing i with
  | zero => intro l h1 h2; omega
  | succ k ih =>
    unfold firstNZ at h
    split_ifs at h with hc
    intro l h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · simpa using hc
    · exact ih h l (by omega) (by omega)

/-! ### Echelon pivot lists and the rank lower bound -/

/-- Echelon form: each pivot vector has a 1 at its position (`< 6`), and all later pivot vectors
vanish there. -/
def Echelon : List (Nat × Nat) → Prop
  | [] => True
  | (p, v) :: rest => p < 6 ∧ coordC v p = 1 ∧ (∀ q ∈ rest, coordC q.2 p = 0) ∧ Echelon rest

lemma echelon_append (piv : List (Nat × Nat)) (p v : Nat) (h : Echelon piv) (hp : p < 6)
    (hv : coordC v p = 1) (hz : ∀ q ∈ piv, coordC v q.1 = 0) : Echelon (piv ++ [(p, v)]) := by
  induction piv with
  | nil => exact ⟨hp, hv, by simp, trivial⟩
  | cons x rest ih =>
    obtain ⟨hx1, hx2, hx3, hx4⟩ := h
    refine ⟨hx1, hx2, ?_, ih hx4 fun q hq => hz q (List.mem_cons_of_mem _ hq)⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hx3 q hq
    · simp at hq; subst hq; exact hz x List.mem_cons_self

/-- One reduction step. -/
lemma coordC_reduce_step (v p w l : Nat) (hl : l < 32) :
    coordC (v ^^^ smulC (coordC v p) w) l = coordC v l + coordC v p * coordC w l := by
  rw [coordC_xor, coordC_smulC _ _ _ hl]

/-- `reduceBy` kills the pivot positions. -/
lemma reduceBy_zero_at (piv : List (Nat × Nat)) (h : Echelon piv) (v : Nat) :
    ∀ q ∈ piv, coordC (reduceBy piv v) q.1 = 0 := by
  induction piv generalizing v with
  | nil => simp
  | cons x rest ih =>
    obtain ⟨hx1, hx2, hx3, hx4⟩ := h
    intro q hq
    have hstep : reduceBy (x :: rest) v = reduceBy rest (v ^^^ smulC (coordC v x.1) x.2) := rfl
    rw [hstep]
    rcases List.mem_cons.mp hq with rfl | hq
    · -- the later pivots vanish at q.1, so the coordinate stays 0
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
lemma reduceBy_mem (piv : List (Nat × Nat)) (v : Nat) :
    decode (reduceBy piv v) - decode v ∈ Submodule.span F4 {x | ∃ q ∈ piv, x = decode q.2} := by
  induction piv generalizing v with
  | nil => simp [reduceBy]
  | cons x rest ih =>
    have hstep : reduceBy (x :: rest) v = reduceBy rest (v ^^^ smulC (coordC v x.1) x.2) := rfl
    rw [hstep]
    have h1 := ih (v ^^^ smulC (coordC v x.1) x.2)
    have : decode (reduceBy rest (v ^^^ smulC (coordC v x.1) x.2)) - decode v =
        (decode (reduceBy rest (v ^^^ smulC (coordC v x.1) x.2)) -
          decode (v ^^^ smulC (coordC v x.1) x.2)) + coordC v x.1 • decode x.2 := by
      rw [decode_xor, decode_smulC]; abel
    rw [this]
    refine Submodule.add_mem _ (Submodule.span_mono ?_ h1) ?_
    · rintro y ⟨q, hq, rfl⟩; exact ⟨q, List.mem_cons_of_mem _ hq, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, List.mem_cons_self, rfl⟩)

/-- Coordinates of a finite combination of decoded codes. -/
lemma v_lin {ι : Type*} [Fintype ι] (c : ι → F4) (w : ι → Nat) (l : Fin 6) :
    (∑ i, c i • decode (w i)).v l = ∑ i, c i * coordC (w i) l.val := by
  rw [GF.v_sum, Finset.sum_apply]
  rfl

/-- Echelon pivot vectors are linearly independent. -/
lemma echelon_indep (piv : List (Nat × Nat)) (h : Echelon piv) :
    LinearIndependent F4 (fun i : Fin piv.length => decode (piv.get i).2) := by
  induction piv with
  | nil => exact linearIndependent_empty_type (ι := Fin 0)
  | cons x rest ih =>
    obtain ⟨hx1, hx2, hx3, hx4⟩ := h
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∑ i : Fin (rest.length + 1), g i • decode ((x :: rest).get i).2 = 0 := hg
    have h0 : g 0 = 0 := by
      have this := v_lin (ι := Fin (rest.length + 1)) (fun i => g i)
        (fun i => ((x :: rest).get i).2) ⟨x.1, hx1⟩
      rw [hg', GF.zero_v, Pi.zero_apply, Fin.sum_univ_succ] at this
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

lemma echelon_pos (piv : List (Nat × Nat)) (h : Echelon piv) : ∀ q ∈ piv, q.1 < 6 := by
  induction piv with
  | nil => simp
  | cons x rest ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact ih h.2.2.2 q hq

/-- `insertPivot` keeps the echelon form. -/
lemma insertPivot_echelon (piv : List (Nat × Nat)) (h : Echelon piv) (v : Nat) :
    Echelon (insertPivot 6 piv v) := by
  cases hf : firstNZ (reduceBy piv v) 0 6 with
  | none => simpa [insertPivot, hf] using h
  | some p =>
    simp only [insertPivot, hf]
    obtain ⟨-, hp6, hcp⟩ := firstNZ_some hf
    apply echelon_append piv _ _ h (by omega)
    · rw [coordC_smulC _ _ _ (by omega), inv_mul_cancel₀ hcp]
    · intro q hq
      have hq6 := echelon_pos piv h q hq
      rw [coordC_smulC _ _ _ (by omega), reduceBy_zero_at piv h v q hq, mul_zero]

/-- The span of the decoded pivot vectors. -/
def pivSpan (piv : List (Nat × Nat)) : Submodule F4 GF :=
  Submodule.span F4 {x | ∃ q ∈ piv, x = decode q.2}

/-- The new pivot vectors lie in the span of the old ones and `v`. -/
lemma insertPivot_span (piv : List (Nat × Nat)) (v : Nat) :
    pivSpan (insertPivot 6 piv v) ≤ pivSpan piv ⊔ Submodule.span F4 {decode v} := by
  rw [pivSpan, Submodule.span_le]
  rintro x ⟨q, hq, rfl⟩
  cases hf : firstNZ (reduceBy piv v) 0 6 with
  | none =>
    simp only [insertPivot, hf] at hq
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨q, hq, rfl⟩)
  | some p =>
    simp only [insertPivot, hf] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨q, hq, rfl⟩)
    · simp only [List.mem_singleton] at hq
      subst hq
      simp only [decode_smulC]
      apply Submodule.smul_mem
      have h1 := reduceBy_mem piv v
      have : decode (reduceBy piv v) = (decode (reduceBy piv v) - decode v) + decode v := by abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left h1)
        (Submodule.mem_sup_right (Submodule.subset_span rfl))

/-- The length of an echelon list is the dimension of its span. -/
lemma echelon_length_le (piv : List (Nat × Nat)) (h : Echelon piv) {W : Submodule F4 GF}
    (hW : pivSpan piv ≤ W) : piv.length ≤ Module.finrank F4 W := by
  have hli := echelon_indep piv h
  have hmem : ∀ i : Fin piv.length, decode (piv.get i).2 ∈ W := fun i =>
    hW (Submodule.subset_span ⟨piv.get i, List.get_mem _ _, rfl⟩)
  let f : Fin piv.length → W := fun i => ⟨decode (piv.get i).2, hmem i⟩
  have hf : LinearIndependent F4 f := by
    apply LinearIndependent.of_comp W.subtype
    exact hli
  simpa using hf.fintype_card_le_finrank

/-- `insertPivot` length bound. -/
lemma insertPivot_length_le (piv : List (Nat × Nat)) (h : Echelon piv) (v : Nat)
    {W : Submodule F4 GF} (hW : pivSpan piv ≤ W) (hv : decode v ∈ W) :
    (insertPivot 6 piv v).length ≤ Module.finrank F4 W := by
  apply echelon_length_le _ (insertPivot_echelon piv h v)
  refine (insertPivot_span piv v).trans (sup_le hW ?_)
  rw [Submodule.span_le]; rintro _ rfl; exact hv

lemma foldl_insertPivot_echelon (vs : List Nat) (piv : List (Nat × Nat)) (h : Echelon piv) :
    Echelon (vs.foldl (insertPivot 6) piv) := by
  induction vs generalizing piv with
  | nil => exact h
  | cons v vs ih => exact ih _ (insertPivot_echelon piv h v)

lemma foldl_insertPivot_span (vs : List Nat) (piv : List (Nat × Nat)) {W : Submodule F4 GF}
    (hW : pivSpan piv ≤ W) (hvs : ∀ v ∈ vs, decode v ∈ W) :
    pivSpan (vs.foldl (insertPivot 6) piv) ≤ W := by
  induction vs generalizing piv with
  | nil => exact hW
  | cons v vs ih =>
    apply ih _ _ (fun u hu => hvs u (List.mem_cons_of_mem _ hu))
    refine (insertPivot_span piv v).trans (sup_le hW ?_)
    rw [Submodule.span_le]; rintro _ rfl; exact hvs v List.mem_cons_self

/-- `rankC` is a lower bound for the true rank: if all vectors lie in `W`, then
`rankC vs ≤ finrank W`. -/
theorem rankC_le (vs : List Nat) {W : Submodule F4 GF} (hvs : ∀ v ∈ vs, decode v ∈ W) :
    rankC vs ≤ Module.finrank F4 W := by
  apply echelon_length_le _ (foldl_insertPivot_echelon vs [] trivial)
  apply foldl_insertPivot_span vs [] _ hvs
  rw [pivSpan, Submodule.span_le]
  rintro x ⟨q, hq, -⟩
  simp at hq

/-- `push2` succeeds when the true rank stays at most 2. -/
lemma push2_isSome (piv : List (Nat × Nat)) (h : Echelon piv) (v : Nat) {W : Submodule F4 GF}
    (hW2 : Module.finrank F4 W ≤ 2) (hpiv : pivSpan piv ≤ W) (hv : decode v ∈ W) :
    ∃ piv', push2 piv v = some piv' ∧ piv' = insertPivot 6 piv v := by
  have := insertPivot_length_le piv h v hpiv hv
  refine ⟨insertPivot 6 piv v, ?_, rfl⟩
  simp only [push2]
  rw [if_pos (by omega)]

/-- `pushAll2` succeeds when all vectors lie in a subspace of dimension at most 2. -/
lemma pushAll2_isSome (vs : List Nat) (piv : List (Nat × Nat)) (h : Echelon piv)
    {W : Submodule F4 GF} (hW2 : Module.finrank F4 W ≤ 2) (hpiv : pivSpan piv ≤ W)
    (hvs : ∀ v ∈ vs, decode v ∈ W) :
    ∃ piv', pushAll2 piv vs = some piv' ∧ Echelon piv' ∧ pivSpan piv' ≤ W := by
  induction vs generalizing piv with
  | nil => exact ⟨piv, rfl, h, hpiv⟩
  | cons v vs ih =>
    obtain ⟨piv', hp, rfl⟩ := push2_isSome piv h v hW2 hpiv (hvs v List.mem_cons_self)
    have hsp : pivSpan (insertPivot 6 piv v) ≤ W := by
      refine (insertPivot_span piv v).trans (sup_le hpiv ?_)
      rw [Submodule.span_le]; rintro _ rfl; exact hvs v List.mem_cons_self
    obtain ⟨piv'', h1, h2, h3⟩ := ih (insertPivot 6 piv v) (insertPivot_echelon piv h v) hsp
      (fun u hu => hvs u (List.mem_cons_of_mem _ hu))
    exact ⟨piv'', by simp [pushAll2, hp, h1], h2, h3⟩

end Mu4.Bridge
