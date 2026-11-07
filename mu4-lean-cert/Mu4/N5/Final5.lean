import Mu4.N5.Reduction5
import Mu4.N5.Triple5
import Mu4.N5.Check5
import Mu4.N5.Upper5
import Mu4.Transfer

/-!
# mu_4(5) = 11: the final assembly

* `noTen`: no 10-term decomposition is valid on `A5 = GF(4^5)`, from the normal form (`normalFormReduction5`), the
  bridge (`bridge5_holds`) and the search check C3(5) (`searchCheck5`, `native_decide`);
* `mu4_5`: `bilinRank GF(4) (mul GF(4^5)) = 11`, with the 11-term scheme `upper5_bound`;
* `mu4_5_general`: the same for every field `K` with 4 elements and every extension `L` of degree 5.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Lower Mu4.Search

lemma or_false_left {a b : Bool} (ha : a = false) (h : (a || b) = true) : b = true := by
  simpa [ha] using h

lemma skip_false {c v : Nat} (h : c ≠ 1 → v = 0) : (c != 1 && v != 0) = false := by
  by_cases hc : c = 1
  · simp [hc]
  · simp [h hc]

/-- What `checkAll5` certifies. -/
lemma checkAll5_sound {p0 p1 s0 s1 : Nat} (h : checkAll5 p0 p1 s0 s1 = true) :
    (mkPCtx5 p0 p1).ok = true ∧ ∀ n0 n1 n2 n3 n4 : Fin 3, n0.val + n1.val + n2.val + n3.val + n4.val = 7 →
      ∀ w0 w1 w2 w3 w4 : Fin 5, (n0.val ≠ 1 → w0.val = 0) → (n1.val ≠ 1 → w1.val = 0) →
        (n2.val ≠ 1 → w2.val = 0) → (n3.val ≠ 1 → w3.val = 0) → (n4.val ≠ 1 → w4.val = 0) →
        caseOK5 (mkPCtx5 p0 p1) s0 s1 [n0.val, n1.val, n2.val, n3.val, n4.val]
          [w0.val, w1.val, w2.val, w3.val, w4.val] = true := by
  unfold checkAll5 at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1, fun n0 n1 n2 n3 n4 hsum w0 w1 w2 w3 w4 h0 h1 h2 h3 h4 => ?_⟩
  have a0 := List.all_eq_true.mp h.2 n0.val (List.mem_range.mpr n0.isLt)
  have a1 := List.all_eq_true.mp a0 n1.val (List.mem_range.mpr n1.isLt)
  have a2 := List.all_eq_true.mp a1 n2.val (List.mem_range.mpr n2.isLt)
  have a3 := List.all_eq_true.mp a2 n3.val (List.mem_range.mpr n3.isLt)
  have a4 := List.all_eq_true.mp a3 n4.val (List.mem_range.mpr n4.isLt)
  have b := or_false_left (by simp [hsum]) a4
  have b0 := or_false_left (skip_false h0) (List.all_eq_true.mp b w0.val (List.mem_range.mpr w0.isLt))
  have b1 := or_false_left (skip_false h1) (List.all_eq_true.mp b0 w1.val (List.mem_range.mpr w1.isLt))
  have b2 := or_false_left (skip_false h2) (List.all_eq_true.mp b1 w2.val (List.mem_range.mpr w2.isLt))
  have b3 := or_false_left (skip_false h3) (List.all_eq_true.mp b2 w3.val (List.mem_range.mpr w3.isLt))
  exact or_false_left (skip_false h4) (List.all_eq_true.mp b3 w4.val (List.mem_range.mpr w4.isLt))

/-- No 10-term decomposition is valid on `A5`. -/
theorem noTen : ∀ D : Decomp5 10, ¬ D.ValidOn ⊤ := by
  intro D hD
  obtain ⟨k, hk, j, hj, n0, n1, n2, n3, n4, hsum, w0, w1, w2, w3, w4, h0, h1, h2, h3, h4, D', hD', ⟨nf⟩⟩ :=
    normalFormReduction5 D hD
  have hP := List.all_eq_true.mp searchCheck5 _ (pList5_mem k hk)
  have hPS := List.all_eq_true.mp hP _ (sList5_mem j hj)
  obtain ⟨hok, hcases⟩ := checkAll5_sound hPS
  have hc := hcases n0 n1 n2 n3 n4 hsum w0 w1 w2 w3 w4 h0 h1 h2 h3 h4
  rw [bridge5_holds _ (pList5_mem k hk) _ (sList5_mem j hj) _ _ hok D' hD' nf] at hc
  exact absurd hc (by simp)

/-- The main theorem over the concrete fields: `mu_4(5) = 11`. -/
theorem mu4_5 : bilinRank F4 (LinearMap.mul F4 GF5) = 11 := by
  refine bilinRank_eq (by norm_num) upper5_bound ?_
  intro h10
  obtain ⟨a, b, c, hf⟩ := h10
  exact noTen ⟨a, b, c⟩ (fun x _ y => by simpa using hf x y)

/-- In GF(4^5), the solutions of `y^4 = y` are the elements of GF(4). -/
lemma pow4_eq_self5 {y : GF5} (hy : y ^ 4 = y) : ∃ d : F4, algebraMap F4 GF5 d = y := by
  classical
  let p : Polynomial GF5 := Polynomial.X ^ 4 - Polynomial.X
  have hdeg : p.natDegree = 4 := by
    simp only [p]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp
  have hp0 : p ≠ 0 := fun h => by rw [h] at hdeg; simp at hdeg
  have hroot : ∀ z : GF5, z ^ 4 = z → z ∈ p.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    simp [p, hz]
  have hsub : Finset.univ.image (algebraMap F4 GF5) ⊆ p.roots.toFinset := by
    intro z hz
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hz
    apply hroot
    rw [← map_pow]
    congr 1
    have := FiniteField.pow_card d
    rwa [F4.card] at this
  have hcard : (Finset.univ.image (algebraMap F4 GF5)).card = 4 := by
    rw [Finset.card_image_of_injective _ (algebraMap F4 GF5).injective, Finset.card_univ, F4.card]
  have heq : Finset.univ.image (algebraMap F4 GF5) = p.roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard]
    calc p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ = 4 := hdeg
  have hy' := hroot y hy
  rw [← heq] at hy'
  obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hy'
  exact ⟨d, hd⟩

/-- Every field pair `K ⊆ L` with `|K| = 4` and `[L : K] = 5` is isomorphic to `(F4, GF5)`. -/
theorem exists_equiv_GF5 (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    (hK : Fintype.card K = 4) (hL : Module.finrank K L = 5) :
    ∃ (e : L ≃+* GF5) (e0 : K ≃+* F4), ∀ c, e (algebraMap K L c) = algebraMap F4 GF5 (e0 c) := by
  classical
  haveI : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  haveI : Finite L := Module.finite_of_finite K
  letI : Fintype L := Fintype.ofFinite L
  have hcardL : Fintype.card L = 1024 := by
    rw [Module.card_eq_pow_finrank (K := K), hK, hL]
    norm_num
  let e : L ≃+* GF5 := FiniteField.ringEquivOfCardEq (K := L) (K' := GF5) (by rw [hcardL, GF5.card_eq])
  have hmem : ∀ c : K, ∃ d : F4, algebraMap F4 GF5 d = e (algebraMap K L c) := by
    intro c
    apply pow4_eq_self5
    rw [← map_pow, ← map_pow]
    congr 2
    have := FiniteField.pow_card c
    rwa [hK] at this
  choose f hf using hmem
  have hinj : Function.Injective (algebraMap F4 GF5) := (algebraMap F4 GF5).injective
  let e0h : K →+* F4 :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [hf, map_mul, map_mul, map_mul, hf, hf])
      map_zero' := hinj (by rw [hf, map_zero, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [hf, map_add, map_add, map_add, hf, hf]) }
  have hbij : Function.Bijective e0h := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨e0h.injective, by rw [hK, F4.card]⟩
  exact ⟨e, RingEquiv.ofBijective e0h hbij, fun c => (hf c).symm⟩

/-- **The main theorem for n = 5**: for every field `K` with 4 elements and every extension `L` of `K` of degree 5, the
bilinear rank of the multiplication `L × L → L` over `K` is 11. -/
theorem mu4_5_general (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    (hK : Fintype.card K = 4) (hL : Module.finrank K L = 5) :
    bilinRank K (LinearMap.mul K L) = 11 := by
  obtain ⟨e, e0, he⟩ := exists_equiv_GF5 K L hK hL
  rw [bilinRank_transfer e e0 he]
  exact mu4_5

end Mu4.N5
