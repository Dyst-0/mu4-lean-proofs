import Mu4.Rank
import Mu4.Field
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Transfer to any field pair `K ⊆ L` with `|K| = 4` and `[L : K] = 6`

The bilinear rank of multiplication does not change along a ring isomorphism `L ≃+* L'` that
restricts to an isomorphism `K ≃+* K'` (`bilinRank_transfer`). Every such pair `(K, L)` is
isomorphic in this sense to the concrete pair `(F4, GF)` (`exists_equiv_GF`): the finite fields
`L` and `GF` with 4096 elements are isomorphic, and any isomorphism maps `K` onto the solutions
of `y^4 = y` in `GF`, which are the elements of `F4` (`pow4_eq_self`).
-/

namespace Mu4

section Transfer

variable {K L K' L' : Type*} [Field K] [Field L] [Algebra K L] [Field K'] [Field L']
  [Algebra K' L']

/-- A decomposition moves along `e : L ≃+* L'` restricting to `e0 : K ≃+* K'`. -/
lemma HasDecomp.transfer (e : L ≃+* L') (e0 : K ≃+* K')
    (he : ∀ c, e (algebraMap K L c) = algebraMap K' L' (e0 c)) {r : ℕ}
    (h : HasDecomp K' (LinearMap.mul K' L') r) : HasDecomp K (LinearMap.mul K L) r := by
  obtain ⟨a, b, c, hf⟩ := h
  have hsm : ∀ (k : K) (x : L), e (k • x) = e0 k • e x := by
    intro k x
    rw [Algebra.smul_def, map_mul, he, ← Algebra.smul_def]
  let tr : (L' →ₗ[K'] K') → (L →ₗ[K] K) := fun f =>
    { toFun := fun x => e0.symm (f (e x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun k x => by
        rw [hsm, map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
        rfl }
  refine ⟨fun i => tr (a i), fun i => tr (b i), fun i => e.symm (c i), fun x y => ?_⟩
  apply e.injective
  have h1 := hf (e x) (e y)
  simp only [LinearMap.mul_apply'] at h1 ⊢
  rw [map_mul, h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsm, RingEquiv.apply_symm_apply, map_mul]
  simp [tr]

/-- The bilinear rank of multiplication is the same for isomorphic field pairs. -/
theorem bilinRank_transfer (e : L ≃+* L') (e0 : K ≃+* K')
    (he : ∀ c, e (algebraMap K L c) = algebraMap K' L' (e0 c)) :
    bilinRank K (LinearMap.mul K L) = bilinRank K' (LinearMap.mul K' L') := by
  have he' : ∀ c, e.symm (algebraMap K' L' c) = algebraMap K L (e0.symm c) := by
    intro c
    apply e.injective
    rw [RingEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply]
  unfold bilinRank
  congr 1
  ext r
  exact ⟨fun h => h.transfer e.symm e0.symm he', fun h => h.transfer e e0 he⟩

end Transfer

/-- In GF(4^6), the solutions of `y^4 = y` are the elements of GF(4). -/
lemma pow4_eq_self {y : GF} (hy : y ^ 4 = y) : ∃ d : F4, algebraMap F4 GF d = y := by
  classical
  let p : Polynomial GF := Polynomial.X ^ 4 - Polynomial.X
  have hdeg : p.natDegree = 4 := by
    simp only [p]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp
  have hp0 : p ≠ 0 := fun h => by rw [h] at hdeg; simp at hdeg
  have hroot : ∀ z : GF, z ^ 4 = z → z ∈ p.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    simp [p, hz]
  have hsub : Finset.univ.image (algebraMap F4 GF) ⊆ p.roots.toFinset := by
    intro z hz
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hz
    apply hroot
    rw [← map_pow]
    congr 1
    have := FiniteField.pow_card d
    rwa [F4.card] at this
  have hcard : (Finset.univ.image (algebraMap F4 GF)).card = 4 := by
    rw [Finset.card_image_of_injective _ (algebraMap F4 GF).injective, Finset.card_univ, F4.card]
  have heq : Finset.univ.image (algebraMap F4 GF) = p.roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard]
    calc p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ = 4 := hdeg
  have hy' := hroot y hy
  rw [← heq] at hy'
  obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hy'
  exact ⟨d, hd⟩

/-- Every field pair `K ⊆ L` with `|K| = 4` and `[L : K] = 6` is isomorphic to `(F4, GF)`. -/
theorem exists_equiv_GF (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    (hK : Fintype.card K = 4) (hL : Module.finrank K L = 6) :
    ∃ (e : L ≃+* GF) (e0 : K ≃+* F4), ∀ c, e (algebraMap K L c) = algebraMap F4 GF (e0 c) := by
  classical
  haveI : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  haveI : Finite L := Module.finite_of_finite K
  letI : Fintype L := Fintype.ofFinite L
  have hcardL : Fintype.card L = 4096 := by
    rw [Module.card_eq_pow_finrank (K := K), hK, hL]
    norm_num
  let e : L ≃+* GF := FiniteField.ringEquivOfCardEq (K := L) (K' := GF) (by rw [hcardL, GF.card_eq])
  have hmem : ∀ c : K, ∃ d : F4, algebraMap F4 GF d = e (algebraMap K L c) := by
    intro c
    apply pow4_eq_self
    rw [← map_pow, ← map_pow]
    congr 2
    have := FiniteField.pow_card c
    rwa [hK] at this
  choose f hf using hmem
  have hinj : Function.Injective (algebraMap F4 GF) := (algebraMap F4 GF).injective
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

end Mu4
