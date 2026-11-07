import Mu4.GFField
import Mu4.Rank
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Upper bound: a 14-term scheme

A symmetric 14-term bilinear scheme for multiplication in GF(4^6) over GF(4), built from scratch by
`lean/tools/gen_crt14.py`: CRT for the product of two polynomials of degree ≤ 5 at the places
`t = 0, 1, ω, ω²` (one product each), the three irreducible quadratics `t² + t + ω`, `t² + t + ω²`,
`t² + ωt + 1` (Karatsuba, three products each) and infinity (`x₅ y₅`), followed by reduction
modulo `t⁶ + t² + t + ω`. Row `r` of `aRow` is the linear form `a_r = b_r`, row `r` of `cRow` the
output vector `c_r`. The kernel checks all 216 coefficient equations (`scheme_check`).
-/

namespace Mu4
open F4

/-- The forms `a_r = b_r` of the scheme, as coefficient rows on the coordinates `x_0..x_5`. -/
def aRow : Fin 14 → Fin 6 → F4 :=
  ![![1, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1], ![1, w, w2, 1, w, w2], 
    ![1, w2, w, 1, w2, w], ![1, 0, w, w, 1, w], ![0, 1, 1, w2, 1, 0], 
    ![1, 1, w2, 1, 0, w], ![1, 0, w2, w2, 1, w2], ![0, 1, 1, w, 1, 0], 
    ![1, 1, w, 1, 0, w2], ![1, 0, 1, w, w, 1], ![0, 1, w, w, 1, 0], 
    ![1, 1, w2, 0, w2, 1], ![0, 0, 0, 0, 0, 1]]

/-- The output vectors `c_r` of the scheme. -/
def cRow : Fin 14 → Fin 6 → F4 :=
  ![![1, 1, 1, 1, 1, 0], ![w, 0, w, 1, w, 1], ![w2, w2, w2, 1, 0, w2], 
    ![1, 0, w, w, w, w], ![0, w2, w, w2, w, w], ![w2, w, 1, w, w2, w], 
    ![w, w, 1, w, 0, w2], ![0, 0, 0, 0, 1, w2], ![1, 1, 1, w, w, w2], 
    ![w, w, w, w2, w, w], ![0, 1, w, w, 1, 0], ![0, 1, 0, w2, w2, 0], 
    ![0, 0, 1, w2, 1, 0], ![0, 1, 1, 1, 1, 1]]

/-- The coefficient equations: `∑ r, a_r(e_i) a_r(e_j) c_r = e_i e_j` for all basis pairs. -/
theorem scheme_check : ∀ i j k : Fin 6,
    ∑ r : Fin 14, aRow r i * aRow r j * cRow r k = T i j k := by decide

/-- The linear form `x ↦ ∑ i, aRow r i * x_i`. -/
def schemeForm (r : Fin 14) : GF →ₗ[F4] F4 where
  toFun x := ∑ i : Fin 6, aRow r i * x.v i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring

lemma upper_coord (x y : GF) (k : Fin 6) :
    (x * y).v k = ∑ r : Fin 14, (schemeForm r x * schemeForm r y) * cRow r k := by
  calc (x * y).v k = ∑ i : Fin 6, ∑ j : Fin 6, x.v i * y.v j * T i j k := GF.mul_v x y k
    _ = ∑ i : Fin 6, ∑ j : Fin 6, ∑ r : Fin 14,
          x.v i * y.v j * (aRow r i * aRow r j * cRow r k) := by
        simp only [← scheme_check, Finset.mul_sum]
    _ = ∑ i : Fin 6, ∑ r : Fin 14, ∑ j : Fin 6,
          x.v i * y.v j * (aRow r i * aRow r j * cRow r k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_comm
    _ = ∑ r : Fin 14, ∑ i : Fin 6, ∑ j : Fin 6,
          x.v i * y.v j * (aRow r i * aRow r j * cRow r k) := Finset.sum_comm
    _ = ∑ r : Fin 14, (schemeForm r x * schemeForm r y) * cRow r k := by
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [schemeForm, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- The upper bound: multiplication in GF(4^6) is a sum of 14 products of linear forms. -/
theorem upper_bound : HasDecomp F4 (LinearMap.mul F4 GF) 14 := by
  refine ⟨schemeForm, schemeForm, fun r => ⟨cRow r⟩, fun x y => ?_⟩
  rw [LinearMap.mul_apply']
  ext k
  rw [upper_coord]
  simp only [GF.v_sum, Finset.sum_apply, GF.smul_v, Pi.smul_apply, smul_eq_mul]

end Mu4
