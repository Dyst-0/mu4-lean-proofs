import Mu4.N5.Field5
import Mu4.Rank
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Upper bound for mu_4(5): an 11-term scheme

A symmetric 11-term bilinear scheme for multiplication in GF(4^5) over GF(4), built from scratch by
`lean/tools/gen_crt11.py`: CRT for the product of two polynomials of degree ≤ 4 at the places `t = 0, 1, ω, ω²`
(one product each), the irreducible quadratics `t² + t + ω`, `t² + t + ω²` (Karatsuba, three products each) and
infinity (`x₄ y₄`), followed by reduction modulo `t⁵ + t + ω`. The kernel checks all 125 coefficient equations
(`scheme5_check`).
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4

/-- The forms `a_r = b_r` of the scheme, as coefficient rows on the coordinates `x_0..x_4`. -/
def aRow5 : Fin 11 → Fin 5 → F4 :=
  ![![1, 0, 0, 0, 0], ![1, 1, 1, 1, 1], ![1, w, w2, 1, w], ![1, w2, w, 1, w2], ![1, 0, w, w, 1],
    ![0, 1, 1, w2, 1], ![1, 1, w2, 1, 0], ![1, 0, w2, w2, 1], ![0, 1, 1, w, 1], ![1, 1, w, 1, 0],
    ![0, 0, 0, 0, 1]]

/-- The output vectors `c_r` of the scheme. -/
def cRow5 : Fin 11 → Fin 5 → F4 :=
  ![![1, 1, w, 0, 0], ![w, w, w2, 1, 1], ![1, w2, 1, w, 1], ![w2, 1, 0, w2, 1], ![w2, 1, 0, 1, w],
    ![w2, 0, 0, w, 1], ![1, 1, 0, 0, 1], ![1, 1, 1, 1, w2], ![1, w2, 0, w2, 1], ![w2, 0, 1, 0, 1],
    ![0, 1, 1, w, 0]]

/-- The coefficient equations: `∑ r, a_r(e_i) a_r(e_j) c_r = e_i e_j` for all basis pairs. -/
theorem scheme5_check : ∀ i j k : Fin 5,
    ∑ r : Fin 11, aRow5 r i * aRow5 r j * cRow5 r k = T5 i j k := by decide

/-- The linear form `x ↦ ∑ i, aRow5 r i * x_i`. -/
def schemeForm5 (r : Fin 11) : GF5 →ₗ[F4] F4 where
  toFun x := ∑ i : Fin 5, aRow5 r i * x.v i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring

lemma upper5_coord (x y : GF5) (k : Fin 5) :
    (x * y).v k = ∑ r : Fin 11, (schemeForm5 r x * schemeForm5 r y) * cRow5 r k := by
  calc (x * y).v k = ∑ i : Fin 5, ∑ j : Fin 5, x.v i * y.v j * T5 i j k := GF5.mul_v x y k
    _ = ∑ i : Fin 5, ∑ j : Fin 5, ∑ r : Fin 11,
          x.v i * y.v j * (aRow5 r i * aRow5 r j * cRow5 r k) := by
        simp only [← scheme5_check, Finset.mul_sum]
    _ = ∑ i : Fin 5, ∑ r : Fin 11, ∑ j : Fin 5,
          x.v i * y.v j * (aRow5 r i * aRow5 r j * cRow5 r k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_comm
    _ = ∑ r : Fin 11, ∑ i : Fin 5, ∑ j : Fin 5,
          x.v i * y.v j * (aRow5 r i * aRow5 r j * cRow5 r k) := Finset.sum_comm
    _ = ∑ r : Fin 11, (schemeForm5 r x * schemeForm5 r y) * cRow5 r k := by
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [schemeForm5, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- The upper bound: multiplication in GF(4^5) is a sum of 11 products of linear forms. -/
theorem upper5_bound : HasDecomp F4 (LinearMap.mul F4 GF5) 11 := by
  refine ⟨schemeForm5, schemeForm5, fun r => ⟨cRow5 r⟩, fun x y => ?_⟩
  rw [LinearMap.mul_apply']
  ext k
  rw [upper5_coord]
  simp only [GF5.v_sum, Finset.sum_apply, GF5.smul_v, Pi.smul_apply, smul_eq_mul]

end Mu4.N5
