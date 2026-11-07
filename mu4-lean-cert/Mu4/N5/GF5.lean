import Mu4.F4
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The field GF5(4^5): commutative ring structure (mu_4(5) certificate)

`A5 = GF5(4)[t] / (t^5 + t + ω)`, as coordinate vectors `v : Fin 5 → F4` in the basis `1, t, ..., t^4`.
Multiplication is given by the structure constants `T5 i j k`, the coefficient of `t^k` in `t^(i+j)` reduced modulo
`t^5 + t + ω` (table `pw5`, from `lean/tools/gen_tables5.py`, the field of `runs/hyper/hp2.c` with
`-DN=5 '-DMOD5=2,1,0,0,0'`).

The ring axioms reduce to identities of the structure constants (commutativity, associativity,
unit), which the kernel checks by `decide`.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4

/-- Coefficient vectors of `t^n mod (t^5 + t + ω)` for `n ≤ 8`. -/
def pw5 : Fin 9 → Fin 5 → F4 :=
  ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1],
    ![w, 1, 0, 0, 0], ![0, w, 1, 0, 0], ![0, 0, w, 1, 0], ![0, 0, 0, w, 1]]

/-- Structure constants: `t^i * t^j = ∑ k, T5 i j k * t^k`. -/
def T5 (i j k : Fin 5) : F4 := pw5 ⟨i.val + j.val, by omega⟩ k

/-- Elements of GF5(4^5), as coordinate vectors in the basis `1, t, ..., t^4`. -/
@[ext] structure GF5 where
  v : Fin 5 → F4
  deriving DecidableEq

namespace GF5

/-- The coordinate equivalence. -/
def equivFun : GF5 ≃ (Fin 5 → F4) where
  toFun := GF5.v
  invFun := GF5.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype GF5 := Fintype.ofEquiv _ equivFun.symm

instance : Zero GF5 := ⟨⟨0⟩⟩
instance : Add GF5 := ⟨fun a b => ⟨a.v + b.v⟩⟩
instance : Neg GF5 := ⟨fun a => ⟨-a.v⟩⟩
instance : Sub GF5 := ⟨fun a b => ⟨a.v - b.v⟩⟩
instance : SMul ℕ GF5 := ⟨fun n a => ⟨n • a.v⟩⟩
instance : SMul ℤ GF5 := ⟨fun n a => ⟨n • a.v⟩⟩
instance : SMul F4 GF5 := ⟨fun c a => ⟨c • a.v⟩⟩

@[simp] lemma zero_v : (0 : GF5).v = 0 := rfl
@[simp] lemma add_v (a b : GF5) : (a + b).v = a.v + b.v := rfl
@[simp] lemma neg_v (a : GF5) : (-a).v = -a.v := rfl
@[simp] lemma sub_v (a b : GF5) : (a - b).v = a.v - b.v := rfl
@[simp] lemma nsmul_v (n : ℕ) (a : GF5) : (n • a).v = n • a.v := rfl
@[simp] lemma zsmul_v (n : ℤ) (a : GF5) : (n • a).v = n • a.v := rfl
@[simp] lemma smul_v (c : F4) (a : GF5) : (c • a).v = c • a.v := rfl

lemma v_injective : Function.Injective GF5.v := fun a b h => GF5.ext h

instance : AddCommGroup GF5 :=
  Function.Injective.addCommGroup GF5.v v_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module F4 GF5 :=
  Function.Injective.module F4 ⟨⟨GF5.v, rfl⟩, fun _ _ => rfl⟩ v_injective (fun _ _ => rfl)


/-- `v` as an additive homomorphism. -/
def vHom : GF5 →+ (Fin 5 → F4) := ⟨⟨GF5.v, rfl⟩, fun _ _ => rfl⟩

lemma v_sum {ι : Type*} (s : Finset ι) (f : ι → GF5) :
    (∑ i ∈ s, f i).v = ∑ i ∈ s, (f i).v := map_sum vHom f s

/-- The unit `1 = t^0`. -/
instance : One GF5 := ⟨⟨pw5 0⟩⟩

/-- Multiplication by structure constants. -/
instance : Mul GF5 := ⟨fun a b => ⟨fun k => ∑ i : Fin 5, ∑ j : Fin 5, a.v i * b.v j * T5 i j k⟩⟩

lemma mul_v (a b : GF5) (k : Fin 5) :
    (a * b).v k = ∑ i : Fin 5, ∑ j : Fin 5, a.v i * b.v j * T5 i j k := rfl

@[simp] lemma one_v : (1 : GF5).v = pw5 0 := rfl

/-! Identities of the structure constants, checked by the kernel. -/

lemma T5_comm : ∀ i j k : Fin 5, T5 i j k = T5 j i k := by decide

lemma T5_assoc : ∀ i j m k : Fin 5,
    ∑ l : Fin 5, T5 i j l * T5 l m k = ∑ l : Fin 5, T5 j m l * T5 i l k := by decide

lemma T5_one : ∀ j k : Fin 5, T5 0 j k = if j = k then 1 else 0 := by decide

lemma pw0 : ∀ k : Fin 5, pw5 0 k = if (0 : Fin 5) = k then 1 else 0 := by decide

/-- `∑ i, (1).v i * f i = f 0`. -/
lemma sum_one_mul (f : Fin 5 → F4) : ∑ i : Fin 5, (1 : GF5).v i * f i = f 0 := by
  simp only [one_v, pw0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

protected lemma mul_comm (a b : GF5) : a * b = b * a := by
  ext k
  simp only [mul_v]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [T5_comm j i k]; ring

protected lemma one_mul (a : GF5) : 1 * a = a := by
  ext k
  simp only [mul_v]
  rw [show (∑ i : Fin 5, ∑ j : Fin 5, (1 : GF5).v i * a.v j * T5 i j k)
        = ∑ i : Fin 5, (1 : GF5).v i * (∑ j : Fin 5, a.v j * T5 i j k) by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring]
  rw [sum_one_mul]
  simp only [T5_one, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

protected lemma mul_one (a : GF5) : a * 1 = a := by rw [GF5.mul_comm, GF5.one_mul]

protected lemma left_distrib (a b c : GF5) : a * (b + c) = a * b + a * c := by
  ext k
  simp only [mul_v, add_v, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring

protected lemma right_distrib (a b c : GF5) : (a + b) * c = a * c + b * c := by
  rw [GF5.mul_comm, GF5.left_distrib, GF5.mul_comm c a, GF5.mul_comm c b]

protected lemma zero_mul (a : GF5) : 0 * a = 0 := by
  ext k; simp [mul_v]

protected lemma mul_zero (a : GF5) : a * 0 = 0 := by rw [GF5.mul_comm, GF5.zero_mul]

lemma reorder1 (f : Fin 5 → Fin 5 → Fin 5 → Fin 5 → F4) :
    ∑ l, ∑ m, ∑ i, ∑ j, f l m i j = ∑ i, ∑ j, ∑ m, ∑ l, f l m i j := by
  calc ∑ l, ∑ m, ∑ i, ∑ j, f l m i j = ∑ l, ∑ i, ∑ m, ∑ j, f l m i j := by
        refine Finset.sum_congr rfl fun l _ => ?_; exact Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ m, ∑ j, f l m i j := Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ m, f l m i j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ l, ∑ m, f l m i j := by
        refine Finset.sum_congr rfl fun i _ => ?_; exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ m, ∑ l, f l m i j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        exact Finset.sum_comm

lemma reorder2 (g : Fin 5 → Fin 5 → Fin 5 → Fin 5 → F4) :
    ∑ i, ∑ l, ∑ j, ∑ m, g i l j m = ∑ i, ∑ j, ∑ m, ∑ l, g i l j m := by
  calc ∑ i, ∑ l, ∑ j, ∑ m, g i l j m = ∑ i, ∑ j, ∑ l, ∑ m, g i l j m := by
        refine Finset.sum_congr rfl fun i _ => ?_; exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ m, ∑ l, g i l j m := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        exact Finset.sum_comm

lemma mul_assoc_v (a b c : GF5) (k : Fin 5) : (a * b * c).v k =
    ∑ i, ∑ j, ∑ m, a.v i * b.v j * c.v m * ∑ l : Fin 5, T5 i j l * T5 l m k := by
  simp only [mul_v, Finset.sum_mul]
  rw [reorder1]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; ring

lemma mul_assoc_v' (a b c : GF5) (k : Fin 5) : (a * (b * c)).v k =
    ∑ i, ∑ j, ∑ m, a.v i * b.v j * c.v m * ∑ l : Fin 5, T5 j m l * T5 i l k := by
  simp only [mul_v, Finset.sum_mul, Finset.mul_sum]
  rw [reorder2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
  ring

protected lemma mul_assoc (a b c : GF5) : a * b * c = a * (b * c) := by
  ext k
  rw [mul_assoc_v, mul_assoc_v']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun m _ => ?_
  rw [T5_assoc]

instance : CommRing GF5 where
  __ := (inferInstance : AddCommGroup GF5)
  mul_assoc := GF5.mul_assoc
  one_mul := GF5.one_mul
  mul_one := GF5.mul_one
  left_distrib := GF5.left_distrib
  right_distrib := GF5.right_distrib
  zero_mul := GF5.zero_mul
  mul_zero := GF5.mul_zero
  mul_comm := GF5.mul_comm

protected lemma smul_mul (c : F4) (a b : GF5) : (c • a) * b = c • (a * b) := by
  ext k
  simp only [mul_v, smul_v, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring

protected lemma mul_smul (c : F4) (a b : GF5) : a * (c • b) = c • (a * b) := by
  rw [GF5.mul_comm, GF5.smul_mul, GF5.mul_comm]

instance : Algebra F4 GF5 := Algebra.ofModule GF5.smul_mul GF5.mul_smul

/-- The coordinate linear equivalence `GF5 ≃ₗ (Fin 5 → F4)`. -/
def linEquiv : GF5 ≃ₗ[F4] (Fin 5 → F4) where
  toFun := GF5.v
  invFun := GF5.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance : Module.Finite F4 GF5 := Module.Finite.equiv linEquiv.symm

lemma finrank_eq : Module.finrank F4 GF5 = 5 := by
  rw [linEquiv.finrank_eq, Module.finrank_fin_fun]

lemma card_eq : Fintype.card GF5 = 1024 := by
  rw [Fintype.card_congr equivFun]; simp [F4.card]

end GF5
end Mu4.N5
