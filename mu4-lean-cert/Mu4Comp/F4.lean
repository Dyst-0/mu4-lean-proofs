/-!
# GF(4): the type and its operations (core Lean only)

Computational part of `Mu4.F4`: no Mathlib import, so that the searches compile to native code
without compiling Mathlib. The `Field` instance and all proofs are in `Mu4/F4.lean`.
-/

namespace Mu4

/-- The four elements of GF(4): `z = 0`, `o = 1`, `w = ω`, `w2 = ω² = ω + 1`. -/
inductive F4 : Type
  | z | o | w | w2
  deriving DecidableEq, Repr, Inhabited

namespace F4

/-- Addition (characteristic 2). -/
@[inline] def add : F4 → F4 → F4
  | z, x => x
  | x, z => x
  | o, o => z
  | o, w => w2
  | o, w2 => w
  | w, o => w2
  | w, w => z
  | w, w2 => o
  | w2, o => w
  | w2, w => o
  | w2, w2 => z

/-- Multiplication. -/
@[inline] def mul : F4 → F4 → F4
  | z, _ => z
  | _, z => z
  | o, x => x
  | x, o => x
  | w, w => w2
  | w, w2 => o
  | w2, w => o
  | w2, w2 => w

/-- Inverse, with `0⁻¹ = 0`. -/
@[inline] def inv : F4 → F4
  | z => z
  | o => o
  | w => w2
  | w2 => w

instance : Zero F4 := ⟨z⟩
instance : One F4 := ⟨o⟩
instance : Add F4 := ⟨add⟩
instance : Mul F4 := ⟨mul⟩
instance : Neg F4 := ⟨id⟩
instance : Sub F4 := ⟨add⟩
instance : Inv F4 := ⟨inv⟩
instance : Div F4 := ⟨fun a b => mul a (inv b)⟩

/-- The element of GF(4) with bits `b0` (coefficient of 1) and `b1` (coefficient of ω). -/
@[inline] def ofBits : Bool → Bool → F4
  | false, false => z
  | true, false => o
  | false, true => w
  | true, true => w2

/-- The 2-bit code of an element of GF(4): `z, o, w, w2 ↦ 0, 1, 2, 3`. -/
@[inline] def code : F4 → Nat
  | z => 0
  | o => 1
  | w => 2
  | w2 => 3

end F4
end Mu4
