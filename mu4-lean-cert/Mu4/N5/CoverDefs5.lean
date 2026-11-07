import Mu4Comp5.Codes
import Mu4Comp5.Data
import Mu4.N5.CoverData5
import Mu4.Normal.CoverDefs

/-!
# The checkers of the coverage facts C1(5), C2(5) (`audit/PROOF.md`, mu_4(5))

`c1Ok5 z`, `c2Ok5 z`: the certificate entry of `Mu4/N5/CoverData5.lean` for the code `z` checks; `ftabOk5`: the table
of `σ^s(p1_k)` is right. `lin2 ab z = a + b z` is that of `Mu4.Normal`. Core Lean only.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Normal

/-- Entry `10 k + s` of `frobTab5`. -/
def ftab5 (k s : Nat) : Nat := (frobTab5 >>> (10 * (10 * k + s))) % 1024

/-- The entry of `c1Tab5` for `z` checks. -/
def c1Ok5 (z : Nat) : Bool :=
  let e := (c1Tab5 >>> (16 * z)) % 65536
  let cd := e % 16
  let ab := (e / 16) % 16
  let s := (e / 256) % 16
  let k := e / 4096
  k < 3 && s < 10 && ab != 0 && mulK5 (lin2 ab z) (ftab5 k s) == lin2 cd z

/-- The entry of `c2Tab5` for `z` checks. -/
def c2Ok5 (z : Nat) : Bool :=
  let e := (c2Tab5 >>> (16 * z)) % 65536
  let cd := e % 16
  let ab := (e / 16) % 16
  let j := e / 256
  j < 17 && ab != 0 && mulK5 (lin2 ab z) (sList5.getD j (0, 0)).2 == lin2 cd z

/-- `frobTab5` lists `σ^s(p1_k)`. -/
def ftabOk5 : Bool :=
  (List.range 3).all fun k => ftab5 k 0 == (pList5.getD k (0, 0)).2 &&
    (List.range 9).all fun s => ftab5 k (s + 1) == mulK5 (ftab5 k s) (ftab5 k s)

end Mu4.N5
