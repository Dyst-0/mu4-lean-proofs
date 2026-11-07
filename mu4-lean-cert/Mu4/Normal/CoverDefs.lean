import Mu4Comp.Codes
import Mu4Comp.Data
import Mu4.Normal.CoverData

/-!
# The checkers of the coverage facts C1, C2 (`audit/PROOF.md`)

`c1Ok z`, `c2Ok z`: the certificate entry of `Mu4/Normal/CoverData.lean` for the code `z` checks; `ftabOk`: the table of
`σ^s(p1_k)` is right. Their meaning is proved in `Mu4/Normal/Cover.lean`; the checks themselves (kernel `decide`)
are in `Mu4/Normal/CoverCheck1.lean` and `CoverCheck2.lean`. Core Lean only.
-/

set_option autoImplicit false

namespace Mu4.Normal
open Mu4 F4 Mu4.Search

/-- The code of `a + b z` for the pair code `ab` (`a = coordC ab 0`, `b = coordC ab 1`). -/
def lin2 (ab z : Nat) : Nat := smulC (coordC ab 0) 1 ^^^ smulC (coordC ab 1) z

/-- Entry `12 k + s` of `frobTab`. -/
def ftab (k s : Nat) : Nat := (frobTab >>> (12 * (12 * k + s))) % 4096

/-- The entry of `c1Tab` for `z` checks. -/
def c1Ok (z : Nat) : Bool :=
  let e := (c1Tab >>> (16 * z)) % 65536
  let cd := e % 16
  let ab := (e / 16) % 16
  let s := (e / 256) % 16
  let k := e / 4096
  k < 10 && s < 12 && ab != 0 && mulK (lin2 ab z) (ftab k s) == lin2 cd z

/-- The entry of `c2Tab` for `z` checks. -/
def c2Ok (z : Nat) : Bool :=
  let e := (c2Tab >>> (16 * z)) % 65536
  let cd := e % 16
  let ab := (e / 16) % 16
  let j := e / 256
  j < 69 && ab != 0 && mulK (lin2 ab z) (sList.getD j (0, 0)).2 == lin2 cd z

/-- `frobTab` lists `σ^s(p1_k)`: entry `s = 0` is `p1_k`, and each entry squares to the next. -/
def ftabOk : Bool :=
  (List.range 10).all fun k => ftab k 0 == (pList.getD k (0, 0)).2 &&
    (List.range 11).all fun s => ftab k (s + 1) == mulK (ftab k s) (ftab k s)

end Mu4.Normal
