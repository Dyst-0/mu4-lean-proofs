import Mu4Comp.Search.Core

/-!
# The reduced echelon pairs of GF(4)^4: the witness check

For every pair `u, u'` of 8-bit codes (vectors of GF(4)^4), a 24-bit witness entry `e` from
`lean/tools/gen_rref4.py` (second agent, 11-06):
- `e / 65536 = 0`: the pair is dependent, with `ab = e % 16 ≠ 0` and `a u + b u' = 0`;
- otherwise `(r0, r1) = (e / 65536, e / 256 % 256)` satisfies the condition of `rrefPairs`, with
  `r0 = a u + b u'` for `ab = e / 16 % 16` and `r1 = c u + d u'` for `cd = e % 16`.
The entries are checked by the kernel in Mu4/Bridge/RrefCheck1..4.lean; Mu4/Bridge/Rref.lean derives
`rref_cover` from them. Core Lean only.
-/

set_option autoImplicit false

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search

/-- `a u + b u'` for the pair code `ab` (`a = coordC ab 0`, `b = coordC ab 1`), as in `inSpan2`. -/
def lin2r (ab u u' : Nat) : Nat := smulC (coordC ab 0) u ^^^ smulC (coordC ab 1) u'

/-- The condition of `rrefPairs` on `(r0, r1)`. -/
def rrefCond (r0 r1 : Nat) : Bool :=
  match firstNZ r0 0 4, firstNZ r1 0 4 with
  | some p, some q => p < q && coordC r0 p == 1 && coordC r1 q == 1 && coordC r0 q == 0
  | _, _ => false

/-- The witness entry `e` of the pair `(u, u')` checks. -/
def rrefEntryOK (e u u' : Nat) : Bool :=
  if e / 65536 == 0 then e % 16 != 0 && lin2r (e % 16) u u' % 256 == 0
  else rrefCond (e / 65536) (e / 256 % 256) && lin2r (e / 16 % 16) u u' == e / 65536 &&
    lin2r (e % 16) u u' == e / 256 % 256

/-- All entries of a chunk (16 values `s .. s + 15` of `u`, all `u' < 256`) check. -/
def rrefChunkOK (tab s : Nat) : Bool :=
  (List.range 16).all fun i => (List.range 256).all fun u' =>
    rrefEntryOK ((tab >>> (24 * (256 * i + u'))) % 16777216) (s + i) u'

end Mu4.Bridge
