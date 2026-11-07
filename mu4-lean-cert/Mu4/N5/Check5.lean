import Mu4Comp5.Search
import Mu4Comp5.Data

/-! C3(5): the mu_4(5) search for all 3 × 17 pairs `(P_k, S_j)` and all 1,350 multiplicity and single-point
patterns (`checkAll5`). `native_decide` (new use, labelled; the kernel cannot do it: the same search runs about 2.5
minutes natively, the kernel is several thousand times slower): trusts the Lean compiler (`Lean.ofReduceBool`,
`Lean.trustCompiler`). The search code is in `Mu4Comp5/Search.lean` (precompiled); its meaning is proved in
`Mu4/N5/` (`sol_complete5`, `bridge5_holds`). -/

set_option autoImplicit false

namespace Mu4.N5

theorem searchCheck5 : (pList5.all fun p => sList5.all fun s => checkAll5 p.1 p.2 s.1 s.2) = true := by
  native_decide

end Mu4.N5
