import Mu4Comp.Search.Dir
import Mu4Comp.Data

/-! C3 for the pencil representative `P_5 = span(1, 348)`: all 69 classes `Ŝ` and all 255
patterns pass the case check (no failed verification, no passing triangle). `native_decide`:
trusts the Lean compiler (`Lean.ofReduceBool`, `Lean.trustCompiler`). -/

namespace Mu4.Check
open Mu4.Search

theorem checkP5 : (sList.all fun s => checkPS 1 348 s.1 s.2) = true := by native_decide

end Mu4.Check
