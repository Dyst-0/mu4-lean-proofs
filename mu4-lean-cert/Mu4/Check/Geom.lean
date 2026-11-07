import Mu4Geom

/-! G1 as a search: no 7 points of PG(4,4) extend the basis `e_0, …, e_4` to 12 points with
every 4 independent. `native_decide`: trusts the Lean compiler (`Lean.ofReduceBool`,
`Lean.trustCompiler`). Soundness of the search: `Mu4/Lower/Geometry.lean`. -/

namespace Mu4.Check
open Mu4.Geom

theorem geomCheck_ok : geomCheck 7 = true := by native_decide

end Mu4.Check
