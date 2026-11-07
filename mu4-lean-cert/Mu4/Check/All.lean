import Mu4.Check.P0
import Mu4.Check.P1
import Mu4.Check.P2
import Mu4.Check.P3
import Mu4.Check.P4
import Mu4.Check.P5
import Mu4.Check.P6
import Mu4.Check.P7
import Mu4.Check.P8
import Mu4.Check.P9

/-! C3: the search check over all 10 pencil representatives. -/

namespace Mu4.Check
open Mu4.Search

theorem searchCheck : (pList.all fun p => sList.all fun s => checkPS p.1 p.2 s.1 s.2) = true := by
  simp only [pList, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨checkP0, checkP1, checkP2, checkP3, checkP4, checkP5, checkP6, checkP7, checkP8, checkP9⟩

end Mu4.Check
