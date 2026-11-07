/-
  The trust base of the two main results, in one command (from this directory, after `lake build`):
      lake env lean Axioms.lean
  Expected for all four: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound].
  Lean.ofReduceBool and Lean.trustCompiler come only from `native_decide` in the three finite searches
  (Mu4/Check/P0..P9 and Mu4/Check/Geom.lean for mu_4(6); Mu4/N5/Check5.lean for mu_4(5)). See README.md, "Trust base".
-/
import Mu4

#print axioms Mu4.Final.mu4_6
#print axioms Mu4.Final.mu4_6_general
#print axioms Mu4.N5.mu4_5
#print axioms Mu4.N5.mu4_5_general
