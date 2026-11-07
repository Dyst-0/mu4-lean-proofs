import Mu4.Upper
import Mu4.Lower.Basic

/-!
# The main theorem, from the lower-bound statement `NoTwelve`

`NoTwelve`: no hyperplane `H` of GF(4^6) carries a 12-term decomposition, i.e. `R(T|_H) ≥ 13`
(`audit/PROOF.md`, L4-L10). With substitution (L0) and the 14-term scheme this gives
`bilinRank GF(4) (mul GF(4^6)) = 14`.
-/

namespace Mu4
open Mu4.Lower

/-- `R(T|_H) ≥ 13` for every hyperplane `H`. -/
def NoTwelve : Prop :=
  ∀ H : Submodule F4 GF, Module.finrank F4 H = 5 → ∀ D : Decomp 12, ¬ D.ValidOn H

theorem no13_of (h : NoTwelve) : ¬ HasDecomp F4 (LinearMap.mul F4 GF) 13 := by
  intro h13
  obtain ⟨H, hH, D, hD⟩ := substitution h13
  exact h H hH D hD

/-- The main theorem over the concrete fields, from `NoTwelve`. -/
theorem rank_GF_of (h : NoTwelve) : bilinRank F4 (LinearMap.mul F4 GF) = 14 :=
  bilinRank_eq (by norm_num) upper_bound (no13_of h)

end Mu4
