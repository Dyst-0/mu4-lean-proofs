import Mu4.Main
import Mu4.Transfer
import Mu4.Lower.Step1
import Mu4.Lower.Geometry
import Mu4.Bridge.Normal
import Mu4.Check.All
import Mu4.Check.Geom
import Mu4.Normal.Reduction
import Mu4.Bridge.Triangle

/-!
# Final assembly

The main theorem from:
* the search check C3 (`Mu4.Check.searchCheck`, `native_decide`);
* G1 (`geometry`): the search `Mu4.Check.geomCheck_ok` (`native_decide`) with its soundness
  proof `Mu4.Lower.geometry_of_check`;
* the two steps of `audit/PROOF.md` that were first stated as explicit propositions, now proved:
  * `NormalFormReduction` (L6 with C1, C2): a 12-term decomposition on a hyperplane can be
    moved to normal form for one of the 175,950 cases of the search
    (`Mu4.Normal.normalFormReduction_holds`, standard axioms only; C1, C2 by kernel `decide`);
  * `BridgeMath` (L7-L10): a decomposition in normal form makes that case's check fail
    (`Mu4.Bridge.bridgeMath_holds`; it includes `setupCase_ne_invalid`: no case of a decomposition in normal
    form is dismissed as invalid).

`mu4_6` is `bilinRank GF(4) (mul GF(4^6)) = 14`, and `mu4_6_general` the same for every field `K` with 4
elements and every extension `L` of `K` of degree 6, with no hypotheses. The conditional forms `mu4_6_of` and
`mu4_6_general_of` are kept. There is no `sorry`, and no axiom beyond Lean's own and the compiler trust of
`native_decide` (`Lean.ofReduceBool`, `Lean.trustCompiler`).
-/

namespace Mu4.Final
open Mu4 Mu4.Lower Mu4.Bridge Mu4.Search

/-- G1: among 12 vectors spanning GF(4)^5, some 4 with distinct indices are dependent. -/
theorem geometry : Geometry := geometry_of_check Mu4.Check.geomCheck_ok

/-- L6 with the coverage facts C1, C2: transport to normal form. -/
def NormalFormReduction : Prop :=
  ∀ H : Submodule F4 GF, Module.finrank F4 H = 5 → ∀ D : Decomp 12, D.ValidOn H →
    Nonempty (Step1Data D H) →
    ∃ P ∈ pList, ∃ S ∈ sList, ∃ mult ws, (mult, ws) ∈ patterns ∧
      ∃ H' : Submodule F4 GF, Module.finrank F4 H' = 5 ∧ ∃ D' : Decomp 12, D'.ValidOn H' ∧
        Nonempty (NF P.1 P.2 S.1 S.2 mult ws D' H')

/-- L7-L9 with L10: a decomposition in normal form makes the case check fail. -/
def BridgeMath : Prop :=
  ∀ P ∈ pList, ∀ S ∈ sList, ∀ mult ws : List Nat, (mkPCtx P.1 P.2).ok = true →
    ∀ H : Submodule F4 GF, Module.finrank F4 H = 5 → ∀ D : Decomp 12, D.ValidOn H →
      NF P.1 P.2 S.1 S.2 mult ws D H → caseOK (mkPCtx P.1 P.2) S.1 S.2 mult ws = false

/-- `R(T|_H) ≥ 13` for every hyperplane, from the two steps and the search checks. -/
theorem noTwelve_of (hNF : NormalFormReduction) (hB : BridgeMath) : NoTwelve := by
  intro H hH D hD
  obtain ⟨P, hP, S, hS, mult, ws, hpat, H', hH', D', hD', ⟨nf⟩⟩ :=
    hNF H hH D hD (step1 geometry hH hD)
  have hc := Mu4.Check.searchCheck
  rw [List.all_eq_true] at hc
  have h1 := hc P hP
  rw [List.all_eq_true] at h1
  have h2 := h1 S hS
  simp only [checkPS, Bool.and_eq_true, List.all_eq_true] at h2
  have hok := h2.2 (mult, ws) hpat
  rw [hB P hP S hS mult ws h2.1 H' hH' D' hD' nf] at hok
  exact absurd hok (by simp)

/-- The main theorem over the concrete fields `F4 = GF(4)` and `GF = GF(4^6)`. -/
theorem mu4_6_of (hNF : NormalFormReduction) (hB : BridgeMath) :
    bilinRank F4 (LinearMap.mul F4 GF) = 14 :=
  rank_GF_of (noTwelve_of hNF hB)

/-- The main theorem for every field `K` with 4 elements and every extension `L` of degree 6. -/
theorem mu4_6_general_of (hNF : NormalFormReduction) (hB : BridgeMath)
    (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    (hK : Fintype.card K = 4) (hL : Module.finrank K L = 6) :
    bilinRank K (LinearMap.mul K L) = 14 := by
  obtain ⟨e, e0, he⟩ := exists_equiv_GF K L hK hL
  rw [bilinRank_transfer e e0 he]
  exact mu4_6_of hNF hB

/-! ### The unconditional theorems -/

/-- L6 with C1, C2 (`audit/PROOF.md`), proved. -/
theorem normalFormReduction : NormalFormReduction := Mu4.Normal.normalFormReduction_holds

/-- L7-L10 (`audit/PROOF.md`), proved. -/
theorem bridgeMath : BridgeMath := Mu4.Bridge.bridgeMath_holds

/-- `R(T|_H) ≥ 13` for every hyperplane `H`. -/
theorem noTwelve : NoTwelve := noTwelve_of normalFormReduction bridgeMath

/-- **The main theorem** over the concrete fields: `mu_4(6) = 14`. -/
theorem mu4_6 : bilinRank F4 (LinearMap.mul F4 GF) = 14 :=
  mu4_6_of normalFormReduction bridgeMath

/-- **The main theorem**: for every field `K` with 4 elements and every extension `L` of `K` of degree 6, the bilinear
rank of the multiplication `L × L → L` over `K` is 14. -/
theorem mu4_6_general (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    (hK : Fintype.card K = 4) (hL : Module.finrank K L = 6) :
    bilinRank K (LinearMap.mul K L) = 14 :=
  mu4_6_general_of normalFormReduction bridgeMath K L hK hL

end Mu4.Final
