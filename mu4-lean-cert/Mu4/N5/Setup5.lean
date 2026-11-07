import Mu4.N5.Keys5
import Mu4.Bridge.Setup

/-!
# mu_4(5): what `setupCase5` guarantees

As `Mu4/Bridge/Setup.lean`: a `valid` result comes with the block split, the verified dual basis, the forms, the
residual coefficients at `m0` and the verified kernel data.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge


theorem setupFrom_valid5 {X : PCtx5} {offB : List (Nat × List Nat)} {m0 : Nat} {gs0 : List Nat}
    {rho : List Nat} {d : CaseData} (h : setupFrom5 X offB m0 gs0 rho = .valid d) :
    d.off = mkOff5 X offB m0 rho ∧ d.m0 = m0 ∧ d.ga = gs0.getD 0 0 ∧ d.gb = gs0.getD 1 0 ∧
      d.rhoOff = chunks (offB.map (·.2.length)) rho ∧
      (∀ t < 5, (residualAt5 X d.off d.ga d.gb d.m0 t).isSome) ∧
      d.fa = formAB5 ((List.range 5).map (residualAt5 X d.off d.ga d.gb d.m0)) d.m0 0 ∧
      d.fb = formAB5 ((List.range 5).map (residualAt5 X d.off d.ga d.gb d.m0)) d.m0 1 ∧
      dependent2 d.fa d.fb = false ∧ kernelData5 d.fa d.fb = some (d.bY, d.ea, d.eb) := by
  unfold setupFrom5 at h
  simp only at h
  split_ifs at h with hres hdep
  split at h
  · simp at h
  · rename_i bY ea eb hker
    simp only [CaseResult.valid.injEq] at h
    subst h
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, by simpa using hdep, hker⟩
    intro t ht
    have := hres
    rw [Bool.not_eq_true, List.any_eq_false] at this
    have h2 := this _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
    simp only [Option.isNone_iff_eq_none, decide_eq_false_iff_not] at h2
    exact Option.isSome_iff_ne_none.mpr (by simpa using h2)

theorem setupCase_valid5 {X : PCtx5} {s0 s1 : Nat} {mult ws : List Nat} {d : CaseData}
    (h : setupCase5 X s0 s1 mult ws = .valid d) :
    ∃ pre gs0 post rho,
      splitFirstPair (blockList5 X s0 s1 mult ws) = some (pre, (d.m0, gs0), post) ∧
      dualBasis5 ((pre ++ post).flatMap (·.2)) = some rho ∧
      setupFrom5 X (pre ++ post) d.m0 gs0 rho = .valid d := by
  unfold setupCase5 at h
  split at h
  · simp at h
  · rename_i pre m0 gs0 post hsplit
    split at h
    · split at h <;> simp at h
    · rename_i rho hrho
      have hm0 := (setupFrom_valid5 h).2.1
      subst hm0
      exact ⟨pre, gs0, post, rho, hsplit, hrho, h⟩

end Mu4.N5
