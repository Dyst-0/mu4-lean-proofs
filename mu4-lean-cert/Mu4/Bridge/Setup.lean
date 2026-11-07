import Mu4.Bridge.Keys

/-!
# What `setupCase` guarantees

`setupCase_valid` unfolds `setupCase`: a `valid` result comes with the block split, the verified
dual basis, the forms, the residual coefficients at `m0` and the verified kernel data.
-/

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower

lemma splitFirstPair_spec {bs pre post : List (Nat × List Nat)} {b : Nat × List Nat}
    (h : splitFirstPair bs = some (pre, b, post)) :
    bs = pre ++ b :: post ∧ b.2.length = 2 ∧ ∀ x ∈ pre, x.2.length ≠ 2 := by
  induction bs generalizing pre with
  | nil => simp [splitFirstPair] at h
  | cons x bs ih =>
    unfold splitFirstPair at h
    split_ifs at h with hx
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hx, by simp⟩
    · split at h
      · rename_i pre' p' post' h'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3⟩ := ih h'
        refine ⟨by simp [h1], h2, ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact h3 z hz
      · simp at h

theorem setupFrom_valid {X : PCtx} {offB : List (Nat × List Nat)} {m0 : Nat} {gs0 : List Nat}
    {rho : List Nat} {d : CaseData} (h : setupFrom X offB m0 gs0 rho = .valid d) :
    d.off = mkOff X offB m0 rho ∧ d.m0 = m0 ∧ d.ga = gs0.getD 0 0 ∧ d.gb = gs0.getD 1 0 ∧
      d.rhoOff = chunks (offB.map (·.2.length)) rho ∧
      (∀ t < 6, (residualAt X d.off d.ga d.gb d.m0 t).isSome) ∧
      d.fa = formAB ((List.range 6).map (residualAt X d.off d.ga d.gb d.m0)) d.m0 0 ∧
      d.fb = formAB ((List.range 6).map (residualAt X d.off d.ga d.gb d.m0)) d.m0 1 ∧
      dependent2 d.fa d.fb = false ∧ kernelData d.fa d.fb = some (d.bY, d.ea, d.eb) := by
  unfold setupFrom at h
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

theorem setupCase_valid {X : PCtx} {s0 s1 : Nat} {mult ws : List Nat} {d : CaseData}
    (h : setupCase X s0 s1 mult ws = .valid d) :
    ∃ pre gs0 post rho,
      splitFirstPair (blockList X s0 s1 mult ws) = some (pre, (d.m0, gs0), post) ∧
      dualBasis ((pre ++ post).flatMap (·.2)) = some rho ∧
      setupFrom X (pre ++ post) d.m0 gs0 rho = .valid d := by
  unfold setupCase at h
  split at h
  · simp at h
  · rename_i pre m0 gs0 post hsplit
    split at h
    · split at h <;> simp at h
    · rename_i rho hrho
      have hm0 := (setupFrom_valid h).2.1
      subst hm0
      exact ⟨pre, gs0, post, rho, hsplit, hrho, h⟩

end Mu4.Bridge
