import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice

/-!
# Bilinear rank

For a field `K` and a `K`-bilinear map `f : U → V → W`, a decomposition of length `r` is a
family of linear forms `a i` on `U`, `b i` on `V` and vectors `c i` of `W` with
`f u v = ∑ i, (a i u * b i v) • c i`. The bilinear rank (bilinear complexity, tensor rank)
`bilinRank K f` is the least such `r`. These are the standard notions; nothing else is assumed.
-/

namespace Mu4

variable (K : Type*) [Field K] {U V W : Type*} [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- `f` is a sum of `r` products of linear forms. -/
def HasDecomp (f : U →ₗ[K] V →ₗ[K] W) (r : ℕ) : Prop :=
  ∃ (a : Fin r → U →ₗ[K] K) (b : Fin r → V →ₗ[K] K) (c : Fin r → W),
    ∀ u v, f u v = ∑ i, (a i u * b i v) • c i

/-- The bilinear rank of `f`: the least length of a decomposition. -/
noncomputable def bilinRank (f : U →ₗ[K] V →ₗ[K] W) : ℕ := sInf {r | HasDecomp K f r}

variable {K}

/-- Padding with zero terms. -/
lemma HasDecomp.mono {f : U →ₗ[K] V →ₗ[K] W} {r s : ℕ} (h : HasDecomp K f r) (hrs : r ≤ s) :
    HasDecomp K f s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrs
  obtain ⟨a, b, c, hf⟩ := h
  refine ⟨Fin.append a (fun _ => 0), Fin.append b (fun _ => 0), Fin.append c (fun _ => 0),
    fun u v => ?_⟩
  rw [Fin.sum_univ_add, hf u v]
  simp

/-- `bilinRank K f = n` from a decomposition of length `n` and none of length `n - 1`. -/
lemma bilinRank_eq {f : U →ₗ[K] V →ₗ[K] W} {n : ℕ} (hn : 0 < n) (h : HasDecomp K f n)
    (h' : ¬ HasDecomp K f (n - 1)) : bilinRank K f = n := by
  apply le_antisymm
  · exact Nat.sInf_le h
  · refine le_csInf ⟨n, h⟩ fun r hr => ?_
    by_contra hlt
    exact h' (hr.mono (by omega))

end Mu4
