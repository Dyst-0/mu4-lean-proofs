import Mu4Comp.Search.Dir
import Mu4.F4

/-!
# Finite facts for the normal form (`audit/PROOF.md`, L6), checked by the kernel

* `mem_patterns`: every multiplicity pattern `(n_0, …, n_4)` with entries `≤ 2` and sum 8, with any choice of single
  points `w_m < 5` at the points with `n_m = 1` (and `w_m = 0` elsewhere), is one of the 255 patterns of the search;
* `pc_cover`: every vector `α e_0 + β e_1` of a 2-dim space is a multiple of one of its five standard points
  `pcA k • e_0 + pcB k • e_1`.
Both by `decide +kernel`. No `native_decide`.
-/

set_option autoImplicit false

namespace Mu4.Normal
open Mu4 Mu4.Search

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem mem_patterns : ∀ c0 c1 c2 c3 c4 : Fin 3, c0.val + c1.val + c2.val + c3.val + c4.val = 8 →
    ∀ v0 : Fin 5, (c0.val ≠ 1 → v0.val = 0) → ∀ v1 : Fin 5, (c1.val ≠ 1 → v1.val = 0) →
    ∀ v2 : Fin 5, (c2.val ≠ 1 → v2.val = 0) → ∀ v3 : Fin 5, (c3.val ≠ 1 → v3.val = 0) →
    ∀ v4 : Fin 5, (c4.val ≠ 1 → v4.val = 0) →
    ([c0.val, c1.val, c2.val, c3.val, c4.val], [v0.val, v1.val, v2.val, v3.val, v4.val]) ∈ patterns := by
  decide +kernel

theorem pc_cover : ∀ α β : F4, ∃ k : Fin 5, ∃ c : F4, α = c * pcA k.val ∧ β = c * pcB k.val := by
  decide +kernel

end Mu4.Normal
