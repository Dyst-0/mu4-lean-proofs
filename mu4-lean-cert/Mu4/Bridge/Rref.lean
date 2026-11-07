import Mu4.Bridge.Sem
import Mu4.Bridge.RrefCheck1
import Mu4.Bridge.RrefCheck2
import Mu4.Bridge.RrefCheck3
import Mu4.Bridge.RrefCheck4

/-!
# GF(4)^4 as 8-bit codes, and the reduced echelon pairs

`vec4 c` is the vector of GF(4)^4 with code `c`. `rref_cover` says that for every independent pair of codes
`u, u'` some pair of `rrefPairs` lies in `span(u, u')`. Since 11-06 (second agent) it is proved from the
witness entries checked by the kernel in Mu4/Bridge/RrefCheck1..4.lean (`rref_cover_spec`); the first version
was a `native_decide` on the precompiled `Mu4.Search.rrefCoverOK`.
-/

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower

/-- The vector of GF(4)^4 with code `c`. -/
def vec4 (c : Nat) : Fin 4 → F4 := fun k => coordC c k.val

/-- The code of a vector of GF(4)^4. -/
def encode4 (v : Fin 4 → F4) : Nat := xorFin fun k : Fin 4 => (v k).code <<< (2 * k.val)

lemma coordC_xorFin {n : Nat} (f : Fin n → Nat) (l : Nat) :
    coordC (xorFin f) l = ∑ i : Fin n, coordC (f i) l := by
  have key : ∀ L : List Nat, coordC (L.foldr (· ^^^ ·) 0) l = (L.map fun x => coordC x l).sum := by
    intro L; induction L with
    | nil => simp
    | cons a L ih => simp [ih]
  rw [xorFin, key, List.map_ofFn, List.sum_ofFn]; rfl

lemma vec4_encode4 (v : Fin 4 → F4) : vec4 (encode4 v) = v := by
  funext k
  simp only [vec4, encode4, coordC_xorFin, coordC_shift]
  simp [Fin.val_inj]

lemma vec4_xor_smul (a b : F4) (x y : Nat) :
    vec4 (smulC a x ^^^ smulC b y) = a • vec4 x + b • vec4 y := by
  funext k
  simp [vec4, coordC_smulC _ _ _ (show k.val < 32 by omega)]

/-! ### The kernel-checked witnesses -/

/-- Membership in `rrefPairs` from its condition. -/
lemma mem_rrefPairs {r0 r1 : Nat} (h0 : r0 < 256) (h1 : r1 < 256) (h : rrefCond r0 r1 = true) :
    (r0, r1) ∈ rrefPairs := by
  simp only [rrefPairs, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  refine ⟨r0, h0, r1, h1, ?_⟩
  unfold rrefCond at h
  generalize firstNZ r0 0 4 = a at h ⊢
  generalize firstNZ r1 0 4 = b at h ⊢
  cases a <;> cases b <;> simp_all

/-- A checked witness entry of an independent pair names an echelon pair in its span. -/
lemma rref_entry_sound {e u u' : Nat} (he : e < 16777216) (hok : rrefEntryOK e u u' = true)
    (hi : indep4 u u' = true) :
    ∃ K ∈ rrefPairs, inSpan2 u u' K.1 = true ∧ inSpan2 u u' K.2 = true := by
  unfold rrefEntryOK at hok
  split at hok
  · exfalso
    rw [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hok
    obtain ⟨hab, h0⟩ := hok
    have h1 := List.all_eq_true.mp hi (e % 16) (List.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
    rcases h1 with h1 | h1
    · exact hab h1
    · exact h1 h0
  · rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    obtain ⟨⟨hc, h1⟩, h2⟩ := hok
    refine ⟨(e / 65536, e / 256 % 256), mem_rrefPairs (by omega) (Nat.mod_lt _ (by norm_num)) hc, ?_, ?_⟩
    · exact List.any_eq_true.mpr ⟨e / 16 % 16, List.mem_range.mpr (Nat.mod_lt _ (by norm_num)),
        beq_iff_eq.mpr h1⟩
    · exact List.any_eq_true.mpr ⟨e % 16, List.mem_range.mpr (Nat.mod_lt _ (by norm_num)), beq_iff_eq.mpr h2⟩

/-- The entry of `(u, u')` in a checked chunk. -/
lemma chunk_entry {tab s : Nat} (h : rrefChunkOK tab s = true) {u u' : Nat} (hs : s ≤ u) (hu : u < s + 16)
    (hu' : u' < 256) : rrefEntryOK ((tab >>> (24 * (256 * (u - s) + u'))) % 16777216) u u' = true := by
  unfold rrefChunkOK at h
  have h1 := List.all_eq_true.mp h (u - s) (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 u' (List.mem_range.mpr hu')
  rwa [Nat.add_sub_cancel' hs] at h2

/-- Every independent pair of 8-bit codes spans a pair of `rrefPairs` (from the 16 kernel-checked chunks). -/
theorem rref_cover_spec (u u' : Nat) (hu : u < 256) (hu' : u' < 256) (hi : indep4 u u' = true) :
    ∃ K ∈ rrefPairs, inSpan2 u u' K.1 = true ∧ inSpan2 u u' K.2 = true := by
  have key : ∀ {tab s : Nat}, rrefChunkOK tab s = true → s ≤ u → u < s + 16 →
      ∃ K ∈ rrefPairs, inSpan2 u u' K.1 = true ∧ inSpan2 u u' K.2 = true :=
    fun h hs hn => rref_entry_sound (Nat.mod_lt _ (by norm_num)) (chunk_entry h hs hn hu') hi
  obtain ⟨k, hk⟩ : ∃ k, k = u / 16 := ⟨_, rfl⟩
  have hk16 : k < 16 := by omega
  have hs : 16 * k ≤ u := by omega
  have hn : u < 16 * k + 16 := by omega
  interval_cases k
  · exact key rref_chunk_0 hs hn
  · exact key rref_chunk_1 hs hn
  · exact key rref_chunk_2 hs hn
  · exact key rref_chunk_3 hs hn
  · exact key rref_chunk_4 hs hn
  · exact key rref_chunk_5 hs hn
  · exact key rref_chunk_6 hs hn
  · exact key rref_chunk_7 hs hn
  · exact key rref_chunk_8 hs hn
  · exact key rref_chunk_9 hs hn
  · exact key rref_chunk_10 hs hn
  · exact key rref_chunk_11 hs hn
  · exact key rref_chunk_12 hs hn
  · exact key rref_chunk_13 hs hn
  · exact key rref_chunk_14 hs hn
  · exact key rref_chunk_15 hs hn

/-- Every independent pair of 8-bit codes spans a pair of `rrefPairs`: the statement of the former
`native_decide` check, now from the kernel checks (`rref_cover_spec`). -/
theorem rref_cover : rrefCoverOK = true := by
  unfold rrefCoverOK
  refine List.all_eq_true.mpr fun u hu => List.all_eq_true.mpr fun u' hu' => ?_
  rw [List.mem_range] at hu hu'
  show (!indep4 u u' || rrefPairs.any fun K => inSpan2 u u' K.1 && inSpan2 u u' K.2) = true
  cases hi : indep4 u u'
  · rfl
  · obtain ⟨K, hK, h1, h2⟩ := rref_cover_spec u u' hu hu' hi
    rw [Bool.not_true, Bool.false_or]
    exact List.any_eq_true.mpr ⟨K, hK, by rw [h1, h2]; rfl⟩

end Mu4.Bridge
