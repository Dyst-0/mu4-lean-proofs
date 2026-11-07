import Mu4.Bridge.Rref

/-!
# The lookup tables of the direction search

`tableOf` is built from all candidate operators (the 124 diagonalizable 2×2 matrices, or the 4
scalars); every candidate sits in the table under its own key. `mkTable` reads the global tables
`pairTables` / `singleTables`, which are `Array.ofFn` of `tableOf`.
-/

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower

/-- Codes below `2^n` are closed under `xor`. -/
lemma xor_lt {x y n : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n) : x ^^^ y < 2 ^ n :=
  Nat.xor_lt_two_pow hx hy

lemma unitC_lt (c : F4) (l : Nat) : unitC c l < 4 ^ (l + 1) := by
  have hc : c.code < 4 := by cases c <;> decide
  simp only [unitC, Nat.shiftLeft_eq]
  calc c.code * 2 ^ (2 * l) < 4 * 2 ^ (2 * l) := Nat.mul_lt_mul_of_pos_right hc (by positivity)
    _ = 4 ^ (l + 1) := by rw [pow_succ, pow_mul]; ring

lemma mat2_lt (a b c d : F4) : mat2 a b c d < 256 := by
  have h0 := unitC_lt a 0; have h1 := unitC_lt b 1; have h2 := unitC_lt c 2; have h3 := unitC_lt d 3
  have e : (256 : Nat) = 2 ^ 8 := by norm_num
  rw [e]
  simp only [mat2]
  refine xor_lt (xor_lt (xor_lt ?_ ?_) ?_) ?_ <;> omega

lemma keyGB_lt (two : Bool) (b00 b01 b10 b11 : F4) (G : Nat) : keyGB two b00 b01 b10 b11 G < 256 := by
  unfold keyGB
  split
  · exact mat2_lt _ _ _ _
  · have h0 := unitC_lt (coordC G 0 * b00) 0
    have h1 := unitC_lt (coordC G 0 * b01) 1
    have e : (256 : Nat) = 2 ^ 8 := by norm_num
    rw [e]; exact xor_lt (by omega) (by omega)

@[simp] lemma coordC_mat2_0 (a b c d : F4) : coordC (mat2 a b c d) 0 = a := m00_mat2 a b c d
@[simp] lemma coordC_mat2_1 (a b c d : F4) : coordC (mat2 a b c d) 1 = b := m01_mat2 a b c d
@[simp] lemma coordC_mat2_2 (a b c d : F4) : coordC (mat2 a b c d) 2 = c := m10_mat2 a b c d
@[simp] lemma coordC_mat2_3 (a b c d : F4) : coordC (mat2 a b c d) 3 = d := m11_mat2 a b c d

/-- Every candidate is in the table under its key. -/
lemma mem_tableOf (two : Bool) (b00 b01 b10 b11 : F4) {G : Nat}
    (hG : G ∈ (if two then diag2 else [0, 1, 2, 3])) :
    G ∈ (tableOf two b00 b01 b10 b11).getD (keyGB two b00 b01 b10 b11 G) [] := by
  unfold tableOf
  generalize (if two then diag2 else [0, 1, 2, 3]) = L at hG ⊢
  have hK : keyGB two b00 b01 b10 b11 G < 256 := keyGB_lt _ _ _ _ _ _
  have key : ∀ (L : List Nat) (arr : Array (List Nat)), arr.size = 256 →
      (G ∈ L ∨ G ∈ (arr[keyGB two b00 b01 b10 b11 G]?).getD []) →
      G ∈ ((L.foldl (fun arr H => arr.modify (keyGB two b00 b01 b10 b11 H) (H :: ·)) arr)[
        keyGB two b00 b01 b10 b11 G]?).getD [] := by
    intro L
    induction L with
    | nil => intro arr _ h; simpa using h
    | cons H L ih =>
      intro arr hsz h
      simp only [List.foldl_cons]
      apply ih _ (by simp [hsz])
      have hsome : arr[keyGB two b00 b01 b10 b11 G]? = some arr[keyGB two b00 b01 b10 b11 G] :=
        Array.getElem?_eq_getElem (by omega)
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · right; rw [Array.getElem?_modify, if_pos rfl, hsome]; simp
        · exact Or.inl h
      · right
        rw [Array.getElem?_modify]
        split_ifs
        · rw [hsome] at h ⊢; simp at h ⊢; exact Or.inr h
        · exact h
  have := key L (Array.replicate 256 []) (by simp) (Or.inl hG)
  rwa [Array.getD_eq_getD_getElem?]

lemma pairTables_getD (b00 b01 b10 b11 : F4) :
    pairTables.getD (mat2 b00 b01 b10 b11) (tableOf true b00 b01 b10 b11) =
      tableOf true b00 b01 b10 b11 := by
  have hlt := mat2_lt b00 b01 b10 b11
  simp [pairTables, Array.getD_eq_getD_getElem?, hlt]

lemma singleTables_getD (b00 b01 : F4) :
    singleTables.getD (mat2 b00 b01 0 0) (tableOf false b00 b01 0 0) = tableOf false b00 b01 0 0 := by
  by_cases hlt : mat2 b00 b01 0 0 < 16
  · simp [singleTables, Array.getD_eq_getD_getElem?, hlt]
  · simp [singleTables, Array.getD_eq_getD_getElem?, hlt]

/-- `mkTable` is `tableOf` of the block entries. -/
lemma mkTable_pair (g0 f0 g1 f1 y1 y2 : Nat) :
    mkTable [(g0, f0), (g1, f1)] y1 y2 =
      tableOf true (dotC f0 y1) (dotC f0 y2) (dotC f1 y1) (dotC f1 y2) :=
  (show mkTable [(g0, f0), (g1, f1)] y1 y2 =
      pairTables.getD (mat2 (dotC f0 y1) (dotC f0 y2) (dotC f1 y1) (dotC f1 y2))
        (tableOf true (dotC f0 y1) (dotC f0 y2) (dotC f1 y1) (dotC f1 y2)) from rfl).trans
    (pairTables_getD _ _ _ _)

lemma mkTable_single (g0 f0 y1 y2 : Nat) :
    mkTable [(g0, f0)] y1 y2 = tableOf false (dotC f0 y1) (dotC f0 y2) 0 0 :=
  (show mkTable [(g0, f0)] y1 y2 =
      singleTables.getD (mat2 (dotC f0 y1) (dotC f0 y2) 0 0)
        (tableOf false (dotC f0 y1) (dotC f0 y2) 0 0) from rfl).trans (singleTables_getD _ _)

end Mu4.Bridge
