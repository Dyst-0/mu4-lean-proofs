import Mu4.N5.Sem5
import Mu4.N5.RrefCheck5
import Mu4.Bridge.Keys

/-!
# mu_4(5): GF(4)^3 codes, the reduced echelon pairs, the lookup tables and keys

`vec3 c` is the vector of GF(4)^3 with code `c`. `rref_cover3`: for every independent pair of 6-bit codes some pair of
`rrefPairs3` lies in their span (from the kernel check of `Mu4/N5/RrefCheck5.lean`). The tables of `Mu4.Search` are generic; `mkTable5` reads them with
the 5-coordinate forms. The keys `keyR5` are linear in the direction.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge

/-- The vector of GF(4)^3 with code `c`. -/
def vec3 (c : Nat) : Fin 3 → F4 := fun k => coordC c k.val

/-- The code of a vector of GF(4)^3. -/
def encode3 (v : Fin 3 → F4) : Nat := xorFin fun k : Fin 3 => (v k).code <<< (2 * k.val)

lemma vec3_encode3 (v : Fin 3 → F4) : vec3 (encode3 v) = v := by
  funext k
  simp only [vec3, encode3, coordC_xorFin, coordC_shift]
  simp [Fin.val_inj]

lemma vec3_xor_smul (a b : F4) (x y : Nat) :
    vec3 (smulC a x ^^^ smulC b y) = a • vec3 x + b • vec3 y := by
  funext k
  simp [vec3, coordC_smulC _ _ _ (show k.val < 32 by omega)]

lemma vec3_smulC (μ : F4) (x : Nat) : vec3 (smulC μ x) = μ • vec3 x := by
  funext k
  simp [vec3, coordC_smulC _ _ _ (show k.val < 32 by omega)]

/-- Every independent pair of codes spans an echelon pair of `rrefPairs3`. -/
theorem rref_cover3 (u u' : Nat) (hu : u < 64) (hu' : u' < 64) (h : indep3 u u' = true) :
    ∃ K ∈ rrefPairs3, (∃ ab < 16, lin2u ab u u' = K.1) ∧ (∃ cd < 16, lin2u cd u u' = K.2) := by
  have hall : ∀ u < 64, (List.range 64).all (rrefOK3 u) = true := by
    intro u hu
    have key : ∀ (s : Nat), (List.range' s 16).all (fun u => (List.range 64).all (rrefOK3 u)) = true →
        s ≤ u → u < s + 16 → (List.range 64).all (rrefOK3 u) = true := fun s h hs hn =>
      List.all_eq_true.mp h u (List.mem_range'_1.mpr ⟨hs, hn⟩)
    by_cases a : u < 16
    · exact key 0 rref_cover3_1 (by omega) (by omega)
    by_cases b : u < 32
    · exact key 16 rref_cover3_2 (by omega) (by omega)
    by_cases c : u < 48
    · exact key 32 rref_cover3_3 (by omega) (by omega)
    · exact key 48 rref_cover3_4 (by omega) (by omega)
  have hok := List.all_eq_true.mp (hall u hu) u' (List.mem_range.mpr hu')
  unfold rrefOK3 at hok
  rw [h] at hok
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  generalize (rrefTab3 >>> (16 * (64 * u + u'))) % 65536 = e at hok
  obtain ⟨⟨h21, h1⟩, h2⟩ := hok
  refine ⟨rref3lit.getD (e / 256) (0, 0), ?_, ⟨_, Nat.mod_lt _ (by norm_num), h1⟩, ⟨_, Nat.mod_lt _ (by norm_num), h2⟩⟩
  rw [rrefPairs3_eq, List.getD_eq_getElem _ _ (by simpa [rref3lit] using h21)]
  exact List.getElem_mem _

/-! ### Tables -/

/-- `mkTable5` is `tableOf` of the block entries. -/
lemma mkTable5_pair (g0 f0 g1 f1 y1 y2 : Nat) :
    mkTable5 [(g0, f0), (g1, f1)] y1 y2 =
      tableOf true (dotC5 f0 y1) (dotC5 f0 y2) (dotC5 f1 y1) (dotC5 f1 y2) :=
  (show mkTable5 [(g0, f0), (g1, f1)] y1 y2 =
      pairTables.getD (mat2 (dotC5 f0 y1) (dotC5 f0 y2) (dotC5 f1 y1) (dotC5 f1 y2))
        (tableOf true (dotC5 f0 y1) (dotC5 f0 y2) (dotC5 f1 y1) (dotC5 f1 y2)) from rfl).trans
    (pairTables_getD _ _ _ _)

lemma mkTable5_single (g0 f0 y1 y2 : Nat) :
    mkTable5 [(g0, f0)] y1 y2 = tableOf false (dotC5 f0 y1) (dotC5 f0 y2) 0 0 :=
  (show mkTable5 [(g0, f0)] y1 y2 =
      singleTables.getD (mat2 (dotC5 f0 y1) (dotC5 f0 y2) 0 0)
        (tableOf false (dotC5 f0 y1) (dotC5 f0 y2) 0 0) from rfl).trans (singleTables_getD _ _)

/-! ### Bounds and keys -/

lemma combo3_lt (c : Nat) (ks : List Nat) {n : Nat} (hks : ∀ k ∈ ks, k < 2 ^ (2 * n)) :
    combo3 c ks < 2 ^ (2 * n) := by
  match ks with
  | [k0, k1, k2] =>
    simp only [combo3]
    refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_ <;>
      exact smulC_lt _ (hks _ (by simp))
  | [] => exact xorFin_lt _ fun i => absurd i.isLt (by simp)
  | [_] => exact xorFin_lt _ fun i => smulC_lt _ (hks _ (List.get_mem _ _))
  | [_, _] => exact xorFin_lt _ fun i => smulC_lt _ (hks _ (List.get_mem _ _))
  | _ :: _ :: _ :: _ :: _ => exact xorFin_lt _ fun i => smulC_lt _ (hks _ (List.get_mem _ _))

lemma keyR5_lt (rhos : List Nat) (a b : Nat) : keyR5 rhos a b < 2 ^ (2 * 4) := by
  match rhos with
  | [r0, r1] => simp only [keyR5]; exact mat2_lt _ _ _ _
  | [r0] =>
    simp only [keyR5]
    have h0 := unitC_lt (dotC5 r0 a) 0
    have h1 := unitC_lt (dotC5 r0 b) 1
    exact Nat.xor_lt_two_pow (by omega) (by omega)
  | [] => simp [keyR5]
  | _ :: _ :: _ :: _ => simp [keyR5]

lemma coordC_keyR5_pair (r0 r1 a b : Nat) :
    coordC (keyR5 [r0, r1] a b) 0 = dotC5 r0 a ∧ coordC (keyR5 [r0, r1] a b) 1 = dotC5 r0 b ∧
    coordC (keyR5 [r0, r1] a b) 2 = dotC5 r1 a ∧ coordC (keyR5 [r0, r1] a b) 3 = dotC5 r1 b := by
  simp [keyR5]

lemma coordC_keyR5_single (r0 a b : Nat) (l : Nat) :
    coordC (keyR5 [r0] a b) l = (if l = 0 then dotC5 r0 a else 0) + (if l = 1 then dotC5 r0 b else 0) := by
  simp only [keyR5, coordC_xor, coordC_unitC]
  by_cases h0 : l = 0 <;> by_cases h1 : l = 1 <;> simp [h0, h1, eq_comm] <;> omega

end Mu4.N5
