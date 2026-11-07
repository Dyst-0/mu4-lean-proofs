import Mu4Comp.Search.Case
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/-!
# List facts for the blocks of a case

The search splits the dual rows `rho` of the off-`m0` vectors `Gam = flatten vss` into chunks of the block lengths
(`chunks`). Entry `u` of chunk `b` and entry `u` of block `b` sit at the same flat position `offs ns b + u`, and
these positions are distinct for distinct `(b, u)`. Pure list facts, no field.
-/

set_option autoImplicit false

namespace Mu4.Bridge
open Mu4.Search

/-- The flat position of block `b`. -/
def offs (ns : List Nat) (b : Nat) : Nat := (ns.take b).sum

lemma offs_zero (ns : List Nat) : offs ns 0 = 0 := by simp [offs]

lemma offs_cons_succ (n : Nat) (ns : List Nat) (b : Nat) : offs (n :: ns) (b + 1) = n + offs ns b := by
  simp [offs]

lemma offs_succ (ns : List Nat) (b : Nat) (hb : b < ns.length) :
    offs ns (b + 1) = offs ns b + ns.getD b 0 := by
  induction ns generalizing b with
  | nil => simp at hb
  | cons n ns ih =>
    cases b with
    | zero => simp [offs]
    | succ b =>
      rw [offs_cons_succ, offs_cons_succ, ih b (by simpa using hb)]
      simp; ring

lemma offs_mono (ns : List Nat) {b b' : Nat} (h : b ≤ b') : offs ns b ≤ offs ns b' := by
  induction ns generalizing b b' with
  | nil => simp [offs]
  | cons n ns ih =>
    cases b with
    | zero => simp [offs_zero]
    | succ b =>
      cases b' with
      | zero => omega
      | succ b' => rw [offs_cons_succ, offs_cons_succ]; have := ih (b := b) (b' := b') (by omega); omega

lemma offs_add_lt_sum (ns : List Nat) {b u : Nat} (hb : b < ns.length) (hu : u < ns.getD b 0) :
    offs ns b + u < ns.sum := by
  have h1 : offs ns (b + 1) ≤ offs ns ns.length := offs_mono ns (by omega)
  have h2 : offs ns ns.length = ns.sum := by simp [offs]
  rw [offs_succ ns b hb] at h1
  omega

/-- Distinct `(b, u)` have distinct flat positions. -/
lemma offs_inj (ns : List Nat) {b b' u u' : Nat} (hb : b < ns.length) (hb' : b' < ns.length)
    (hu : u < ns.getD b 0) (hu' : u' < ns.getD b' 0) (h : offs ns b + u = offs ns b' + u') :
    b = b' ∧ u = u' := by
  rcases Nat.lt_trichotomy b b' with hlt | heq | hgt
  · exfalso
    have h1 := offs_succ ns b hb
    have h2 := offs_mono ns (show b + 1 ≤ b' by omega)
    omega
  · subst heq; exact ⟨rfl, by omega⟩
  · exfalso
    have h1 := offs_succ ns b' hb'
    have h2 := offs_mono ns (show b' + 1 ≤ b by omega)
    omega

lemma chunks_length (ns xs : List Nat) : (chunks ns xs).length = ns.length := by
  induction ns generalizing xs with
  | nil => rfl
  | cons n ns ih => simp [chunks, ih]

/-- Entry `u` of chunk `b` is the entry at the flat position. -/
lemma chunks_getD (ns xs : List Nat) (b : Nat) (hb : b < ns.length) (u : Nat) (hu : u < ns.getD b 0) :
    ((chunks ns xs).getD b []).getD u 0 = xs.getD (offs ns b + u) 0 := by
  induction ns generalizing xs b with
  | nil => simp at hb
  | cons n ns ih =>
    cases b with
    | zero =>
      simp only [chunks, List.getD_cons_zero, offs_zero, zero_add] at hu ⊢
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
      simp [hu]
    | succ b =>
      simp only [chunks, List.getD_cons_succ] at hu ⊢
      rw [ih (xs.drop n) b (by simpa using hb) hu, offs_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      congr 2; ring

lemma chunks_getD_length (ns xs : List Nat) (hxs : ns.sum ≤ xs.length) (b : Nat) (hb : b < ns.length) :
    ((chunks ns xs).getD b []).length = ns.getD b 0 := by
  induction ns generalizing xs b with
  | nil => simp at hb
  | cons n ns ih =>
    simp only [List.sum_cons] at hxs
    cases b with
    | zero => simp [chunks]; omega
    | succ b =>
      simp only [chunks, List.getD_cons_succ]
      exact ih (xs.drop n) (by simp; omega) b (by simpa using hb)

/-- Entry `u` of block `b` is the entry of the flattening at the flat position. -/
lemma flatten_getD (L : List (List Nat)) (b : Nat) (hb : b < L.length) (u : Nat)
    (hu : u < (L.getD b []).length) :
    L.flatten.getD (offs (L.map List.length) b + u) 0 = (L.getD b []).getD u 0 := by
  induction L generalizing b with
  | nil => simp at hb
  | cons l L ih =>
    cases b with
    | zero =>
      simp only [List.getD_cons_zero, List.map_cons, offs_zero, zero_add] at hu ⊢
      rw [List.flatten_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hu]
    | succ b =>
      simp only [List.getD_cons_succ, List.map_cons] at hu ⊢
      rw [offs_cons_succ, List.flatten_cons, List.getD_eq_getElem?_getD, add_assoc,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        ← List.getD_eq_getElem?_getD]
      exact ih b (by simpa using hb) hu

lemma sum_map_length_flatten (L : List (List Nat)) : (L.map List.length).sum = L.flatten.length := by
  simp [List.length_flatten]

/-- Sum over a `filterMap`, as a sum over the list. -/
lemma sum_map_filterMap {α β : Type*} (l : List α) (f : α → Option β) (g : β → Nat) :
    ((l.filterMap f).map g).sum = (l.map fun a => ((f a).map g).getD 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← ih]
    cases h : f a with
    | none => simp
    | some b => simp

end Mu4.Bridge
