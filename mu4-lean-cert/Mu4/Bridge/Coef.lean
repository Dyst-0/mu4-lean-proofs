import Mu4.Bridge.Lin

/-!
# Coefficients of the off blocks

`CaseWF d` collects the properties of a valid case used by the completeness proof (they follow
from `setupCase`'s verifications). `rho_offSem` extracts the coefficient of term `u` of block `i`
from the sum over the off blocks, by duality.
-/

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower

/-- The form of term `u` of off block `i`. -/
def fOf (d : CaseData) (i u : Nat) : Nat := ((blkOf d i).getD u (0, 0)).2

/-- The properties of a valid case used by the completeness proof. -/
structure CaseWF (d : CaseData) : Prop where
  shape : ∀ i < d.off.length, (blkOf d i).length = 1 ∨ (blkOf d i).length = 2
  rhoLen : d.rhoOff.length = d.off.length
  rhoShape : ∀ i < d.off.length, (d.rhoOff.getD i []).length = (blkOf d i).length
  dual : ∀ i < d.off.length, ∀ u < (blkOf d i).length, ∀ j < d.off.length,
    ∀ u' < (blkOf d j).length,
      formC (rhoOf d i u) (decode (gOf d j u')) = if i = j ∧ u = u' then 1 else 0
  bY4 : d.bY.length = 4
  bYker : ∀ y ∈ d.bY, dotC d.fa y = 0 ∧ dotC d.fb y = 0
  bYind : rankC d.bY = 4
  eaf : dotC d.fa d.ea = 1 ∧ dotC d.fb d.ea = 0
  ebf : dotC d.fa d.eb = 0 ∧ dotC d.fb d.eb = 1

/-- The coefficient of term `u` in `G Block y`. -/
def coefS (G : Nat) (ts : List Term) (y : GF) (u : Nat) : F4 :=
  match ts with
  | [(_, f0), (_, f1)] =>
    if u = 0 then m00 G * formC f0 y + m01 G * formC f1 y
    else m10 G * formC f0 y + m11 G * formC f1 y
  | [(_, f0)] => coordC G 0 * formC f0 y
  | _ => 0

lemma blockSem_eq_sum (G : Nat) (ts : List Term) (hts : ts.length = 1 ∨ ts.length = 2) (y : GF) :
    blockSem G ts y = ∑ u : Fin ts.length, coefS G ts y u • decode ((ts.getD u (0, 0)).1) := by
  match ts, hts with
  | [(g0, f0), (g1, f1)], _ => simp [blockSem, coefS, Fin.sum_univ_two]
  | [(g0, f0)], _ => simp [blockSem, coefS]

/-- `List.sum` over a zip as a sum over indices. -/
lemma sum_zip_map {α β M : Type*} [AddCommMonoid M] (L : List α) (K : List β)
    (h : K.length = L.length) (f : α → β → M) (a0 : α) (b0 : β) :
    ((L.zip K).map fun x => f x.1 x.2).sum = ∑ j : Fin L.length, f (L.getD j a0) (K.getD j b0) := by
  induction L generalizing K with
  | nil => simp
  | cons a L ih =>
    match K, h with
    | b :: K, h =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons,
        Fin.sum_univ_succ, List.getD_cons_zero, Fin.val_zero, Fin.val_succ, List.getD_cons_succ]
      rw [ih K h]

/-- Duality extracts the coefficient of term `u` of block `i` from the off sum. -/
lemma rho_offSem (d : CaseData) (hd : CaseWF d) (goff : List Nat) (hg : goff.length = d.off.length)
    (y : GF) {i u : Nat} (hi : i < d.off.length) (hu : u < (blkOf d i).length) :
    formC (rhoOf d i u) (offSem d.off goff y) = coefS (goff.getD i 0) (blkOf d i) y u := by
  rw [offSem, sum_zip_map d.off goff hg (fun b G => blockSem G b.2 y) (0, []) 0, map_sum]
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · show formC (rhoOf d i u) (blockSem (goff.getD i 0) (blkOf d i) y) = _
    rw [blockSem_eq_sum _ _ (hd.shape i hi) y, map_sum]
    rw [Finset.sum_eq_single ⟨u, hu⟩]
    · rw [map_smul, smul_eq_mul]
      have := hd.dual i hi u hu i hi u hu
      simp only [and_self, if_true] at this
      rw [show (decode ((blkOf d i).getD u (0, 0)).1) = decode (gOf d i u) from rfl, this, mul_one]
    · intro v _ hv
      rw [map_smul, smul_eq_mul]
      have := hd.dual i hi u hu i hi v v.isLt
      rw [show (decode ((blkOf d i).getD v (0, 0)).1) = decode (gOf d i v) from rfl, this]
      rw [if_neg (by intro h; exact hv (Fin.ext h.2.symm))]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j _ hj
    show formC (rhoOf d i u) (blockSem (goff.getD j 0) (blkOf d j) y) = 0
    rw [blockSem_eq_sum _ _ (hd.shape j j.isLt) y, map_sum]
    apply Finset.sum_eq_zero
    intro v _
    rw [map_smul, smul_eq_mul]
    have := hd.dual i hi u hu j j.isLt v v.isLt
    rw [show (decode ((blkOf d j).getD v (0, 0)).1) = decode (gOf d j v) from rfl,
      this, if_neg (by intro h; exact hj (Fin.ext h.1.symm))]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The runtime certificate gives the invariants. -/
theorem caseWF_of_check (d : CaseData) (h : wfCheck d = true) : CaseWF d := by
  simp only [wfCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hlen, hshape, hdual, hb4, hbk, hbr, hea1, hea2, heb1, heb2, -⟩ := h
  refine ⟨fun i hi => (hshape i hi).1, hlen, fun i hi => (hshape i hi).2, ?_, hb4,
    fun y hy => hbk y hy, hbr, ⟨hea1, hea2⟩, ⟨heb1, heb2⟩⟩
  intro i hi u hu j hj u' hu'
  have := hdual i hi u hu j hj u' hu'
  rw [← dotC_eq]
  by_cases h1 : i = j ∧ u = u'
  · obtain ⟨e1, e2⟩ := h1
    subst e1; subst e2
    simpa using this
  · rw [if_neg h1]
    simp only [beq_iff_eq, Bool.and_eq_true] at this
    rw [if_neg h1] at this
    exact this

end Mu4.Bridge
