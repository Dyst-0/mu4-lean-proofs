import Mu4.N5.Lin5
import Mu4.Bridge.Coef

/-!
# mu_4(5): coefficients of the off blocks

As `Mu4/Bridge/Coef.lean`: `CaseWF5 d` collects the properties of a valid case used by the completeness proof
(from `wfCheck5`), and `rho_offSem5` extracts the coefficient of term `u` of block `i` by duality.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge


/-- The properties of a valid case used by the completeness proof. -/
structure CaseWF5 (d : CaseData) : Prop where
  shape : ∀ i < d.off.length, (blkOf d i).length = 1 ∨ (blkOf d i).length = 2
  rhoLen : d.rhoOff.length = d.off.length
  rhoShape : ∀ i < d.off.length, (d.rhoOff.getD i []).length = (blkOf d i).length
  dual : ∀ i < d.off.length, ∀ u < (blkOf d i).length, ∀ j < d.off.length,
    ∀ u' < (blkOf d j).length,
      formC5 (rhoOf d i u) (decode5 (gOf d j u')) = if i = j ∧ u = u' then 1 else 0
  bY3 : d.bY.length = 3
  bYker : ∀ y ∈ d.bY, dotC5 d.fa y = 0 ∧ dotC5 d.fb y = 0
  bYind : rankC5 d.bY = 3
  eaf : dotC5 d.fa d.ea = 1 ∧ dotC5 d.fb d.ea = 0
  ebf : dotC5 d.fa d.eb = 0 ∧ dotC5 d.fb d.eb = 1

/-- The coefficient of term `u` in `G Block y`. -/
def coefS5 (G : Nat) (ts : List Term) (y : GF5) (u : Nat) : F4 :=
  match ts with
  | [(_, f0), (_, f1)] =>
    if u = 0 then m00 G * formC5 f0 y + m01 G * formC5 f1 y
    else m10 G * formC5 f0 y + m11 G * formC5 f1 y
  | [(_, f0)] => coordC G 0 * formC5 f0 y
  | _ => 0

lemma blockSem_eq_sum5 (G : Nat) (ts : List Term) (hts : ts.length = 1 ∨ ts.length = 2) (y : GF5) :
    blockSem5 G ts y = ∑ u : Fin ts.length, coefS5 G ts y u • decode5 ((ts.getD u (0, 0)).1) := by
  match ts, hts with
  | [(g0, f0), (g1, f1)], _ => simp [blockSem5, coefS5, Fin.sum_univ_two]
  | [(g0, f0)], _ => simp [blockSem5, coefS5]

/-- Duality extracts the coefficient of term `u` of block `i` from the off sum. -/
lemma rho_offSem5 (d : CaseData) (hd : CaseWF5 d) (goff : List Nat) (hg : goff.length = d.off.length)
    (y : GF5) {i u : Nat} (hi : i < d.off.length) (hu : u < (blkOf d i).length) :
    formC5 (rhoOf d i u) (offSem5 d.off goff y) = coefS5 (goff.getD i 0) (blkOf d i) y u := by
  rw [offSem5, sum_zip_map d.off goff hg (fun b G => blockSem5 G b.2 y) (0, []) 0, map_sum]
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · show formC5 (rhoOf d i u) (blockSem5 (goff.getD i 0) (blkOf d i) y) = _
    rw [blockSem_eq_sum5 _ _ (hd.shape i hi) y, map_sum]
    rw [Finset.sum_eq_single ⟨u, hu⟩]
    · rw [map_smul, smul_eq_mul]
      have := hd.dual i hi u hu i hi u hu
      simp only [and_self, if_true] at this
      rw [show (decode5 ((blkOf d i).getD u (0, 0)).1) = decode5 (gOf d i u) from rfl, this, mul_one]
    · intro v _ hv
      rw [map_smul, smul_eq_mul]
      have := hd.dual i hi u hu i hi v v.isLt
      rw [show (decode5 ((blkOf d i).getD v (0, 0)).1) = decode5 (gOf d i v) from rfl, this]
      rw [if_neg (by intro h; exact hv (Fin.ext h.2.symm))]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j _ hj
    show formC5 (rhoOf d i u) (blockSem5 (goff.getD j 0) (blkOf d j) y) = 0
    rw [blockSem_eq_sum5 _ _ (hd.shape j j.isLt) y, map_sum]
    apply Finset.sum_eq_zero
    intro v _
    rw [map_smul, smul_eq_mul]
    have := hd.dual i hi u hu j j.isLt v v.isLt
    rw [show (decode5 ((blkOf d j).getD v (0, 0)).1) = decode5 (gOf d j v) from rfl,
      this, if_neg (by intro h; exact hj (Fin.ext h.1.symm))]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The runtime certificate gives the invariants. -/
theorem caseWF_of_check5 (d : CaseData) (h : wfCheck5 d = true) : CaseWF5 d := by
  simp only [wfCheck5, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hlen, hshape, hdual, hb4, hbk, hbr, hea1, hea2, heb1, heb2, -⟩ := h
  refine ⟨fun i hi => (hshape i hi).1, hlen, fun i hi => (hshape i hi).2, ?_, hb4,
    fun y hy => hbk y hy, hbr, ⟨hea1, hea2⟩, ⟨heb1, heb2⟩⟩
  intro i hi u hu j hj u' hu'
  have := hdual i hi u hu j hj u' hu'
  rw [← dotC_eq5]
  by_cases h1 : i = j ∧ u = u'
  · obtain ⟨e1, e2⟩ := h1
    subst e1; subst e2
    simpa using this
  · rw [if_neg h1]
    simp only [beq_iff_eq, Bool.and_eq_true] at this
    rw [if_neg h1] at this
    exact this

end Mu4.N5
