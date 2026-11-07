import Mu4.Bridge.Setup

/-!
# Linearity of the solution operator, and reduction modulo `W_{m0}`
-/

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower

/-! ### Linearity -/

lemma blockSem_add (G : Nat) (ts : List Term) (y y' : GF) :
    blockSem G ts (y + y') = blockSem G ts y + blockSem G ts y' := by
  match ts with
  | [(g0, f0), (g1, f1)] => simp only [blockSem, map_add]; module
  | [(g0, f0)] => simp only [blockSem, map_add]; module
  | [] => simp [blockSem]
  | _ :: _ :: _ :: _ => simp [blockSem]

lemma blockSem_smul (G : Nat) (ts : List Term) (c : F4) (y : GF) :
    blockSem G ts (c • y) = c • blockSem G ts y := by
  match ts with
  | [(g0, f0), (g1, f1)] => simp only [blockSem, map_smul, smul_eq_mul]; module
  | [(g0, f0)] => simp only [blockSem, map_smul, smul_eq_mul]; module
  | [] => simp [blockSem]
  | _ :: _ :: _ :: _ => simp [blockSem]

lemma offSem_add (off : List (Nat × List Term)) (goff : List Nat) (y y' : GF) :
    offSem off goff (y + y') = offSem off goff y + offSem off goff y' := by
  simp only [offSem, blockSem_add]
  induction (off.zip goff) with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; abel

lemma offSem_smul (off : List (Nat × List Term)) (goff : List Nat) (c : F4) (y : GF) :
    offSem off goff (c • y) = c • offSem off goff y := by
  simp only [offSem, blockSem_smul]
  induction (off.zip goff) with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih, smul_add]

/-- The operator `E` of a solution, as a linear map. -/
def Elin (X : PCtx) (d : CaseData) (s : Sol) : GF →ₗ[F4] GF where
  toFun := Esem X d s
  map_add' y y' := by
    simp only [Esem, mul_add, offSem_add, blockSem_add]; abel
  map_smul' c y := by
    simp only [Esem, RingHom.id_apply, mul_smul_comm, offSem_smul, blockSem_smul, smul_add]

/-! ### Reduction modulo a pivot list -/

/-- One reduction step `x ↦ x + x_p • w`, as a linear map. -/
def stepLin (p : Fin 6) (u : GF) : GF →ₗ[F4] GF where
  toFun x := x + x.v p • u
  map_add' x y := by simp only [GF.add_v, Pi.add_apply, add_smul]; abel
  map_smul' c x := by
    simp only [GF.smul_v, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, smul_add]

/-- The reduction by a pivot list, as a linear map (positions `≥ 6` are skipped; echelon lists
have none). -/
def redLin : List (Nat × Nat) → (GF →ₗ[F4] GF)
  | [] => LinearMap.id
  | (p, vv) :: rest => if h : p < 6 then redLin rest ∘ₗ stepLin ⟨p, h⟩ (decode vv) else redLin rest

lemma decode_reduceBy (piv : List (Nat × Nat)) (h : ∀ q ∈ piv, q.1 < 6) (v : Nat) :
    decode (reduceBy piv v) = redLin piv (decode v) := by
  induction piv generalizing v with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨p, vv⟩ := x
    have hp : p < 6 := h (p, vv) List.mem_cons_self
    have hrest : ∀ q ∈ rest, q.1 < 6 := fun q hq => h q (List.mem_cons_of_mem _ hq)
    show decode (reduceBy rest (v ^^^ smulC (coordC v p) vv)) = _
    rw [ih hrest, redLin, dif_pos hp, LinearMap.comp_apply]
    congr 1
    simp [stepLin, decode_v]

lemma reduceBy_append (piv piv' : List (Nat × Nat)) (v : Nat) :
    reduceBy (piv ++ piv') v = reduceBy piv' (reduceBy piv v) := by
  simp [reduceBy, List.foldl_append]

/-- Inserting `v` makes the reduction kill `v`. -/
lemma reduceBy_insertPivot_self (piv : List (Nat × Nat)) (v : Nat) :
    decode (reduceBy (insertPivot 6 piv v) v) = 0 := by
  cases hf : firstNZ (reduceBy piv v) 0 6 with
  | none =>
    simp only [insertPivot, hf]
    ext l
    have := firstNZ_none hf l.val (by omega) (by omega)
    simp [this]
  | some p =>
    simp only [insertPivot, hf]
    obtain ⟨-, hp6, hcp⟩ := firstNZ_some hf
    rw [reduceBy_append]
    show decode (reduceBy piv v ^^^ smulC (coordC (reduceBy piv v) p)
      (smulC (coordC (reduceBy piv v) p)⁻¹ (reduceBy piv v))) = 0
    rw [decode_xor, decode_smulC, decode_smulC, smul_smul, mul_inv_cancel₀ hcp, one_smul]
    ext l
    simp only [GF.add_v, Pi.add_apply, GF.zero_v, Pi.zero_apply]
    exact F4.add_self _

/-- `insertPivot` only appends (positions `< 6`). -/
lemma insertPivot_eq_append (piv : List (Nat × Nat)) (v : Nat) :
    ∃ ext : List (Nat × Nat), insertPivot 6 piv v = piv ++ ext ∧ ∀ q ∈ ext, q.1 < 6 := by
  cases hf : firstNZ (reduceBy piv v) 0 6 with
  | none => exact ⟨[], by simp [insertPivot, hf], by simp⟩
  | some p =>
    refine ⟨[(p, smulC (coordC (reduceBy piv v) p)⁻¹ (reduceBy piv v))], by simp [insertPivot, hf], ?_⟩
    intro q hq; simp at hq; subst hq; exact (firstNZ_some hf).2.1

/-- Appending pivots keeps a killed vector killed. -/
lemma reduceBy_append_kill (piv ext : List (Nat × Nat)) (u : Nat) (hext : ∀ q ∈ ext, q.1 < 6)
    (h0 : decode (reduceBy piv u) = 0) : decode (reduceBy (piv ++ ext) u) = 0 := by
  rw [reduceBy_append]
  generalize reduceBy piv u = r at h0
  induction ext generalizing r with
  | nil => exact h0
  | cons x ext ih =>
    show decode (reduceBy ext (r ^^^ smulC (coordC r x.1) x.2)) = 0
    apply ih (fun q hq => hext q (List.mem_cons_of_mem _ hq))
    have hc : coordC r x.1 = 0 := by
      have := congrArg (fun z : GF => z.v ⟨x.1, hext x List.mem_cons_self⟩) h0
      simpa using this
    rw [decode_xor, decode_smulC, hc, zero_smul, add_zero, h0]

/-- The reduction modulo `W_{m0}` kills `ga` and `gb`. -/
lemma pivW_kills (d : CaseData) :
    decode (reduceBy (pivW d) d.ga) = 0 ∧ decode (reduceBy (pivW d) d.gb) = 0 := by
  have hpw : pivW d = insertPivot 6 (insertPivot 6 [] d.ga) d.gb := rfl
  refine ⟨?_, by rw [hpw]; exact reduceBy_insertPivot_self _ d.gb⟩
  obtain ⟨ext, hext, hpos⟩ := insertPivot_eq_append (insertPivot 6 [] d.ga) d.gb
  rw [hpw, hext]
  exact reduceBy_append_kill _ _ _ hpos (reduceBy_insertPivot_self [] d.ga)

/-- Independent pairs in a subspace of dimension at least 2 (any finite-dimensional space). -/
lemma exists_pair_of_two_le' {M : Type*} [AddCommGroup M] [Module F4 M] [Module.Finite F4 M]
    {V : Submodule F4 M} (hV : 2 ≤ Module.finrank F4 V) :
    ∃ p q : M, p ∈ V ∧ q ∈ V ∧ LinearIndependent F4 ![p, q] := by
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank F4 V)
  obtain ⟨y, hy⟩ :=
    exists_linearIndependent_pair_of_one_lt_finrank (by omega : 1 < Module.finrank F4 V) hx
  refine ⟨x, y, x.2, y.2, ?_⟩
  have := hy.map' V.subtype (Submodule.ker_subtype V)
  convert this using 1
  ext i; fin_cases i <;> rfl

end Mu4.Bridge
