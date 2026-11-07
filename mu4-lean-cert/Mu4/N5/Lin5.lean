import Mu4.N5.Setup5
import Mu4.Bridge.Lin

/-!
# mu_4(5): linearity of the solution operator, and reduction modulo `W_{m0}`

As `Mu4/Bridge/Lin.lean`, with reduction positions `< 5`.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge


/-! ### Linearity -/

lemma blockSem_add5 (G : Nat) (ts : List Term) (y y' : GF5) :
    blockSem5 G ts (y + y') = blockSem5 G ts y + blockSem5 G ts y' := by
  match ts with
  | [(g0, f0), (g1, f1)] => simp only [blockSem5, map_add]; module
  | [(g0, f0)] => simp only [blockSem5, map_add]; module
  | [] => simp [blockSem5]
  | _ :: _ :: _ :: _ => simp [blockSem5]

lemma blockSem_smul5 (G : Nat) (ts : List Term) (c : F4) (y : GF5) :
    blockSem5 G ts (c • y) = c • blockSem5 G ts y := by
  match ts with
  | [(g0, f0), (g1, f1)] => simp only [blockSem5, map_smul, smul_eq_mul]; module
  | [(g0, f0)] => simp only [blockSem5, map_smul, smul_eq_mul]; module
  | [] => simp [blockSem5]
  | _ :: _ :: _ :: _ => simp [blockSem5]

lemma offSem_add5 (off : List (Nat × List Term)) (goff : List Nat) (y y' : GF5) :
    offSem5 off goff (y + y') = offSem5 off goff y + offSem5 off goff y' := by
  simp only [offSem5, blockSem_add5]
  induction (off.zip goff) with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; abel

lemma offSem_smul5 (off : List (Nat × List Term)) (goff : List Nat) (c : F4) (y : GF5) :
    offSem5 off goff (c • y) = c • offSem5 off goff y := by
  simp only [offSem5, blockSem_smul5]
  induction (off.zip goff) with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih, smul_add]

/-- The operator `E` of a solution, as a linear map. -/
def Elin5 (X : PCtx5) (d : CaseData) (s : Sol) : GF5 →ₗ[F4] GF5 where
  toFun := Esem5 X d s
  map_add' y y' := by
    simp only [Esem5, mul_add, offSem_add5, blockSem_add5]; abel
  map_smul' c y := by
    simp only [Esem5, RingHom.id_apply, mul_smul_comm, offSem_smul5, blockSem_smul5, smul_add]

/-! ### Reduction modulo a pivot list -/

/-- One reduction step `x ↦ x + x_p • w`, as a linear map. -/
def stepLin5 (p : Fin 5) (u : GF5) : GF5 →ₗ[F4] GF5 where
  toFun x := x + x.v p • u
  map_add' x y := by simp only [GF5.add_v, Pi.add_apply, add_smul]; abel
  map_smul' c x := by
    simp only [GF5.smul_v, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, smul_add]

/-- The reduction by a pivot list, as a linear map (positions `≥ 5` are skipped; echelon lists
have none). -/
def redLin5 : List (Nat × Nat) → (GF5 →ₗ[F4] GF5)
  | [] => LinearMap.id
  | (p, vv) :: rest => if h : p < 5 then redLin5 rest ∘ₗ stepLin5 ⟨p, h⟩ (decode5 vv) else redLin5 rest

lemma decode_reduceBy5 (piv : List (Nat × Nat)) (h : ∀ q ∈ piv, q.1 < 5) (v : Nat) :
    decode5 (reduceBy piv v) = redLin5 piv (decode5 v) := by
  induction piv generalizing v with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨p, vv⟩ := x
    have hp : p < 5 := h (p, vv) List.mem_cons_self
    have hrest : ∀ q ∈ rest, q.1 < 5 := fun q hq => h q (List.mem_cons_of_mem _ hq)
    show decode5 (reduceBy rest (v ^^^ smulC (coordC v p) vv)) = _
    rw [ih hrest, redLin5, dif_pos hp, LinearMap.comp_apply]
    congr 1
    simp [stepLin5, decode5_v]

/-- Inserting `v` makes the reduction kill `v`. -/
lemma reduceBy_insertPivot_self5 (piv : List (Nat × Nat)) (v : Nat) :
    decode5 (reduceBy (insertPivot 5 piv v) v) = 0 := by
  cases hf : firstNZ (reduceBy piv v) 0 5 with
  | none =>
    simp only [insertPivot, hf]
    ext l
    have := firstNZ_none hf l.val (by omega) (by omega)
    simp [this]
  | some p =>
    simp only [insertPivot, hf]
    obtain ⟨-, hp6, hcp⟩ := firstNZ_some hf
    rw [reduceBy_append]
    show decode5 (reduceBy piv v ^^^ smulC (coordC (reduceBy piv v) p)
      (smulC (coordC (reduceBy piv v) p)⁻¹ (reduceBy piv v))) = 0
    rw [decode5_xor, decode5_smulC, decode5_smulC, smul_smul, mul_inv_cancel₀ hcp, one_smul]
    ext l
    simp only [GF5.add_v, Pi.add_apply, GF5.zero_v, Pi.zero_apply]
    exact F4.add_self _

/-- `insertPivot 5` only appends (positions `< 5`). -/
lemma insertPivot_eq_append5 (piv : List (Nat × Nat)) (v : Nat) :
    ∃ ext : List (Nat × Nat), insertPivot 5 piv v = piv ++ ext ∧ ∀ q ∈ ext, q.1 < 5 := by
  cases hf : firstNZ (reduceBy piv v) 0 5 with
  | none => exact ⟨[], by simp [insertPivot, hf], by simp⟩
  | some p =>
    refine ⟨[(p, smulC (coordC (reduceBy piv v) p)⁻¹ (reduceBy piv v))], by simp [insertPivot, hf], ?_⟩
    intro q hq; simp at hq; subst hq; exact (firstNZ_some hf).2.1

/-- Appending pivots3 keeps a killed vector killed. -/
lemma reduceBy_append_kill5 (piv ext : List (Nat × Nat)) (u : Nat) (hext : ∀ q ∈ ext, q.1 < 5)
    (h0 : decode5 (reduceBy piv u) = 0) : decode5 (reduceBy (piv ++ ext) u) = 0 := by
  rw [reduceBy_append]
  generalize reduceBy piv u = r at h0
  induction ext generalizing r with
  | nil => exact h0
  | cons x ext ih =>
    show decode5 (reduceBy ext (r ^^^ smulC (coordC r x.1) x.2)) = 0
    apply ih (fun q hq => hext q (List.mem_cons_of_mem _ hq))
    have hc : coordC r x.1 = 0 := by
      have := congrArg (fun z : GF5 => z.v ⟨x.1, hext x List.mem_cons_self⟩) h0
      simpa using this
    rw [decode5_xor, decode5_smulC, hc, zero_smul, add_zero, h0]

/-- The reduction modulo `W_{m0}` kills `ga` and `gb`. -/
lemma pivW_kills5 (d : CaseData) :
    decode5 (reduceBy (pivW5 d) d.ga) = 0 ∧ decode5 (reduceBy (pivW5 d) d.gb) = 0 := by
  have hpw : pivW5 d = insertPivot 5 (insertPivot 5 [] d.ga) d.gb := rfl
  refine ⟨?_, by rw [hpw]; exact reduceBy_insertPivot_self5 _ d.gb⟩
  obtain ⟨ext, hext, hpos⟩ := insertPivot_eq_append5 (insertPivot 5 [] d.ga) d.gb
  rw [hpw, hext]
  exact reduceBy_append_kill5 _ _ _ hpos (reduceBy_insertPivot_self5 [] d.ga)

end Mu4.N5
