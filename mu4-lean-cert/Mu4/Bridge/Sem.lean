import Mu4.Bridge.Codes

/-!
# Semantics of the search objects

Linear forms of codes (`formC`), the pencil context (`mkPCtx`: points, complement, the columns of
`x_c`), block operators, and the operator `E` of a solution, in terms of the field `GF`.
-/

namespace Mu4.Bridge
open Mu4 F4 Mu4.Search Mu4.Lower

/-! ### Linear forms of codes -/

/-- The linear form `y ↦ ∑_l f_l y_l` of a code `f`. -/
def formC (f : Nat) : GF →ₗ[F4] F4 where
  toFun y := ∑ l : Fin 6, coordC f l * y.v l
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [GF.smul_v, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_; ring

lemma dotC_eq (f y : Nat) : dotC f y = formC f (decode y) := by
  simp [dotC, formC, Fin.sum_univ_six]

/-! ### The basis vectors `e_l = t^l` -/

lemma decode_eC (l : Fin 6) : decode (eC l) = tG ^ l.val := by
  rw [tG_pow]
  ext k
  fin_cases l <;> fin_cases k <;> rfl

lemma decode_eq_sum_eC (y : Nat) : decode y = ∑ l : Fin 6, coordC y l • decode (eC l) := by
  rw [decode_eq_sum y]
  simp only [decode_eC]

/-! ### The pencil context -/

lemma ssC_eq : ∀ m : Fin 5, ssC m.val = ss m := by decide
lemma ttC_eq : ∀ m : Fin 5, ttC m.val = tt m := by decide

lemma decode_ptC (p0 p1 : Nat) (m : Fin 5) :
    decode (ptC p0 p1 m.val) = pt (decode p0) (decode p1) m := by
  simp [ptC, pt, ssC_eq, ttC_eq]

lemma mkPCtx_pts (p0 p1 : Nat) (m : Fin 5) :
    (mkPCtx p0 p1).pts.getD m.val 0 = ptC p0 p1 m.val := by
  simp [mkPCtx, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range m.isLt]

lemma xcCols_eq (X : PCtx) (hX : X.xcTab = Array.ofFn (n := 256) fun c => xcColsOf X.tcols c.val)
    (c : Nat) : X.xcCols c = xcColsOf X.tcols c := by
  rw [PCtx.xcCols, hX]
  by_cases hc : c < 256
  · simp [Array.getD_eq_getD_getElem?, hc]
  · simp [Array.getD_eq_getD_getElem?, hc]

/-- The direction element `x_c = ∑ c_k t_k`. -/
def xcG (X : PCtx) (c : Nat) : GF := decode (X.xc c)

/-- The pencil context is well formed: four complement vectors, and the stored tables. -/
structure PCtxWF (X : PCtx) : Prop where
  tv4 : X.tv.length = 4
  tcols : X.tcols = X.tv.map fun t => (List.range 6).map fun l => mulK t (eC l)
  xcTab : X.xcTab = Array.ofFn (n := 256) fun c => xcColsOf X.tcols c.val

lemma mkPCtx_WF (p0 p1 : Nat) (h : (mkPCtx p0 p1).ok = true) : PCtxWF (mkPCtx p0 p1) := by
  refine ⟨?_, by simp only [mkPCtx], by simp only [mkPCtx]⟩
  simp only [PCtx.ok, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

lemma decode_xcColsOf (X : PCtx) (hX : PCtxWF X) (c : Nat) (l : Fin 6) :
    decode ((xcColsOf X.tcols c).getD l.val 0) = xcG X c * decode (eC l) := by
  obtain ⟨h4, htc, -⟩ := hX
  rw [xcG, PCtx.xc, ← combo4_eq_combo]
  have hcol : (xcColsOf X.tcols c).getD l.val 0 =
      combo4 c (X.tcols.map fun col => col.getD l.val 0) := by
    rw [xcColsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range l.isLt,
      Option.map_some, Option.getD_some]
  rw [hcol]
  match hv : X.tv, h4 with
  | [t0, t1, t2, t3], _ =>
    have : X.tcols.map (fun col => col.getD l.val 0) =
        [mulK t0 (eC l), mulK t1 (eC l), mulK t2 (eC l), mulK t3 (eC l)] := by
      rw [htc, hv]
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range l.isLt]
    rw [this, decode_combo4, decode_combo4]
    simp only [decode_mulK, smul_mul_assoc, add_mul]

lemma xcColsOf_length (tcols : List (List Nat)) (c : Nat) : (xcColsOf tcols c).length = 6 := by
  simp [xcColsOf]

lemma decode_applyCols_xc (X : PCtx) (hX : PCtxWF X) (c y : Nat) :
    decode (applyCols (X.xcCols c) y) = xcG X c * decode y := by
  rw [xcCols_eq X hX.xcTab c]
  have hl := xcColsOf_length X.tcols c
  match hcols : xcColsOf X.tcols c, hl with
  | [a0, a1, a2, a3, a4, a5], _ =>
    have e : ∀ l : Fin 6, decode ((xcColsOf X.tcols c).getD l.val 0) = xcG X c * decode (eC l) :=
      decode_xcColsOf X hX c
    rw [hcols] at e
    rw [decode_applyCols6, decode_eq_sum_eC y, Finset.mul_sum, Fin.sum_univ_six]
    have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5
    simp only [List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero, Fin.val_one, Fin.val_two]
      at e0 e1 e2
    simp only [mul_smul_comm]
    rw [e0, e1, e2]
    have e3' : decode a3 = xcG X c * decode (eC 3) := e3
    have e4' : decode a4 = xcG X c * decode (eC 4) := e4
    have e5' : decode a5 = xcG X c * decode (eC 5) := e5
    rw [e3', e4', e5']
    rfl

/-! ### Blocks -/

/-- `G Block y` in the field: `Block y = ∑_u f_u(y) g_u`, `G` acting on the coefficients. -/
def blockSem (G : Nat) (ts : List Term) (y : GF) : GF :=
  match ts with
  | [(g0, f0), (g1, f1)] =>
    (m00 G * formC f0 y + m01 G * formC f1 y) • decode g0 +
      (m10 G * formC f0 y + m11 G * formC f1 y) • decode g1
  | [(g0, f0)] => (coordC G 0 * formC f0 y) • decode g0
  | _ => 0

lemma decode_applyG (G : Nat) (ts : List Term) (y : Nat) :
    decode (applyG G ts y) = blockSem G ts (decode y) := by
  match ts with
  | [(g0, f0), (g1, f1)] => simp [applyG, blockSem, dotC_eq]
  | [(g0, f0)] => simp [applyG, blockSem, dotC_eq]
  | [] => simp [applyG, blockSem]
  | _ :: _ :: _ :: _ => simp [applyG, blockSem]

lemma applyGE_entriesAt (G : Nat) (ts : List Term) (y : Nat) :
    applyGE G ts (entriesAt ts y) = applyG G ts y := by
  match ts with
  | [(g0, f0), (g1, f1)] => rfl
  | [(g0, f0)] => rfl
  | [] => rfl
  | _ :: _ :: _ :: _ => rfl

/-- The sum over the off blocks. -/
def offSem (off : List (Nat × List Term)) (goff : List Nat) (y : GF) : GF :=
  ((off.zip goff).map fun (b, G) => blockSem G b.2 y).sum

lemma decode_offFold (off : List (Nat × List Term)) (goff : List Nat) (y : Nat) :
    decode (((off.zip goff).map fun (b, G) => applyG G b.2 y).foldl (· ^^^ ·) 0) =
      offSem off goff (decode y) := by
  rw [offSem]
  have key : ∀ (L : List ((Nat × List Term) × Nat)) (a : Nat),
      decode ((L.map fun (b, G) => applyG G b.2 y).foldl (· ^^^ ·) a) =
        decode a + (L.map fun (b, G) => blockSem G b.2 (decode y)).sum := by
    intro L
    induction L with
    | nil => intro a; simp
    | cons x L ih =>
      intro a
      simp only [List.map_cons, List.foldl_cons, List.sum_cons]
      rw [ih, decode_xor, decode_applyG]
      abel
  rw [key, decode_zero, zero_add]

/-- The operator `E` of a solution. -/
def Esem (X : PCtx) (d : CaseData) (s : Sol) (y : GF) : GF :=
  xcG X s.c * y + offSem d.off s.goff y + blockSem s.g0 [(d.ga, d.fa), (d.gb, d.fb)] y

lemma decode_Eval (X : PCtx) (hX : PCtxWF X) (d : CaseData) (s : Sol) (y : Nat) :
    decode (Eval X d s y) = Esem X d s (decode y) := by
  have := decode_offFold d.off s.goff y
  simp only [Eval] at *
  rw [decode_xor, decode_xor, decode_applyCols_xc X hX, decode_applyG]
  rw [show (((d.off.zip s.goff).map fun x => applyG x.2 x.1.2 y).foldl (· ^^^ ·) 0) =
      (((d.off.zip s.goff).map fun (b, G) => applyG G b.2 y).foldl (· ^^^ ·) 0) from rfl, this]
  rfl

/-- `E` without the `m0` block. -/
def E0sem (X : PCtx) (d : CaseData) (c : Nat) (goff : List Nat) (y : GF) : GF :=
  xcG X c * y + offSem d.off goff y

lemma decode_E0val (X : PCtx) (hX : PCtxWF X) (d : CaseData) (c : Nat) (goff : List Nat) (y : Nat) :
    decode (E0val (X.xcCols c) d goff y) = E0sem X d c goff (decode y) := by
  have := decode_offFold d.off goff y
  simp only [E0val] at *
  rw [decode_xor, decode_applyCols_xc X hX]
  rw [show (((d.off.zip goff).map fun x => applyG x.2 x.1.2 y).foldl (· ^^^ ·) 0) =
      (((d.off.zip goff).map fun (b, G) => applyG G b.2 y).foldl (· ^^^ ·) 0) from rfl, this]
  rfl

end Mu4.Bridge
