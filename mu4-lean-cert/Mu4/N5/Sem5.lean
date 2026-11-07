import Mu4.N5.BCodes5
import Mu4.N5.Pencil5
import Mu4.Bridge.Sem

/-!
# mu_4(5): semantics of the search objects

The n = 5 versions of `Mu4/Bridge/Sem.lean`: linear forms of codes on five coordinates (`formC5`), the pencil
context (`mkPCtx5`), block operators and the operator `E` of a solution, in GF(4^5).
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge


/-! ### Linear forms of codes -/

/-- The linear form `y ↦ ∑_l f_l y_l` of a code `f`. -/
def formC5 (f : Nat) : GF5 →ₗ[F4] F4 where
  toFun y := ∑ l : Fin 5, coordC f l * y.v l
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [GF5.smul_v, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_; ring

lemma dotC_eq5 (f y : Nat) : dotC5 f y = formC5 f (decode5 y) := by
  simp [dotC5, formC5, Fin.sum_univ_five]

/-! ### The basis vectors `e_l = t^l` -/

lemma decode_eC5 (l : Fin 5) : decode5 (eC l) = tG5 ^ l.val := by
  rw [tG5_pow]
  ext k
  fin_cases l <;> fin_cases k <;> rfl

lemma decode_eq_sum_eC5 (y : Nat) : decode5 y = ∑ l : Fin 5, coordC y l • decode5 (eC l) := by
  rw [decode5_eq_sum y]
  simp only [decode_eC5]

/-! ### The pencil context -/

lemma decode_ptC5 (p0 p1 : Nat) (m : Fin 5) :
    decode5 (ptC p0 p1 m.val) = pt5 (decode5 p0) (decode5 p1) m := by
  simp [ptC, pt5, ssC_eq, ttC_eq]

lemma mkPCtx5_pts (p0 p1 : Nat) (m : Fin 5) :
    (mkPCtx5 p0 p1).pts.getD m.val 0 = ptC p0 p1 m.val := by
  simp [mkPCtx5, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range m.isLt]

lemma xcCols_eq5 (X : PCtx5) (hX : X.xcTab = Array.ofFn (n := 64) fun c => xcColsOf5 X.tcols c.val)
    (c : Nat) : X.xcCols c = xcColsOf5 X.tcols c := by
  rw [PCtx5.xcCols, hX]
  by_cases hc : c < 64
  · simp [Array.getD_eq_getD_getElem?, hc]
  · simp [Array.getD_eq_getD_getElem?, hc]

/-- The direction element `x_c = ∑ c_k t_k`. -/
def xcG5 (X : PCtx5) (c : Nat) : GF5 := decode5 (X.xc c)

/-- The pencil context is well formed: three complement vectors, and the stored tables. -/
structure PCtx5WF (X : PCtx5) : Prop where
  tv3 : X.tv.length = 3
  tcols : X.tcols = X.tv.map fun t => (List.range 5).map fun l => mulK5 t (eC l)
  xcTab : X.xcTab = Array.ofFn (n := 64) fun c => xcColsOf5 X.tcols c.val

lemma mkPCtx5_WF (p0 p1 : Nat) (h : (mkPCtx5 p0 p1).ok = true) : PCtx5WF (mkPCtx5 p0 p1) := by
  refine ⟨?_, by simp only [mkPCtx5], by simp only [mkPCtx5]⟩
  simp only [PCtx5.ok, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

lemma decode_xcColsOf5 (X : PCtx5) (hX : PCtx5WF X) (c : Nat) (l : Fin 5) :
    decode5 ((xcColsOf5 X.tcols c).getD l.val 0) = xcG5 X c * decode5 (eC l) := by
  obtain ⟨h4, htc, -⟩ := hX
  rw [xcG5, PCtx5.xc, ← combo3_eq_combo]
  have hcol : (xcColsOf5 X.tcols c).getD l.val 0 =
      combo3 c (X.tcols.map fun col => col.getD l.val 0) := by
    rw [xcColsOf5, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range l.isLt,
      Option.map_some, Option.getD_some]
  rw [hcol]
  match hv : X.tv, h4 with
  | [t0, t1, t2], _ =>
    have : X.tcols.map (fun col => col.getD l.val 0) =
        [mulK5 t0 (eC l), mulK5 t1 (eC l), mulK5 t2 (eC l)] := by
      rw [htc, hv]
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range l.isLt]
    rw [this, decode5_combo3, decode5_combo3]
    simp only [decode5_mulK5, smul_mul_assoc, add_mul]

lemma xcColsOf_length5 (tcols : List (List Nat)) (c : Nat) : (xcColsOf5 tcols c).length = 5 := by
  simp [xcColsOf5]

lemma decode_applyCols_xc5 (X : PCtx5) (hX : PCtx5WF X) (c y : Nat) :
    decode5 (applyCols5 (X.xcCols c) y) = xcG5 X c * decode5 y := by
  rw [xcCols_eq5 X hX.xcTab c]
  have hl := xcColsOf_length5 X.tcols c
  match hcols : xcColsOf5 X.tcols c, hl with
  | [a0, a1, a2, a3, a4], _ =>
    have e : ∀ l : Fin 5, decode5 ((xcColsOf5 X.tcols c).getD l.val 0) = xcG5 X c * decode5 (eC l) :=
      decode_xcColsOf5 X hX c
    rw [hcols] at e
    rw [decode5_applyCols5, decode_eq_sum_eC5 y, Finset.mul_sum, Fin.sum_univ_five]
    have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
    simp only [List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero, Fin.val_one, Fin.val_two]
      at e0 e1 e2
    simp only [mul_smul_comm]
    rw [e0, e1, e2]
    have e3' : decode5 a3 = xcG5 X c * decode5 (eC 3) := e3
    have e4' : decode5 a4 = xcG5 X c * decode5 (eC 4) := e4
    rw [e3', e4']
    rfl

/-! ### Blocks -/

/-- `G Block y` in the field: `Block y = ∑_u f_u(y) g_u`, `G` acting on the coefficients. -/
def blockSem5 (G : Nat) (ts : List Term) (y : GF5) : GF5 :=
  match ts with
  | [(g0, f0), (g1, f1)] =>
    (m00 G * formC5 f0 y + m01 G * formC5 f1 y) • decode5 g0 +
      (m10 G * formC5 f0 y + m11 G * formC5 f1 y) • decode5 g1
  | [(g0, f0)] => (coordC G 0 * formC5 f0 y) • decode5 g0
  | _ => 0

lemma decode_applyG5 (G : Nat) (ts : List Term) (y : Nat) :
    decode5 (applyG5 G ts y) = blockSem5 G ts (decode5 y) := by
  match ts with
  | [(g0, f0), (g1, f1)] => simp [applyG5, blockSem5, dotC_eq5]
  | [(g0, f0)] => simp [applyG5, blockSem5, dotC_eq5]
  | [] => simp [applyG5, blockSem5]
  | _ :: _ :: _ :: _ => simp [applyG5, blockSem5]

lemma applyGE_entriesAt5 (G : Nat) (ts : List Term) (y : Nat) :
    applyGE G ts (entriesAt5 ts y) = applyG5 G ts y := by
  match ts with
  | [(g0, f0), (g1, f1)] => rfl
  | [(g0, f0)] => rfl
  | [] => rfl
  | _ :: _ :: _ :: _ => rfl

/-- The sum over the off blocks. -/
def offSem5 (off : List (Nat × List Term)) (goff : List Nat) (y : GF5) : GF5 :=
  ((off.zip goff).map fun (b, G) => blockSem5 G b.2 y).sum

lemma decode_offFold5 (off : List (Nat × List Term)) (goff : List Nat) (y : Nat) :
    decode5 (((off.zip goff).map fun (b, G) => applyG5 G b.2 y).foldl (· ^^^ ·) 0) =
      offSem5 off goff (decode5 y) := by
  rw [offSem5]
  have key : ∀ (L : List ((Nat × List Term) × Nat)) (a : Nat),
      decode5 ((L.map fun (b, G) => applyG5 G b.2 y).foldl (· ^^^ ·) a) =
        decode5 a + (L.map fun (b, G) => blockSem5 G b.2 (decode5 y)).sum := by
    intro L
    induction L with
    | nil => intro a; simp
    | cons x L ih =>
      intro a
      simp only [List.map_cons, List.foldl_cons, List.sum_cons]
      rw [ih, decode5_xor, decode_applyG5]
      abel
  rw [key, decode5_zero, zero_add]

/-- The operator `E` of a solution. -/
def Esem5 (X : PCtx5) (d : CaseData) (s : Sol) (y : GF5) : GF5 :=
  xcG5 X s.c * y + offSem5 d.off s.goff y + blockSem5 s.g0 [(d.ga, d.fa), (d.gb, d.fb)] y

lemma decode_Eval5 (X : PCtx5) (hX : PCtx5WF X) (d : CaseData) (s : Sol) (y : Nat) :
    decode5 (Eval5 X d s y) = Esem5 X d s (decode5 y) := by
  have := decode_offFold5 d.off s.goff y
  simp only [Eval5] at *
  rw [decode5_xor, decode5_xor, decode_applyCols_xc5 X hX, decode_applyG5]
  rw [show (((d.off.zip s.goff).map fun x => applyG5 x.2 x.1.2 y).foldl (· ^^^ ·) 0) =
      (((d.off.zip s.goff).map fun (b, G) => applyG5 G b.2 y).foldl (· ^^^ ·) 0) from rfl, this]
  rfl

/-- `E` without the `m0` block. -/
def E0sem5 (X : PCtx5) (d : CaseData) (c : Nat) (goff : List Nat) (y : GF5) : GF5 :=
  xcG5 X c * y + offSem5 d.off goff y

end Mu4.N5
