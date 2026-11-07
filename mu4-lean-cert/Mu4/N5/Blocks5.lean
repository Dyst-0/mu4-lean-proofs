import Mu4.N5.Normal5
import Mu4.Bridge.Blocks

/-!
# mu_4(5), N6: the blocks of a decomposition in normal form (`audit/PROOF.md`)

As `Mu4/Bridge/Blocks.lean`, for GF(4^5): the five off-`m0` vectors are a basis (`dependency_none5`), the off
blocks' forms are the true blocks (`offBlock_eq5`), the residual at the second point is `l_{m0}(x_{q2}) Block_{m0}`
(`residual_eq5`), the forms `fa, fb` are independent (`dependent2_false5`): `setupCase5` never returns
`invalid` for a case in normal form (`setupCase_ne_invalid5`).
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge


/-! ### Bounds of codes -/

lemma timesT_lt5 (v : Nat) : timesT5 v < 1024 := by
  have h1 : (v <<< 2) &&& 1023 < 1024 := by
    have := Nat.and_le_right (n := v <<< 2) (m := 1023); omega
  have h2 : smulC (coordC v 4) 6 < 1024 := smulC_lt_1024 _ (by norm_num)
  have e : (1024 : Nat) = 2 ^ 10 := by norm_num
  rw [e] at h1 h2 ⊢
  exact Nat.xor_lt_two_pow h1 h2

lemma mulK_lt5 (x : Nat) {y : Nat} (hy : y < 1024) : mulK5 x y < 1024 := by
  have e : (1024 : Nat) = 2 ^ 10 := by norm_num
  unfold mulK5
  simp only
  have t1 := timesT_lt5 y
  have t2 := timesT_lt5 (timesT5 y)
  have t3 := timesT_lt5 (timesT5 (timesT5 y))
  have t4 := timesT_lt5 (timesT5 (timesT5 (timesT5 y)))
  have a0 := smulC_lt_1024 (coordC x 0) hy
  have a1 := smulC_lt_1024 (coordC x 1) t1
  have a2 := smulC_lt_1024 (coordC x 2) t2
  have a3 := smulC_lt_1024 (coordC x 3) t3
  have a4 := smulC_lt_1024 (coordC x 4) t4
  rw [e] at a0 a1 a2 a3 a4 ⊢
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow a0 a1) a2) a3) a4

lemma xor_lt_1024 {x y : Nat} (hx : x < 1024) (hy : y < 1024) : x ^^^ y < 1024 := by
  have e : (1024 : Nat) = 2 ^ 10 := by norm_num
  rw [e] at hx hy ⊢; exact Nat.xor_lt_two_pow hx hy

lemma eC_lt5 (t : Nat) (ht : t < 5) : eC t < 1024 := by
  unfold eC; interval_cases t <;> decide

/-- Codes below `1024` are determined by their decoding. -/
lemma code_eq_of_decode5 {x y : Nat} (hx : x < 1024) (hy : y < 1024) (h : decode5 x = decode5 y) :
    x = y := by
  apply code_ext (n := 5) (by norm_num; exact hx) (by norm_num; exact hy)
  intro l hl
  have := congrArg (fun z : GF5 => z.v ⟨l, hl⟩) h
  simpa using this

lemma decode_foldl_xor5 (L : List Nat) (a : Nat) :
    decode5 (L.foldl (· ^^^ ·) a) = decode5 a + (L.map decode5).sum := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih => rw [List.foldl_cons, ih, decode5_xor, List.map_cons, List.sum_cons, add_assoc]

lemma foldl_xor_lt5 (L : List Nat) (a : Nat) (ha : a < 1024) (hL : ∀ x ∈ L, x < 1024) :
    L.foldl (· ^^^ ·) a < 1024 := by
  induction L generalizing a with
  | nil => exact ha
  | cons x L ih =>
    rw [List.foldl_cons]
    exact ih _ (xor_lt_1024 ha (hL x List.mem_cons_self)) (fun y hy => hL y (List.mem_cons_of_mem _ hy))

/-! ### The block list -/

/-- The vectors of the block at `m` (as in `blockList5`). -/
def bvecs5 (X : PCtx5) (s0 s1 : Nat) (mult ws : List Nat) (m : Nat) : List Nat :=
  if mult.getD m 0 = 2 then [Wv5 X s0 s1 m 0, Wv5 X s0 s1 m 1]
  else [smulC (pcA (ws.getD m 0)) (Wv5 X s0 s1 m 0) ^^^ smulC (pcB (ws.getD m 0)) (Wv5 X s0 s1 m 1)]

lemma blockList_eq5 (X : PCtx5) (s0 s1 : Nat) (mult ws : List Nat) :
    blockList5 X s0 s1 mult ws = (List.range 5).filterMap fun m =>
      if mult.getD m 0 = 2 ∨ mult.getD m 0 = 1 then some (m, bvecs5 X s0 s1 mult ws m) else none := by
  unfold blockList5
  congr 1
  funext m
  unfold bvecs5
  by_cases h2 : mult.getD m 0 = 2
  · rw [if_pos h2, if_pos (Or.inl h2), if_pos h2]
  · by_cases h1 : mult.getD m 0 = 1
    · rw [if_neg h2, if_pos h1, if_pos (Or.inr h1), if_neg h2]
    · rw [if_neg h2, if_neg h1, if_neg (by tauto)]

lemma mem_blockList5 {X : PCtx5} {s0 s1 : Nat} {mult ws : List Nat} {x : Nat × List Nat} :
    x ∈ blockList5 X s0 s1 mult ws ↔
      x.1 < 5 ∧ (mult.getD x.1 0 = 2 ∨ mult.getD x.1 0 = 1) ∧ x.2 = bvecs5 X s0 s1 mult ws x.1 := by
  rw [blockList_eq5, List.mem_filterMap]
  constructor
  · rintro ⟨m, hm, h⟩
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨List.mem_range.mp hm, hc, rfl⟩
  · rintro ⟨h5, hc, h2⟩
    refine ⟨x.1, List.mem_range.mpr h5, ?_⟩
    rw [if_pos hc, ← h2]

lemma blockList_fst5 (X : PCtx5) (s0 s1 : Nat) (mult ws : List Nat) :
    (blockList5 X s0 s1 mult ws).map Prod.fst =
      (List.range 5).filter fun m => decide (mult.getD m 0 = 2 ∨ mult.getD m 0 = 1) := by
  rw [blockList_eq5, List.map_filterMap, ← List.filterMap_eq_filter]
  congr 1
  funext m
  by_cases h : mult.getD m 0 = 2 ∨ mult.getD m 0 = 1
  · rw [if_pos h]; simp only [Option.map_some, Option.guard, decide_eq_true h, if_true]
  · rw [if_neg h]; simp only [Option.map_none, Option.guard, decide_eq_false h]; rfl

lemma blockList_nodup5 (X : PCtx5) (s0 s1 : Nat) (mult ws : List Nat) :
    ((blockList5 X s0 s1 mult ws).map Prod.fst).Nodup := by
  rw [blockList_fst5]; exact List.nodup_range.filter _

lemma bvecs_length5 (X : PCtx5) (s0 s1 : Nat) (mult ws : List Nat) (m : Nat)
    (h : mult.getD m 0 = 2 ∨ mult.getD m 0 = 1) : (bvecs5 X s0 s1 mult ws m).length = mult.getD m 0 := by
  unfold bvecs5
  rcases h with h | h
  · rw [if_pos h, h]; rfl
  · rw [if_neg (by omega), h]; rfl

lemma blockList_sum5 (X : PCtx5) (s0 s1 : Nat) (mult ws : List Nat) (hle : ∀ m < 5, mult.getD m 0 ≤ 2) :
    ((blockList5 X s0 s1 mult ws).map fun x => x.2.length).sum =
      ((List.range 5).map fun m => mult.getD m 0).sum := by
  rw [blockList_eq5, sum_map_filterMap]
  congr 1
  apply List.map_congr_left
  intro m hm
  have hm5 := hle m (List.mem_range.mp hm)
  by_cases h : mult.getD m 0 = 2 ∨ mult.getD m 0 = 1
  · rw [if_pos h]; simp [bvecs_length5 X s0 s1 mult ws m h]
  · rw [if_neg h]; show 0 = mult.getD m 0; omega

/-! ### Under the normal form -/

section NF5

variable {p0 p1 s0 s1 : Nat} {mult ws : List Nat} {D : Decomp5 10} {H : Submodule F4 GF5}

/-- The standard points of the pencil, as a function of `Nat`. -/
noncomputable def xpt5 (nf : NF5 p0 p1 s0 s1 mult ws D H) (m : Nat) : GF5 :=
  if h : m < 5 then pt5 nf.S.p nf.S.q ⟨m, h⟩ else 0

/-- The true block at `m` (zero off `0..4`). -/
noncomputable def tb5 (nf : NF5 p0 p1 s0 s1 mult ws D H) (m : Nat) (y : GF5) : GF5 :=
  if h : m < 5 then trueBlock5 nf.S ⟨m, h⟩ y else 0

/-- The number of alive terms vanishing at `x_m`. -/
noncomputable def nv5 (nf : NF5 p0 p1 s0 s1 mult ws D H) (m : Nat) : Nat :=
  if h : m < 5 then (vanAt5 nf.S ⟨m, h⟩).card else 0

variable (nf : NF5 p0 p1 s0 s1 mult ws D H)

lemma mult_eq_nv5 (m : Nat) (hm : m < 5) : mult.getD m 0 = nv5 nf m := by
  rw [nv5, dif_pos hm]; exact nf.mult_eq ⟨m, hm⟩

lemma nv_le_two5 (hD : D.ValidOn H) (m : Nat) : nv5 nf m ≤ 2 := by
  unfold nv5; split_ifs with h
  · exact vanAt_le_two5 hD nf.S _
  · omega

lemma sum_nv5 : ((List.range 5).map fun m => nv5 nf m).sum = 7 := by
  have h := sum_vanAt5 nf.S
  simp only [Fin.sum_univ_five] at h
  simp [List.range_succ, nv5]
  have e0 : (vanAt5 nf.S 0).card = (vanAt5 nf.S ⟨0, by norm_num⟩).card := rfl
  omega

lemma tb_zero5 (m : Nat) (hm : nv5 nf m = 0) (y : GF5) : tb5 nf m y = 0 := by
  unfold tb5
  split_ifs with h
  · rw [nv5, dif_pos h, Finset.card_eq_zero] at hm
    rw [trueBlock5, hm, Finset.sum_empty]
  · rfl

/-- The point `x_m` from the search's code of the point. -/
lemma decode_pts5 (hp0 : p0 < 1024) (hp1 : p1 < 1024) (m : Nat) (hm : m < 5) :
    decode5 ((mkPCtx5 p0 p1).pts.getD m 0) = xpt5 nf m := by
  have h1 : (mkPCtx5 p0 p1).pts.getD m 0 = ptC p0 p1 m := mkPCtx5_pts p0 p1 ⟨m, hm⟩
  have h2 : decode5 (ptC p0 p1 m) = pt5 (decode5 p0) (decode5 p1) ⟨m, hm⟩ := decode_ptC5 p0 p1 ⟨m, hm⟩
  rw [h1, h2, xpt5, dif_pos hm, ← nf.hp, ← nf.hq]

lemma decode_Wv'5 (hp0 : p0 < 1024) (hp1 : p1 < 1024) (m : Nat) (hm : m < 5) (i : Nat) :
    decode5 (Wv5 (mkPCtx5 p0 p1) s0 s1 m i) = (xpt5 nf m)⁻¹ * decode5 (if i = 0 then s0 else s1) := by
  have h1 : decode5 (Wv5 (mkPCtx5 p0 p1) s0 s1 m i) =
      (pt5 (decode5 p0) (decode5 p1) ⟨m, hm⟩)⁻¹ * decode5 (if i = 0 then s0 else s1) :=
    decode_Wv5 p0 p1 s0 s1 hp0 hp1 ⟨m, hm⟩ i
  rw [h1, xpt5, dif_pos hm, nf.hp, nf.hq]

lemma xpt_ne_zero5 (m : Nat) (hm : m < 5) : xpt5 nf m ≠ 0 := by
  rw [xpt5, dif_pos hm]; exact pt_ne_zero5 nf.S.hind _

/-- The span of the vectors of a block. -/
def bspan5 (vs : List Nat) : Submodule F4 GF5 :=
  Submodule.span F4 (Set.range fun u : Fin vs.length => decode5 (vs.getD u 0))

/-- Every `g_i` vanishing at `x_m` lies in the span of the block at `m`. -/
lemma g_mem_bspan5 (hp0 : p0 < 1024) (hp1 : p1 < 1024) (m : Nat) (hm : m < 5)
    (hc : mult.getD m 0 = 2 ∨ mult.getD m 0 = 1) (i : Fin 10) (hi : i ∈ vanAt5 nf.S ⟨m, hm⟩) :
    D.g i ∈ bspan5 (bvecs5 (mkPCtx5 p0 p1) s0 s1 mult ws m) := by
  obtain ⟨hiW, hiz⟩ := (mem_vanAt5 nf.S).mp hi
  have hx := xpt_ne_zero5 nf m hm
  by_cases h2 : mult.getD m 0 = 2
  · have hmem := nf.shat i hiW ⟨m, hm⟩ hiz
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    have hg : D.g i = α • ((xpt5 nf m)⁻¹ * decode5 s0) + β • ((xpt5 nf m)⁻¹ * decode5 s1) := by
      have : D.g i = (xpt5 nf m)⁻¹ * (pt5 nf.S.p nf.S.q ⟨m, hm⟩ * D.g i) := by
        rw [← mul_assoc, show pt5 nf.S.p nf.S.q ⟨m, hm⟩ = xpt5 nf m by rw [xpt5, dif_pos hm],
          inv_mul_cancel₀ hx, one_mul]
      rw [this, ← hαβ, mul_add, mul_smul_comm, mul_smul_comm]
    rw [hg]
    unfold bspan5 bvecs5
    rw [if_pos h2]
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨⟨0, by simp⟩, ?_⟩
      simp only [List.getD_cons_zero]
      rw [decode_Wv'5 nf hp0 hp1 m hm 0, if_pos rfl]
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨⟨1, by simp⟩, ?_⟩
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [decode_Wv'5 nf hp0 hp1 m hm 1, if_neg one_ne_zero]
  · have h1 : mult.getD m 0 = 1 := by tauto
    have hcard : (vanAt5 nf.S ⟨m, hm⟩).card = 1 := by rw [← nf.mult_eq]; exact h1
    have hmem := nf.single ⟨m, hm⟩ hcard i hi
    unfold bspan5 bvecs5
    rw [if_neg h2]
    refine Submodule.span_mono ?_ hmem
    rintro _ rfl
    refine ⟨⟨0, by simp⟩, ?_⟩
    simp only [List.getD_cons_zero, decode5_xor, decode5_smulC]
    rw [decode_Wv'5 nf hp0 hp1 m hm 0, decode_Wv'5 nf hp0 hp1 m hm 1, if_pos rfl, if_neg one_ne_zero,
      xpt5, dif_pos hm]

/-- The true block at a point of the block list lies in the span of its block. -/
lemma tb_mem_bspan5 (hp0 : p0 < 1024) (hp1 : p1 < 1024) (m : Nat) (hm : m < 5)
    (hc : mult.getD m 0 = 2 ∨ mult.getD m 0 = 1) (y : GF5) :
    tb5 nf m y ∈ bspan5 (bvecs5 (mkPCtx5 p0 p1) s0 s1 mult ws m) := by
  rw [tb5, dif_pos hm, trueBlock5]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (g_mem_bspan5 nf hp0 hp1 m hm hc i hi)

/-! ### The split at the first pair point -/

lemma split_bl5 {bl pre post : List (Nat × List Nat)} {m0 : Nat} {gs0 : List Nat}
    (hsplit : splitFirstPair bl = some (pre, (m0, gs0), post)) :
    bl = pre ++ (m0, gs0) :: post ∧ gs0.length = 2 := by
  obtain ⟨h1, h2, -⟩ := splitFirstPair_spec hsplit
  exact ⟨h1, h2⟩

variable {pre post : List (Nat × List Nat)} {m0 : Nat} {gs0 : List Nat}

lemma split_m05 (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post)) :
    m0 < 5 ∧ mult.getD m0 0 = 2 ∧ gs0 = [Wv5 (mkPCtx5 p0 p1) s0 s1 m0 0, Wv5 (mkPCtx5 p0 p1) s0 s1 m0 1] := by
  obtain ⟨hbl, hlen⟩ := split_bl5 hsplit
  have hmem : (m0, gs0) ∈ blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws := by rw [hbl]; simp
  obtain ⟨h5, hc, hgs⟩ := mem_blockList5.mp hmem
  simp only at h5 hc hgs
  have h2 : mult.getD m0 0 = 2 := by
    have := bvecs_length5 (mkPCtx5 p0 p1) s0 s1 mult ws m0 hc
    rw [← hgs, hlen] at this; omega
  refine ⟨h5, h2, ?_⟩
  rw [hgs, bvecs5, if_pos h2]

lemma off_mem_bl5 (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {x : Nat × List Nat} (hx : x ∈ pre ++ post) : x ∈ blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws := by
  rw [(split_bl5 hsplit).1]
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

lemma off_ne_m05 (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {x : Nat × List Nat} (hx : x ∈ pre ++ post) : x.1 ≠ m0 := by
  have hnd := blockList_nodup5 (mkPCtx5 p0 p1) s0 s1 mult ws
  rw [(split_bl5 hsplit).1, List.map_append, List.map_cons, List.nodup_append] at hnd
  obtain ⟨-, hpost, hdisj⟩ := hnd
  intro heq
  rcases List.mem_append.mp hx with h | h
  · exact hdisj _ (List.mem_map_of_mem h) _ List.mem_cons_self heq
  · have := (List.nodup_cons.mp hpost).1
    simp only at this
    exact this (List.mem_map.mpr ⟨x, h, heq⟩)

lemma off_cover5 (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    (m : Nat) (hm : m < 5) (hne : m ≠ m0) (hc : mult.getD m 0 = 2 ∨ mult.getD m 0 = 1) :
    ∃ x ∈ pre ++ post, x.1 = m := by
  have hmem : m ∈ (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws).map Prod.fst := by
    rw [blockList_fst5, List.mem_filter]
    exact ⟨List.mem_range.mpr hm, by simpa using hc⟩
  rw [(split_bl5 hsplit).1] at hmem
  simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons, List.mem_map] at hmem
  rcases hmem with ⟨x, hx, rfl⟩ | rfl | ⟨x, hx, rfl⟩
  · exact ⟨x, List.mem_append_left _ hx, rfl⟩
  · exact absurd rfl hne
  · exact ⟨x, List.mem_append_right _ hx, rfl⟩

/-- The off-`m0` blocks and the block at `m0` add up to the sum over the five points. -/
lemma off_sum_add5 (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {M : Type*} [AddCommMonoid M] (F : Nat → M) (hF : ∀ m < 5, ¬ (mult.getD m 0 = 2 ∨ mult.getD m 0 = 1) → F m = 0) :
    (((pre ++ post).map Prod.fst).map F).sum + F m0 = ((List.range 5).map F).sum := by
  have h1 : ((blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws).map Prod.fst).map F =
      (pre.map Prod.fst).map F ++ F m0 :: (post.map Prod.fst).map F := by
    rw [(split_bl5 hsplit).1]; simp
  have h2 : (((blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws).map Prod.fst).map F).sum =
      ((List.range 5).map F).sum := by
    rw [blockList_fst5]
    have key : ∀ l : List Nat, (∀ m ∈ l, m < 5) →
        ((l.filter fun m => decide (mult.getD m 0 = 2 ∨ mult.getD m 0 = 1)).map F).sum = (l.map F).sum := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a l ih =>
        have ha := hl a List.mem_cons_self
        have ih' := ih (fun m hm => hl m (List.mem_cons_of_mem _ hm))
        by_cases hc : mult.getD a 0 = 2 ∨ mult.getD a 0 = 1
        · rw [List.filter_cons_of_pos (by simpa using hc), List.map_cons, List.sum_cons, ih',
            List.map_cons, List.sum_cons]
        · rw [List.filter_cons_of_neg (by simpa using hc), ih', List.map_cons, List.sum_cons,
            hF a ha hc, zero_add]
    exact key _ (fun m hm => List.mem_range.mp hm)
  rw [← h2, h1]
  simp only [List.map_append, List.sum_append, List.sum_cons]
  abel

include nf in
lemma off_lengths5 (hD : D.ValidOn H)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post)) :
    ((pre ++ post).map fun x => x.2.length).sum = 5 := by
  have hsum := blockList_sum5 (mkPCtx5 p0 p1) s0 s1 mult ws
    (fun m hm => by rw [mult_eq_nv5 nf m hm]; exact nv_le_two5 nf hD m)
  have h8 : ((List.range 5).map fun m => mult.getD m 0).sum = 7 := by
    rw [← sum_nv5 nf]
    congr 1
    apply List.map_congr_left
    intro m hm
    exact mult_eq_nv5 nf m (List.mem_range.mp hm)
  rw [h8, (split_bl5 hsplit).1] at hsum
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, (split_bl5 hsplit).2] at hsum
  simp only [List.map_append, List.sum_append]
  omega

/-! ### The off-`m0` vectors are a basis -/

/-- Membership of a block vector in the off-`m0` vectors. -/
lemma bvec_mem_Gam5 {x : Nat × List Nat} (hx : x ∈ pre ++ post) {v : Nat} (hv : v ∈ x.2) :
    v ∈ (pre ++ post).flatMap (·.2) :=
  List.mem_flatMap.mpr ⟨x, hx, hv⟩

include nf in
lemma Gam_length5 (hD : D.ValidOn H)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post)) :
    ((pre ++ post).flatMap (·.2)).length = 5 := by
  rw [List.length_flatMap]; exact off_lengths5 nf hD hsplit

include nf in
/-- The off-`m0` vectors span `A`. -/
lemma Gam_span5 (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post)) :
    (⊤ : Submodule F4 GF5) ≤ Submodule.span F4 (Set.range fun j : Fin ((pre ++ post).flatMap (·.2)).length =>
      decode5 (((pre ++ post).flatMap (·.2)).get j)) := by
  classical
  obtain ⟨hm05, hm02, -⟩ := split_m05 hsplit
  set Gam := (pre ++ post).flatMap (·.2)
  have h6 : (aliveAt5 D (pt5 nf.S.p nf.S.q ⟨m0, hm05⟩)).card = 5 := by
    have := card_aliveAt_pt5 nf.S ⟨m0, hm05⟩
    have h2 : (vanAt5 nf.S ⟨m0, hm05⟩).card = 2 := by rw [← nf.mult_eq]; exact hm02
    omega
  have hbasis := point_basis5 hD (pt_mem5 nf.S _) (pt_ne_zero5 nf.S.hind _) h6
  have htop := hbasis.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_coe, h6, GF5.finrank_eq])
  rw [← htop, Submodule.span_le]
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  -- `i` vanishes at a point `m ≠ m0` of the block list
  rw [aliveAt_pt_eq5, Finset.mem_sdiff, Finset.mem_compl] at hi
  obtain ⟨hiW, hiv⟩ := hi
  obtain ⟨m, hm⟩ := vanish_point_exists5 nf.S hiW
  have hmne : m.val ≠ m0 := by
    intro h
    apply hiv
    rw [mem_vanAt5]
    exact ⟨hiW, by rw [show (⟨m0, hm05⟩ : Fin 5) = m from Fin.ext h.symm]; exact hm⟩
  have him : i ∈ vanAt5 nf.S m := (mem_vanAt5 nf.S).mpr ⟨hiW, hm⟩
  have hc : mult.getD m.val 0 = 2 ∨ mult.getD m.val 0 = 1 := by
    have h1 : 1 ≤ (vanAt5 nf.S m).card := Finset.card_pos.mpr ⟨i, him⟩
    have h2 := vanAt_le_two5 hD nf.S m
    rw [nf.mult_eq]; omega
  obtain ⟨x, hx, hxm⟩ := off_cover5 hsplit m.val m.isLt hmne hc
  have hxbl := off_mem_bl5 hsplit hx
  have hx2 : x.2 = bvecs5 (mkPCtx5 p0 p1) s0 s1 mult ws m.val := by
    rw [(mem_blockList5.mp hxbl).2.2, hxm]
  have hg := g_mem_bspan5 nf hp0 hp1 m.val m.isLt hc i him
  rw [← hx2] at hg
  refine Submodule.span_mono ?_ hg
  rintro _ ⟨u, rfl⟩
  have hv : x.2.getD u 0 ∈ Gam := by
    apply bvec_mem_Gam5 hx
    rw [List.getD_eq_getElem _ _ u.isLt]; exact List.getElem_mem _
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
  exact ⟨j, by show decode5 (Gam.get j) = decode5 (x.2.getD u 0); rw [hj]⟩

include nf in
lemma Gam_indep5 (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post)) :
    LinearIndependent F4 fun j : Fin ((pre ++ post).flatMap (·.2)).length =>
      decode5 (((pre ++ post).flatMap (·.2)).get j) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (Gam_span5 nf hD hp0 hp1 hsplit)
    (by rw [Fintype.card_fin, Gam_length5 nf hD hsplit, GF5.finrank_eq])

/-- A code below `1024` with zero coordinates is zero. -/
lemma code_zero_of_coord5 {x : Nat} (hx : x < 1024) (h : ∀ l < 5, coordC x l = 0) : x = 0 :=
  code_ext (n := 5) (by norm_num; exact hx) (by norm_num) (fun l hl => by rw [h l hl, coordC_zero])

include nf in
/-- Stage 1: the dependency5 search finds nothing. -/
lemma dependency_none5 (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post)) :
    dependency5 ((pre ++ post).flatMap (·.2)) = none := by
  set Gam := (pre ++ post).flatMap (·.2) with hGam
  have hind := Gam_indep5 nf hD hp0 hp1 hsplit
  have hlen := Gam_length5 nf hD hsplit
  unfold dependency5
  rw [List.find?_eq_none]
  intro lam hlam hp
  rw [List.mem_range] at hlam
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
  obtain ⟨hne, h0⟩ := hp
  apply hne
  have hd := congrArg decode5 h0
  rw [decode5_combo, decode5_zero] at hd
  have hc := Fintype.linearIndependent_iff.mp hind (fun k => coordC lam k) hd
  apply code_zero_of_coord5 hlam
  intro l hl
  exact hc ⟨l, by rw [← hGam, hlen]; exact hl⟩

/-! ### The dual rows of the off blocks -/

lemma isDual_spec5 {rho cols : List Nat} (h : isDual5 rho cols = true) :
    rho.length = 5 ∧ cols.length = 5 ∧
      ∀ j < 5, ∀ j' < 5, dotC5 (rho.getD j 0) (cols.getD j' 0) = if j = j' then 1 else 0 := by
  simp only [isDual5, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun j hj j' hj' => ?_⟩
  have := h3 j hj j' hj'
  by_cases hjj : j = j'
  · subst hjj; simpa using this
  · rw [if_neg hjj]; simpa [hjj] using this

lemma dualBasis_spec5 {cols rho : List Nat} (h : dualBasis5 cols = some rho) : isDual5 rho cols = true := by
  unfold dualBasis5 at h
  split at h
  · split_ifs at h with hd
    simp only [Option.some.injEq] at h
    subst h; exact hd
  · simp at h

/-- The block `b` of the off list. -/
abbrev ob5 (offB : List (Nat × List Nat)) (b : Nat) : Nat × List Nat := offB.getD b (0, [])

/-- Row `u` of chunk `b` of the dual rows. -/
abbrev rb5 (offB : List (Nat × List Nat)) (rho : List Nat) (b u : Nat) : Nat :=
  ((chunks (offB.map fun x => x.2.length) rho).getD b []).getD u 0

lemma ob_mem5 {offB : List (Nat × List Nat)} {b : Nat} (hb : b < offB.length) : ob5 offB b ∈ offB := by
  rw [ob5, List.getD_eq_getElem _ _ hb]; exact List.getElem_mem _

lemma lens_getD5 (offB : List (Nat × List Nat)) (b : Nat) :
    (offB.map fun x => x.2.length).getD b 0 = (ob5 offB b).2.length := by
  rw [show (0 : Nat) = (fun x : Nat × List Nat => x.2.length) (0, []) from rfl, List.getD_map]

include nf in
/-- The duality of the rows `rb5 b u` with the block vectors. -/
lemma block_dual5 (hD : D.ValidOn H)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {rho : List Nat} (hrho : isDual5 rho ((pre ++ post).flatMap (·.2)) = true)
    {b u b' u' : Nat} (hb : b < (pre ++ post).length) (hu : u < (ob5 (pre ++ post) b).2.length)
    (hb' : b' < (pre ++ post).length) (hu' : u' < (ob5 (pre ++ post) b').2.length) :
    formC5 (rb5 (pre ++ post) rho b u) (decode5 ((ob5 (pre ++ post) b').2.getD u' 0)) =
      if b = b' ∧ u = u' then 1 else 0 := by
  set offB := pre ++ post
  set L := offB.map (·.2) with hL
  have hns : offB.map (fun x => x.2.length) = L.map List.length := by rw [hL, List.map_map]; rfl
  have hsum : (L.map List.length).sum = 5 := by rw [← hns]; exact off_lengths5 nf hD hsplit
  obtain ⟨-, -, hd⟩ := isDual_spec5 hrho
  have hLb : ∀ c, L.getD c [] = (ob5 offB c).2 := fun c => by
    rw [hL, show ([] : List Nat) = (fun x : Nat × List Nat => x.2) (0, []) from rfl, List.getD_map]
  have hlb : ∀ c, (L.map List.length).getD c 0 = (ob5 offB c).2.length := fun c => by
    rw [← hns, lens_getD5]
  have hbL : b < (L.map List.length).length := by simpa [hL] using hb
  have hbL' : b' < (L.map List.length).length := by simpa [hL] using hb'
  have e1 : rb5 offB rho b u = rho.getD (offs (L.map List.length) b + u) 0 := by
    rw [rb5, hns, chunks_getD _ _ b hbL u (by rw [hlb]; exact hu)]
  have e2 : (ob5 offB b').2.getD u' 0 = (offB.flatMap (·.2)).getD (offs (L.map List.length) b' + u') 0 := by
    rw [List.flatMap_def, flatten_getD L b' (by simpa [hL] using hb') u' (by rw [hLb]; exact hu'), hLb]
  have hj := offs_add_lt_sum (L.map List.length) hbL (by rw [hlb]; exact hu)
  have hj' := offs_add_lt_sum (L.map List.length) hbL' (by rw [hlb]; exact hu')
  rw [hsum] at hj hj'
  rw [e1, e2, ← dotC_eq5, hd _ hj _ hj']
  by_cases h : b = b' ∧ u = u'
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h, if_neg]
    intro heq
    exact h (offs_inj (L.map List.length) hbL hbL' (by rw [hlb]; exact hu) (by rw [hlb]; exact hu') heq)

include nf in
/-- Expansion of a vector of block `b` in its basis, by the dual rows. -/
lemma dual_expand5 (hD : D.ValidOn H)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {rho : List Nat} (hrho : isDual5 rho ((pre ++ post).flatMap (·.2)) = true)
    {b : Nat} (hb : b < (pre ++ post).length) {v : GF5} (hv : v ∈ bspan5 (ob5 (pre ++ post) b).2) :
    ∑ u : Fin (ob5 (pre ++ post) b).2.length, formC5 (rb5 (pre ++ post) rho b u) v •
      decode5 ((ob5 (pre ++ post) b).2.getD u 0) = v := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F4).mp hv
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single u]
  · rw [block_dual5 nf hD hsplit hrho hb u.isLt hb u.isLt, if_pos ⟨rfl, rfl⟩, mul_one]
  · intro u' _ hu'
    rw [block_dual5 nf hD hsplit hrho hb u.isLt hb u'.isLt, if_neg (fun h => hu' (Fin.ext h.2.symm)),
      mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

include nf in
/-- The rows of block `b` vanish on the other blocks. -/
lemma dual_cross5 (hD : D.ValidOn H)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {rho : List Nat} (hrho : isDual5 rho ((pre ++ post).flatMap (·.2)) = true)
    {b b' u : Nat} (hb : b < (pre ++ post).length) (hu : u < (ob5 (pre ++ post) b).2.length)
    (hb' : b' < (pre ++ post).length) (hbb : b ≠ b') {v : GF5} (hv : v ∈ bspan5 (ob5 (pre ++ post) b').2) :
    formC5 (rb5 (pre ++ post) rho b u) v = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F4).mp hv
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro u' _
  rw [map_smul, smul_eq_mul, block_dual5 nf hD hsplit hrho hb hu hb' u'.isLt, if_neg (fun h => hbb h.1),
    mul_zero]

lemma lval_self5 : ∀ m < 5, lval m m = 0 := by decide

lemma lval_ne5 : ∀ m < 5, ∀ q < 5, m ≠ q → lval m q ≠ 0 := by decide

/-- The facts of an off block. -/
lemma ob_facts5 (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {b : Nat} (hb : b < (pre ++ post).length) :
    (ob5 (pre ++ post) b).1 < 5 ∧ (ob5 (pre ++ post) b).1 ≠ m0 ∧
      (mult.getD (ob5 (pre ++ post) b).1 0 = 2 ∨ mult.getD (ob5 (pre ++ post) b).1 0 = 1) ∧
      (ob5 (pre ++ post) b).2 = bvecs5 (mkPCtx5 p0 p1) s0 s1 mult ws (ob5 (pre ++ post) b).1 := by
  have hx := ob_mem5 hb
  obtain ⟨h5, hc, h2⟩ := mem_blockList5.mp (off_mem_bl5 hsplit hx)
  exact ⟨h5, off_ne_m05 hsplit hx, hc, h2⟩

include nf in
/-- L7: the forms of an off block, `f_j(y) = rho_j(x_{m0} y) / l_m(x_{m0})`, give the true block. -/
theorem offBlock_eq5 (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {rho : List Nat} (hrho : isDual5 rho ((pre ++ post).flatMap (·.2)) = true)
    {b : Nat} (hb : b < (pre ++ post).length) (y : GF5) :
    ∑ u : Fin (ob5 (pre ++ post) b).2.length,
      (formC5 (rb5 (pre ++ post) rho b u) (xpt5 nf m0 * y) * (lval (ob5 (pre ++ post) b).1 m0)⁻¹) •
        decode5 ((ob5 (pre ++ post) b).2.getD u 0) = tb5 nf (ob5 (pre ++ post) b).1 y := by
  classical
  obtain ⟨hm05, -, -⟩ := split_m05 hsplit
  obtain ⟨hb5, hbne, hbc, hb2⟩ := ob_facts5 hsplit hb
  set mb := (ob5 (pre ++ post) b).1 with hmb
  have hl : lval mb m0 ≠ 0 := lval_ne5 mb hb5 m0 hm05 hbne
  have htb : tb5 nf mb y ∈ bspan5 (ob5 (pre ++ post) b).2 := by
    rw [hb2]; exact tb_mem_bspan5 nf hp0 hp1 mb hb5 hbc y
  rw [← dual_expand5 nf hD hsplit hrho hb htb]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  -- the coefficient
  have hx : xpt5 nf m0 * y = ∑ m : Fin 5, lval m m0 • trueBlock5 nf.S m y := by
    rw [xpt5, dif_pos hm05]
    have := mul_pt_eq5 nf hD ⟨m0, hm05⟩ y
    simpa using this
  rw [hx, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single ⟨mb, hb5⟩]
  · rw [show trueBlock5 nf.S ⟨mb, hb5⟩ y = tb5 nf mb y by rw [tb5, dif_pos hb5]]
    simp only
    rw [mul_comm (lval mb m0), mul_assoc, mul_inv_cancel₀ hl, mul_one]
  · intro m _ hm
    by_cases hm0 : m.val = m0
    · rw [hm0, lval_self5 m0 hm05, zero_mul]
    · by_cases hc : mult.getD m.val 0 = 2 ∨ mult.getD m.val 0 = 1
      · obtain ⟨x, hxo, hxm⟩ := off_cover5 hsplit m.val m.isLt hm0 hc
        obtain ⟨b', hb', hxb'⟩ := List.mem_iff_getElem.mp hxo
        have hob : ob5 (pre ++ post) b' = x := by rw [ob5, List.getD_eq_getElem _ _ hb', hxb']
        have hbb : b ≠ b' := by
          intro h; subst h
          apply hm; apply Fin.ext; simp only; rw [← hxm, ← hob]
        have hv : trueBlock5 nf.S m y ∈ bspan5 (ob5 (pre ++ post) b').2 := by
          have h1 := tb_mem_bspan5 nf hp0 hp1 m.val m.isLt hc y
          rw [tb5, dif_pos m.isLt] at h1
          rw [hob, (mem_blockList5.mp (off_mem_bl5 hsplit hxo)).2.2, hxm]
          exact h1
        rw [dual_cross5 nf hD hsplit hrho hb u.isLt hb' hbb hv, mul_zero]
      · have h0 : (vanAt5 nf.S m).card = 0 := by
          have h1 := vanAt_le_two5 hD nf.S m
          rw [← nf.mult_eq]; rw [nf.mult_eq] at hc ⊢; omega
        rw [Finset.card_eq_zero] at h0
        rw [trueBlock5, h0, Finset.sum_empty, map_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The residual at the second point -/

lemma sum_flatMap_list5 {α β M : Type*} [AddCommMonoid M] (l : List α) (g : α → List β) (h : β → M) :
    ((l.flatMap g).map h).sum = (l.map fun x => ((g x).map h).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

lemma sum_fin_getD5 {α M : Type*} [AddCommMonoid M] (l : List α) (d : α) (F : α → M) :
    ∑ b : Fin l.length, F (l.getD b d) = (l.map F).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun b => F (l.getD b d))]
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]

lemma sum_fin_range5 {M : Type*} [AddCommMonoid M] (n : Nat) (F : Nat → M) :
    ∑ m : Fin n, F m = ((List.range n).map F).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun m => F m)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

/-- The off sum of the search, for any off list. -/
lemma decode_offAt_gen5 (off : List (Nat × List Term)) (q y : Nat) :
    decode5 (offAt5 off q y) =
      (off.map fun x => (x.2.map fun gf => (lval x.1 q * dotC5 gf.2 y) • decode5 gf.1).sum).sum := by
  unfold offAt5
  rw [decode_foldl_xor5, decode5_zero, zero_add, sum_flatMap_list5]
  congr 1
  apply List.map_congr_left
  rintro ⟨m, ts⟩ _
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨g, f⟩ _
  simp [decode5_smulC]

lemma pts_lt5 (hp0 : p0 < 1024) (hp1 : p1 < 1024) (m : Nat) : (mkPCtx5 p0 p1).pts.getD m 0 < 1024 := by
  by_cases hm : m < 5
  · have h1 : (mkPCtx5 p0 p1).pts.getD m 0 = ptC p0 p1 m := mkPCtx5_pts p0 p1 ⟨m, hm⟩
    rw [h1]; exact ptC_lt5 hp0 hp1 m
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [mkPCtx5]; omega)]
    simp

lemma Wv_lt5 (hs0 : s0 < 1024) (hs1 : s1 < 1024) (X : PCtx5) (m i : Nat) : Wv5 X s0 s1 m i < 1024 := by
  unfold Wv5; split_ifs
  · exact mulK_lt5 _ hs0
  · exact mulK_lt5 _ hs1

lemma bvecs_lt5 (hs0 : s0 < 1024) (hs1 : s1 < 1024) (X : PCtx5) (m : Nat) :
    ∀ v ∈ bvecs5 X s0 s1 mult ws m, v < 1024 := by
  intro v hv
  unfold bvecs5 at hv
  split_ifs at hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> exact Wv_lt5 hs0 hs1 X _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    exact xor_lt_1024 (smulC_lt_1024 _ (Wv_lt5 hs0 hs1 X _ _)) (smulC_lt_1024 _ (Wv_lt5 hs0 hs1 X _ _))

/-- The terms of `mkOff5`. -/
lemma mem_mkOff_terms5 {X : PCtx5} {offB : List (Nat × List Nat)} {m0' : Nat} {rho : List Nat}
    {x : Nat × List Term} (hx : x ∈ mkOff5 X offB m0' rho) {gf : Term} (hgf : gf ∈ x.2) :
    ∃ y ∈ offB, gf.1 ∈ y.2 := by
  unfold mkOff5 at hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
  exact ⟨z.1, List.of_mem_zip hz |>.1, (List.of_mem_zip hgf).1⟩

lemma offAt_lt5 (hs0 : s0 < 1024) (hs1 : s1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    (rho : List Nat) (q y : Nat) :
    offAt5 (mkOff5 (mkPCtx5 p0 p1) (pre ++ post) m0 rho) q y < 1024 := by
  unfold offAt5
  apply foldl_xor_lt5 _ _ (by norm_num)
  intro v hv
  obtain ⟨x, hx, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨gf, hgf, rfl⟩ := List.mem_map.mp hv
  apply smulC_lt_1024
  obtain ⟨z, hz, hgz⟩ := mem_mkOff_terms5 hx hgf
  have := (mem_blockList5.mp (off_mem_bl5 hsplit hz)).2.2
  rw [this] at hgz
  exact bvecs_lt5 hs0 hs1 _ _ _ hgz

include nf in
/-- The off sum of the search, decoded. -/
lemma decode_offAt5 (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {rho : List Nat} (hrho : isDual5 rho ((pre ++ post).flatMap (·.2)) = true) (q y : Nat) :
    decode5 (offAt5 (mkOff5 (mkPCtx5 p0 p1) (pre ++ post) m0 rho) q y) =
      (((pre ++ post).map Prod.fst).map fun m => lval m q • tb5 nf m (decode5 y)).sum := by
  obtain ⟨hm05, -, -⟩ := split_m05 hsplit
  have hlen6 : rho.length = 5 := (isDual_spec5 hrho).1
  have hsum6 := off_lengths5 nf hD hsplit
  set offB := pre ++ post with hoffB
  set C := chunks (offB.map fun x => x.2.length) rho with hC
  have hClen : C.length = offB.length := by rw [hC, chunks_length, List.length_map]
  rw [decode_offAt_gen5]
  unfold mkOff5
  simp only [List.map_map, Function.comp_def]
  rw [sum_zip_map offB C hClen (fun xb rs => ((xb.2.zip (rs.map (formOf5 ((mkPCtx5 p0 p1).pts.getD m0 0)
    (lval xb.1 m0)))).map fun gf => (lval xb.1 q * dotC5 gf.2 y) • decode5 gf.1).sum) (0, []) []]
  rw [← sum_fin_getD5 offB (0, []) (fun x => lval x.1 q • tb5 nf x.1 (decode5 y))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb := b.isLt
  have hCb : (C.getD b []).length = (ob5 offB b).2.length := by
    rw [hC, chunks_getD_length _ _ (by rw [hsum6, hlen6]) b (by simpa using hb), lens_getD5]
  rw [sum_zip_map (ob5 offB b).2 _ (by rw [List.length_map, hCb])
    (fun g f => (lval (ob5 offB b).1 q * dotC5 f y) • decode5 g) 0
    (formOf5 ((mkPCtx5 p0 p1).pts.getD m0 0) (lval (ob5 offB b).1 m0) 0)]
  rw [← offBlock_eq5 nf hD hp0 hp1 hsplit hrho hb (decode5 y), Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [List.getD_map]
  simp only [dotC_eq5, formC_formOf5, smul_smul]
  rw [decode_pts5 nf hp0 hp1 m0 hm05]

lemma GF_add_self_cancel5 (a b : GF5) : a + b + b = a := by
  rw [add_assoc, GF5_add_self, add_zero]

include nf in
lemma xpt_mul_eq5 (hD : D.ValidOn H) (q : Nat) (hq : q < 5) (y : GF5) :
    xpt5 nf q * y = ((List.range 5).map fun m => lval m q • tb5 nf m y).sum := by
  rw [xpt5, dif_pos hq, mul_pt_eq5 nf hD ⟨q, hq⟩ y, ← sum_fin_range5 5 (fun m => lval m q • tb5 nf m y)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [tb5, dif_pos m.isLt]

include nf in
/-- The residual at the second point is `l_{m0}(x_{q2}) Block_{m0}`. -/
lemma residual_eq5 (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {rho : List Nat} (hrho : isDual5 rho ((pre ++ post).flatMap (·.2)) = true) (q : Nat) (hq : q < 5)
    (y : Nat) :
    decode5 (mulK5 ((mkPCtx5 p0 p1).pts.getD q 0) y ^^^
        offAt5 (mkOff5 (mkPCtx5 p0 p1) (pre ++ post) m0 rho) q y) =
      lval m0 q • tb5 nf m0 (decode5 y) := by
  rw [decode5_xor, decode5_mulK5, decode_pts5 nf hp0 hp1 q hq, decode_offAt5 nf hD hp0 hp1 hsplit hrho,
    xpt_mul_eq5 nf hD q hq]
  have h := off_sum_add5 hsplit (fun m => lval m q • tb5 nf m (decode5 y)) (by
    intro m hm hc
    have h0 : nv5 nf m = 0 := by
      have := nv_le_two5 nf hD m; rw [mult_eq_nv5 nf m hm] at hc; omega
    show lval m q • tb5 nf m (decode5 y) = 0
    rw [tb_zero5 nf m h0, smul_zero])
  rw [← h, add_comm (List.sum _) (lval m0 q • _), add_assoc, GF5_add_self, add_zero]

lemma inW_isSome5 {ga gb s : Nat} (hga : ga < 1024) (hgb : gb < 1024) (hs : s < 1024)
    (h : decode5 s ∈ Submodule.span F4 {decode5 ga, decode5 gb}) : (inW ga gb s).isSome := by
  obtain ⟨A, C, hAC⟩ := Submodule.mem_span_pair.mp h
  unfold inW
  rw [List.find?_isSome]
  refine ⟨unitC A 0 ^^^ unitC C 1, ?_, ?_⟩
  · rw [List.mem_range]
    have h0 := unitC_lt A 0
    have h1 := unitC_lt C 1
    have e : (16 : Nat) = 2 ^ 4 := by norm_num
    rw [e]; exact Nat.xor_lt_two_pow (by omega) (by omega)
  · rw [beq_iff_eq]
    have c0 : coordC (unitC A 0 ^^^ unitC C 1) 0 = A := by simp [coordC_unitC]
    have c1 : coordC (unitC A 0 ^^^ unitC C 1) 1 = C := by simp [coordC_unitC]
    rw [c0, c1]
    apply code_eq_of_decode5 (xor_lt_1024 (smulC_lt_1024 _ hga) (smulC_lt_1024 _ hgb)) hs
    rw [decode5_xor, decode5_smulC, decode5_smulC, hAC]

/-- The block at `m0` lies in the span of `ga, gb`. -/
lemma tb_m0_mem5 (hp0 : p0 < 1024) (hp1 : p1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    (y : GF5) :
    tb5 nf m0 y ∈ Submodule.span F4 {decode5 (gs0.getD 0 0), decode5 (gs0.getD 1 0)} := by
  obtain ⟨hm05, hm02, hgs⟩ := split_m05 hsplit
  have h := tb_mem_bspan5 nf hp0 hp1 m0 hm05 (Or.inl hm02) y
  unfold bspan5 bvecs5 at h
  rw [if_pos hm02] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨u, rfl⟩
  rw [hgs]
  fin_cases u
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

include nf in
/-- Stage 2: every residual is found. -/
lemma residualAt_isSome5 (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024) (hs0 : s0 < 1024)
    (hs1 : s1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {rho : List Nat} (hrho : isDual5 rho ((pre ++ post).flatMap (·.2)) = true) (t : Nat) (ht : t < 5) :
    (residualAt5 (mkPCtx5 p0 p1) (mkOff5 (mkPCtx5 p0 p1) (pre ++ post) m0 rho) (gs0.getD 0 0) (gs0.getD 1 0)
      m0 t).isSome := by
  obtain ⟨hm05, -, hgs⟩ := split_m05 hsplit
  have hq2 : secondPt m0 < 5 := by unfold secondPt; split_ifs <;> omega
  unfold residualAt5
  apply inW_isSome5
  · rw [hgs]; exact Wv_lt5 hs0 hs1 _ _ _
  · rw [hgs]; exact Wv_lt5 hs0 hs1 _ _ _
  · exact xor_lt_1024 (mulK_lt5 _ (eC_lt5 t ht)) (offAt_lt5 hs0 hs1 hsplit rho _ _)
  · rw [residual_eq5 nf hD hp0 hp1 hsplit hrho _ hq2]
    exact Submodule.smul_mem _ _ (tb_m0_mem5 nf hp0 hp1 hsplit _)

/-! ### The block at `m0` -/

lemma coordC_foldl_unit5 (F : Nat → F4) (L : List Nat) (a l : Nat) :
    coordC (L.foldl (fun acc t => acc ^^^ unitC (F t) t) a) l =
      coordC a l + ((L.filter (· = l)).map fun _ => F l).sum := by
  induction L generalizing a with
  | nil => simp
  | cons k L ih =>
    simp only [List.foldl_cons]
    rw [ih, coordC_xor, coordC_unitC]
    by_cases hk : k = l
    · subst hk; simp [add_assoc]
    · simp [hk]

lemma coordC_formAB5 (res : List (Option Nat)) (m0' i : Nat) (t : Nat) (ht : t < 5) :
    coordC (formAB5 res m0' i) t = coordC ((res.getD t none).getD 0) i * (lval m0' (secondPt m0'))⁻¹ := by
  unfold formAB5
  rw [coordC_foldl_unit5, coordC_zero, zero_add]
  have : (List.range 5).filter (· = t) = [t] := by interval_cases t <;> decide
  rw [this]; simp

lemma formC_formAB5 (res : List (Option Nat)) (m0' i : Nat) (Y : GF5) :
    formC5 (formAB5 res m0' i) Y =
      ∑ t : Fin 5, coordC ((res.getD t none).getD 0) i * (lval m0' (secondPt m0'))⁻¹ * Y.v t := by
  show ∑ t : Fin 5, coordC (formAB5 res m0' i) t * Y.v t = _
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [coordC_formAB5 res m0' i t t.isLt]

/-- `tb5` is linear in `y`. -/
lemma tb_sum5 (m : Nat) {ι : Type*} (s : Finset ι) (c : ι → F4) (v : ι → GF5) :
    tb5 nf m (∑ t ∈ s, c t • v t) = ∑ t ∈ s, c t • tb5 nf m (v t) := by
  unfold tb5
  split_ifs with h
  · unfold trueBlock5
    simp only [map_sum, map_smul, smul_eq_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  · simp

lemma secondPt_lt5 (m0' : Nat) : secondPt m0' < 5 := by unfold secondPt; split_ifs <;> omega

lemma secondPt_ne5 (m0' : Nat) : secondPt m0' ≠ m0' := by unfold secondPt; split_ifs <;> omega

lemma find5?_spec_inW {ga gb s ac : Nat} (h : inW ga gb s = some ac) :
    smulC (coordC ac 0) ga ^^^ smulC (coordC ac 1) gb = s := by
  have := List.find?_some h
  simpa using this

include nf in
/-- The forms `fa, fb` of the block at `m0` give the true block. -/
theorem m0Block_eq5 (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {rho : List Nat} (hrho : isDual5 rho ((pre ++ post).flatMap (·.2)) = true)
    (hres : ∀ t < 5, (residualAt5 (mkPCtx5 p0 p1) (mkOff5 (mkPCtx5 p0 p1) (pre ++ post) m0 rho)
      (gs0.getD 0 0) (gs0.getD 1 0) m0 t).isSome) (Y : GF5) :
    let res := (List.range 5).map (residualAt5 (mkPCtx5 p0 p1) (mkOff5 (mkPCtx5 p0 p1) (pre ++ post) m0 rho)
      (gs0.getD 0 0) (gs0.getD 1 0) m0)
    formC5 (formAB5 res m0 0) Y • decode5 (gs0.getD 0 0) + formC5 (formAB5 res m0 1) Y • decode5 (gs0.getD 1 0) =
      tb5 nf m0 Y := by
  intro res
  obtain ⟨hm05, -, -⟩ := split_m05 hsplit
  set l := lval m0 (secondPt m0) with hl
  have hl0 : l ≠ 0 := lval_ne5 m0 hm05 _ (secondPt_lt5 m0) (secondPt_ne5 m0).symm
  rw [formC_formAB5, formC_formAB5, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib]
  conv_rhs => rw [GF_expand5 Y, tb_sum5 nf]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hrt : res.getD t none = residualAt5 (mkPCtx5 p0 p1) (mkOff5 (mkPCtx5 p0 p1) (pre ++ post) m0 rho)
      (gs0.getD 0 0) (gs0.getD 1 0) m0 t := by
    simp [res, List.getD_eq_getElem?_getD, List.getElem?_range t.isLt]
  obtain ⟨ac, hac⟩ := Option.isSome_iff_exists.mp (hres t t.isLt)
  rw [hrt, hac, Option.getD_some]
  have hdec := congrArg decode5 (find5?_spec_inW hac)
  rw [decode5_xor, decode5_smulC, decode5_smulC, residual_eq5 nf hD hp0 hp1 hsplit hrho _ (secondPt_lt5 m0)] at hdec
  calc (coordC ac 0 * l⁻¹ * Y.v t) • decode5 (gs0.getD 0 0) +
        (coordC ac 1 * l⁻¹ * Y.v t) • decode5 (gs0.getD 1 0)
      = (Y.v t * l⁻¹) • (coordC ac 0 • decode5 (gs0.getD 0 0) + coordC ac 1 • decode5 (gs0.getD 1 0)) := by
        rw [smul_add, smul_smul, smul_smul]; congr 1 <;> congr 1 <;> ring
    _ = Y.v t • tb5 nf m0 (decode5 (eC t)) := by
        rw [hdec, ← hl, smul_smul, mul_assoc, inv_mul_cancel₀ hl0, mul_one]

lemma dep2_fact5 : ∀ a b u0 v0 u1 v1 : F4, (a ≠ 0 ∨ b ≠ 0) → a * u0 + b * v0 = 0 → a * u1 + b * v1 = 0 →
    ∃ μ ν : F4, (μ ≠ 0 ∨ ν ≠ 0) ∧ μ * u0 + ν * u1 = 0 ∧ μ * v0 + ν * v1 = 0 := by
  decide +kernel

lemma ab16_ne5 : ∀ ab < 16, ab ≠ 0 → coordC ab 0 ≠ 0 ∨ coordC ab 1 ≠ 0 := by decide

lemma formC_smulC_xor5 (a b : F4) (f g : Nat) (Y : GF5) :
    formC5 (smulC a f ^^^ smulC b g) Y = a * formC5 f Y + b * formC5 g Y := by
  show ∑ l : Fin 5, coordC (smulC a f ^^^ smulC b g) l * Y.v l =
    a * (∑ l : Fin 5, coordC f l * Y.v l) + b * (∑ l : Fin 5, coordC g l * Y.v l)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coordC_xor, coordC_smulC _ _ _ (by omega), coordC_smulC _ _ _ (by omega)]
  ring

lemma formC_zero5 (Y : GF5) : formC5 0 Y = 0 := by
  show ∑ l : Fin 5, coordC 0 l * Y.v l = 0
  simp

include nf in
/-- A second point with two vanishing terms. -/
lemma exists_second_pair5 (hD : D.ValidOn H) {m0 : Nat} (hm05 : m0 < 5) (hm02 : nv5 nf m0 = 2) :
    ∃ m' : Fin 5, m'.val ≠ m0 ∧ (vanAt5 nf.S m').card = 2 := by
  by_contra h
  push_neg at h
  have hle : ∀ m : Fin 5, m.val ≠ m0 → (vanAt5 nf.S m).card ≤ 1 := fun m hm => by
    have := vanAt_le_two5 hD nf.S m; have := h m hm; omega
  have hsum := sum_vanAt5 nf.S
  have h0 : (vanAt5 nf.S ⟨m0, hm05⟩).card = 2 := by rw [nv5, dif_pos hm05] at hm02; exact hm02
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨m0, hm05⟩ : Fin 5)), h0] at hsum
  have : ∑ m ∈ Finset.univ.erase (⟨m0, hm05⟩ : Fin 5), (vanAt5 nf.S m).card ≤
      ∑ m ∈ Finset.univ.erase (⟨m0, hm05⟩ : Fin 5), 1 :=
    Finset.sum_le_sum fun m hm => hle m (fun h' => (Finset.ne_of_mem_erase hm) (Fin.ext h'))
  simp at this
  omega

lemma pair_indep_of_family5 {s : Finset (Fin 10)} {g : Fin 10 → GF5}
    (hli : LinearIndependent F4 (fun i : s => g i.val)) {a b : Fin 10} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) : LinearIndependent F4 ![g a, g b] := by
  have := hli.comp ![⟨a, ha⟩, ⟨b, hb⟩] (by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [Subtype.ext_iff])
  convert this using 1
  ext u; fin_cases u <;> rfl

include nf in
/-- The two terms at a pair point `m0` are alive at another pair point `m'`, where the `g`'s are a basis and the
`b`'s separate points. -/
lemma pair_terms5 (hD : D.ValidOn H) {m0 : Nat} (hm05 : m0 < 5) (hnv : nv5 nf m0 = 2) :
    ∃ k0 k1 : Fin 10, k0 ≠ k1 ∧ vanAt5 nf.S ⟨m0, hm05⟩ = {k0, k1} ∧
      LinearIndependent F4 ![D.g k0, D.g k1] ∧
      (∃ y0 : GF5, D.b k0 y0 = 1 ∧ D.b k1 y0 = 0) ∧ (∃ y1 : GF5, D.b k0 y1 = 0 ∧ D.b k1 y1 = 1) := by
  classical
  have hcard : (vanAt5 nf.S ⟨m0, hm05⟩).card = 2 := by rw [nv5, dif_pos hm05] at hnv; exact hnv
  obtain ⟨k0, k1, hk01, hvan⟩ := Finset.card_eq_two.mp hcard
  obtain ⟨m', hm'ne, hm'2⟩ := exists_second_pair5 nf hD hm05 hnv
  have h6 : (aliveAt5 D (pt5 nf.S.p nf.S.q m')).card = 5 := by
    have := card_aliveAt_pt5 nf.S m'; omega
  have halive : ∀ k ∈ vanAt5 nf.S ⟨m0, hm05⟩, k ∈ aliveAt5 D (pt5 nf.S.p nf.S.q m') := by
    intro k hk
    obtain ⟨hkW, hkz⟩ := (mem_vanAt5 nf.S).mp hk
    rw [aliveAt_pt_eq5, Finset.mem_sdiff, Finset.mem_compl]
    refine ⟨hkW, fun hk' => hm'ne ?_⟩
    have := vanish_point_unique5 nf.S hkW hkz ((mem_vanAt5 nf.S).mp hk').2
    rw [← this]
  have hk0 := halive k0 (by rw [hvan]; simp)
  have hk1 := halive k1 (by rw [hvan]; simp)
  have hbasis := point_basis5 hD (pt_mem5 nf.S m') (pt_ne_zero5 nf.S.hind m') h6
  obtain ⟨y0, hy0⟩ := point_dual5 hD (pt_mem5 nf.S m') (pt_ne_zero5 nf.S.hind m') h6 k0 hk0
  obtain ⟨y1, hy1⟩ := point_dual5 hD (pt_mem5 nf.S m') (pt_ne_zero5 nf.S.hind m') h6 k1 hk1
  refine ⟨k0, k1, hk01, hvan, pair_indep_of_family5 hbasis hk0 hk1 hk01, ⟨y0, ?_, ?_⟩, ⟨y1, ?_, ?_⟩⟩
  · rw [hy0 k0 hk0, if_pos rfl]
  · rw [hy0 k1 hk1, if_neg hk01.symm]
  · rw [hy1 k0 hk0, if_neg hk01]
  · rw [hy1 k1 hk1, if_pos rfl]

include nf in
/-- Stage 3: the forms `fa, fb` of the block at `m0` are independent. -/
lemma dependent2_false5 (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024)
    (hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (pre, (m0, gs0), post))
    {rho : List Nat} (hrho : isDual5 rho ((pre ++ post).flatMap (·.2)) = true)
    (hres : ∀ t < 5, (residualAt5 (mkPCtx5 p0 p1) (mkOff5 (mkPCtx5 p0 p1) (pre ++ post) m0 rho)
      (gs0.getD 0 0) (gs0.getD 1 0) m0 t).isSome) :
    let res := (List.range 5).map (residualAt5 (mkPCtx5 p0 p1) (mkOff5 (mkPCtx5 p0 p1) (pre ++ post) m0 rho)
      (gs0.getD 0 0) (gs0.getD 1 0) m0)
    dependent2 (formAB5 res m0 0) (formAB5 res m0 1) = false := by
  intro res
  have hblock := m0Block_eq5 nf hD hp0 hp1 hsplit hrho hres
  simp only at hblock
  set fa := formAB5 res m0 0
  set fb := formAB5 res m0 1
  by_contra h
  rw [Bool.not_eq_false] at h
  unfold dependent2 at h
  rw [List.any_eq_true] at h
  obtain ⟨ab, hab16, hab⟩ := h
  rw [List.mem_range] at hab16
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hab
  obtain ⟨hab0, hab⟩ := hab
  have hlin : ∀ Y, coordC ab 0 * formC5 fa Y + coordC ab 1 * formC5 fb Y = 0 := by
    intro Y; rw [← formC_smulC_xor5, hab, formC_zero5]
  obtain ⟨hm05, hm02, -⟩ := split_m05 hsplit
  have hnv : nv5 nf m0 = 2 := by rw [← mult_eq_nv5 nf m0 hm05]; exact hm02
  obtain ⟨k0, k1, hk01, hvan, hli, ⟨y0, h00, h01⟩, ⟨y1, h10, h11⟩⟩ := pair_terms5 nf hD hm05 hnv
  have ht : ∀ y, tb5 nf m0 y = D.b k0 y • D.g k0 + D.b k1 y • D.g k1 := by
    intro y
    rw [tb5, dif_pos hm05, trueBlock5, hvan, Finset.sum_pair hk01]
  have e0 := hblock y0
  rw [ht, h00, h01, one_smul, zero_smul, add_zero] at e0
  have e1 := hblock y1
  rw [ht, h10, h11, one_smul, zero_smul, zero_add] at e1
  obtain ⟨μ, ν, hμν, h1, h2⟩ := dep2_fact5 (coordC ab 0) (coordC ab 1) (formC5 fa y0) (formC5 fb y0)
    (formC5 fa y1) (formC5 fb y1) (ab16_ne5 ab hab16 hab0) (hlin y0) (hlin y1)
  have hz : μ • D.g k0 + ν • D.g k1 = 0 := by
    rw [← e0, ← e1]
    calc μ • (formC5 fa y0 • decode5 (gs0.getD 0 0) + formC5 fb y0 • decode5 (gs0.getD 1 0)) +
        ν • (formC5 fa y1 • decode5 (gs0.getD 0 0) + formC5 fb y1 • decode5 (gs0.getD 1 0))
        = (μ * formC5 fa y0 + ν * formC5 fa y1) • decode5 (gs0.getD 0 0) +
          (μ * formC5 fb y0 + ν * formC5 fb y1) • decode5 (gs0.getD 1 0) := by module
      _ = 0 := by rw [h1, h2, zero_smul, zero_smul, add_zero]
  have := LinearIndependent.pair_iff.mp hli μ ν hz
  rcases hμν with h | h
  · exact h this.1
  · exact h this.2

include nf in
/-- `setupCase5` never dismisses a case in normal form as `invalid`. -/
theorem setupCase_ne_invalid5 (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024) (hs0 : s0 < 1024)
    (hs1 : s1 < 1024) : setupCase5 (mkPCtx5 p0 p1) s0 s1 mult ws ≠ .invalid := by
  unfold setupCase5
  split
  · simp
  · rename_i pre' m0' gs0' post' hsplit
    split
    · rw [dependency_none5 nf hD hp0 hp1 hsplit]; simp
    · rename_i rho hrho
      have hd := dualBasis_spec5 hrho
      have hres := residualAt_isSome5 nf hD hp0 hp1 hs0 hs1 hsplit hd
      have hdep := dependent2_false5 nf hD hp0 hp1 hsplit hd hres
      unfold setupFrom5
      simp only at hdep ⊢
      rw [if_neg, if_neg]
      · split <;> simp
      · rw [hdep]; simp
      · rw [Bool.not_eq_true, List.any_eq_false]
        intro r hr
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
        rw [List.mem_range] at ht
        have := hres t ht
        simp only [Option.isNone_iff_eq_none, decide_eq_true_eq]
        exact Option.isSome_iff_ne_none.mp this

end NF5

end Mu4.N5
