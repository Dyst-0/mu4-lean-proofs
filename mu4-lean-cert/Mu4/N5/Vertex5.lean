import Mu4.N5.Blocks5
import Mu4.Bridge.Vertex

/-!
# mu_4(5), N7: the operators of a decomposition in normal form

As `Mu4/Bridge/Vertex.lean`, for GF(4^5): for every family of eigenvalues `λ : Fin 10 → GF(4)`, operators of the
blocks with `∑ G_m Block_m (y) = ∑_{i alive} λ_i b_i(y) g_i`, commuting for any two families (`ops_exist`).
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Search Mu4.Lower Mu4.Bridge


variable {p0 p1 s0 s1 : Nat} {mult ws : List Nat} {D : Decomp5 10} {H : Submodule F4 GF5}

/-- The data of a valid case of a decomposition in normal form. -/
structure VCtx5 (p0 p1 s0 s1 : Nat) (mult ws : List Nat) (D : Decomp5 10) (H : Submodule F4 GF5)
    (d : CaseData) where
  nf : NF5 p0 p1 s0 s1 mult ws D H
  hD : D.ValidOn H
  hp0 : p0 < 1024
  hp1 : p1 < 1024
  hs0 : s0 < 1024
  hs1 : s1 < 1024
  bpre : List (Nat × List Nat)
  bpost : List (Nat × List Nat)
  gs0 : List Nat
  rho : List Nat
  hsplit : splitFirstPair (blockList5 (mkPCtx5 p0 p1) s0 s1 mult ws) = some (bpre, (d.m0, gs0), bpost)
  hrho : isDual5 rho ((bpre ++ bpost).flatMap (·.2)) = true
  hoff : d.off = mkOff5 (mkPCtx5 p0 p1) (bpre ++ bpost) d.m0 rho
  hga : d.ga = gs0.getD 0 0
  hgb : d.gb = gs0.getD 1 0
  hres : ∀ t < 5, (residualAt5 (mkPCtx5 p0 p1) (mkOff5 (mkPCtx5 p0 p1) (bpre ++ bpost) d.m0 rho)
    (gs0.getD 0 0) (gs0.getD 1 0) d.m0 t).isSome
  hfa : d.fa = formAB5 ((List.range 5).map (residualAt5 (mkPCtx5 p0 p1)
    (mkOff5 (mkPCtx5 p0 p1) (bpre ++ bpost) d.m0 rho) (gs0.getD 0 0) (gs0.getD 1 0) d.m0)) d.m0 0
  hfb : d.fb = formAB5 ((List.range 5).map (residualAt5 (mkPCtx5 p0 p1)
    (mkOff5 (mkPCtx5 p0 p1) (bpre ++ bpost) d.m0 rho) (gs0.getD 0 0) (gs0.getD 1 0) d.m0)) d.m0 1

/-- A valid result of `setupCase5` gives the context. -/
theorem vctx_of5 (nf : NF5 p0 p1 s0 s1 mult ws D H) (hD : D.ValidOn H) (hp0 : p0 < 1024) (hp1 : p1 < 1024)
    (hs0 : s0 < 1024) (hs1 : s1 < 1024) {d : CaseData}
    (h : setupCase5 (mkPCtx5 p0 p1) s0 s1 mult ws = .valid d) :
    Nonempty (VCtx5 p0 p1 s0 s1 mult ws D H d) := by
  obtain ⟨l1, gs0, l2, rho, hsplit, hrho, hfrom⟩ := setupCase_valid5 h
  obtain ⟨hoff, -, hga, hgb, -, hres, hfa, hfb, -, -⟩ := setupFrom_valid5 hfrom
  rw [hoff, hga, hgb] at hres hfa hfb
  exact ⟨⟨nf, hD, hp0, hp1, hs0, hs1, l1, l2, gs0, rho, hsplit, dualBasis_spec5 hrho, hoff, hga, hgb,
    hres, hfa, hfb⟩⟩

namespace VCtx5

variable {d : CaseData} (V : VCtx5 p0 p1 s0 s1 mult ws D H d)

/-- The off list of the split. -/
abbrev offB : List (Nat × List Nat) := V.bpre ++ V.bpost

lemma off_length : d.off.length = V.offB.length := by
  rw [V.hoff]; simp [mkOff5, chunks_length]

lemma rho_length : V.rho.length = 5 := (isDual_spec5 V.hrho).1

lemma lens_sum : (V.offB.map fun x => x.2.length).sum = 5 := off_lengths5 V.nf V.hD V.hsplit

lemma chunk_length {b : Nat} (hb : b < V.offB.length) :
    ((chunks (V.offB.map fun x => x.2.length) V.rho).getD b []).length = (ob5 V.offB b).2.length := by
  rw [chunks_getD_length _ _ (by rw [V.lens_sum, V.rho_length]) b (by simpa using hb), lens_getD5]

/-- Block `b` of the case data. -/
lemma off_getD {b : Nat} (hb : b < V.offB.length) :
    d.off.getD b (0, []) = ((ob5 V.offB b).1, (ob5 V.offB b).2.zip
      (((chunks (V.offB.map fun x => x.2.length) V.rho).getD b []).map
        (formOf5 ((mkPCtx5 p0 p1).pts.getD d.m0 0) (lval (ob5 V.offB b).1 d.m0)))) := by
  have hlen : (chunks (V.offB.map fun x => x.2.length) V.rho).length = V.offB.length := by
    rw [chunks_length, List.length_map]
  have hb' : b < d.off.length := by rw [V.off_length]; exact hb
  rw [List.getD_eq_getElem d.off (0, []) hb']
  simp only [V.hoff, mkOff5, List.getElem_map, List.getElem_zip]
  rw [ob5, List.getD_eq_getElem V.offB (0, []) hb,
    List.getD_eq_getElem (chunks (V.offB.map fun x => x.2.length) V.rho) [] (by rw [hlen]; exact hb)]

lemma blkOf_length {b : Nat} (hb : b < V.offB.length) : (blkOf d b).length = (ob5 V.offB b).2.length := by
  rw [blkOf, V.off_getD hb, List.length_zip, List.length_map, V.chunk_length hb, Nat.min_self]

lemma gOf_eq {b u : Nat} (hb : b < V.offB.length) (hu : u < (ob5 V.offB b).2.length) :
    gOf d b u = (ob5 V.offB b).2.getD u 0 := by
  rw [gOf, blkOf, V.off_getD hb]
  have hz : u < ((ob5 V.offB b).2.zip (((chunks (V.offB.map fun x => x.2.length) V.rho).getD b []).map
      (formOf5 ((mkPCtx5 p0 p1).pts.getD d.m0 0) (lval (ob5 V.offB b).1 d.m0)))).length := by
    rw [List.length_zip, List.length_map, V.chunk_length hb, Nat.min_self]; exact hu
  rw [List.getD_eq_getElem _ (0, 0) hz, List.getElem_zip, List.getD_eq_getElem (ob5 V.offB b).2 0 hu]

lemma fOf_eq {b u : Nat} (hb : b < V.offB.length) (hu : u < (ob5 V.offB b).2.length) :
    fOf d b u = formOf5 ((mkPCtx5 p0 p1).pts.getD d.m0 0) (lval (ob5 V.offB b).1 d.m0) (rb5 V.offB V.rho b u) := by
  rw [fOf, blkOf, V.off_getD hb]
  have hz : u < ((ob5 V.offB b).2.zip (((chunks (V.offB.map fun x => x.2.length) V.rho).getD b []).map
      (formOf5 ((mkPCtx5 p0 p1).pts.getD d.m0 0) (lval (ob5 V.offB b).1 d.m0)))).length := by
    rw [List.length_zip, List.length_map, V.chunk_length hb, Nat.min_self]; exact hu
  rw [List.getD_eq_getElem _ (0, 0) hz, List.getElem_zip, List.getElem_map]
  simp only [rb5]
  rw [List.getD_eq_getElem ((chunks (V.offB.map fun x => x.2.length) V.rho).getD b []) 0
    (by rw [V.chunk_length hb]; exact hu)]

include V in
lemma m0_lt : d.m0 < 5 := (split_m05 V.hsplit).1

lemma nv_m0 : nv5 V.nf d.m0 = 2 := by
  rw [← mult_eq_nv5 V.nf d.m0 V.m0_lt]; exact (split_m05 V.hsplit).2.1

/-- L7 in the case data: block `b`'s terms give the true block at its point. -/
lemma blk_sem {b : Nat} (hb : b < V.offB.length) (y : GF5) :
    ∑ u : Fin (ob5 V.offB b).2.length, formC5 (fOf d b u) y • decode5 (gOf d b u) = tb5 V.nf (ob5 V.offB b).1 y := by
  rw [← offBlock_eq5 V.nf V.hD V.hp0 V.hp1 V.hsplit V.hrho hb y]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [V.fOf_eq hb u.isLt, V.gOf_eq hb u.isLt, formC_formOf5, decode_pts5 V.nf V.hp0 V.hp1 d.m0 V.m0_lt]

/-- The block at `m0`. -/
lemma m0_sem (y : GF5) : formC5 d.fa y • decode5 d.ga + formC5 d.fb y • decode5 d.gb = tb5 V.nf d.m0 y := by
  rw [V.hfa, V.hfb, V.hga, V.hgb]
  exact m0Block_eq5 V.nf V.hD V.hp0 V.hp1 V.hsplit V.hrho V.hres y

/-- The duality of the rows with the block vectors, in the case data. -/
lemma rb_dual {b u b' u' : Nat} (hb : b < V.offB.length) (hu : u < (ob5 V.offB b).2.length)
    (hb' : b' < V.offB.length) (hu' : u' < (ob5 V.offB b').2.length) :
    formC5 (rb5 V.offB V.rho b u) (decode5 (gOf d b' u')) = if b = b' ∧ u = u' then 1 else 0 := by
  rw [V.gOf_eq hb' hu']
  exact block_dual5 V.nf V.hD V.hsplit V.hrho hb hu hb' hu'

end VCtx5

/-! ### Operators of the blocks -/

lemma coordC_code5 : ∀ c : F4, coordC c.code 0 = c := by decide

lemma code_mem5 : ∀ c : F4, c.code ∈ [0, 1, 2, 3] := by decide

lemma det2_fact5 : ∀ a0 a1 b0 b1 : F4, a0 * b1 + b0 * a1 = 0 →
    ∃ μ ν : F4, (μ ≠ 0 ∨ ν ≠ 0) ∧ μ * a0 + ν * b0 = 0 ∧ μ * a1 + ν * b1 = 0 := by
  decide +kernel

/-- Two independent vectors have an invertible coordinate matrix. -/
lemma det_ne_zero5 {u0 u1 x y : GF5} {a0 a1 b0 b1 : F4} (hx : x = a0 • u0 + a1 • u1)
    (hy : y = b0 • u0 + b1 • u1) (hxy : LinearIndependent F4 ![x, y]) : a0 * b1 + b0 * a1 ≠ 0 := by
  intro h0
  obtain ⟨μ, ν, hμν, h1, h2⟩ := det2_fact5 a0 a1 b0 b1 h0
  have hz : μ • x + ν • y = 0 := by
    rw [hx, hy]
    calc μ • (a0 • u0 + a1 • u1) + ν • (b0 • u0 + b1 • u1) = (μ * a0 + ν * b0) • u0 + (μ * a1 + ν * b1) • u1 := by
          module
      _ = 0 := by rw [h1, h2, zero_smul, zero_smul, add_zero]
  have := LinearIndependent.pair_iff.mp hxy μ ν hz
  rcases hμν with h | h
  · exact h this.1
  · exact h this.2

/-- `blockSem5` of a 2×2 operator with prescribed eigenvectors. -/
lemma blockSem_conj5 {g0 f0 g1 f1 : Nat} {a0 a1 b0 b1 l l' : F4} (hdet : a0 * b1 + b0 * a1 ≠ 0) {y : GF5}
    {β β' : F4} (hF0 : formC5 f0 y = β * a0 + β' * b0) (hF1 : formC5 f1 y = β * a1 + β' * b1) :
    blockSem5 (conjCode a0 a1 b0 b1 l l') [(g0, f0), (g1, f1)] y =
      l • (β • (a0 • decode5 g0 + a1 • decode5 g1)) + l' • (β' • (b0 • decode5 g0 + b1 • decode5 g1)) := by
  obtain ⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩ := conjCode_eigen a0 a1 b0 b1 l l' hdet
  set G := conjCode a0 a1 b0 b1 l l'
  simp only [blockSem5, hF0, hF1]
  have r0 : m00 G * (β * a0 + β' * b0) + m01 G * (β * a1 + β' * b1) = β * (l * a0) + β' * (l' * b0) := by
    rw [← e1, ← e3]; ring
  have r1 : m10 G * (β * a0 + β' * b0) + m11 G * (β * a1 + β' * b1) = β * (l * a1) + β' * (l' * b1) := by
    rw [← e2, ← e4]; ring
  rw [r0, r1]
  module

/-- The pair list of a block of length 2. -/
lemma pair_list5 {L : List Term} (h : L.length = 2) :
    L = [((L.getD 0 (0, 0)).1, (L.getD 0 (0, 0)).2), ((L.getD 1 (0, 0)).1, (L.getD 1 (0, 0)).2)] := by
  match L, h with
  | [a, b], _ => rfl

lemma single_list5 {L : List Term} (h : L.length = 1) : L = [((L.getD 0 (0, 0)).1, (L.getD 0 (0, 0)).2)] := by
  match L, h with
  | [a], _ => rfl

lemma sum_fin_len_two5 {α : Type*} {L : List α} (h : L.length = 2) (f : Nat → GF5) :
    ∑ u : Fin L.length, f u = f 0 + f 1 := by
  match L, h with
  | [a, b], _ => simp [Fin.sum_univ_two]

lemma sum_fin_len_one5 {α : Type*} {L : List α} (h : L.length = 1) (f : Nat → GF5) :
    ∑ u : Fin L.length, f u = f 0 := by
  match L, h with
  | [a], _ => simp

namespace VCtx5

variable {d : CaseData} (V : VCtx5 p0 p1 s0 s1 mult ws D H d)

/-- The `g`'s alive at `x_{m0}` are a basis. -/
lemma basis_m0 : LinearIndependent F4 (fun i : aliveAt5 D (pt5 V.nf.S.p V.nf.S.q ⟨d.m0, V.m0_lt⟩) => D.g i) := by
  have h6 : (aliveAt5 D (pt5 V.nf.S.p V.nf.S.q ⟨d.m0, V.m0_lt⟩)).card = 5 := by
    have := card_aliveAt_pt5 V.nf.S ⟨d.m0, V.m0_lt⟩
    have h2 := V.nv_m0
    rw [nv5, dif_pos V.m0_lt] at h2
    omega
  exact point_basis5 V.hD (pt_mem5 V.nf.S _) (pt_ne_zero5 V.nf.S.hind _) h6

lemma alive_m0 {m : Fin 5} (hm : m.val ≠ d.m0) {k : Fin 10} (hk : k ∈ vanAt5 V.nf.S m) :
    k ∈ aliveAt5 D (pt5 V.nf.S.p V.nf.S.q ⟨d.m0, V.m0_lt⟩) := by
  obtain ⟨hkW, hkz⟩ := (mem_vanAt5 V.nf.S).mp hk
  rw [aliveAt_pt_eq5, Finset.mem_sdiff, Finset.mem_compl]
  refine ⟨hkW, fun hk' => hm ?_⟩
  have := vanish_point_unique5 V.nf.S hkW hkz ((mem_vanAt5 V.nf.S).mp hk').2
  rw [this]

/-- The operator of an off block, for any eigenvalues. -/
lemma blockOp_exists {b : Nat} (hb : b < V.offB.length) :
    ∃ op : (Fin 10 → F4) → Nat,
      (∀ lam, op lam ∈ candOps (blkOf d b)) ∧
      (∀ lam y, blockSem5 (op lam) (blkOf d b) y =
        ∑ k ∈ vanAt5 V.nf.S ⟨(ob5 V.offB b).1, (ob_facts5 V.hsplit hb).1⟩, lam k • (D.b k y • D.g k)) ∧
      (∀ lam lam', (blkOf d b).length = 2 → comm2 (op lam) (op lam') = true) := by
  classical
  obtain ⟨hb5, hbne, hbc, hb2⟩ := ob_facts5 V.hsplit hb
  set m := (ob5 V.offB b).1 with hm
  have hlen : (blkOf d b).length = (ob5 V.offB b).2.length := V.blkOf_length hb
  have hnv : (vanAt5 V.nf.S ⟨m, hb5⟩).card = (ob5 V.offB b).2.length := by
    rw [hb2, bvecs_length5 _ _ _ _ _ _ hbc, mult_eq_nv5 V.nf m hb5, nv5, dif_pos hb5]
  have hsem := V.blk_sem hb
  have htb : ∀ y, tb5 V.nf m y = ∑ k ∈ vanAt5 V.nf.S ⟨m, hb5⟩, D.b k y • D.g k := fun y => by
    rw [tb5, dif_pos hb5]; rfl
  have hspan : ∀ j ∈ vanAt5 V.nf.S ⟨m, hb5⟩, D.g j ∈ bspan5 (ob5 V.offB b).2 := fun j hj => by
    rw [hb2]; exact g_mem_bspan5 V.nf V.hp0 V.hp1 m hb5 hbc j hj
  have hexp := fun j hj => dual_expand5 V.nf V.hD V.hsplit V.hrho hb (hspan j hj)
  -- the coefficient of a block vector in the block, by the rows
  have hcoef : ∀ (u : Nat) (hu : u < (ob5 V.offB b).2.length) (y : GF5),
      formC5 (rb5 V.offB V.rho b u) (tb5 V.nf m y) = formC5 (fOf d b u) y := by
    intro u hu y
    rw [← hsem y, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single ⟨u, hu⟩]
    · rw [V.rb_dual hb hu hb hu, if_pos ⟨rfl, rfl⟩, mul_one]
    · intro u' _ hu'
      rw [V.rb_dual hb hu hb u'.isLt, if_neg (fun h => hu' (Fin.ext h.2.symm)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rcases hbc with h2 | h1
  · -- a pair
    have hl2 : (ob5 V.offB b).2.length = 2 := by rw [hb2, bvecs_length5 _ _ _ _ _ _ (Or.inl h2), h2]
    obtain ⟨k, k', hkk, hvan⟩ := Finset.card_eq_two.mp (by rw [hnv, hl2] : (vanAt5 V.nf.S ⟨m, hb5⟩).card = 2)
    have hk : k ∈ vanAt5 V.nf.S ⟨m, hb5⟩ := by rw [hvan]; simp
    have hk' : k' ∈ vanAt5 V.nf.S ⟨m, hb5⟩ := by rw [hvan]; simp
    have hli : LinearIndependent F4 ![D.g k, D.g k'] :=
      pair_indep_of_family5 V.basis_m0 (V.alive_m0 hbne hk) (V.alive_m0 hbne hk') hkk
    set α0 := formC5 (rb5 V.offB V.rho b 0) (D.g k)
    set α1 := formC5 (rb5 V.offB V.rho b 1) (D.g k)
    set β0 := formC5 (rb5 V.offB V.rho b 0) (D.g k')
    set β1 := formC5 (rb5 V.offB V.rho b 1) (D.g k')
    have hu0 : 0 < (ob5 V.offB b).2.length := by omega
    have hu1 : 1 < (ob5 V.offB b).2.length := by omega
    have hgk : D.g k = α0 • decode5 (gOf d b 0) + α1 • decode5 (gOf d b 1) := by
      conv_lhs => rw [← hexp k hk]
      rw [sum_fin_len_two5 hl2 (fun u => formC5 (rb5 V.offB V.rho b u) (D.g k) • decode5 ((ob5 V.offB b).2.getD u 0)),
        V.gOf_eq hb hu0, V.gOf_eq hb hu1]
    have hgk' : D.g k' = β0 • decode5 (gOf d b 0) + β1 • decode5 (gOf d b 1) := by
      conv_lhs => rw [← hexp k' hk']
      rw [sum_fin_len_two5 hl2 (fun u => formC5 (rb5 V.offB V.rho b u) (D.g k') • decode5 ((ob5 V.offB b).2.getD u 0)),
        V.gOf_eq hb hu0, V.gOf_eq hb hu1]
    have hdet := det_ne_zero5 hgk hgk' hli
    have hblk : blkOf d b = [(gOf d b 0, fOf d b 0), (gOf d b 1, fOf d b 1)] := pair_list5 (by rw [hlen, hl2])
    refine ⟨fun lam => conjCode α0 α1 β0 β1 (lam k) (lam k'), fun lam => ?_, fun lam y => ?_,
      fun lam lam' _ => conjCode_comm _ _ _ _ _ _ _ _ hdet⟩
    · rw [hblk, candOps, if_pos (by simp), diag2, List.mem_filter, List.mem_range]
      exact ⟨conjCode_lt _ _ _ _ _ _, conjCode_diag _ _ _ _ _ _ hdet⟩
    · have hF : ∀ u (hu : u < (ob5 V.offB b).2.length), formC5 (fOf d b u) y =
          D.b k y * formC5 (rb5 V.offB V.rho b u) (D.g k) + D.b k' y * formC5 (rb5 V.offB V.rho b u) (D.g k') := by
        intro u hu
        rw [← hcoef u hu y, htb y, hvan, Finset.sum_pair hkk, map_add, map_smul, map_smul, smul_eq_mul,
          smul_eq_mul]
      rw [hblk, blockSem_conj5 hdet (hF 0 hu0) (hF 1 hu1), ← hgk, ← hgk', hvan, Finset.sum_pair hkk]
  · -- a single
    have hl1 : (ob5 V.offB b).2.length = 1 := by
      rw [hb2, bvecs_length5 _ _ _ _ _ _ (Or.inr h1), h1]
    obtain ⟨k, hvan⟩ := Finset.card_eq_one.mp (by rw [hnv, hl1] : (vanAt5 V.nf.S ⟨m, hb5⟩).card = 1)
    have hblk : blkOf d b = [(gOf d b 0, fOf d b 0)] := single_list5 (by rw [hlen, hl1])
    refine ⟨fun lam => (lam k).code, fun lam => ?_, fun lam y => ?_, fun lam lam' h => ?_⟩
    · rw [hblk, candOps, if_neg (by simp)]
      exact code_mem5 _
    · have h0 := hsem y
      rw [sum_fin_len_one5 hl1 (fun u => formC5 (fOf d b u) y • decode5 (gOf d b u)), htb y, hvan,
        Finset.sum_singleton] at h0
      rw [hblk, hvan, Finset.sum_singleton]
      simp only [blockSem5]
      rw [coordC_code5, mul_smul, h0]
    · rw [hblk] at h; simp at h

end VCtx5

/-- The pair-block operators of two solutions commute when each block's operators do. -/
lemma all_zip_filterMap5 (L : List (Nat × List Term)) (goff goff' : List Nat) (hl : goff.length = L.length)
    (hl' : goff'.length = L.length) (R : Nat → Nat → Bool)
    (h : ∀ j < L.length, (L.getD j (0, [])).2.length = 2 → R (goff.getD j 0) (goff'.getD j 0) = true) :
    (((L.zip goff).filterMap fun ((_, ts), G) => if ts.length = 2 then some G else none).zip
      ((L.zip goff').filterMap fun ((_, ts), G) => if ts.length = 2 then some G else none)).all
      (fun (G, H) => R G H) = true := by
  induction L generalizing goff goff' with
  | nil => simp
  | cons x L ih =>
    match goff, goff', hl, hl' with
    | G :: gs, G' :: gs', hl, hl' =>
      obtain ⟨m, ts⟩ := x
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl hl'
      have ih' := ih gs gs' hl hl' (fun j hj hj2 => by
        have := h (j + 1) (by simp; omega) (by simpa using hj2)
        simpa using this)
      simp only [List.zip_cons_cons, List.filterMap_cons]
      by_cases h2 : ts.length = 2
      · rw [if_pos h2, if_pos h2]
        simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
        refine ⟨?_, ih'⟩
        have := h 0 (by simp) (by simpa using h2)
        simpa using this
      · rw [if_neg h2, if_neg h2]
        exact ih'

namespace VCtx5

variable {d : CaseData} (V : VCtx5 p0 p1 s0 s1 mult ws D H d)

lemma g_m0_mem {k : Fin 10} (hk : k ∈ vanAt5 V.nf.S ⟨d.m0, V.m0_lt⟩) :
    D.g k ∈ Submodule.span F4 {decode5 d.ga, decode5 d.gb} := by
  obtain ⟨-, hm02, hgs⟩ := split_m05 V.hsplit
  have h := g_mem_bspan5 V.nf V.hp0 V.hp1 d.m0 V.m0_lt (Or.inl hm02) k hk
  unfold bspan5 bvecs5 at h
  rw [if_pos hm02] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨u, rfl⟩
  rw [V.hga, V.hgb, hgs]
  fin_cases u
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

/-- The operator of the block at `m0`, for any eigenvalues. -/
lemma m0Op_exists :
    ∃ op : (Fin 10 → F4) → Nat,
      (∀ lam, op lam < 256 ∧ diagPred (op lam) = true) ∧
      (∀ lam y, blockSem5 (op lam) [(d.ga, d.fa), (d.gb, d.fb)] y =
        ∑ k ∈ vanAt5 V.nf.S ⟨d.m0, V.m0_lt⟩, lam k • (D.b k y • D.g k)) ∧
      (∀ lam lam', comm2 (op lam) (op lam') = true) := by
  classical
  obtain ⟨k, k', hkk, hvan, hli, -, -⟩ := pair_terms5 V.nf V.hD V.m0_lt V.nv_m0
  have hk : k ∈ vanAt5 V.nf.S ⟨d.m0, V.m0_lt⟩ := by rw [hvan]; simp
  have hk' : k' ∈ vanAt5 V.nf.S ⟨d.m0, V.m0_lt⟩ := by rw [hvan]; simp
  obtain ⟨α0, α1, hα⟩ := Submodule.mem_span_pair.mp (V.g_m0_mem hk)
  obtain ⟨β0, β1, hβ⟩ := Submodule.mem_span_pair.mp (V.g_m0_mem hk')
  have hdet := det_ne_zero5 hα.symm hβ.symm hli
  have hgab : LinearIndependent F4 ![decode5 d.ga, decode5 d.gb] := by
    by_contra hdep
    exact not_indep_in_span_dep5 hdep (V.g_m0_mem hk) (V.g_m0_mem hk') hli
  refine ⟨fun lam => conjCode α0 α1 β0 β1 (lam k) (lam k'), fun lam => ⟨conjCode_lt _ _ _ _ _ _,
    conjCode_diag _ _ _ _ _ _ hdet⟩, fun lam y => ?_, fun lam lam' => conjCode_comm _ _ _ _ _ _ _ _ hdet⟩
  have hs := V.m0_sem y
  rw [tb5, dif_pos V.m0_lt] at hs
  change _ = ∑ k ∈ vanAt5 V.nf.S ⟨d.m0, V.m0_lt⟩, D.b k y • D.g k at hs
  rw [hvan, Finset.sum_pair hkk, ← hα, ← hβ] at hs
  set c0 := D.b k y * α0 + D.b k' y * β0
  set c1 := D.b k y * α1 + D.b k' y * β1
  have hs' : formC5 d.fa y • decode5 d.ga + formC5 d.fb y • decode5 d.gb = c0 • decode5 d.ga + c1 • decode5 d.gb := by
    rw [hs]; module
  have key : (formC5 d.fa y - c0) • decode5 d.ga + (formC5 d.fb y - c1) • decode5 d.gb = 0 := by
    rw [sub_smul, sub_smul]
    calc formC5 d.fa y • decode5 d.ga - c0 • decode5 d.ga + (formC5 d.fb y • decode5 d.gb - c1 • decode5 d.gb)
        = (formC5 d.fa y • decode5 d.ga + formC5 d.fb y • decode5 d.gb) - (c0 • decode5 d.ga + c1 • decode5 d.gb) := by
          abel
      _ = 0 := by rw [hs', sub_self]
  obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.mp hgab _ _ key
  rw [sub_eq_zero] at h0 h1
  rw [blockSem_conj5 hdet h0 h1, hα, hβ, hvan, Finset.sum_pair hkk]

end VCtx5

lemma sum_fin_congr_len5 {M : Type*} [AddCommMonoid M] {n m : Nat} (h : n = m) (f : Nat → M) :
    ∑ j : Fin n, f j = ∑ j : Fin m, f j := by subst h; rfl

/-- The alive terms, grouped by their vanishing point. -/
lemma sum_alive_fiber5 (S : Step1Data5 D H) (f : Fin 10 → GF5) :
    ∑ m : Fin 5, ∑ k ∈ vanAt5 S m, f k = ∑ k ∈ S.Wᶜ, f k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := S.Wᶜ) (t := Finset.univ) (g := vpt5 S)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_compl, mem_vanAt_iff_vpt5]
  · intro _ _; rfl

namespace VCtx5

variable {d : CaseData} (V : VCtx5 p0 p1 s0 s1 mult ws D H d)

/-- L8: operators of all blocks for any eigenvalues, with the block sum and commutation. -/
theorem ops_exist :
    ∃ (F : (Fin 10 → F4) → List Nat) (G0 : (Fin 10 → F4) → Nat),
      (∀ lam, (F lam).length = d.off.length) ∧
      (∀ lam, ∀ i < d.off.length, (F lam).getD i 0 ∈ candOps (blkOf d i)) ∧
      (∀ lam, G0 lam < 256 ∧ diagPred (G0 lam) = true) ∧
      (∀ lam y, offSem5 d.off (F lam) y + blockSem5 (G0 lam) [(d.ga, d.fa), (d.gb, d.fb)] y =
        ∑ k ∈ V.nf.S.Wᶜ, lam k • (D.b k y • D.g k)) ∧
      (∀ lam lam' c c', ((pairOps d ⟨c, F lam, G0 lam⟩).zip (pairOps d ⟨c', F lam', G0 lam'⟩)).all
        (fun (G, H) => comm2 G H) = true) := by
  classical
  have hb : ∀ b, ∃ op : (Fin 10 → F4) → Nat, ∀ hb : b < V.offB.length,
      (∀ lam, op lam ∈ candOps (blkOf d b)) ∧
      (∀ lam y, blockSem5 (op lam) (blkOf d b) y =
        ∑ k ∈ vanAt5 V.nf.S ⟨(ob5 V.offB b).1, (ob_facts5 V.hsplit hb).1⟩, lam k • (D.b k y • D.g k)) ∧
      (∀ lam lam', (blkOf d b).length = 2 → comm2 (op lam) (op lam') = true) := fun b => by
    by_cases h : b < V.offB.length
    · obtain ⟨op, h1, h2, h3⟩ := V.blockOp_exists h
      exact ⟨op, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  choose opb hopb using hb
  obtain ⟨op0, h01, h02, h03⟩ := V.m0Op_exists
  have hget : ∀ lam (i : Nat) (hi : i < d.off.length),
      ((List.range d.off.length).map fun b => opb b lam).getD i 0 = opb i lam := by
    intro lam i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  refine ⟨fun lam => (List.range d.off.length).map fun b => opb b lam, op0, fun lam => by simp,
    fun lam i hi => ?_, h01, fun lam y => ?_, fun lam lam' c c' => ?_⟩
  · rw [hget lam i hi]
    exact (hopb i (by rw [← V.off_length]; exact hi)).1 lam
  · -- the sum over the blocks
    set T : Nat → GF5 := fun m => if h : m < 5 then ∑ k ∈ vanAt5 V.nf.S ⟨m, h⟩, lam k • (D.b k y • D.g k)
      else 0 with hT
    rw [offSem5, sum_zip_map d.off _ (by simp) (fun b G => blockSem5 G b.2 y) (0, []) 0]
    have hterm : ∀ j : Fin d.off.length,
        blockSem5 (((List.range d.off.length).map fun b => opb b lam).getD j 0) (d.off.getD j (0, [])).2 y =
          T (ob5 V.offB j).1 := by
      intro j
      have hj : j.val < V.offB.length := by rw [← V.off_length]; exact j.isLt
      rw [hget lam j j.isLt]
      rw [show (d.off.getD j (0, [])).2 = blkOf d j from rfl, (hopb j hj).2.1 lam y, hT]
      simp only
      rw [dif_pos (ob_facts5 V.hsplit hj).1]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    rw [sum_fin_congr_len5 V.off_length (fun j => T (ob5 V.offB j).1)]
    rw [sum_fin_getD5 V.offB (0, []) (fun x => T x.1),
      show V.offB.map (fun x => T x.1) = (V.offB.map Prod.fst).map T by rw [List.map_map]; rfl]
    have h0 : blockSem5 (op0 lam) [(d.ga, d.fa), (d.gb, d.fb)] y = T d.m0 := by
      rw [h02 lam y, hT]; simp only; rw [dif_pos V.m0_lt]
    rw [h0, off_sum_add5 V.hsplit T (by
      intro m hm hc
      rw [hT]; simp only; rw [dif_pos hm]
      have : vanAt5 V.nf.S ⟨m, hm⟩ = ∅ := by
        rw [← Finset.card_eq_zero]
        have h2 := vanAt_le_two5 V.hD V.nf.S ⟨m, hm⟩
        have := V.nf.mult_eq ⟨m, hm⟩
        simp only at this
        rw [← this]; omega
      rw [this, Finset.sum_empty])]
    rw [← sum_fin_range5 5 T, ← sum_alive_fiber5 V.nf.S]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hT]; simp only; rw [dif_pos m.isLt]
  · -- commutation
    simp only [pairOps, List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
    refine ⟨h03 lam lam', ?_⟩
    apply all_zip_filterMap5 _ _ _ (by simp) (by simp)
    intro j hj h2
    rw [hget lam j hj, hget lam' j hj]
    exact (hopb j (by rw [← V.off_length]; exact hj)).2.2 lam lam' h2

end VCtx5

end Mu4.N5
