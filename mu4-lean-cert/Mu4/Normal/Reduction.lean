import Mu4.Normal.Cover
import Mu4.Normal.Patterns
import Mu4.Bridge.Normal

/-!
# L6: the normal form (`audit/PROOF.md`)

`normalFormReduction_holds`: a 12-term decomposition valid on a hyperplane `H`, with step-1 data, moves to the normal
form `Mu4.Bridge.NF` of one of the search's cases `(P_k, S_j, multiplicities, single points)`:
1. (`toRep`) by `x ↦ u σ^r(x)` the pencil `P` becomes the representative `P_k = span(1, p1_k)`, with the basis
   `1, p1_k` (C1, `cover1`);
2. (`normalize`) the rescaling `(c_i a_i, c_i⁻¹ b_i)` makes `a_i|_P = l_{m(i)}` on the standard points;
3. by `y ↦ V y` the plane `Ŝ` of the pencil structure lemma (L5) becomes the representative `S_j = span(1, s1_j)`
   (C2, `cover2`);
4. the multiplicities and single points are one of the 255 patterns (`mem_patterns`).
-/

set_option autoImplicit false

namespace Mu4.Normal
open Mu4 F4 Mu4.Lower Mu4.Search Mu4.Bridge

/-! ### Small facts -/

lemma line_of_vanish : ∀ m : Fin 5, ∀ α β : F4, ss m * α + tt m * β = 0 →
    ∃ c : F4, α = c * tt m ∧ β = c * ss m := by decide

/-- A form vanishing at `x_m` is `c · l_m` on the standard points, with `c = 0` only if it is zero on `P`. -/
theorem form_eq_lval (f : GF →ₗ[F4] F4) (p q : GF) (m : Fin 5) (h : f (pt p q m) = 0) :
    ∃ c : F4, (∀ q' : Fin 5, f (pt p q q') = c * lval m.val q'.val) ∧
      (c = 0 → f p = 0 ∧ f q = 0) := by
  have hlin : ∀ q' : Fin 5, f (pt p q q') = ss q' * f p + tt q' * f q := by
    intro q'; simp [pt, map_add, map_smul, smul_eq_mul]
  rw [hlin] at h
  obtain ⟨c, hp, hq⟩ := line_of_vanish m (f p) (f q) h
  refine ⟨c, fun q' => ?_, fun hc => ?_⟩
  · rw [hlin, lval_eq, hp, hq]
    ring
  · subst hc
    simp [hp, hq]

lemma indep_one_div {p q : GF} (h : LinearIndependent F4 ![p, q]) :
    LinearIndependent F4 ![1, p⁻¹ * q] := by
  have hp : p ≠ 0 := by simpa using h.ne_zero 0
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  apply h
  have := congrArg (p * ·) hst
  simp only [mul_add, mul_smul_comm, mul_one, mul_zero] at this
  rwa [← mul_assoc, mul_inv_cancel₀ hp, one_mul] at this

lemma not_scalar_of_indep {z : GF} (h : LinearIndependent F4 ![1, z]) : ∀ c : F4, z ≠ c • 1 := by
  intro c hc
  have := (LinearIndependent.pair_iff.mp h) c 1 (by rw [hc, one_smul, GF_add_self'])
  exact one_ne_zero this.2

lemma mul_indep {x u v : GF} (hx : x ≠ 0) (h : LinearIndependent F4 ![u, v]) :
    LinearIndependent F4 ![x * u, x * v] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  apply h
  have := congrArg (x⁻¹ * ·) hst
  simp only [mul_add, mul_smul_comm, mul_zero] at this
  rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hx, one_mul, one_mul] at this

lemma exists_pair_point {H : Submodule F4 GF} {D : Decomp 12} (hD : D.ValidOn H) (S : Step1Data D H) :
    ∃ m : Fin 5, (vanAt S m).card = 2 := by
  by_contra h
  push_neg at h
  have hle : ∀ m : Fin 5, (vanAt S m).card ≤ 1 := fun m => by
    have := vanAt_le_two hD S m; have := h m; omega
  have hsum := sum_vanAt S
  have : ∑ m : Fin 5, (vanAt S m).card ≤ ∑ _m : Fin 5, 1 := Finset.sum_le_sum fun m _ => hle m
  simp at this
  omega

/-! ### Step 1: the pencil -/

theorem toRep {H : Submodule F4 GF} (hH : Module.finrank F4 H = 5) {D : Decomp 12}
    (hD : D.ValidOn H) (S : Step1Data D H) :
    ∃ k < 10, ∃ H1 : Submodule F4 GF, Module.finrank F4 H1 = 5 ∧ ∃ D1 : Decomp 12, D1.ValidOn H1 ∧
      ∃ S1 : Step1Data D1 H1, S1.p = decode (pList.getD k (0, 0)).1 ∧
        S1.q = decode (pList.getD k (0, 0)).2 := by
  obtain ⟨k, hk, s, hs, a, b, c, d, hab, heq⟩ :=
    cover1 (S.p⁻¹ * S.q) (not_scalar_of_indep (indep_one_div S.hind))
  obtain ⟨hp0k, hp4, hp4096⟩ := pList_spec k hk
  set r := if s = 0 then 0 else 12 - s with hr
  set t := (pList.getD k (0, 0)).2 with ht
  set S1 := S.frobPow r
  have hz1 : S1.p⁻¹ * S1.q = frob^[r] (S.p⁻¹ * S.q) := by
    rw [S.frobPow_p, S.frobPow_q, frobIter_mul, frobIter_inv]
  set z1 := S1.p⁻¹ * S1.q with hz1def
  have heq' : (tau^[r] a • (1 : GF) + tau^[r] b • z1) * decode t =
      tau^[r] c • (1 : GF) + tau^[r] d • z1 := by
    have := congrArg (frob^[r]) heq
    rw [frobIter_mul, frobIter_add, frobIter_add, frobIter_smul, frobIter_smul, frobIter_smul,
      frobIter_smul, frobIter_one, frobIter_cancel s hs] at this
    rw [hz1]; exact this
  have hS1p : S1.p ≠ 0 := by simpa using S1.hind.ne_zero 0
  have hind1 := indep_one_div S1.hind
  set v := tau^[r] a • (1 : GF) + tau^[r] b • z1 with hvdef
  have hv : v ≠ 0 := by
    intro h0
    have := (LinearIndependent.pair_iff.mp hind1) _ _ h0
    rcases hab with ha | hb
    · exact tauIter_ne_zero r ha this.1
    · exact tauIter_ne_zero r hb this.2
  set u := S1.p * v with hudef
  have hu : u ≠ 0 := mul_ne_zero hS1p hv
  set S2 := S1.scaleX hu
  have hS2p : S2.p = v⁻¹ := by
    show u⁻¹ * S1.p = v⁻¹
    rw [hudef, mul_inv, mul_comm S1.p⁻¹, mul_assoc, inv_mul_cancel₀ hS1p, mul_one]
  have hS2q : S2.q = v⁻¹ * z1 := by
    show u⁻¹ * S1.q = v⁻¹ * z1
    rw [hudef, mul_inv, hz1def]; ring
  have h1mem : (1 : GF) ∈ Submodule.span F4 {S2.p, S2.q} := by
    rw [Submodule.mem_span_pair]
    refine ⟨tau^[r] a, tau^[r] b, ?_⟩
    rw [hS2p, hS2q]
    calc tau^[r] a • v⁻¹ + tau^[r] b • (v⁻¹ * z1) = v⁻¹ * v := by
          rw [hvdef, mul_add, mul_smul_comm, mul_smul_comm, mul_one]
      _ = 1 := inv_mul_cancel₀ hv
  have htmem : decode t ∈ Submodule.span F4 {S2.p, S2.q} := by
    rw [Submodule.mem_span_pair]
    refine ⟨tau^[r] c, tau^[r] d, ?_⟩
    rw [hS2p, hS2q]
    calc tau^[r] c • v⁻¹ + tau^[r] d • (v⁻¹ * z1) = v⁻¹ * (v * decode t) := by
          rw [heq', mul_add, mul_smul_comm, mul_smul_comm, mul_one]
      _ = decode t := by rw [← mul_assoc, inv_mul_cancel₀ hv, one_mul]
  refine ⟨k, hk, (frobImagePow H r).comap (LinearMap.mulLeft F4 u), ?_, (D.frobPow r).scaleX u,
    Decomp.scaleX_validOn (Decomp.frobPow_validOn hD r) hu,
    S2.rebase 1 (decode t) h1mem htmem (indep_one_decode hp4 hp4096), ?_, rfl⟩
  · rw [finrank_comap_mulLeft _ hu, finrank_frobImagePow, hH]
  · show (1 : GF) = decode (pList.getD k (0, 0)).1
    rw [hp0k, decode_one]

/-! ### Step 2: the normalization `a_i|_P = l_m` -/

theorem normalize {H : Submodule F4 GF} {D : Decomp 12} (S : Step1Data D H) :
    ∃ c : Fin 12 → F4, (∀ i, c i ≠ 0) ∧
      ∀ i, i ∉ S.W → ∀ m : Fin 5, D.a i (pt S.p S.q m) = 0 → ∀ q : Fin 5,
        c i * D.a i (pt S.p S.q q) = lval m q := by
  classical
  have key : ∀ i, ∃ c : F4, c ≠ 0 ∧ (i ∉ S.W → ∀ m : Fin 5, D.a i (pt S.p S.q m) = 0 →
      ∀ q : Fin 5, c * D.a i (pt S.p S.q q) = lval m q) := by
    intro i
    by_cases hi : i ∈ S.W
    · exact ⟨1, one_ne_zero, fun h => absurd hi h⟩
    · obtain ⟨m0, hm0⟩ := vanish_point_exists S hi
      obtain ⟨c, hc, hc0⟩ := form_eq_lval (D.a i) S.p S.q m0 hm0
      have hcne : c ≠ 0 := by
        intro h
        have := hc0 h
        rcases alive_of_not_W S hi with h1 | h1
        · exact h1 this.1
        · exact h1 this.2
      refine ⟨c⁻¹, inv_ne_zero hcne, fun _ m hm q => ?_⟩
      have hmm : m = m0 := vanish_point_unique S hi hm hm0
      subst hmm
      rw [hc q, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  choose c hc0 hc using key
  exact ⟨c, hc0, fun i hi m hm q => hc i hi m hm q⟩

/-! ### The reduction -/

theorem normalFormReduction_holds (H : Submodule F4 GF) (hH : Module.finrank F4 H = 5)
    (D : Decomp 12) (hD : D.ValidOn H) (hS : Nonempty (Step1Data D H)) :
    ∃ P ∈ pList, ∃ S ∈ sList, ∃ mult ws, (mult, ws) ∈ patterns ∧
      ∃ H' : Submodule F4 GF, Module.finrank F4 H' = 5 ∧ ∃ D' : Decomp 12, D'.ValidOn H' ∧
        Nonempty (NF P.1 P.2 S.1 S.2 mult ws D' H') := by
  classical
  obtain ⟨S⟩ := hS
  obtain ⟨k, hk, H1, hH1, D1, hD1, S1, hS1p, hS1q⟩ := toRep hH hD S
  obtain ⟨c, hc0, hc⟩ := normalize S1
  have hD2 := Decomp.rescale_validOn hD1 hc0
  set D2 := D1.rescale c with hD2def
  set S2 := S1.rescale hc0
  -- a point with two vanishing terms, and the plane `Ŝ` there
  obtain ⟨m1, hm1⟩ := exists_pair_point hD2 S2
  obtain ⟨ia, ib, hab, hvan⟩ := Finset.card_eq_two.mp hm1
  have ha : ia ∈ vanAt S2 m1 := by rw [hvan]; simp
  have hb : ib ∈ vanAt S2 m1 := by rw [hvan]; simp
  obtain ⟨hspan, hgab⟩ := pencil_structure hD2 S2 hab ha hb
  have hx1 : pt S2.p S2.q m1 ≠ 0 := pt_ne_zero S2.hind m1
  set e1 := pt S2.p S2.q m1 * D2.g ia with he1
  set e2 := pt S2.p S2.q m1 * D2.g ib with he2
  have he : LinearIndependent F4 ![e1, e2] := mul_indep hx1 hgab
  have he1ne : e1 ≠ 0 := by simpa using he.ne_zero 0
  obtain ⟨j, hj, a, b, c', d, hab', heq⟩ :=
    cover2 (e1⁻¹ * e2) (not_scalar_of_indep (indep_one_div he))
  obtain ⟨hs0, hs4, hs4096⟩ := sList_spec j hj
  set s1 := decode (sList.getD j (0, 0)).2 with hs1
  set V := e1 * (a • (1 : GF) + b • (e1⁻¹ * e2)) with hVdef
  have hV : V ≠ 0 := by
    apply mul_ne_zero he1ne
    intro h0
    have := (LinearIndependent.pair_iff.mp (indep_one_div he)) _ _ h0
    rcases hab' with h | h
    · exact h this.1
    · exact h this.2
  have hVe : V = a • e1 + b • e2 := by
    rw [hVdef, mul_add, mul_smul_comm, mul_smul_comm, mul_one, ← mul_assoc, mul_inv_cancel₀ he1ne,
      one_mul]
  have hVs : V * s1 = c' • e1 + d • e2 := by
    rw [hVdef, mul_assoc, heq, mul_add, mul_smul_comm, mul_smul_comm, mul_one, ← mul_assoc,
      mul_inv_cancel₀ he1ne, one_mul]
  have hVmem : V ∈ Submodule.span F4 {e1, e2} := by
    rw [hVe]; exact Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩
  have hVsmem : V * s1 ∈ Submodule.span F4 {e1, e2} := by
    rw [hVs]; exact Submodule.mem_span_pair.mpr ⟨c', d, rfl⟩
  have hVind : LinearIndependent F4 ![V, V * s1] := by
    have := mul_indep hV (indep_one_decode hs4 hs4096)
    simpa using this
  have hspanV := span_pair_eq hVmem hVsmem he hVind
  clear_value V
  -- the transport `y ↦ V y`
  have hD3 := Decomp.scaleY_validOn hD2 hV
  set D3 := D2.scaleY V with hD3def
  set S3 := S2.scaleY V
  have hshat : ∀ i, i ∉ S3.W → ∀ m : Fin 5, D3.a i (pt S3.p S3.q m) = 0 →
      pt S3.p S3.q m * D3.g i ∈ Submodule.span F4 {decode (sList.getD j (0, 0)).1, s1} := by
    intro i hi m hm
    have h := hspan i hi m hm
    rw [← hspanV] at h
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h
    rw [hs0, decode_one, Submodule.mem_span_pair]
    refine ⟨α, β, ?_⟩
    show α • (1 : GF) + β • s1 = pt S2.p S2.q m * (V⁻¹ * D2.g i)
    rw [mul_left_comm, ← hαβ, mul_add, mul_smul_comm, mul_smul_comm, ← mul_assoc,
      inv_mul_cancel₀ hV, one_mul]
  -- the single points
  have hsingle : ∀ m : Fin 5, ∃ w : ℕ, w < 5 ∧ ((vanAt S3 m).card ≠ 1 → w = 0) ∧
      ((vanAt S3 m).card = 1 → ∀ i ∈ vanAt S3 m, D3.g i ∈ Submodule.span F4
        {pcA w • ((pt S3.p S3.q m)⁻¹ * decode (sList.getD j (0, 0)).1) +
          pcB w • ((pt S3.p S3.q m)⁻¹ * s1)}) := by
    intro m
    by_cases h1 : (vanAt S3 m).card = 1
    · obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp h1
      have hi0m : i0 ∈ vanAt S3 m := by rw [hi0]; simp
      obtain ⟨hiW, hiz⟩ := (mem_vanAt S3).mp hi0m
      have hmem := hshat i0 hiW m hiz
      rw [hs0, decode_one] at hmem
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
      obtain ⟨w, κ, hα, hβ⟩ := pc_cover α β
      refine ⟨w.val, w.isLt, fun h => absurd h1 h, fun _ i hi => ?_⟩
      rw [hi0, Finset.mem_singleton] at hi
      rw [hi, hs0, decode_one, Submodule.mem_span_singleton]
      refine ⟨κ, ?_⟩
      have hxm : pt S3.p S3.q m ≠ 0 := pt_ne_zero S3.hind m
      have hg : D3.g i0 = (pt S3.p S3.q m)⁻¹ * (α • 1 + β • s1) := by
        rw [hαβ, ← mul_assoc, inv_mul_cancel₀ hxm, one_mul]
      rw [hg, hα, hβ, mul_add, mul_smul_comm, mul_smul_comm, smul_add, smul_smul, smul_smul]
    · exact ⟨0, by norm_num, fun _ => rfl, fun h => absurd h h1⟩
  choose wf hw5 hw0 hw using hsingle
  have hle : ∀ m : Fin 5, (vanAt S3 m).card < 3 := fun m => by
    have := vanAt_le_two hD3 S3 m; omega
  have hsum := sum_vanAt S3
  simp only [Fin.sum_univ_five] at hsum
  refine ⟨pList.getD k (0, 0), pList_mem k hk, sList.getD j (0, 0), sList_mem j hj,
    [(vanAt S3 0).card, (vanAt S3 1).card, (vanAt S3 2).card, (vanAt S3 3).card, (vanAt S3 4).card],
    [wf 0, wf 1, wf 2, wf 3, wf 4], ?_, H1, hH1, D3, hD3, ⟨?_⟩⟩
  · exact mem_patterns ⟨_, hle 0⟩ ⟨_, hle 1⟩ ⟨_, hle 2⟩ ⟨_, hle 3⟩ ⟨_, hle 4⟩ hsum
      ⟨_, hw5 0⟩ (hw0 0) ⟨_, hw5 1⟩ (hw0 1) ⟨_, hw5 2⟩ (hw0 2) ⟨_, hw5 3⟩ (hw0 3) ⟨_, hw5 4⟩ (hw0 4)
  · exact {
      S := S3
      hp := hS1p
      hq := hS1q
      norm := by
        intro i hi m hm q
        have hm' : D1.a i (pt S1.p S1.q m) = 0 := by
          have := (rescale_a_eq_zero hc0 i (pt S1.p S1.q m)).mp hm
          exact this
        have := hc i hi m hm' q
        show (D1.rescale c).a i (pt S1.p S1.q q) = lval m q
        simp only [Decomp.rescale, LinearMap.smul_apply, smul_eq_mul]
        exact this
      mult_eq := by intro m; fin_cases m <;> rfl
      shat := hshat
      single := by
        intro m h1 i hi
        have := hw m h1 i hi
        fin_cases m <;> exact this }

end Mu4.Normal
