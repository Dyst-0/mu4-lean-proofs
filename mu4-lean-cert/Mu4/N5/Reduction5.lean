import Mu4.N5.Cover5
import Mu4.N5.Normal5
import Mu4.Normal.Patterns

/-!
# mu_4(5), N5: the normal form

`normalFormReduction5`: a 10-term decomposition valid on `A5` moves to the normal form `NF5` of one of the search's
cases `(P_k, S_j, multiplicities, single points)`, as `Mu4/Normal/Reduction.lean` for n = 6 (with C1(5), C2(5)).
The multiplicities are `n_m ≤ 2` with sum 7, the single points `w_m < 5` at the points with `n_m = 1`, 0 elsewhere.
-/

set_option autoImplicit false

namespace Mu4.N5
open Mu4 F4 Mu4.Lower Mu4.Search Mu4.Bridge Mu4.Normal

lemma indep_one_div5 {p q : GF5} (h : LinearIndependent F4 ![p, q]) :
    LinearIndependent F4 ![1, p⁻¹ * q] := by
  have hp : p ≠ 0 := by simpa using h.ne_zero 0
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  apply h
  have := congrArg (p * ·) hst
  simp only [mul_add, mul_smul_comm, mul_one, mul_zero] at this
  rwa [← mul_assoc, mul_inv_cancel₀ hp, one_mul] at this

lemma not_scalar_of_indep5 {z : GF5} (h : LinearIndependent F4 ![1, z]) : ∀ c : F4, z ≠ c • 1 := by
  intro c hc
  have := (LinearIndependent.pair_iff.mp h) c 1 (by rw [hc, one_smul, GF5_add_self'])
  exact one_ne_zero this.2

lemma mul_indep5 {x u v : GF5} (hx : x ≠ 0) (h : LinearIndependent F4 ![u, v]) :
    LinearIndependent F4 ![x * u, x * v] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  apply h
  have := congrArg (x⁻¹ * ·) hst
  simp only [mul_add, mul_smul_comm, mul_zero] at this
  rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hx, one_mul, one_mul] at this

lemma exists_pair_point5 {D : Decomp5 10} {H : Submodule F4 GF5} (hD : D.ValidOn H) (S : Step1Data5 D H) :
    ∃ m : Fin 5, (vanAt5 S m).card = 2 := by
  by_contra h
  push_neg at h
  have hle : ∀ m : Fin 5, (vanAt5 S m).card ≤ 1 := fun m => by
    have := vanAt_le_two5 hD S m; have := h m; omega
  have hsum := sum_vanAt5 S
  have : ∑ m : Fin 5, (vanAt5 S m).card ≤ ∑ _m : Fin 5, 1 := Finset.sum_le_sum fun m _ => hle m
  simp at this
  omega

/-! ### Step 1: the pencil -/

theorem toRep5 {D : Decomp5 10} (hD : D.ValidOn ⊤) (S : Step1Data5 D ⊤) :
    ∃ k < 3, ∃ D1 : Decomp5 10, D1.ValidOn ⊤ ∧
      ∃ S1 : Step1Data5 D1 ⊤, S1.p = decode5 (pList5.getD k (0, 0)).1 ∧
        S1.q = decode5 (pList5.getD k (0, 0)).2 := by
  obtain ⟨k, hk, s, hs, a, b, c, d, hab, heq⟩ :=
    cover1_5 (S.p⁻¹ * S.q) (not_scalar_of_indep5 (indep_one_div5 S.hind))
  obtain ⟨hp0k, hp4, hp1024⟩ := pList5_spec k hk
  set r := if s = 0 then 0 else 10 - s with hr
  set t := (pList5.getD k (0, 0)).2 with ht
  set S1 := S.frobPow r
  have hz1 : S1.p⁻¹ * S1.q = frob5^[r] (S.p⁻¹ * S.q) := by
    rw [S.frobPow_p, S.frobPow_q, frob5Iter_mul, frob5Iter_inv]
  set z1 := S1.p⁻¹ * S1.q with hz1def
  have heq' : (tau^[r] a • (1 : GF5) + tau^[r] b • z1) * decode5 t =
      tau^[r] c • (1 : GF5) + tau^[r] d • z1 := by
    have := congrArg (frob5^[r]) heq
    rw [frob5Iter_mul, frob5Iter_add, frob5Iter_add, frob5Iter_smul, frob5Iter_smul, frob5Iter_smul,
      frob5Iter_smul, frob5Iter_one, frob5Iter_cancel s hs] at this
    rw [hz1]; exact this
  have hS1p : S1.p ≠ 0 := by simpa using S1.hind.ne_zero 0
  have hind1 := indep_one_div5 S1.hind
  set v := tau^[r] a • (1 : GF5) + tau^[r] b • z1 with hvdef
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
  have h1mem : (1 : GF5) ∈ Submodule.span F4 {S2.p, S2.q} := by
    rw [Submodule.mem_span_pair]
    refine ⟨tau^[r] a, tau^[r] b, ?_⟩
    rw [hS2p, hS2q]
    calc tau^[r] a • v⁻¹ + tau^[r] b • (v⁻¹ * z1) = v⁻¹ * v := by
          rw [hvdef, mul_add, mul_smul_comm, mul_smul_comm, mul_one]
      _ = 1 := inv_mul_cancel₀ hv
  have htmem : decode5 t ∈ Submodule.span F4 {S2.p, S2.q} := by
    rw [Submodule.mem_span_pair]
    refine ⟨tau^[r] c, tau^[r] d, ?_⟩
    rw [hS2p, hS2q]
    calc tau^[r] c • v⁻¹ + tau^[r] d • (v⁻¹ * z1) = v⁻¹ * (v * decode5 t) := by
          rw [heq', mul_add, mul_smul_comm, mul_smul_comm, mul_one]
      _ = decode5 t := by rw [← mul_assoc, inv_mul_cancel₀ hv, one_mul]
  refine ⟨k, hk, (D.frobPow r).scaleX u, Decomp5.scaleX_validOn (Decomp5.frobPow_validOn hD r) hu,
    S2.rebase 1 (decode5 t) h1mem htmem (indep_one_decode5 hp4 hp1024), ?_, rfl⟩
  show (1 : GF5) = decode5 (pList5.getD k (0, 0)).1
  rw [hp0k, decode5_one]

/-! ### Step 2: the normalization `a_i|_P = l_m` -/

lemma line_of_vanish5 : ∀ m : Fin 5, ∀ α β : F4, ss m * α + tt m * β = 0 →
    ∃ c : F4, α = c * tt m ∧ β = c * ss m := by decide

theorem form_eq_lval5 (f : GF5 →ₗ[F4] F4) (p q : GF5) (m : Fin 5) (h : f (pt5 p q m) = 0) :
    ∃ c : F4, (∀ q' : Fin 5, f (pt5 p q q') = c * lval m.val q'.val) ∧
      (c = 0 → f p = 0 ∧ f q = 0) := by
  have hlin : ∀ q' : Fin 5, f (pt5 p q q') = ss q' * f p + tt q' * f q := by
    intro q'; simp [pt5, map_add, map_smul, smul_eq_mul]
  rw [hlin] at h
  obtain ⟨c, hp, hq⟩ := line_of_vanish5 m (f p) (f q) h
  refine ⟨c, fun q' => ?_, fun hc => ?_⟩
  · rw [hlin, lval_eq, hp, hq]
    ring
  · subst hc
    simp [hp, hq]

theorem normalize5 {H : Submodule F4 GF5} {D : Decomp5 10} (S : Step1Data5 D H) :
    ∃ c : Fin 10 → F4, (∀ i, c i ≠ 0) ∧
      ∀ i, i ∉ S.W → ∀ m : Fin 5, D.a i (pt5 S.p S.q m) = 0 → ∀ q : Fin 5,
        c i * D.a i (pt5 S.p S.q q) = lval m q := by
  classical
  have key : ∀ i, ∃ c : F4, c ≠ 0 ∧ (i ∉ S.W → ∀ m : Fin 5, D.a i (pt5 S.p S.q m) = 0 →
      ∀ q : Fin 5, c * D.a i (pt5 S.p S.q q) = lval m q) := by
    intro i
    by_cases hi : i ∈ S.W
    · exact ⟨1, one_ne_zero, fun h => absurd hi h⟩
    · obtain ⟨m0, hm0⟩ := vanish_point_exists5 S hi
      obtain ⟨c, hc, hc0⟩ := form_eq_lval5 (D.a i) S.p S.q m0 hm0
      have hcne : c ≠ 0 := by
        intro h
        have := hc0 h
        rcases alive_of_not_W5 S hi with h1 | h1
        · exact h1 this.1
        · exact h1 this.2
      refine ⟨c⁻¹, inv_ne_zero hcne, fun _ m hm q => ?_⟩
      have hmm : m = m0 := vanish_point_unique5 S hi hm hm0
      subst hmm
      rw [hc q, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  choose c hc0 hc using key
  exact ⟨c, hc0, fun i hi m hm q => hc i hi m hm q⟩

/-! ### The reduction -/

theorem normalFormReduction5 (D : Decomp5 10) (hD : D.ValidOn ⊤) :
    ∃ k < 3, ∃ j < 17, ∃ n0 n1 n2 n3 n4 : Fin 3, n0.val + n1.val + n2.val + n3.val + n4.val = 7 ∧
      ∃ w0 w1 w2 w3 w4 : Fin 5, (n0.val ≠ 1 → w0.val = 0) ∧ (n1.val ≠ 1 → w1.val = 0) ∧
        (n2.val ≠ 1 → w2.val = 0) ∧ (n3.val ≠ 1 → w3.val = 0) ∧ (n4.val ≠ 1 → w4.val = 0) ∧
        ∃ D' : Decomp5 10, D'.ValidOn ⊤ ∧
          Nonempty (NF5 (pList5.getD k (0, 0)).1 (pList5.getD k (0, 0)).2 (sList5.getD j (0, 0)).1
            (sList5.getD j (0, 0)).2 [n0.val, n1.val, n2.val, n3.val, n4.val]
            [w0.val, w1.val, w2.val, w3.val, w4.val] D' ⊤) := by
  classical
  obtain ⟨S⟩ := step1_5 hD
  obtain ⟨k, hk, D1, hD1, S1, hS1p, hS1q⟩ := toRep5 hD S
  obtain ⟨c, hc0, hc⟩ := normalize5 S1
  have hD2 := Decomp5.rescale_validOn hD1 hc0
  set D2 := D1.rescale c with hD2def
  set S2 := S1.rescale hc0
  -- a point with two vanishing terms, and the plane `Ŝ` there
  obtain ⟨m1, hm1⟩ := exists_pair_point5 hD2 S2
  obtain ⟨ia, ib, hab, hvan⟩ := Finset.card_eq_two.mp hm1
  have ha : ia ∈ vanAt5 S2 m1 := by rw [hvan]; simp
  have hb : ib ∈ vanAt5 S2 m1 := by rw [hvan]; simp
  obtain ⟨hspan, hgab⟩ := pencil_structure5 hD2 S2 hab ha hb
  have hx1 : pt5 S2.p S2.q m1 ≠ 0 := pt_ne_zero5 S2.hind m1
  set e1 := pt5 S2.p S2.q m1 * D2.g ia with he1
  set e2 := pt5 S2.p S2.q m1 * D2.g ib with he2
  have he : LinearIndependent F4 ![e1, e2] := mul_indep5 hx1 hgab
  have he1ne : e1 ≠ 0 := by simpa using he.ne_zero 0
  obtain ⟨j, hj, a, b, c', d, hab', heq⟩ :=
    cover2_5 (e1⁻¹ * e2) (not_scalar_of_indep5 (indep_one_div5 he))
  obtain ⟨hs0, hs4, hs1024⟩ := sList5_spec j hj
  set s1 := decode5 (sList5.getD j (0, 0)).2 with hs1
  set V := e1 * (a • (1 : GF5) + b • (e1⁻¹ * e2)) with hVdef
  have hV : V ≠ 0 := by
    apply mul_ne_zero he1ne
    intro h0
    have := (LinearIndependent.pair_iff.mp (indep_one_div5 he)) _ _ h0
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
    have := mul_indep5 hV (indep_one_decode5 hs4 hs1024)
    simpa using this
  have hspanV := span_pair_eq5 hVmem hVsmem he hVind
  clear_value V
  -- the transport `y ↦ V y`
  have hD3 := Decomp5.scaleY_validOn hD2 hV
  set D3 := D2.scaleY V with hD3def
  set S3 := S2.scaleY V
  have hshat : ∀ i, i ∉ S3.W → ∀ m : Fin 5, D3.a i (pt5 S3.p S3.q m) = 0 →
      pt5 S3.p S3.q m * D3.g i ∈ Submodule.span F4 {decode5 (sList5.getD j (0, 0)).1, s1} := by
    intro i hi m hm
    have h := hspan i hi m hm
    rw [← hspanV] at h
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h
    rw [hs0, decode5_one, Submodule.mem_span_pair]
    refine ⟨α, β, ?_⟩
    show α • (1 : GF5) + β • s1 = pt5 S2.p S2.q m * (V⁻¹ * D2.g i)
    rw [mul_left_comm, ← hαβ, mul_add, mul_smul_comm, mul_smul_comm, ← mul_assoc,
      inv_mul_cancel₀ hV, one_mul]
  -- the single points
  have hsingle : ∀ m : Fin 5, ∃ w : Fin 5, ((vanAt5 S3 m).card ≠ 1 → w.val = 0) ∧
      ((vanAt5 S3 m).card = 1 → ∀ i ∈ vanAt5 S3 m, D3.g i ∈ Submodule.span F4
        {pcA w.val • ((pt5 S3.p S3.q m)⁻¹ * decode5 (sList5.getD j (0, 0)).1) +
          pcB w.val • ((pt5 S3.p S3.q m)⁻¹ * s1)}) := by
    intro m
    by_cases h1 : (vanAt5 S3 m).card = 1
    · obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp h1
      have hi0m : i0 ∈ vanAt5 S3 m := by rw [hi0]; simp
      obtain ⟨hiW, hiz⟩ := (mem_vanAt5 S3).mp hi0m
      have hmem := hshat i0 hiW m hiz
      rw [hs0, decode5_one] at hmem
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
      obtain ⟨w, κ, hα, hβ⟩ := pc_cover α β
      refine ⟨w, fun h => absurd h1 h, fun _ i hi => ?_⟩
      rw [hi0, Finset.mem_singleton] at hi
      rw [hi, hs0, decode5_one, Submodule.mem_span_singleton]
      refine ⟨κ, ?_⟩
      have hxm : pt5 S3.p S3.q m ≠ 0 := pt_ne_zero5 S3.hind m
      have hg : D3.g i0 = (pt5 S3.p S3.q m)⁻¹ * (α • 1 + β • s1) := by
        rw [hαβ, ← mul_assoc, inv_mul_cancel₀ hxm, one_mul]
      rw [hg, hα, hβ, mul_add, mul_smul_comm, mul_smul_comm, smul_add, smul_smul, smul_smul]
    · exact ⟨0, fun _ => rfl, fun h => absurd h h1⟩
  choose wf hw0 hw using hsingle
  have hle : ∀ m : Fin 5, (vanAt5 S3 m).card < 3 := fun m => by
    have := vanAt_le_two5 hD3 S3 m; omega
  have hsum := sum_vanAt5 S3
  simp only [Fin.sum_univ_five] at hsum
  refine ⟨k, hk, j, hj, ⟨_, hle 0⟩, ⟨_, hle 1⟩, ⟨_, hle 2⟩, ⟨_, hle 3⟩, ⟨_, hle 4⟩, hsum,
    wf 0, wf 1, wf 2, wf 3, wf 4, hw0 0, hw0 1, hw0 2, hw0 3, hw0 4, D3, hD3, ⟨?_⟩⟩
  exact {
      S := S3
      hp := hS1p
      hq := hS1q
      norm := by
        intro i hi m hm q
        have hm' : D1.a i (pt5 S1.p S1.q m) = 0 := (rescale_a_eq_zero5 hc0 i (pt5 S1.p S1.q m)).mp hm
        have := hc i hi m hm' q
        show (D1.rescale c).a i (pt5 S1.p S1.q q) = lval m q
        simp only [Decomp5.rescale, LinearMap.smul_apply, smul_eq_mul]
        exact this
      mult_eq := by intro m; fin_cases m <;> rfl
      shat := hshat
      single := by
        intro m h1 i hi
        have := hw m h1 i hi
        fin_cases m <;> exact this }

end Mu4.N5
