# mu_4(6) = 14: the proof as precise lemmas

Released 2026-11-07 with the Lean archive (see ../README.md). This is the publication-standard statement of the proof; the
exploration notes it cites (runs/hyper/README.md, section 1) are not part of this release. Each step is a lemma with its hypotheses. Each lemma has a status: the Lean name that proves it, or a
finite check with its command, or "hand", with the reason. The Lean project is lean/ (see lean/README.md).

## Setting

- F = GF(4) = {0, 1, w, w^2}, with w^2 = w + 1.
- A = GF(4^6) = F[t]/(t^6 + t^2 + t + w), basis 1, t, ..., t^5 (Lean: `Mu4.GF`, a Mathlib `Field`).
- T is the multiplication map A x A -> A, an F-bilinear map.
- For a subspace U of A, a *decomposition of length r valid on U* is a family (a_i, b_i, g_i), i < r, with a_i, b_i
  linear forms on A and g_i in A, such that x y = sum_i a_i(x) b_i(y) g_i for all x in U and y in A
  (Lean: `Mu4.Decomp`, `Decomp.ValidOn`).
- alive(V) = {i : a_i is not identically 0 on V}.
- M_x denotes y -> x y. For x != 0, M_x is invertible (A is a field).
- Standard points of a pencil P = span(p0, p1): x_0 = p0, x_1 = p1, x_2 = p0 + p1, x_3 = w p0 + p1,
  x_4 = w^2 p0 + p1.
- l_m(s p0 + t p1) = tt_m s + ss_m t, with (ss_m, tt_m) = (1,0), (0,1), (1,1), (w,1), (w^2,1), is the form on P
  vanishing at x_m.

## Main theorem

**Theorem.** For every field K with 4 elements and every field extension L of K with [L : K] = 6, the bilinear
rank of the multiplication map L x L -> L over K is 14.
Lean: `Mu4.Final.mu4_6_general` (no hypotheses), for any such K, L, from the concrete case `Mu4.Final.mu4_6`
(K = `Mu4.F4`, L = `Mu4.GF`) and the transfer `Mu4.bilinRank_transfer` with `Mu4.exists_equiv_GF` (EXACT, standard
axioms only). Status: EXACT (11-05 evening, second agent). The two steps that were hypotheses until then,
`NormalFormReduction` (L6, C1, C2) and `BridgeMath` (L7-L10), are proved (`Mu4.Final.normalFormReduction`,
`Mu4.Final.bridgeMath`). The conditional forms `mu4_6_of`, `mu4_6_general_of` are kept.

**Upper bound.** An explicit symmetric 14-term scheme:
- CRT at t = 0, 1, w, w^2;
- the irreducible quadratics t^2 + t + w, t^2 + t + w^2 and t^2 + wt + 1, with Karatsuba;
- infinity;
- then reduction mod t^6 + t^2 + t + w.

It was built from scratch in lean/tools/gen_crt14.py. Status: EXACT, `Mu4.upper_bound`; all 216 coefficient
equations are checked by `decide`.

## Lower bound

**L0 (substitution).**
- Hypothesis: T has a decomposition of length 13 valid on A.
- Conclusion: there are a hyperplane H (dim 5) and a decomposition of length 12 valid on H.
- Proof: some a_j != 0, since otherwise 1 * 1 = 0. Take H = ker a_j and drop term j.
- No orbit argument is needed: L4-L10 below hold for every hyperplane.
- Status: EXACT, Lean `Mu4.Lower.substitution` (used in `Mu4.rank_GF_of`).

**L1 (point bound).**
- Hypothesis: D is valid on U, and x in U is nonzero.
- Conclusion: #{i : a_i(x) != 0} >= 6.
- If equality holds, then {g_i : a_i(x) != 0} is a basis of A, and y -> (b_i(y))_{a_i(x) != 0} is a bijection
  A -> F^6.
- Proof: M_x is onto and its image lies in span{g_i : a_i(x) != 0}. If b_i(y) = 0 for those i, then x y = 0 and
  so y = 0.
- Status: EXACT, Lean `Mu4.Lower.point_bound`, `point_dual`, `point_basis`.

**L2 (pencil count).**
- Hypothesis: D is valid on U, and P = span(p0, p1) <= U has dim 2.
- Conclusion: |alive(P)| >= 8.
- If |alive(P)| <= 8, then:
  - |alive(P)| = 8;
  - each alive form vanishes at exactly one standard point x_m;
  - n_m := #{i alive : a_i(x_m) = 0} <= 2, and the n_m sum to 8.
- Proof: a nonzero form on P vanishes at exactly one of the 5 points (finite check over F^2). Summing L1 over the
  5 points gives 4 |alive| >= 30.
- Status: EXACT, Lean `Mu4.Lower.pencil_count`, `pencil_exact`.

**L3 (plane bound).**
- Hypothesis: D is valid on U, and V <= U has dim 3.
- Conclusion: |alive(V)| >= 9.
- Proof: pick i in alive(V). The subspace V cap ker a_i contains a 2-dim P with alive(P) contained in
  alive(V) \ {i}; then apply L2.
- (This is the Griesmer bound [9,3,6]_4 of the README, by substitution.)
- Status: EXACT, Lean `Mu4.Lower.plane_bound`.

**G1 (geometry, finite).**
- Statement: among any 12 vectors of F^5 that span F^5, some 4 with distinct indices are linearly dependent.
- Reduction: if every 4 were independent, choose 5 independent ones and map them to e_1..e_5; normalize the other 7
  (first nonzero coordinate 1). They are distinct, and every 4 of the 12 stay independent. So it suffices that no
  sorted 7-list of normalized vectors extends the frame with every 4 independent.
- That is checked by a depth-first search with a forbidden-set pruning that is exact: a point is forbidden iff it
  lies in the span of 3 chosen points.
- Status: EXACT via `native_decide`. Lean `Mu4.Final.geometry : Geometry`, from:
  - `Mu4.Lower.geometry_of_check : geomCheck = true → Geometry` (standard axioms only): the reduction to a frame,
    the normalization, and the soundness of the search (`Mu4.Lower.noExt_eq_false`, a marked code always lies in
    the span of 3 chosen points);
  - `Mu4.Check.geomCheck_ok : geomCheck 7 = true` (`native_decide`, 213 s), the search of lean/Mu4Geom.lean,
    which mirrors geom_main.c.
- Independent checks: geom.c, geom_main.c and CP-SAT (geom_cpsat.py) all give max 11 (audit/controls_1105).

**L4 (step 1).**
- Hypothesis: D of length 12 is valid on H, dim H = 5.
- Conclusion: there are 4 indices W (the "W-forms") with:
  - P := {x in H : a_i(x) = 0 for i in W} of dim exactly 2;
  - alive(P) = the other 8 indices.
- Proof:
  1. The forms span H^*, since otherwise some x != 0 kills all of them, contradicting L1.
  2. G1 gives 4 forms that are dependent on H. So x -> (a_i(x))_{i in W} has rank <= 3, and its kernel P has
     dim >= 2.
  3. dim P >= 3 would leave at most 8 alive terms on a 3-dim subspace, contradicting L3.
  4. Then L2 forces alive(P) to be all 8 others.
- Status: EXACT, Lean `Mu4.Lower.step1` with `Mu4.Final.geometry`.

**L5 (pencil structure lemma).**
- Hypotheses: as in L4, and x_1 is a standard point of P with n_{x_1} = 2.
- Conclusion: let S^1 = span{g_i : i alive, a_i(x_1) = 0} and Ŝ = x_1 S^1. Then:
  - dim Ŝ = 2;
  - g_i lies in x_{m(i)}^{-1} Ŝ for every alive i, where x_{m(i)} is the point where a_i vanishes.
- Proof (README step 3):
  1. At x_1, the 6 terms off the pair are alive. By L1, their g's form a basis.
  2. For i0 off the pair, choose y0 with b_i(y0) = delta_{i,i0} (L1, bijection). Then x_1 y0 = a_i0(x_1) g_i0.
  3. With n = m(i0), x_n y0 is a combination of the pair's g's. So (x_n / x_1) g_i0 is in S^1.
  4. If dim S^1 = 1, two g's at a second pair point would be proportional, contradicting the basis in 1.
- Status: EXACT, Lean `Mu4.Lower.pencil_structure`.

**L6 (normal form).**
- The following substitutions transform a decomposition valid on H into one of the same length valid on another
  hyperplane, or on the same one:
  - x -> u x for u != 0;
  - x -> sigma(x), where sigma(z) = z^2 is the Frobenius of A over GF(2) (F-semilinear);
  - y -> v y for v != 0;
  - (a_i, b_i) -> (c a_i, c^{-1} b_i).
- With C1 and C2, one may therefore assume that:
  - P = P_k for one of the 10 representatives;
  - Ŝ = S_j for one of the 69 representatives;
  - a_i|_P = l_{m(i)} for every alive i;
  - the multiplicities and single points are one of the 255 patterns.
- Status: EXACT, Lean `Mu4.Normal.normalFormReduction_holds` (= `Mu4.Final.normalFormReduction`), axioms
  [propext, Classical.choice, Quot.sound]. Steps (lean/Mu4/Normal/):
  - the four substitutions with their step-1 data (Transport.lean, Frobenius.lean: `Decomp.scaleX_validOn`,
    `scaleY_validOn`, `rescale_validOn`, `frobT_validOn`, iterates `frobPow`, `finrank_frobImagePow`,
    `finrank_comap_mulLeft`), and `Step1Data.rebase` (another basis of the same pencil);
  - `toRep`: write P = p span(1, z) with z = p^-1 q not in F; C1 gives k, s, (a, b) != 0, c, d with
    (a + b z) sigma^s(p1_k) = c + d z; then sigma^r (r = 12 - s) and x -> u x with u = sigma^r(p) (a' + b' sigma^r(z))
    bring the pencil to P_k = span(1, p1_k), with the basis 1, p1_k;
  - `normalize`: the rescaling (c_i a_i, c_i^-1 b_i) with c_i from `form_eq_lval` gives a_i = l_m on the five points;
  - Ŝ = span(x_m1 g_a, x_m1 g_b) at a pair point (L5); C2 gives S_j and V with Ŝ = V S_j; y -> V y makes
    x_m g_i lie in span(1, s1_j);
  - the single points from `pc_cover`, and the pattern membership `mem_patterns` (kernel `decide`).

**C1, C2 (coverage, finite).**
- C1: every 2-dim subspace of A is u sigma^s(P_k) for some u != 0, s < 12 and k < 10 (runs/hyper/plist.txt).
- C2: every 2-dim subspace of A is v S_j for some v != 0 and j < 69 (runs/hyper/Sclasses6.txt).
- Status: EXACT, kernel. Formulation used in Lean: every 2-dim subspace is x span(1, z) with z not in F, so it
  suffices that every code z in 4..4095 has a witness. C1: k < 10, s < 12, (a, b) != 0, c, d with
  (a + b z) sigma^s(p1_k) = c + d z; C2: j < 69, (a, b) != 0, c, d with (a + b z) s1_j = c + d z. The witnesses are
  tables (lean/Mu4/Normal/CoverData.lean, from lean/tools/gen_cover.py); the kernel checks all 4092 entries of each
  (`decide +kernel` in chunks of 1023, Mu4/Normal/CoverCheck1.lean, CoverCheck2.lean, about 20 s and 1.4 GB each),
  and `cover1`, `cover2` (Cover.lean) state the result in the field. Also computed earlier by porbits.py and
  main_check/coverage_ps.py (both: 93,093 of 93,093 covered).
- Independent checks: porbits.py, main_check/coverage_ps.py (audit/controls_1105/coverage_ps.log).

**L7 (blocks).**
- Hypothesis: normal form.
- Conclusion 1: for x in P, M_x = sum_m l_m(x) Block_m with Block_m = sum_{m(i)=m} g_i b_i^T.
- Conclusion 2, for m0 = the first point with n_m = 2:
  - the off-m0 spaces W'_m form a direct sum: W_m = x_m^{-1} Ŝ at pairs, and the line of the single's g at
    singles. Their basis Gam has a dual basis rho;
  - Block_m (m != m0) has forms f_j(y) = rho_j(x_m0 y) / l_m(x_m0);
  - Block_m0 y = (x_q2 y - sum_{m != m0} l_m(x_q2) Block_m y) / l_m0(x_q2), and it lies in W_m0;
  - Block_m0 has two independent forms fa, fb.
- So `setupCase` returns `valid` with exactly these blocks (README step 3, last paragraph).
- Status: EXACT. L7a `Mu4.Bridge.mul_pt_eq`; the rest in lean/Mu4/Bridge/Blocks.lean:
  - `offBlock_eq`: the forms of an off block, f_j(y) = rho_j(x_m0 y) / l_m(x_m0), give the true block;
  - `residual_eq`: the residual at the second point is l_m0(x_q2) Block_m0;
  - `m0Block_eq`: fa(y) ga + fb(y) gb = Block_m0(y);
  - `setupCase_ne_invalid` (axioms [propext, Classical.choice, Quot.sound]): `setupCase` never returns `invalid`
    for a case of a decomposition in normal form.
- Note: `setupCase` returns `invalid` in three situations, each excluded by L7 under the normal form: the off-m0
  basis Gam is dependent; the residual at the second point is not in W_m0; fa, fb are dependent. These dismiss
  56,250 of the 175,950 cases (MEASURED, audit/lean_search_1105): 4,375 for each of P_0..P_6 and P_8, 3,655 for
  P_7, and all 17,595 for P_9. P_9 = span(1, 1960) is the subfield GF(16) (MEASURED, audit/scratch/p9_subfield.py:
  x^16 = x on all 16 elements; on no other representative). There L5 puts every alive g_i in GF(16) Ŝ, of
  dimension at most 4, against the basis of L1 (ARGUMENT, now superseded).
  Formalized 11-05 evening (EXACT, `setupCase_ne_invalid`), uniformly for all ten P, with no special case for P_9:
  1. the dependency step: under the normal form the six off-m0 vectors span A (they span the W'_m, which contain the
     six g_i alive at x_m0, a basis by L1), so `dependency` finds nothing (`dependency_none`);
  2. the residual step: the residual at e_t is l_m0(x_q2) Block_m0(e_t), which lies in W_m0 = span(ga, gb), so `inW`
     finds it (`residualAt_isSome`);
  3. the forms fa, fb are independent: fa(y) ga + fb(y) gb = b_k(y) g_k + b_k'(y) g_k', and at a second pair point
     the b's of the two terms at m0 separate points (L1), while g_k, g_k' are independent (`dependent2_false`).
  For P_9 this means that no decomposition in normal form has P = P_9; the first step is where it fails.

**L8 (directions).**
- Hypothesis: normal form.
- Conclusion: for x in H, M_x = sum_m G_m(x) Block_m + E_x, where:
  - G_m(x) in End(W'_m) has the g_i (m(i) = m) as eigenvectors, with eigenvalues a_i(x). It is diagonalizable,
    linear in x, equal to l_m(x) on P, and G_m(x), G_m(x') commute;
  - E_x = sum_{i in W} a_i(x) g_i b_i^T, so rank E_x <= #{i in W : a_i(x) != 0}.
- Status: EXACT, `Mu4.Bridge.VCtx.ops_exist` (lean/Mu4/Bridge/Vertex.lean): for every family of eigenvalues
  lambda, operators of all blocks (`conjCode` with the two g's as eigenvectors at a pair, the scalar at a single)
  with sum_blocks G_m Block_m(y) = sum_{i alive} lambda_i b_i(y) g_i, candidates of the search, diagonalizable,
  and commuting for any two families. With lambda_i = a_i(x) for a direction element x in H, the operator E of
  the search's solution is E_x(y) = sum_{i in W} a_i(x) b_i(y) g_i (`hE` in `triFree_false_valid`).
  The three finite facts on `conjCode` (diagonalizable, eigenvectors, commuting; Mu4/Bridge/Mat2.lean) are kernel
  checks since 11-06 (Mu4/Bridge/Mat2Check.lean: Bool checks over the list of GF(4), 4,096 + 4,096 + 65,536
  cases); they were `native_decide` before.

**L9 (triangle).**
- Hypothesis: 4 forms on H whose common kernel in H is exactly P (codim 3).
- Conclusion: there are 3 of them, w_a, w_b, w_c, and d_1, d_2, d_3 in H, independent modulo P, with:
  - w_b(d_1) = w_c(d_1) = 0;
  - w_a(d_2) = w_c(d_2) = 0;
  - w_a(d_3) = w_b(d_3) = 0.
- For the fourth form w_e, either w_e(d_k) = 0 for some k (a vertex where 3 W-forms vanish: rank <= 1), or each
  edge d_i d_j contains an interior point d_i + lam d_j, lam != 0, where w_e also vanishes (rank <= 2).
- This replaces the README's case list:
  - it also covers a W-form that is identically zero on H, a case the README did not list;
  - the final test becomes "a vertex of rank <= 1, or an interior point of rank <= 2 on each edge". This is
    weaker than the README's plane-profile test, and so is enough.
- Status: EXACT. The abstract form `Mu4.Bridge.triangle_abstract` (lean/Mu4/Bridge/Triangle.lean, first in
  lean/wip/Triangle.lean), applied to the four W-forms on H (`finrank_range_wforms`: rank 3, kernel P) in
  `triFree_false_valid`: the vertices are decomposed as pi + sum gamma_k t_k (`decompose`), normalized
  (`dir_of_ne_zero`), and their directions are independent (`hind`).

**L10 (search completeness).**
- Hypothesis: normal form, for a case (k, j, pattern).
- Conclusion: the search `Mu4.Search.runCase` for that case counts a passing triangle (pass >= 1).
- Proof sketch:
  1. By L8 and L9, the three vertices (normalized c, G(d_k)) are solutions: rank E <= 2, every G diagonalizable.
  2. Each solution is found. rank E <= 2 gives a 2-dim K in Y1 cap ker E (dimension count), and K is one of the
     357 reduced echelon pairs. Then, on K, E y = 0 splits block by block into G_m B_m = R_m(c), so G_m is in the
     lookup table built from all 124 diagonalizable 2x2 matrices. G_m0 is in the 16 x 16 enumeration.
  3. Every rank test uses `rankC`, a lower bound for the true rank, so true rank <= r implies a pass.
  4. The three vertices are pairwise edges (common W-form zero on each line), have independent directions, and pass
     the final test by L9.
- Status: EXACT. `Mu4.Bridge.sol_complete` (every solution of a valid case is in `allSols`; uses `rref_cover`,
  a kernel check since 11-06: a witness table of all 65,536 pairs of 8-bit codes, generated by
  lean/tools/gen_rref4.py and checked by the kernel in 16 chunks, Mu4/Bridge/RrefCheck1..4.lean, with its
  meaning in Mu4/Bridge/Rref.lean, `rref_cover_spec`; it was `native_decide` before; and `rankC` as a proved
  lower bound), and `Mu4.Bridge.triFree_false_valid`: the three vertex
  solutions are in `allSols`, pairwise edges (distinct directions, commuting operators by L8, rank <= 3 on the
  whole line), with independent directions, and pass the final test (a vertex of rank <= 1, or an interior point
  of rank <= 2 on each edge), so `triFree` is false (`triFree_false_of_three`). With `setupCase_ne_invalid`
  this is `Mu4.Bridge.bridgeMath_holds` (= `Mu4.Final.bridgeMath`). Its axioms added Lean.ofReduceBool and
  Lean.trustCompiler only through the native_decide facts `rref_cover` and Mat2.lean's `conjCode_*`; since both
  are kernel checks (11-06), it has the standard axioms only.

**C3 (the search, finite).**
- Statement: for all 690 pairs (P_k, S_j) and all 255 patterns, `runCase` reports pass = 0 and no error.
- Status: EXACT via `native_decide`, Lean `Mu4.Check.searchCheck` (modules Mu4/Check/P0..P9, built 11-05 in 2.9
  core-hours, MEASURED). It
  also certifies the case invariants (`wfCheck`).
- Independent implementations with the same counters: hp2.c, hp3.py, main_check/fullcheck.c, and the Lean
  program itself run as an executable (audit/lean_search_1105).

**Conclusion.**
- L4 to L10 with C1 to C3: no hyperplane H has a 12-term decomposition, so R(T|_H) >= 13.
- With L0, mu_4(6) >= 14; with the upper bound, mu_4(6) = 14.

## Hand steps

None since 11-05 evening. The first agent's Lean certificate took two hypotheses, `NormalFormReduction` (L6 with
C1, C2) and `BridgeMath` (L7-L9 with L10's last step). The second agent proved both
(`Mu4.Normal.normalFormReduction_holds`, `Mu4.Bridge.bridgeMath_holds`), and the main theorems
`Mu4.Final.mu4_6` and `Mu4.Final.mu4_6_general` have no hypotheses.

How to read the earlier conditional theorem (ARGUMENT, kept for the record): each hypothesis had a 12-term
decomposition valid on a hyperplane among its premises, so it held trivially if mu_4(6) = 14 was true. The
conditional theorem was therefore no evidence for the claim by itself.

The trust base is now:
- the Lean kernel and Mathlib;
- the Lean compiler, for the `native_decide` checks: C3 (the search) and G1's search (for mu_4(5): C3(5)).
  C1, C2, the pattern list, `rref_cover` and the 2x2 facts of Mu4/Bridge/Mat2.lean are kernel checks (the last
  two since 11-06; they were `native_decide` before).

The README's statements that are *not* used by the Lean proof:
- the k = 3 / k = 4 classifications;
- Wang's certificates;
- the orbit completeness of hyperplanes (newtech/orbit_completeness.py);
- the plane-profile (0,0,4,8,9) observation.

# mu_4(5) = 11: the proof as precise lemmas (second agent, 11-05 evening)

Written before its Lean proof, as asked (user via the coordinator, 11-05). Lean statuses added after the proof
(11-05 evening): the files are lean/Mu4/N5/*.lean and lean/Mu4Comp5/*.lean. It is the argument of runs/hyper/README.md
(section 3, "Bonus: mu_4(5)") and of the runs `hp2_5` (hp2.c with `-DN=5 '-DMOD5=2,1,0,0,0'`) and `mu45.py`
(runs/hyper/ctrl_logs/n5_hp2.log, n5_mu45.log). Each lemma gets its Lean name or check when it is proved.

## Setting (n = 5)

- F = GF(4) as above; A5 = F[t]/(t^5 + t + w), basis 1, t, ..., t^4 (hp2.c's MODLOW = {2,1,0,0,0}: t^5 = w + t).
- T5 is the multiplication map A5 x A5 -> A5. A decomposition of length r *valid on A5*: (a_i, b_i, g_i), i < r, with
  x y = sum_i a_i(x) b_i(y) g_i for all x, y in A5. (No hyperplane: for n = 5 the argument works on A5 itself.)
- alive(V), M_x, the standard points x_0..x_4 of a pencil and the forms l_m as in the n = 6 setting.

## Theorem 5

For every field K with 4 elements and every extension L of K with [L : K] = 5, the bilinear rank of the multiplication
L x L -> L over K is 11.

**U5 (upper bound).** An explicit symmetric 11-term scheme: CRT for the product of two polynomials of degree <= 4 at
t = 0, 1, w, w^2 and infinity (one product each) and the irreducible quadratics t^2 + t + w, t^2 + t + w^2 (Karatsuba,
three products each); the moduli have total degree 8, so with infinity they fix the 9 coefficients of the product;
then reduction mod t^5 + t + w. Check: all 125 coefficient equations by `decide`.
Status: EXACT, `Mu4.N5.upper5_bound` (Mu4/N5/Upper5.lean; scheme from lean/tools/gen_crt11.py).

## Lower bound: no 10-term decomposition valid on A5

**N1 (point bound).** D valid on A5, x != 0: #{i : a_i(x) != 0} >= 5. If equality holds, {g_i : a_i(x) != 0} is a basis
of A5 and y -> (b_i(y))_{a_i(x) != 0} is a bijection A5 -> F^5. (Proof of L1, with dim A5 = 5.)
Status: EXACT, `Mu4.N5.point_bound5`, `point_dual5`, `point_basis5` (Mu4/N5/Lower5.lean).

**N2 (pencil count).** P = span(p, q) of dim 2: |alive(P)| >= 7 (4 |alive(P)| = sum over the five points >= 25). If
|alive(P)| = 7: every alive form vanishes at exactly one standard point, n_m <= 2 (at x_m at least 5 of the 7 are
alive), and sum_m n_m = 7.
Status: EXACT, `Mu4.N5.pencil_count5`, `pencil_exact5`, `vanAt_le_two5`, `sum_vanAt5`.

**N3 (three forms).** D of length 10 valid on A5. The forms a_i span A5^* (else some x != 0 kills all, against N1).
Choose three independent ones, indices W, and let P be their common kernel (dim 2). Then alive(P) is exactly the other
seven indices (>= 7 by N2, and the W-forms vanish on P). So the multiplicities are (2,2,2,1,0) or (2,2,1,1,1) up to
order (n_m <= 2, sum 7).
Status: EXACT, `Mu4.N5.step1_5` (Mu4/N5/Step15.lean: five independent forms among the ten by
`exists_linearIndependent'`, three of them, the joint map onto F^3, its kernel of dim 2).

**N4 (pencil structure).** As L5: at a standard point x_m1 with n_m1 = 2 (terms a, b), Ŝ = span(x_m1 g_a, x_m1 g_b)
has dim 2 and x_m(i) g_i is in Ŝ for every alive i. (At x_m1 the 5 alive terms off the pair have a basis of g's and
separating b's by N1; the proof of L5 goes through word for word.)
Status: EXACT, `Mu4.N5.pencil_structure5` (Mu4/N5/Pencil5.lean).

**N5 (normal form).** As L6, with the substitutions x -> u x, x -> sigma(x) (sigma(z) = z^2, of order 10 on A5),
y -> v y and (a_i, b_i) -> (c a_i, c^-1 b_i); they keep a decomposition valid on A5. With C1(5) and C2(5) one may
assume P = P_k for one of 3 representatives (runs/hyper/plist5.txt: span(1,4), span(1,20), span(1,28)), Ŝ = S_j for
one of 17 representatives (runs/hyper/ctrl5/Sclasses5.txt), a_i|_P = l_m(i), and multiplicities and single points
one of the 1,350 patterns (20 x 5 of shape (2,2,2,1,0), 10 x 125 of shape (2,2,1,1,1)).
Status: EXACT, `Mu4.N5.normalFormReduction5` (Mu4/N5/Reduction5.lean; transports in Transport5.lean, sigma^10 = id).
The patterns are given as n_m < 3 with sum 7 and w_m < 5 (0 off the singles); the search check enumerates exactly
these (`checkAll5`), so no list membership is needed.

**C1(5), C2(5) (coverage, finite).** Every 2-dim subspace of A5 (5,797 of them) is u sigma^s(P_k), and v S_j. As for
n = 6, it suffices that each code z in 4..1023 (z not in F) has a witness: C1(5) k < 3, s < 10, (a, b) != 0, c, d
with (a + b z) sigma^s(p1_k) = c + d z; C2(5) j < 17, (a, b) != 0, c, d with (a + b z) s1_j = c + d z.
Status: EXACT, kernel: tables from lean/tools/gen_cover5.py (Mu4/N5/CoverData5.lean), all 1020 entries checked by
`decide +kernel` (CoverCheck5.lean, about 18 s, 1.1 GB), `cover1_5`, `cover2_5` (Cover5.lean).

**N6 (blocks).** As L7: under the normal form the search's set-up of the case (the five off-m0 vectors, their dual
rows, the residual at the second point, the forms fa, fb of the block at m0) succeeds and gives the true blocks; it
never dismisses the case as invalid.
Status: EXACT, `Mu4.N5.setupCase_ne_invalid5` (Mu4/N5/Blocks5.lean), as L7 (five off-m0 vectors).

**N7 (operators).** As L8: for x in A5, M_x = sum_m G_m(x) Block_m + E_x with E_x(y) = sum_{i in W} a_i(x) b_i(y) g_i,
G_m(x) with the g_i as eigenvectors and eigenvalues a_i(x); operators of one block commute for different x.
Status: EXACT, `Mu4.N5.VCtx5.ops_exist` (Mu4/N5/Vertex5.lean).

**N8 (triple).** The three W-forms induce a basis of (A5/P)^*. Let d_1, d_2, d_3 in A5 be dual to them
(a_{w_k}(d_j) = delta_kj); they are independent modulo P. At d_j only the W-term j is alive, so rank E_{d_j} <= 1.
The three solutions (normalized directions of d_j in A5/P, operators of N7) have pairwise commuting pair operators,
pairwise distinct directions, and independent directions.
Status: EXACT, `Mu4.N5.wforms_dual`, `tripleFree5_false_valid`, `bridge5_holds` (Mu4/N5/Triple5.lean).

**N9 (search completeness).** For a valid case, every solution (a normalized direction of A5/P, one diagonalizable
operator per block, rank E <= 1) is listed by the search. (As L10: rank E <= 1 gives a 2-dim K in Y cap ker E, where
Y = ker fa cap ker fb has dim 3, and K is one of the 21 reduced echelon pairs of F^3; the operators of the off blocks
are found in the same lookup tables; the operator at m0 by the 16 x 16 enumeration.)
Status: EXACT, `Mu4.N5.sol_complete5` (Mu4/N5/Complete5.lean), with `rref_cover3` (Keys5.lean: a witness table of
the 4096 pairs of 6-bit codes checked by the kernel in RrefCheck5.lean, 38 s, 1.4 GB; a first direct `decide` on
the search over all 21 pairs reached 8.7 GB and was stopped by PID).

**C3(5) (the search, finite).** For all 3 x 17 pairs (P_k, S_j) and all 1,350 patterns: the set-up of the case does
not fail, and no three solutions of rank <= 1 have pairwise commuting pair operators and independent directions.
(Runs: hp2_5 finds 16,142 solutions of rank 1 and none of rank 0 or 2 in 68,850 cases, 17,010 invalid; mu45.py
finds 2,560 commuting pairs at distinct directions and 0 independent commuting triples.)
Status: EXACT via `native_decide` (new use, labelled: the kernel cannot run the search), `Mu4.N5.searchCheck5`
(Mu4/N5/Check5.lean) on `checkAll5` of Mu4Comp5/Search.lean (precompiled library Mu4Comp5). Second, independent
implementation: the same Lean search run as an executable (`mu4search5`) reproduces hp2_5's and mu45.py's counters
exactly (audit/n5_1105b/lean_search5.log).

**Conclusion.** N3-N9 with C1(5)-C3(5): no 10-term decomposition valid on A5, so mu_4(5) >= 11; with U5,
mu_4(5) = 11. Transfer to any (K, L) with |K| = 4 and [L : K] = 5 as for n = 6.
Status: EXACT, `Mu4.N5.noTen`, `Mu4.N5.mu4_5`, `Mu4.N5.mu4_5_general` (Mu4/N5/Final5.lean; `exists_equiv_GF5`, and
`bilinRank_transfer` of Mu4/Transfer.lean).

Differences from n = 6: no substitution step and no hyperplane (the decomposition is valid on A5), no G1 (any three
independent forms work), and no edges with rank <= 3 on lines (all three vertices have rank <= 1).
