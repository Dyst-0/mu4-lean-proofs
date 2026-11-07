# Lean 4 certificate: mu_4(6) = 14 and mu_4(5) = 11

SECRET until 2027-01-20 (local only; see ../README.md).

Lean 4 v4.28.0 with Mathlib v4.28.0 (8f9d9cff). The proof as precise lemmas is in ../audit/PROOF.md, and the
decision log is in ../audit/LOG.md.

## Statement

```lean
-- Mu4/Rank.lean
def HasDecomp (f : U →ₗ[K] V →ₗ[K] W) (r : ℕ) : Prop :=
  ∃ (a : Fin r → U →ₗ[K] K) (b : Fin r → V →ₗ[K] K) (c : Fin r → W),
    ∀ u v, f u v = ∑ i, (a i u * b i v) • c i
noncomputable def bilinRank (f : U →ₗ[K] V →ₗ[K] W) : ℕ := sInf {r | HasDecomp K f r}

-- Mu4/Final.lean
theorem Mu4.Final.mu4_6_general
    (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    (hK : Fintype.card K = 4) (hL : Module.finrank K L = 6) :
    bilinRank K (LinearMap.mul K L) = 14

theorem Mu4.Final.mu4_6 : bilinRank F4 (LinearMap.mul F4 GF) = 14
```

`LinearMap.mul K L` is Mathlib's multiplication map of the `K`-algebra `L`. The concrete fields:
- `F4` is GF(4), a Mathlib `Field` whose axioms are checked by `decide`.
- `GF` is GF(4^6) = GF(4)[t]/(t^6+t^2+t+w), a Mathlib `Field` with `Algebra F4 GF` and `finrank F4 GF = 6`.
  The ring axioms come from structure-tensor identities checked by `decide`. Inverses are checked by the kernel
  on all 4095 nonzero elements.

`mu4_6_general` follows from `mu4_6` by the transfer of Mu4/Transfer.lean: every pair `K ⊆ L` with
`|K| = 4` and `[L : K] = 6` is isomorphic to `(F4, GF)`, and the rank does not change along such an isomorphism.

## mu_4(5) = 11

```lean
-- Mu4/N5/Final5.lean
theorem Mu4.N5.mu4_5_general
    (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    (hK : Fintype.card K = 4) (hL : Module.finrank K L = 5) :
    bilinRank K (LinearMap.mul K L) = 11

theorem Mu4.N5.mu4_5 : bilinRank F4 (LinearMap.mul F4 GF5) = 11
```

`GF5` is GF(4^5) = GF(4)[t]/(t^5 + t + w) (the field of `hp2_5`), a Mathlib `Field` (Mu4/N5/GF5, Code5, GFField5,
Field5). The proof (audit/PROOF.md, "mu_4(5) = 11", lemmas N1-N9, C1(5)-C3(5), U5) follows the n = 6 certificate:
- upper bound: an 11-term CRT scheme (Mu4/N5/Upper5.lean, `decide`);
- no 10-term decomposition valid on GF(4^5) (`Mu4.N5.noTen`): three independent forms give a pencil `P` with seven
  alive terms (Lower5, Step15, Pencil5); the normal form (Transport5, Cover5 with kernel-checked C1(5), C2(5),
  Reduction5); the blocks and `setupCase5` never invalid (Normal5, Blocks5); the operators (Vertex5); the three
  vertices of rank <= 1, pairwise adjacent with independent directions (Triple5); the completeness of the search
  (BCodes5 ... Complete5, with the echelon-pair cover `rref_cover3` checked by the kernel in RrefCheck5); the search
  check C3(5) (`Mu4.N5.searchCheck5`, Mu4/N5/Check5.lean, `native_decide` on the precompiled library Mu4Comp5).
- the transfer to any (K, L) with |K| = 4 and [L : K] = 5 (`exists_equiv_GF5` and `bilinRank_transfer`).
The search Mu4Comp5 is a second, independent implementation of hp2_5 + mu45.py: run as the executable
`mu4search5`, it reproduces their counters exactly (cases 22,950, invalid 5,670, rank-1 solutions 5,940 / 4,894 /
5,308, commuting pairs 1,280 / 512 / 768 per P; 0 independent commuting triples).

## Status

Unconditional since 11-05 evening (second proof agent). The first agent's certificate proved the theorem from two
hypotheses, `NormalFormReduction` (L6, C1, C2) and `BridgeMath` (L7-L10); both are now proved:

| Former hypothesis | Proved as | File | Axioms |
| --- | --- | --- | --- |
| `NormalFormReduction` (L6, C1, C2) | `Mu4.Final.normalFormReduction` = `Mu4.Normal.normalFormReduction_holds` | Mu4/Normal/*.lean | standard only (C1, C2 and the pattern list by kernel `decide`) |
| `BridgeMath` (L7-L10) | `Mu4.Final.bridgeMath` = `Mu4.Bridge.bridgeMath_holds` | Mu4/Bridge/Blocks, Vertex, Triangle.lean | standard only (since 11-06: `rref_cover` and Mat2's 2x2 facts are kernel checks; they were `native_decide`) |

The conditional theorems `mu4_6_of`, `mu4_6_general_of` are kept; `mu4_6`, `mu4_6_general` apply them to the two
proofs. The case dismissal of `setupCase` ("invalid", 56,250 of 175,950 cases, all 17,595 of P_9) is covered by
`Mu4.Bridge.setupCase_ne_invalid` (standard axioms): a decomposition in normal form never gives an invalid case.

Proved in Lean (all of audit/PROOF.md):
- **Upper bound.** `upper_bound` in Mu4/Upper.lean: an independent 14-term CRT scheme, all 216 coefficient
  equations by `decide`.
- **Reduction to R(T|_H) >= 13.** `rank_GF_of : NoTwelve → … = 14` in Mu4/Main.lean, by substitution (L0).
- **Lower-bound lemmas.** In Mu4/Lower/: L1 (`point_bound`, `point_dual`, `point_basis`); L2 (`pencil_count`,
  `pencil_exact`); L3 (`plane_bound`); L4 (`step1`); L5 (`pencil_structure`).
- **G1.** `Mu4.Final.geometry : Geometry`, from `geometry_of_check` (Mu4/Lower/Geometry.lean, standard axioms) and
  `geomCheck_ok` (Mu4/Check/Geom.lean, `native_decide` on the search of Mu4Geom.lean).
- **L6 with C1, C2.** Mu4/Normal/: the transports (Transport, Frobenius), the coverage C1, C2 as kernel checks of
  witness tables (CoverData, CoverDefs, CoverCheck1, CoverCheck2, Cover), the pattern list (Patterns), and the
  reduction to `NF` (Reduction).
- **L7.** Mu4/Bridge/Blocks.lean: the blocks of the search are the true blocks; `setupCase_ne_invalid`.
- **L8.** Mu4/Bridge/Vertex.lean: `VCtx.ops_exist`, the operators of the blocks for any eigenvalues.
- **L9, L10.** Mu4/Bridge/Triangle.lean: `triangle_abstract`, the vertex solutions, `triFree_false_valid`,
  `bridgeMath_holds`; with `sol_complete` (Mu4/Bridge/Complete.lean) for the completeness of the direction search.
- **The search check C3.** `searchCheck` in Mu4/Check/: for all 10 x 69 pairs (P, S) and all 255 patterns,
  `caseOK` holds, by `native_decide`.
- **Transfer.** `bilinRank_transfer` and `exists_equiv_GF` in Mu4/Transfer.lean.

## Proof outline mapped to the files

The steps are those of ../audit/PROOF.md.

| Step | Lean | File | Status |
| --- | --- | --- | --- |
| upper bound (14-term CRT scheme) | `upper_bound` | Mu4/Upper.lean | kernel (`decide`) |
| L0 substitution | `substitution`, `no13_of`, `rank_GF_of` | Mu4/Lower/Basic.lean, Mu4/Main.lean | kernel |
| L1 point bound | `point_bound`, `point_dual`, `point_basis` | Mu4/Lower/Basic.lean | kernel |
| L2 pencil count | `pencil_count`, `pencil_exact` | Mu4/Lower/Count.lean | kernel |
| L3 plane bound | `plane_bound` | Mu4/Lower/Count.lean | kernel |
| G1 geometry | `geometry_of_check`, `geomCheck_ok`, `geometry` | Mu4/Lower/Geometry.lean, Mu4Geom.lean, Mu4/Check/Geom.lean, Mu4/Final.lean | kernel + `native_decide` |
| L4 step 1 | `step1` | Mu4/Lower/Step1.lean | kernel |
| L5 pencil structure | `pencil_structure` | Mu4/Lower/Pencil.lean | kernel |
| L6 normal form | `normalFormReduction_holds` (target `NF`), `toRep`, `normalize` | Mu4/Normal/Transport, Frobenius, Reduction.lean, Mu4/Bridge/Normal.lean | kernel |
| C1, C2 coverage | `cover1`, `cover2` (witness tables) | Mu4/Normal/CoverData, CoverDefs, CoverCheck1, CoverCheck2, Cover.lean | kernel (`decide`) |
| pattern list | `mem_patterns`, `pc_cover` | Mu4/Normal/Patterns.lean | kernel (`decide`) |
| L7a blocks on the pencil | `mul_pt_eq` | Mu4/Bridge/Normal.lean | kernel |
| L7 blocks of the search, no invalid case | `offBlock_eq`, `residual_eq`, `m0Block_eq`, `setupCase_ne_invalid` | Mu4/Bridge/Chunks, Blocks.lean | kernel |
| L8 operators | `VCtx.ops_exist`, with `conjCode_diag`, `conjCode_eigen`, `conjCode_comm` | Mu4/Bridge/Vertex.lean, Mat2.lean, Mat2Check.lean | kernel (`decide +kernel` on Bool checks over GF(4), since 11-06) |
| L9 triangle | `triangle_abstract`, `finrank_range_wforms` | Mu4/Bridge/Triangle.lean | kernel |
| L10 search completeness and the passing triangle | `sol_complete` (with `rref_cover`, from `rref_cover_spec`), `triFree_false_valid`, `bridgeMath_holds` | Mu4/Bridge/Complete.lean, Rref.lean, RrefDefs.lean, RrefCheck1-4.lean, Triangle.lean | kernel (`rref_cover`: witness tables checked by `decide +kernel` in 16 chunks, since 11-06) |
| C3 the search | `searchCheck` | Mu4Comp/Search/*.lean, Mu4/Check/P*.lean, Mu4/Check/All.lean | `native_decide` |
| assembly | `noTwelve`, `mu4_6` (and the conditional `noTwelve_of`, `mu4_6_of`) | Mu4/Final.lean | kernel |
| transfer to any K, L | `bilinRank_transfer`, `exists_equiv_GF`, `mu4_6_general` | Mu4/Transfer.lean, Mu4/Final.lean | kernel |

## Trust base

- The Lean 4 kernel and Mathlib.
- The Lean compiler, for the three big searches only, by `native_decide`. These checks depend on the axioms
  `Lean.ofReduceBool` and `Lean.trustCompiler`:
  - Mu4/Check/P*.lean: the search C3 of mu_4(6), 2.9 core-hours (MEASURED 11-05: 10,509 s over the ten modules);
  - Mu4/Check/Geom.lean: the G1 search;
  - Mu4/N5/Check5.lean: the search C3(5) of mu_4(5), `searchCheck5`, 151 s (MEASURED 11-05). New use (second
    agent), labelled: the kernel cannot run the search.
  All other finite facts are kernel checks (`decide`), among them the new ones of the second agent: C1, C2 for
  n = 6 (Mu4/Normal/CoverCheck1, CoverCheck2), the pattern list (Mu4/Normal/Patterns), C1(5), C2(5)
  (Mu4/N5/CoverCheck5), the echelon-pair cover of GF(4)^3 (Mu4/N5/RrefCheck5), and, moved from `native_decide`
  to the kernel on 11-06: `rref_cover` (n = 6; witness tables of all 65,536 pairs of 8-bit codes in 16 chunks,
  Mu4/Bridge/RrefDefs, RrefCheck1-4, meaning in Rref.lean) and the 2x2 facts of Mu4/Bridge/Mat2.lean
  (Mu4/Bridge/Mat2Check: 4,096 + 4,096 + 65,536 cases; used by both results).
- The computational code is in Mu4Comp/, Mu4Comp5/ and Mu4Geom.lean (core Lean only, compiled with
  `precompileModules = true`). It is executed, not trusted for meaning: its meaning is proved in Mu4/Bridge/,
  Mu4/N5/ and Mu4/Lower/Geometry.lean.
- `#print axioms` (MEASURED 11-06, `lake env lean scratch/axioms/PrintAxioms.lean` and `PrintAxioms5.lean`;
  outputs in the project's audit/axioms_1106.txt and audit/axioms5_1106.txt):
  - `Mu4.Final.mu4_6_general`, `mu4_6`: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler,
    Quot.sound]; `Lean.ofReduceBool` enters only through C3 (`searchCheck`) and G1 (`geomCheck_ok`): they are the
    only `native_decide` modules that Mu4/Final.lean imports;
  - `Mu4.N5.mu4_5_general`, `mu4_5`: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler,
    Quot.sound]; `Lean.ofReduceBool` enters only through C3(5) (`searchCheck5`), the only `native_decide` module
    that Mu4/N5/Final5.lean imports;
  - [propext, Classical.choice, Quot.sound] or fewer: `normalFormReduction`, `bridgeMath`, `bridgeMath_holds`,
    `setupCase_ne_invalid`, `VCtx.ops_exist`, `sol_complete`, `rref_cover`, `rref_cover_spec`, `conjCode_diag`,
    `conjCode_eigen`, `conjCode_comm`, `cover1`, `cover2`, `normalFormReduction5`, `bridge5_holds`,
    `VCtx5.ops_exist`, `sol_complete5`, `setupCase_ne_invalid5`, `upper_bound`, `upper5_bound`, the transfers.
- There is no `sorry`, `admit`, `axiom` declaration, `implemented_by` or `extern` in the project.

## Build

```sh
cd mu4-lean-cert       # the bundle root (lean/ in the project)
lake exe cache get    # prebuilt Mathlib v4.28.0 (commit 8f9d9cff); or skip it and let lake build Mathlib (hours)
lake build            # this project: about 3 core-hours, almost all in the native searches (times below)
lake env lean Axioms.lean   # prints the axioms of mu4_6, mu4_6_general, mu4_5, mu4_5_general
```

- The toolchain is leanprover/lean4:v4.28.0 (lean-toolchain), installed by elan.
- lakefile.toml has one git requirement, Mathlib at tag v4.28.0. lake-manifest.json pins Mathlib and every transitive package to an
  exact commit: mathlib 8f9d9cff6bd728b17a24e163c9402775d9e6a365, batteries 495c008c, Qq b8f98e90, aesop f642a64c,
  proofwidgets be3b2e63, importGraph 85b59af4, LeanSearchClient c5d5b8fe, plausible 55c8532e, Cli 4f10f476. So a fresh
  checkout builds against exactly the packages this certificate was checked with.
- Offline: put checkouts of those packages at those commits in .lake/packages/ (for example hardlinks of an existing v4.28.0
  Mathlib build). Lake then fetches nothing. This is how the project was built and its clean build was run (audit/LOG.md).

Memory: each Mu4/Check/P*.lean module needs about 0.85 GB, a typical proof module 2-3 GB of resident memory (mostly
the mapped Mathlib files), and a plain `lake build` from a clean checkout may run many at once. On a small machine,
build the check modules in waves first:

```sh
lake build Mu4.Check.P0 Mu4.Check.P1 Mu4.Check.P2 Mu4.Check.P3 Mu4.Check.P4
lake build Mu4.Check.P5 Mu4.Check.P6 Mu4.Check.P7 Mu4.Check.P8 Mu4.Check.P9
lake build
```

A clean build with at most two Lean processes at a time, in import order: `python3 -I audit/clean_build2.py` (from
the project root; it extracts the bundle into bundle/cleanbuild; MU4_PKGS=DIR hardlinks the pinned packages from DIR).

Build time (MEASURED 11-05 and 11-06 on a 16-core machine shared with other jobs; details in the project's
audit/LOG.md):
- the C3 modules Mu4/Check/P0..P8: 1032-1237 s each, single-threaded; P9: 33 s (all its cases are invalid);
  10,509 s = 2.9 core-hours in total, about 40 min wall in two waves;
- the G1 check Mu4/Check/Geom.lean: 213 s;
- the C3(5) check Mu4/N5/Check5.lean: 151 s; the Mu4Comp5 library 175 s;
- the kernel checks C1, C2 (Mu4/Normal/CoverCheck1, CoverCheck2): 58 s and 64 s; C1(5), C2(5): about 20 s; the
  echelon-pair cover of GF(4)^3 (Mu4/N5/RrefCheck5): about 40 s;
- the kernel checks of 11-06: Mu4/Bridge/Mat2Check.lean 146-202 s, 2.7 GB; Mu4/Bridge/RrefCheck1-4.lean (four
  chunks each, about 31 s of kernel time per chunk): 151-384 s each, 2.4 GB, two at a time on the loaded machine;
- everything else: about 1 min per module, most of it loading the precompiled search libraries (their lookup
  tables are built when the shared library is loaded).

## Files

| File | Content |
| --- | --- |
| Mu4Comp/F4.lean, Codes.lean | GF(4) type, 12-bit codes, smulC, mulK (Horner), invC table; core Lean only |
| Mu4Comp/Search/{Core,Case,Dir}.lean | the step 5-7 search: setupCase, solsK, allSols, triFree, wfCheck, caseOK, checkPS |
| Mu4Comp/Data.lean | the case lists pList (runs/hyper/plist.txt), sList (runs/hyper/Sclasses6.txt) |
| Mu4Geom.lean | the G1 search (a library of its own; core Lean only) |
| Mu4/F4, GF, Code, GFField, Field.lean | the fields and the code semantics |
| Mu4/Rank.lean, Upper.lean, Main.lean | definitions, upper bound, reduction to NoTwelve |
| Mu4/Transfer.lean | transfer to any field K with 4 elements and any extension L of degree 6 |
| Mu4/Lower/*.lean | L0-L5, and G1 from its search (Geometry.lean) |
| Mu4/Bridge/*.lean | semantics of the search and its completeness (sol_complete), normal form; Chunks, Blocks (L7), Vertex (L8), Triangle (L9, L10, `bridgeMath_holds`); Mat2Check (kernel checks of Mat2's 2x2 facts), RrefDefs and RrefCheck1-4 (kernel check of `rref_cover`'s witness tables, generated by tools/gen_rref4.py) |
| Mu4/Normal/*.lean | L6 with C1, C2: Transport, Frobenius, CoverData (witness tables), CoverDefs, CoverCheck1/2 (kernel), Cover, Patterns (kernel), Reduction (`normalFormReduction_holds`) |
| Mu4/Check/*.lean | C3 and the G1 search by native_decide |
| Mu4/Final.lean | the main theorems: `mu4_6`, `mu4_6_general` (and the conditional `_of` forms) |
| Mu4Comp5/*.lean | the mu_4(5) search (core Lean only, precompiled): mulK5, invC5, setupCase5, allSols5, tripleFree5, checkAll5; the case lists |
| Mu4/N5/*.lean | mu_4(5): the field GF5, the 11-term scheme (Upper5), N1-N9, C1(5), C2(5), C3(5) (Check5), `mu4_5`, `mu4_5_general` (Final5) |
| tools/*.py | table generators (pw, inverse tables, 14- and 11-term schemes, coverage witnesses, echelon-pair witnesses for n = 5 and n = 6), each with a self-check |
| SearchMain, ProfMain, CheckMain, Search5Main.lean | drivers used for timing and cross-checks (not part of the certificate); `mu4search5` runs the mu_4(5) search with counters |
