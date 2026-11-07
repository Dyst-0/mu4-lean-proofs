# Lean 4 proofs: μ₄(6) = 14 and μ₄(5) = 11

Machine-checked proofs (Lean 4 + Mathlib) of the bilinear complexity of multiplication in two extensions of GF(4):

- **μ₄(6) = 14**: multiplication in GF(4⁶) has bilinear rank exactly 14 over GF(4). No algorithm with 13 or fewer
  GF(4)-bilinear multiplications exists, symmetric or not.
- **μ₄(5) = 11**: multiplication in GF(4⁵) has bilinear rank exactly 11 over GF(4).

Both are proved for every field extension L/K with |K| = 4 and [L : K] = 6 (resp. 5), not just for one model.

## The archive and its hash

`mu4-lean-cert.tar` is the archive whose SHA-256 was posted publicly on 2026-11-06:

```
58e138356aba88aa5af1763aa1aa0d6a506cab0c9024b812d1f6498745accd51  mu4-lean-cert.tar
```

Check it with `sha256sum -c mu4-lean-cert.tar.sha256`. The directory `mu4-lean-cert/` holds exactly the archive's
contents, unpacked for reading.

## Statements

```lean
-- mu4-lean-cert/Mu4/Rank.lean
def HasDecomp (f : U →ₗ[K] V →ₗ[K] W) (r : ℕ) : Prop :=
  ∃ (a : Fin r → U →ₗ[K] K) (b : Fin r → V →ₗ[K] K) (c : Fin r → W),
    ∀ u v, f u v = ∑ i, (a i u * b i v) • c i
noncomputable def bilinRank (f : U →ₗ[K] V →ₗ[K] W) : ℕ := sInf {r | HasDecomp K f r}

-- mu4-lean-cert/Mu4/Final.lean
theorem Mu4.Final.mu4_6_general
    (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    (hK : Fintype.card K = 4) (hL : Module.finrank K L = 6) :
    bilinRank K (LinearMap.mul K L) = 14

-- mu4-lean-cert/Mu4/N5/Final5.lean
theorem Mu4.N5.mu4_5_general
    (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    (hK : Fintype.card K = 4) (hL : Module.finrank K L = 5) :
    bilinRank K (LinearMap.mul K L) = 11
```

`LinearMap.mul K L` is Mathlib's multiplication map of the K-algebra L. The concrete theorems `Mu4.Final.mu4_6` and
`Mu4.N5.mu4_5` state the same for explicit models GF(4)[t]/(t⁶+t²+t+ω) and GF(4)[t]/(t⁵+t+ω); the general forms follow
by transfer along field isomorphisms.

## Trust base

```
$ lake env lean Axioms.lean
'Mu4.Final.mu4_6' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'Mu4.Final.mu4_6_general' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'Mu4.N5.mu4_5' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'Mu4.N5.mu4_5_general' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
```

- `propext`, `Classical.choice` and `Quot.sound` are Lean's standard axioms.
- `Lean.ofReduceBool` and `Lean.trustCompiler` mean the proof trusts Lean's compiler for some `native_decide` checks.
  They come only from three finite searches, too large for the kernel:
  - the main case search for n = 6 (`Mu4/Check/P0..P9`);
  - a geometry check (`Mu4/Check/Geom.lean`);
  - the case search for n = 5 (`Mu4/N5/Check5.lean`).
- Everything else, including the coverage tables and the completeness of the searches, is checked by the kernel.
- The project has no `sorry`, `admit`, `axiom` declaration, `implemented_by` or `extern`.

## How to check it

Lean v4.28.0 (installed by elan from `lean-toolchain`) and Mathlib v4.28.0 (commit 8f9d9cff, pinned in
`lake-manifest.json`):

```sh
sha256sum -c mu4-lean-cert.tar.sha256
tar -xf mu4-lean-cert.tar && cd mu4-lean-cert
lake exe cache get        # prebuilt Mathlib; without it, lake builds Mathlib itself (hours)
lake build                # about 2 hours on 2 cores; the n = 6 search modules dominate
lake env lean Axioms.lean # prints the trust base above
```

`mu4-lean-cert/README.md` lists every file, the pinned package commits and an offline build.

## How the proof goes

- **Upper bounds:** explicit 14-term and 11-term schemes built from the Chinese remainder theorem, with every
  coefficient equation checked by `decide`.
- **Lower bounds, in outline:**
  - restrict to a hyperplane, by substitution;
  - count the "alive" terms and find a pencil structure;
  - reduce to a normal form, whose coverage is checked by kernel tables;
  - describe the remaining cases by blocks, operators and triangles;
  - run an exhaustive search: about 2.4 million candidate triangles for n = 6, none of which survives, with the
    search's completeness proved in Lean.

`audit/PROOF.md` states every step as a lemma with its Lean name. Its header was updated for this release, and the
exploration notes it cites are not included. The README inside the archive still has two pre-release lines, kept
unchanged so the archive matches its hash: a "secret until 2027-01-20" note, and a pointer to a decision log that is
not published here.

## Related work and credit

- **田村 (Kaggle: xolotlmictlan)** posted the first public computer-assisted proofs of μ₄(5) = 11 and of the
  symmetric μ₄^sym(6) = 14 on 2026-11-06, with code, in the Kaggle discussion "Two exact finite-field multiplication
  complexities — reproducible proofs"
  (https://www.kaggle.com/competitions/google-verifiable-quantum-circuit-compilation/discussion/756476).
- **pjmathematician** sketched the asymmetric μ₄(6) = 14 in a reply there.
- The proofs here were found independently. They are formal, and confirm both results in Lean.
- Chengu Wang's work on automated lower bounds for bilinear complexity (arXiv:2603.07280) and his prover were
  consulted during exploration. The Lean proof does not depend on them.

## License

Apache-2.0 (see LICENSE) for the files in this repository. Lean and Mathlib have their own licenses.
