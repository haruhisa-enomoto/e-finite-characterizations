# Characterizations of E-finite algebras and conjectures on brick-finiteness

[Website](https://haruhisa-enomoto.github.io/e-finite-characterizations/) ·
[Main theorems in Lean](EFiniteCharacterizations/Characterizations/Equivalences.lean) ·
[Independent statement](EFiniteCharacterizations/Statement.lean) ·
[Paper correspondence](docs/PAPER-CORRESPONDENCE.md) ·
[Proof guide](docs/proofs/PROOF-ROUTES.md) ·
[Verification](docs/VERIFICATION.md)

This repository contains a Lean 4 formalization of the paper *Characterizations of
E-finite algebras and conjectures on brick-finiteness* by Haruhisa Enomoto (frozen
manuscript of November 25, 2026; see [docs/MANUSCRIPT.md](docs/MANUSCRIPT.md)),
covering Theorems A and B, Corollary C, all 44 numbered statements of the paper, and
the cited inputs used by their proofs. Mathlib is the only external dependency.

---

## Mathematical overview

Let `Λ` be a finite-dimensional algebra over a field `k`, and let `n` be its rank (the
number of isomorphism classes of simple right `Λ`-modules). By results of Demonet,
Iyama, and Jasso and of Asai, `Λ` has finitely many isomorphism classes of bricks
(*brick-finiteness*) if and only if it is `τ`-tilting finite, and if and only if its
`g`-vector fan `Σ(Λ) ⊆ K₀(proj Λ)_ℝ` covers the entire real vector space.

An algebra `Λ` is called **E-finite** if `Σ(Λ)` contains every integral lattice point
`K₀(proj Λ)`—equivalently, every rational vector (*rational completeness* of the
`g`-vector fan, or vanishing of the generic self E-invariant when `k` is algebraically
closed). Demonet's lattice point conjecture asks whether every E-finite algebra is
already brick-finite. Alongside Demonet's polyhedral question, several categorical,
numerical, and infinite-dimensional conjectures ask whether brick-finiteness is forced
by finiteness of semibricks, functorial finiteness of wide subcategories, bounded
brick counts (in analogy with the second Brauer–Thrall conjecture), or the absence of
generic bricks. Over a general field `k`, the natural size invariant of a brick `B` is
its *endolength* `dim_k B / dim_k End_Λ(B)`, and `Λ` is called *brick-discrete* when
only finitely many isomorphism classes of bricks have each endolength `r ≥ 1`.

### Theorem A (`equivalences_arbitraryField`, `equivalences_infiniteField`, `equivalences_algebraicallyClosedField`)

Let `Λ` be a finite-dimensional `k`-algebra of rank `n`.

**(I) Over an arbitrary field `k`, the following conditions are equivalent:**

* *Projective lattice, dimension vectors, and torsion classes:*
  * `(E-fin)` `Λ` is E-finite (`K₀(proj Λ) ⊆ Σ(Λ)`).
  * `(K₀-Hom)` For all nonzero `M, N ∈ mod Λ`, if `[M] = [N]` in `K₀(mod Λ)`, then `Hom_Λ(M, N) ≠ 0`.
  * `(mon-dim)` For every torsion class `T ⊆ mod Λ`, the dimension-vector map `M(T) → K₀(mod Λ)` on its Grothendieck monoid is injective.
  * `(comp-tors)` Every compact (singly generated) torsion class in `mod Λ` is functorially finite.
  * `(num-disj)` Every torsion pair `(T, F)` in `mod Λ` is numerically disjoint (`[X] ≠ [Y]` for nonzero `X ∈ T`, `Y ∈ F`).
* *Wide subcategories and brick labels:*
  * `(wide)` Every wide subcategory of `mod Λ` is functorially finite.
  * `(wide₁)` For every brick `B ∈ brick Λ`, the filtration subcategory `Filt(B)` is functorially finite.
  * `(brick-label)` Every brick `B ∈ brick Λ` arises as the label `Filt(B) = T ∩ (T')⊥` of a cover `T' ⋖ T` in `f-tors Λ`.
* *Semibricks and brick counts:*
  * `(n-sbrick)` The simple modules `{S₁, …, S_n}` form the unique `n`-element semibrick in `mod Λ`.
  * `(fin-sbrick)` Every semibrick in `mod Λ` is finite.
  * `(brick-discrete)` For every `r ≥ 1`, only finitely many isomorphism classes in `brick Λ` have endolength `r`.
  * `(endo-stab)` For every `θ ∈ K₀(proj Λ)` and `r ≥ 1`, only finitely many `θ`-stable bricks have endolength `r`.
  * `(poly-brick)` The number of isomorphism classes of bricks of composition length `≤ m` is bounded by a polynomial in `m` (explicitly, `2(n - 1)(m + 1)^{n(n - 1)}` for `n ≥ 2`).
* *Large modules, two-term complexes, and ring epimorphisms:*
  * `(no-gen-brick)` `Mod Λ` contains no generic brick.
  * `(no-gen-grain)` `Mod Λ` contains no generic grain.
  * `(thick-gen)` Every thick subcategory of `K^{[-1,0]}(proj Λ)` has the form `thick(U) ∩ K^{[-1,0]}(proj Λ)` for a two-term presilting complex `U`.
  * `(univ-loc)` Every universal localization of `Λ` is finite-dimensional over `k`.
  * `(ring-epi)` Every ring epimorphism `Λ → Γ` with simple Artinian target satisfies `dim_k Γ < ∞`.

**(II) If `k` is infinite, each of the following is also equivalent to `(E-fin)`:**

* `(dim-brick)` For every dimension vector `d ∈ ℕ^n`, `brick Λ` contains only finitely many classes of dimension vector `d` (*Schur-representation-finiteness*).
* `(dim-stab)` For every `θ ∈ K₀(proj Λ)` and `d ∈ ℕ^n`, only finitely many `θ`-stable bricks have dimension vector `d`.

**(III) If `k` is algebraically closed, each of the following geometric conditions is also equivalent to `(E-fin)`:**

* `(moduli-pt)` For every `θ ∈ K₀(proj Λ)` and `d ∈ ℕ^n`, King's moduli space `M_θ^{ss}(Λ, d)` has at most one closed point.
* `(open-brick)` Every brick `B ∈ brick Λ` has a Zariski-open `GL(d)`-orbit in `rep(Λ, d)`.
* `(open-wide)` For every `d ∈ ℕ^n` and every wide subcategory `W ⊆ mod Λ`, `{X ∈ rep(Λ, d) | X ∈ W}` is Zariski-open in `rep(Λ, d)`.

### Consequences: unified conjectures, rank two, and Weyman's conjecture

By Theorem A(I), seven open problems in the literature become equivalent **for each
individual finite-dimensional `k`-algebra `Λ`** (`seven_pointwise_implications` in
[BrickFiniteness.lean](EFiniteCharacterizations/Characterizations/BrickFiniteness.lean)):
Demonet's lattice point conjecture (`(E-fin) ⇒ brick-finite`), Enomoto's finite
semibrick conjecture (`(fin-sbrick)`), Mousavand–Paquette's `n`-semibrick question
(`(n-sbrick)`), the second brick-Brauer–Thrall conjecture (`(brick-discrete)`),
Mousavand–Paquette's generic brick conjecture (`(no-gen-brick)`), Pfeifer's stable
Brauer–Thrall II′ conjecture (`(endo-stab)`), and Angeleri Hügel–Sentieri's wide
subcategory question (`(wide)`).

**Theorem B (`rankTwoEquivalences`).** Let `Λ` be a finite-dimensional algebra of rank
`n ≤ 2` over an arbitrary field `k`. Then `Λ` is E-finite if and only if `Λ` is
brick-finite (equivalently, `τ`-tilting finite). In particular, all seven conjectures
hold in rank at most two over every field.

**Corollary C (`brick_discrete_iff_multiplicityFree`, Weyman's conjecture).** Over an
algebraically closed field of arbitrary characteristic, `Λ` is
Schur-representation-finite `(dim-brick)` if and only if it is multiplicity-free (on
every irreducible component of every `rep(Λ, d)`, each `GL(d)`-semi-invariant weight
space has dimension at most one).

Among the numbered results in the body, the library also proves:
- **Corollary 4.3 (`MonoidCancellation.lean`):** `Λ` is E-finite if and only if every
  torsion class—equivalently, every torsion-free class—in `mod Λ` has a cancellative
  Grothendieck monoid.
- **Corollary 7.9 (`ArtinTargets.lean`):** If every ring epimorphism `Λ → Γ` with
  `Tor₁^Λ(Γ, Γ) = 0` has an Artin algebra target, then `Λ` is E-finite (and hence
  `τ`-tilting finite when `n ≤ 2`, answering questions of Angeleri Hügel–Marks–Vitória
  and Angeleri Hügel–Sentieri in rank at most two).

The results address researchers in the representation theory of finite-dimensional
algebras, `τ`-tilting and silting theory, lattices of subcategories, and geometric
invariant theory of module varieties.

---

## How the Lean proofs work

The mathematical architecture and all differences from the paper's proof routes are
explained in [docs/proofs/PROOF-ROUTES.md](docs/proofs/PROOF-ROUTES.md).

The central bridge of Theorem A(I) links the polyhedral condition `(E-fin)` with the
module-theoretic condition `(K₀-Hom)`. At any weight in the relative interior `C°(U)`
of the cone of a basic two-term presilting complex `U` with `r` indecomposable
summands, the semistable category is the `τ`-perpendicular category `J(U)`
(`ConeTorsionPairs.lean`), which is equivalent to `mod Γ_U` for a finite-dimensional
reduction algebra of rank `n - r` (`PerpendicularReduction.lean`,
`PerpendicularSimpleCount.lean`; at `U = 0` the weight is `0` and `J(0) = mod Λ` of
rank `n`, while points on a proper face are treated on that face), so the dimension
vectors of its stable bricks are linearly independent. Conversely, any pair of nonzero modules `M, N` with `[M] = [N]`
and `Hom_Λ(M, N) = 0` yields a finite semibrick with linearly dependent dimension
vectors jointly stable at a single integral weight (`RationalExtraction.lean`), giving
`(E-fin) ⇒ (K₀-Hom)`. In the reverse direction, an integral class `g ∉ Σ(Λ)` produces
minimal-image stable bricks across a presentation space (`MissingWeightWitnesses.lean`),
descended to finite ground fields via Frobenius orbits (`AbsoluteFrobeniusCorrespondence.lean`,
`SharpFiniteFieldCount.lean`), yielding two nonisomorphic bricks of equal dimension
vector stable at a common weight over every field.

In rank at most two (Theorem B), the two mixed-sign quadrants are subdivided by
repeatedly inserting a presilting representative of the Stern–Brocot mediant
`[E] + [L]`; Lemma 8.1 (`StableRigidComparison.lean`) shows that this strictly decreases
`dim_k Hom(L, E[1])` on both child sectors, so the subdivision terminates in finitely
many compatible cones (`SectorSubdivision.lean`, `RankTwoBricks.lean`,
`RankTwoTauTilting.lean`).

Three proof routes in Lean are deliberately more self-contained than the manuscript's
citations:

1. **Generic grains without Cohn's universal skew field (`DivisionRings/`, `LargeModules/GenericGrainCriterion.lean`):**
   Where Proposition 7.6 of the paper uses Cohn's free skew field, Lean constructs the
   needed division-ring coefficients directly from Malcev–Neumann well-ordered series
   on a bi-ordered finitely generated free group.
2. **Universal localizations by direct rank induction (`Presentations/RigidPencilInversion.lean`, `RingEpimorphisms/UniversalLocalization.lean`):**
   In addition to `(E-fin) ⇔ (thick-gen)`, Lean proves `(E-fin) ⇒ (univ-loc)` directly
   by induction on `n`, specializing module-theoretic inversion along a presilting
   pencil for nonzero `g`-vectors and applying Fitting decomposition for `g = 0`.
3. **Closed points of King moduli spaces (`Geometry/KingModuli.lean`, `Geometry/KingSplitting.lean`):**
   Rather than importing King's full polystable classification of closed points of
   `M_θ^{ss}(Λ, d)`, Lean splits extensions directly while preserving point evaluations
   in `Proj`.

---

## Start reading

- [`EFiniteCharacterizations/Statement.lean`](EFiniteCharacterizations/Statement.lean):
  standalone Mathlib-only definitions and the five endpoint propositions
  (`ArbitraryField`, `InfiniteField`, `AlgebraicallyClosedField`, `RankTwo`,
  `BrickDiscreteMultiplicityFree`).
- [`Challenge.lean`](Challenge.lean) and [`Solution.lean`](Solution.lean): the
  generated standalone comparison surface and its proof via
  [`MainTheorems.lean`](EFiniteCharacterizations/MainTheorems.lean).
- [`Characterizations/Equivalences.lean`](EFiniteCharacterizations/Characterizations/Equivalences.lean):
  assembly of Theorem A(I), A(II), and A(III).
- [`Silting/Fans/RankTwoTauTilting.lean`](EFiniteCharacterizations/Silting/Fans/RankTwoTauTilting.lean)
  and [`Geometry/ComponentMultiplicity.lean`](EFiniteCharacterizations/Geometry/ComponentMultiplicity.lean):
  Theorem B and Corollary C.
- [`docs/PAPER-CORRESPONDENCE.md`](docs/PAPER-CORRESPONDENCE.md): complete lookup table
  for the 22 conditions of Theorem A and all numbered environments of the manuscript.

### What is compared and conventions

`Challenge.lean` (generated from `Statement.lean` by `scripts/generate_challenge.py`)
imports Mathlib alone and states five theorems: `arbitraryField`, `infiniteField`,
`algebraicallyClosedField`, `rankTwo`, and `brickDiscreteMultiplicityFree`.

Conventions match the paper:
- **Right modules** over `R` are formalized as left modules over `Rᵐᵒᵖ`
  (`FGModuleCat Rᵐᵒᵖ` for `mod Λ` and `ModuleCat Rᵐᵒᵖ` for `Mod Λ`).
- **Integral weights** in `K₀(proj Λ)` are represented as differences `[Q] - [P]` of
  finitely generated projectives, evaluated as `dim_k Hom(Q, -) - dim_k Hom(P, -)`.
- **Dimension vectors** are encoded by classes in the exact Grothendieck group
  `K₀(mod Λ)`.
- **Representation varieties (`Statement.Chart k R`):** over an algebraically closed
  field, Theorem A(III) proves that every finite-dimensional algebra admits a split
  basic Morita chart and establishes `(moduli-pt)`, `(open-brick)`, and `(open-wide)`
  across *all* such charts.
- All rings, fields, and modules live in one universe `u`.

### Axioms and review status

All 6,463 declarations across the proof library and `Solution.lean` compile in the
Lean 4 kernel and depend only on the three standard axioms `propext`,
`Classical.choice`, and `Quot.sound`, with zero `sorry`. In addition, `lake comparator`
replays the five standalone `Challenge.lean` endpoint proofs in `Solution.lean` (and
their transitive proof dependencies) through the Lean 4 kernel and the external
checkers **NanoDa** and **con-ron**.

No human expert has reviewed the Lean source files line-by-line. For the five compared
endpoints, human mathematical review reduces to checking that the Mathlib-only
definitions in `Statement.lean` faithfully express the statements in the paper; for
the remaining 41 body and appendix statements (such as Corollary 7.9, which compiles
in the library outside `Solution.lean`'s import closure), human judgment also applies
to comparing their Lean declarations in `docs/PAPER-CORRESPONDENCE.md` with the
manuscript.

---

## Library layout

The 388 modules under `EFiniteCharacterizations/` are organized by mathematical subject:

| Directory | Modules | Mathematical content |
| --- | ---: | --- |
| `Statement.lean`, `MainTheorems.lean` | 2 | Standalone Mathlib-only endpoint definitions and the bridge from the proof library |
| [`Algebra/`](EFiniteCharacterizations/Algebra) | 7 | Split basic corners, full-idempotent Morita equivalence, and matrix-image algebras |
| [`Characterizations/`](EFiniteCharacterizations/Characterizations) | 6 | Theorem A(I–III), fixed-vector finiteness, the seven unified conjectures, and finite-field growth |
| [`DivisionRings/`](EFiniteCharacterizations/DivisionRings) | 7 | Bi-ordered free groups, Malcev–Neumann well-ordered series, and division-ring coefficients |
| [`Geometry/`](EFiniteCharacterizations/Geometry) | 37 | Vertex representation varieties, Zariski open loci, semi-invariants, King moduli (`Proj`), and Weyman's conjecture |
| [`GrothendieckGroups/`](EFiniteCharacterizations/GrothendieckGroups) | 11 | Exact Grothendieck groups and monoids, torsion-monoid dimension embeddings, and cancellation |
| [`LargeModules/`](EFiniteCharacterizations/LargeModules) | 18 | Endofinite modules, generic bricks, generic grains, and large `τ`-perpendicular categories |
| [`LinearAlgebra/`](EFiniteCharacterizations/LinearAlgebra) | 47 | Maximal geometric rank, polynomial covers, Farkas's lemma, duals, and balanced tensor products |
| [`Modules/`](EFiniteCharacterizations/Modules) | 31 | Finite modules, composition series, bricks, Hom extraction, endolength, contragredient duality, and Nakayama functors |
| [`Presentations/`](EFiniteCharacterizations/Presentations) | 50 | Two-term projective complexes, `K₀(proj Λ)`, Euler pairings, presilting pencils, and `τ`-tilting modules |
| [`RingEpimorphisms/`](EFiniteCharacterizations/RingEpimorphisms) | 15 | Universal localizations, vanishing of `Tor₁`, residual localizations, and Artin algebra targets |
| [`ScalarExtension/`](EFiniteCharacterizations/ScalarExtension) | 38 | Scalar extension and restriction, algebraic semistability, Frobenius orbits, and finite-field brick counts |
| [`Silting/`](EFiniteCharacterizations/Silting) | 43 | Bongartz completion, `τ`-perpendicular reduction, `g`-vector cones, Stern–Brocot rank-two subdivision, and `K^{[-1,0]}` thick generation |
| [`Stability/`](EFiniteCharacterizations/Stability) | 54 | Numerical torsion pairs, separating weights, dependent semibrick extraction, missing-weight witnesses, and normalized submodule polytopes |
| [`Subcategories/`](EFiniteCharacterizations/Subcategories) | 22 | Compact torsion classes, wide subcategories, `Filt(B)` approximations, brick labels, and exact embeddings |

---

## Build and verify

The package pins Lean `v4.35.0-rc3` and Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`
(tag `v4.35.0-rc3`). Every Lean file uses the Lean 4 module system.

```sh
lake exe cache get
lake build
python3 scripts/audit_axioms.py
python3 scripts/scan_axioms.py
```

To verify `Challenge.lean` synchronization and run `lake comparator` (Lean kernel,
NanoDa, and con-ron inside `bwrap`, requiring `bwrap` on `PATH` and a real directory at
`.lake/packages`):

```sh
python3 scripts/check-lean-sources.py
python3 scripts/generate_challenge.py --check
lake build Challenge Solution
./scripts/verify-comparator.sh
```

See [docs/VERIFICATION.md](docs/VERIFICATION.md) for full details and
[verification/2026-11-25/README.md](verification/2026-11-25/README.md) for the passing
[hosted Palomar preflight](https://github.com/haruhisa-enomoto/e-finite-characterizations/actions/runs/45530650450)
on release tag [`v0.1.0`](https://github.com/haruhisa-enomoto/e-finite-characterizations/releases/tag/v0.1.0)
(commit `f594ef1`).

## Provenance and licence

Authorship and AI contributions to both the manuscript and the Lean formalization are
recorded in [PROVENANCE.md](PROVENANCE.md), and the 24 modules adapted from earlier
Apache-2.0 formalizations are documented in [VENDORED.md](VENDORED.md). Released under
the [Apache License 2.0](LICENSE).
