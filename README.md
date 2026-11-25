# Characterizations of E-finite algebras

Lean proofs for Haruhisa Enomoto’s *Characterizations of E-finite algebras and conjectures on brick-finiteness*, following the manuscript of November 25, 2026. The [statement correspondence](docs/PAPER-CORRESPONDENCE.md) links all 44 numbered results to their proofs. The [proof guide](docs/proofs/PROOF-ROUTES.md) traces the implications from silting cones and stable bricks and explains where Lean takes a different route from the paper.

For a finite-dimensional algebra Λ, E-finiteness means that every integral class of finite projective right modules belongs to a two-term silting cone. Theorem A gives seventeen equivalent conditions over any field. They include the existence of a nonzero map between every pair of modules with the same nonzero composition vector, finiteness of every semibrick, and the absence of generic bricks. Two further criteria count bricks and stable modules over an infinite field. Over an algebraically closed field three geometric criteria use King moduli, open brick orbits and open wide loci. [Theorem A](EFiniteCharacterizations/Characterizations/Equivalences.lean)

For algebras with at most two isomorphism classes of simple right modules, Theorem B identifies E-finiteness with both brick-finiteness and τ-tilting finiteness. Corollary C identifies brick-discreteness with multiplicity-freeness of irreducible components over an algebraically closed field. [Theorem B](EFiniteCharacterizations/Silting/Fans/RankTwoTauTilting.lean) · [Corollary C](EFiniteCharacterizations/Geometry/ComponentMultiplicity.lean)

The [independent statement](EFiniteCharacterizations/Statement.lean) uses Mathlib alone. The [five comparison theorems](Challenge.lean) state the three field cases of Theorem A, Theorem B and Corollary C. Their [proofs](Solution.lean) pass through the [translation to the library](EFiniteCharacterizations/MainTheorems.lean). The comparison statements use all split basic presentations, and Lean proves that every algebra under consideration has one.

## Reading and building

The library is organized by mathematical subject. Start with [two-term projective classes](EFiniteCharacterizations/Presentations/ProjectiveClasses.lean), [semi-invariants and King moduli](EFiniteCharacterizations/Geometry/KingSemiInvariants.lean), or the [torsion-monoid criterion](EFiniteCharacterizations/GrothendieckGroups/TorsionMonoidEmbedding.lean). The [website](https://haruhisa-enomoto.github.io/e-finite-characterizations/) includes the library map and searchable API.

```sh
lake exe cache get
lake build
```

The proof package uses Lean 4.35.0-rc3 and depends only on pinned Mathlib. See the [verification guide](docs/VERIFICATION.md), [manuscript identification](docs/MANUSCRIPT.md), [authorship](PROVENANCE.md) and [code origins](VENDORED.md).
