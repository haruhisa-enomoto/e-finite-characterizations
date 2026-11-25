module

public import EFiniteCharacterizations.MainTheorems

/-!
# Proofs of the five Challenge theorems

This file connects the standalone Mathlib-only statements in `Challenge.lean`
(Theorem A(I–III), Theorem B, and Corollary C) to their proofs in
`EFiniteCharacterizations/MainTheorems.lean` without importing `Challenge.lean`.
-/

@[expose] public section
universe u

namespace EFiniteCharacterizations.Challenge

/-- **Theorem A(I):** Over an arbitrary field, E-finiteness is equivalent to each of the
seventeen conditions `(K₀-Hom)` through `(ring-epi)`. -/
theorem arbitraryField : Statement.ArbitraryField.{u} := proveArbitraryField

/-- **Theorem A(II):** Over an infinite field, E-finiteness is also equivalent to
`(dim-brick)` (finitely many bricks of each dimension vector) and `(dim-stab)`. -/
theorem infiniteField : Statement.InfiniteField.{u} := proveInfiniteField

/-- **Theorem A(III):** Over an algebraically closed field, E-finiteness is also equivalent to
`(moduli-pt)`, `(open-brick)`, and `(open-wide)` in every split basic Morita chart. -/
theorem algebraicallyClosedField : Statement.AlgebraicallyClosedField.{u} := proveAlgebraicallyClosedField

/-- **Theorem B:** For a finite-dimensional algebra of rank at most two over any field,
E-finiteness, `τ`-tilting finiteness, and brick-finiteness are equivalent. -/
theorem rankTwo : Statement.RankTwo.{u} := proveRankTwo

/-- **Corollary C (Weyman's conjecture):** Over an algebraically closed field,
Schur-representation-finiteness `(dim-brick)` is equivalent to multiplicity-freeness on every
irreducible component of every representation variety. -/
theorem brickDiscreteMultiplicityFree : Statement.BrickDiscreteMultiplicityFree.{u} := proveBrickDiscreteMultiplicityFree

end EFiniteCharacterizations.Challenge
