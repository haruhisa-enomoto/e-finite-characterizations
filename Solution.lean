module

public import EFiniteCharacterizations.MainTheorems

/-! # Proofs of the five independent statements -/

@[expose] public section
universe u

namespace EFiniteCharacterizations.Challenge

/-- Theorem A(I). Seventeen equivalent characterizations over an arbitrary field. -/
theorem arbitraryField : Statement.ArbitraryField.{u} := proveArbitraryField

/-- Theorem A(II). Finiteness of brick and stable classes with a fixed composition vector. -/
theorem infiniteField : Statement.InfiniteField.{u} := proveInfiniteField

/-- Theorem A(III). King closed points, open brick orbits and open wide loci in the basic representation varieties. -/
theorem algebraicallyClosedField : Statement.AlgebraicallyClosedField.{u} := proveAlgebraicallyClosedField

/-- Theorem B. E-finiteness, brick-finiteness and τ-tilting finiteness coincide in rank at most two. -/
theorem rankTwo : Statement.RankTwo.{u} := proveRankTwo

/-- Corollary C. Brick-discreteness is equivalent to multiplicity-freeness on every irreducible component. -/
theorem brickDiscreteMultiplicityFree : Statement.BrickDiscreteMultiplicityFree.{u} := proveBrickDiscreteMultiplicityFree

end EFiniteCharacterizations.Challenge
