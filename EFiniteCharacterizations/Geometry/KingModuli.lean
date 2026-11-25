module

public import EFiniteCharacterizations.Geometry.BasicPresentation
public import EFiniteCharacterizations.Geometry.KingCompositionFactors

/-! # The King moduli criterion in the right-module convention -/

@[expose] public section

universe u
namespace EFiniteCharacterizations

/-- Each King scheme for the chosen basic presentation has at most one closed point. -/
def BasicPresentation.KingClosedPointCondition {k R : Type u} [Field k] [Ring R]
    (P : BasicPresentation k R) : Prop :=
  letI := IsNoetherianRing.of_finite k P.Carrier
  ∀ g d, P.vertices.atMostOneKingClosedPoint P.algebraBasis d g

theorem kingModuli_of_isEFinite (k R : Type u) [Field k] [IsAlgClosed k] [Ring R]
    [Algebra k R] [Module.Finite k R] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    IsEFinite Rᵐᵒᵖ → (basicPresentation k R).KingClosedPointCondition := by
  let P := basicPresentation k R
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  let := IsNoetherianRing.of_finite k P.Carrier
  let := IsArtinianRing.of_finite k P.Carrier
  intro he g d
  exact P.vertices.atMostOneKingClosedPoint_of_isEFinite P.algebraBasis g
    ((isEFinite_iff_of_module_equivalence k k P.equivalence).1 he)

end EFiniteCharacterizations
