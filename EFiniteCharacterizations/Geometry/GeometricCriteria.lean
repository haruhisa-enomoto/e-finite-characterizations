module

public import EFiniteCharacterizations.Geometry.VertexMatrixLocalization
public import EFiniteCharacterizations.Geometry.KingModuli
public import EFiniteCharacterizations.Characterizations.ModuleCriteria

/-! # E-finiteness over an algebraically closed field -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations

variable (k R : Type u) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] [Module.Finite k R]

theorem isEFinite_iff_kingClosedPoints :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    IsEFinite Rᵐᵒᵖ ↔ (basicPresentation k R).KingClosedPointCondition := by
  let P := basicPresentation k R
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  let := IsNoetherianRing.of_finite k P.Carrier
  let := IsArtinianRing.of_finite k P.Carrier
  refine ⟨kingModuli_of_isEFinite k R,fun h ↦ ?_⟩
  apply (isEFinite_iff_of_module_equivalence k k P.equivalence).2
  by_contra hn
  obtain ⟨a,d,ha⟩ := P.vertices.exists_king_counterexample P.algebraBasis hn
  exact ha (h a d)

end EFiniteCharacterizations
