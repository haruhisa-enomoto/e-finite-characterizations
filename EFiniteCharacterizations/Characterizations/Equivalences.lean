module

public import EFiniteCharacterizations.Geometry.GeometricCriteria
public import EFiniteCharacterizations.LargeModules.GenericGrainCriterion
public import EFiniteCharacterizations.Subcategories.BrickLabels
public import EFiniteCharacterizations.GrothendieckGroups.TorsionMonoidEmbedding
public import EFiniteCharacterizations.Silting.ThickSubcategories.BoundedProjectiveHomotopy

/-! # Characterizations of E-finiteness -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra ZeroObject
universe u
namespace EFiniteCharacterizations

variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

/-- The seventeen tests over an arbitrary field, in the order of the manuscript. -/
theorem equivalences_arbitraryField :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    letI := IsArtinianRing.of_finite k Rᵐᵒᵖ
    (IsEFinite Rᵐᵒᵖ ↔ EqualClassHom (FGModuleCat.{u} Rᵐᵒᵖ)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ T : ObjectProperty (FGModuleCat.{u} Rᵐᵒᵖ),
      T.IsClosedUnderQuotients → T.IsClosedUnderExtensions → T 0 →
      Function.Injective (GrothendieckMonoid.dimensionMap T)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ M : FGModuleCat.{u} Rᵐᵒᵖ, FunctoriallyFinite (generatedTorsionClass M)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ NumericallyDisjointTorsionPairs (FGModuleCat.{u} Rᵐᵒᵖ)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ W : ObjectProperty (FGModuleCat.{u} Rᵐᵒᵖ), IsWideClass W → FunctoriallyFinite W) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ B : FGModuleCat.{u} Rᵐᵒᵖ, IsBrick B → FunctoriallyFinite (FilteredBy B)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ BrickLabels Rᵐᵒᵖ) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ s : Set (Skeleton (FGModuleCat.{u} Rᵐᵒᵖ)), IsSemibrick s → s.Finite →
      s.ncard = (simpleIsomorphismClasses Rᵐᵒᵖ).ncard → s = simpleIsomorphismClasses Rᵐᵒᵖ) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ s : Set (Skeleton (FGModuleCat.{u} Rᵐᵒᵖ)), IsSemibrick s → s.Finite) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ r : ℕ, 0 < r → (brickClassesOfEndolength (R := Rᵐᵒᵖ) k r).Finite) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ (g : ProjectiveClass Rᵐᵒᵖ) (r : ℕ), 0 < r →
      (stableClassesOfEndolength k (projectiveClassWeight k g) r).Finite) ∧
    (IsEFinite Rᵐᵒᵖ ↔ PolynomialBrickGrowth Rᵐᵒᵖ) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ¬ ∃ M : ModuleCat.{u} Rᵐᵒᵖ, IsGenericBrick k M) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ¬ ∃ M : ModuleCat.{u} Rᵐᵒᵖ, IsGenericGrain k M) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ H : TwoTerm Rᵐᵒᵖ → Prop, TwoTerm.IsBoundedTwoTermThick H →
      ∃ U : TwoTerm Rᵐᵒᵖ, U.IsPresilting ∧ ∀ X : TwoTerm Rᵐᵒᵖ,
        H X ↔ (ObjectProperty.singleton U.inBoundedProjectives).triangEnvelope X.inBoundedProjectives) ∧
    (IsEFinite Rᵐᵒᵖ ↔ RightUniversalLocalizationsFinite k R) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ (B : Type u) [Ring B] [IsSimpleRing B] [IsArtinianRing B] (f : R →+* B)
      (hf : IsRingEpimorphism f), letI := hf.targetAlgebra k; Module.Finite k B) := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  obtain ⟨hom,_,_,compact,_,_,disjoint,wide,oneWide,fullSize,semibrick,endoBrick,endoStable,
    growth,_,_,brick,localization,epic⟩ := moduleCriteria k R
  exact ⟨hom,isEFinite_iff_injective_torsionMonoid k,compact,disjoint,wide,oneWide,
    isEFinite_iff_brickLabels k,fullSize,semibrick,endoBrick,endoStable,growth,brick,
    isEFinite_iff_no_genericGrain k,isEFinite_iff_boundedProjectiveThickGeneration k,localization,epic⟩

/-- The two additional dimension-vector tests over an infinite field. -/
theorem equivalences_infiniteField [Infinite k] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    letI := IsArtinianRing.of_finite k Rᵐᵒᵖ
    (IsEFinite Rᵐᵒᵖ ↔ ∀ d : simpleIsomorphismClasses Rᵐᵒᵖ → ℕ,
      (brickClassesOfClass (classOfCompositionVector k d)).Finite) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ (g : ProjectiveClass Rᵐᵒᵖ) (d : simpleIsomorphismClasses Rᵐᵒᵖ → ℕ),
      (stableClassesOfClass (projectiveClassWeight k g) (classOfCompositionVector k d)).Finite) := by
  obtain ⟨brick,stable,_⟩ := compositionVectorCriteria k R
  exact ⟨brick,stable⟩

/-- The three geometric tests over an algebraically closed field. -/
theorem equivalences_algebraicallyClosedField [IsAlgClosed k] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    (IsEFinite Rᵐᵒᵖ ↔ (basicPresentation k R).KingClosedPointCondition) ∧
    (IsEFinite Rᵐᵒᵖ ↔ (basicPresentation k R).OpenBrickOrbits) ∧
    (IsEFinite Rᵐᵒᵖ ↔ (basicPresentation k R).OpenWideLoci) := by
  obtain ⟨brick,wide,_⟩ := equivalences_openLoci k R
  exact ⟨isEFinite_iff_kingClosedPoints k R,brick,wide⟩

end EFiniteCharacterizations
