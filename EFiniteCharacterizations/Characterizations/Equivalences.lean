module

public import EFiniteCharacterizations.Geometry.GeometricCriteria
public import EFiniteCharacterizations.LargeModules.GenericGrainCriterion
public import EFiniteCharacterizations.Subcategories.BrickLabels
public import EFiniteCharacterizations.GrothendieckGroups.TorsionMonoidEmbedding
public import EFiniteCharacterizations.Silting.ThickSubcategories.BoundedProjectiveHomotopy

/-!
# Theorem A: Characterizations of E-finite algebras

This file assembles the three parts of Theorem A (`intro:main`) in the right-module
convention (`Rᵐᵒᵖ`) of the manuscript:

* `equivalences_arbitraryField` (**Theorem A(I)**): over an arbitrary field `k`,
  E-finiteness `(E-fin)` is equivalent to each of the seventeen module-theoretic,
  categorical, numerical, homological, and ring-theoretic conditions `(K₀-Hom)`,
  `(mon-dim)`, `(comp-tors)`, `(num-disj)`, `(wide)`, `(wide₁)`, `(brick-label)`,
  `(n-sbrick)`, `(fin-sbrick)`, `(brick-discrete)`, `(endo-stab)`, `(poly-brick)`,
  `(no-gen-brick)`, `(no-gen-grain)`, `(thick-gen)`, `(univ-loc)`, and `(ring-epi)`.
* `equivalences_infiniteField` (**Theorem A(II)**): when `k` is infinite,
  E-finiteness is also equivalent to `(dim-brick)` (Schur-representation-finiteness)
  and `(dim-stab)`.
* `equivalences_algebraicallyClosedField` (**Theorem A(III)**, Theorem 6.1): when `k`
  is algebraically closed, E-finiteness is also equivalent to `(moduli-pt)`,
  `(open-brick)`, and `(open-wide)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra ZeroObject
universe u
namespace EFiniteCharacterizations

variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

/-- **Theorem A(I):** Over an arbitrary field, E-finiteness `(E-fin)` is equivalent to each of
the seventeen conditions `(K₀-Hom)` through `(ring-epi)`, listed in manuscript order. -/
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

/-- **Theorem A(II)** (Corollary 5.4): Over an infinite field, E-finiteness is also equivalent to
finiteness of bricks of each dimension vector `(dim-brick)` and finiteness of `θ`-stable bricks
of each dimension vector `(dim-stab)`. -/
theorem equivalences_infiniteField [Infinite k] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    letI := IsArtinianRing.of_finite k Rᵐᵒᵖ
    (IsEFinite Rᵐᵒᵖ ↔ ∀ d : simpleIsomorphismClasses Rᵐᵒᵖ → ℕ,
      (brickClassesOfClass (classOfCompositionVector k d)).Finite) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ (g : ProjectiveClass Rᵐᵒᵖ) (d : simpleIsomorphismClasses Rᵐᵒᵖ → ℕ),
      (stableClassesOfClass (projectiveClassWeight k g) (classOfCompositionVector k d)).Finite) := by
  obtain ⟨brick,stable,_⟩ := compositionVectorCriteria k R
  exact ⟨brick,stable⟩

/-- **Theorem A(III)** (Theorem 6.1): Over an algebraically closed field, E-finiteness is also
equivalent to `(moduli-pt)` (at most one closed point in each King moduli space), `(open-brick)`
(every brick has an open orbit), and `(open-wide)` (every wide locus is open). -/
theorem equivalences_algebraicallyClosedField [IsAlgClosed k] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    (IsEFinite Rᵐᵒᵖ ↔ (basicPresentation k R).KingClosedPointCondition) ∧
    (IsEFinite Rᵐᵒᵖ ↔ (basicPresentation k R).OpenBrickOrbits) ∧
    (IsEFinite Rᵐᵒᵖ ↔ (basicPresentation k R).OpenWideLoci) := by
  obtain ⟨brick,wide,_⟩ := equivalences_openLoci k R
  exact ⟨isEFinite_iff_kingClosedPoints k R,brick,wide⟩

end EFiniteCharacterizations
