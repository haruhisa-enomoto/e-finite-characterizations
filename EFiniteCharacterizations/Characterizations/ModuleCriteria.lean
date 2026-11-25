module

public import EFiniteCharacterizations.RingEpimorphisms.GenericEpicTarget
public import EFiniteCharacterizations.RingEpimorphisms.GroundLocalization
public import EFiniteCharacterizations.Silting.Fans.BrickFacets
public import EFiniteCharacterizations.Subcategories.BrickFiltrationEquivalences
public import EFiniteCharacterizations.Subcategories.CompactTorsionEquivalences
public import EFiniteCharacterizations.Stability.EndInvariantSubmodules
public import EFiniteCharacterizations.ScalarExtension.GroundFieldWitnesses
public import EFiniteCharacterizations.Characterizations.HomCharacterizations
public import EFiniteCharacterizations.Stability.PolynomialBrickGrowth
public import EFiniteCharacterizations.Stability.RealWalls
public import EFiniteCharacterizations.Stability.SemistableSimples
public import EFiniteCharacterizations.Stability.SharpBrickGrowth
public import EFiniteCharacterizations.GrothendieckGroups.WideGrothendieckEquivalence
public import EFiniteCharacterizations.Subcategories.WideSubcategories

/-! # Arbitrary-field E-finiteness criteria for right modules -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

/-- Module-theoretic equivalences, with E-finiteness as the reference
condition and all finite module categories taken in the right-module convention. -/
theorem moduleCriteria :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    letI := IsArtinianRing.of_finite k Rᵐᵒᵖ
    (IsEFinite Rᵐᵒᵖ ↔ EqualClassHom (FGModuleCat.{u} Rᵐᵒᵖ)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ EqualClassBrickHom (FGModuleCat.{u} Rᵐᵒᵖ)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ (W : ObjectProperty (FGModuleCat.{u} Rᵐᵒᵖ)) (h : IsWideClass W),
      Function.Injective h.inclusionK₀) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ M : FGModuleCat.{u} Rᵐᵒᵖ, FunctoriallyFinite (generatedTorsionClass M)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ g : ProjectiveClass Rᵐᵒᵖ, (semistableSimpleClasses (C := FGModuleCat.{u} Rᵐᵒᵖ) (projectiveClassWeight (R := Rᵐᵒᵖ) k g)).Finite) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ B : FGModuleCat.{u} Rᵐᵒᵖ, IsBrick B → FunctoriallyFinite (generatedTorsionClass B)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ NumericallyDisjointTorsionPairs (FGModuleCat.{u} Rᵐᵒᵖ)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ W : ObjectProperty (FGModuleCat.{u} Rᵐᵒᵖ), IsWideClass W → FunctoriallyFinite W) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ B : FGModuleCat.{u} Rᵐᵒᵖ, IsBrick B → FunctoriallyFinite (FilteredBy B)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ s : Set (Skeleton (FGModuleCat.{u} Rᵐᵒᵖ)), IsSemibrick s → s.Finite →
      s.ncard = (simpleIsomorphismClasses Rᵐᵒᵖ).ncard → s = simpleIsomorphismClasses Rᵐᵒᵖ) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ s : Set (Skeleton (FGModuleCat.{u} Rᵐᵒᵖ)), IsSemibrick s → s.Finite) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ r : ℕ, 0 < r → (brickClassesOfEndolength (R := Rᵐᵒᵖ) k r).Finite) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ (g : ProjectiveClass Rᵐᵒᵖ) (r : ℕ), 0 < r →
      (stableClassesOfEndolength k (projectiveClassWeight k g) r).Finite) ∧
    (IsEFinite Rᵐᵒᵖ ↔ PolynomialBrickGrowth Rᵐᵒᵖ) ∧
    (IsEFinite Rᵐᵒᵖ ↔ BrickWallFaces (R := Rᵐᵒᵖ) k) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ X Y : FGModuleCat.{u} Rᵐᵒᵖ, IsBrick X → IsBrick Y →
      realStabilityWall k X = realStabilityWall k Y → Nonempty (X ≅ Y)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ¬ ∃ M : ModuleCat.{u} Rᵐᵒᵖ, IsGenericBrick k M) ∧
    (IsEFinite Rᵐᵒᵖ ↔ RightUniversalLocalizationsFinite k R) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ (B : Type u) [Ring B] [IsSimpleRing B] [IsArtinianRing B] (f : R →+* B)
        (hf : IsRingEpimorphism f), letI := hf.targetAlgebra k; Module.Finite k B) := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  let := IsNoetherianRing.of_finite k R
  let := IsArtinianRing.of_finite k R
  have hgen := (isEFinite_iff_opposite (R := R) k).symm.trans
    (FieldExtension.isEFinite_iff_no_generic_right_brick (R := R) k)
  exact ⟨isEFinite_iff_equalClassHom k,
    isEFinite_iff_equalClassBrickHom k,
    isEFinite_iff_injective_wideK₀ k,
    isEFinite_iff_generatedTorsionClass_functoriallyFinite k,
    isEFinite_iff_finite_semistable_simples k,
    isEFinite_iff_brick_generatedTorsionClass_functoriallyFinite k,
    isEFinite_iff_numericallyDisjointTorsionPairs k,
    isEFinite_iff_functoriallyFinite_wideClasses k,
    isEFinite_iff_functoriallyFinite_filteredBy k,
    isEFinite_iff_unique_fullSize_semibrick k,
    isEFinite_iff_finite_semibricks k,
    isEFinite_iff_endo_brick k,
    isEFinite_iff_endo_stab k,
    isEFinite_iff_poly_brick k,
    isEFinite_iff_wall_face k,
    isEFinite_iff_wall_inj k,
    hgen,
    isEFinite_iff_rightUniversalLocalizationsFinite k,
    hgen.trans (no_generic_right_brick_iff_finite_ring_epimorphisms k)⟩

/-- The ordinary composition-vector criteria and brick-continuity over an
infinite field, in the right-module convention. -/
theorem compositionVectorCriteria [Infinite k] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    letI := IsArtinianRing.of_finite k Rᵐᵒᵖ
    (IsEFinite Rᵐᵒᵖ ↔ ∀ d : simpleIsomorphismClasses Rᵐᵒᵖ → ℕ,
      (brickClassesOfClass (classOfCompositionVector k d)).Finite) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ (g : ProjectiveClass Rᵐᵒᵖ) (d : simpleIsomorphismClasses Rᵐᵒᵖ → ℕ),
      (stableClassesOfClass (projectiveClassWeight k g) (classOfCompositionVector k d)).Finite) ∧
    ((∃ r : ℕ, 0 < r ∧ (brickClassesOfEndolength (R := Rᵐᵒᵖ) k r).Infinite) ↔
      ∃ d : simpleIsomorphismClasses Rᵐᵒᵖ → ℕ, (brickClassesOfClass (classOfCompositionVector k d)).Infinite) := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  refine ⟨isEFinite_iff_dim_brick k, isEFinite_iff_dim_stab k, ?_⟩
  rw [← not_isEFinite_iff_infinite_bricks_at_one_vector k, isEFinite_iff_endo_brick k]
  constructor
  · rintro ⟨r,hr,hi⟩ h
    exact hi (h r hr)
  · intro h
    by_contra! hall
    exact h hall

/-- The polynomial and exponential alternatives over a finite field. -/
theorem finiteFieldGrowthDichotomy [Finite k] :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    letI := IsArtinianRing.of_finite k Rᵐᵒᵖ
    (IsEFinite Rᵐᵒᵖ → PolynomialBrickGrowth Rᵐᵒᵖ) ∧
      (¬ IsEFinite Rᵐᵒᵖ → ∃ (c : ℝ) (m₀ : ℕ), 0 < c ∧ ∀ m ≥ m₀,
        ∃ s : Finset (Skeleton (FGModuleCat.{u} Rᵐᵒᵖ)), Real.exp (c * m) ≤ s.card ∧
          ∀ x ∈ s, ∃ M : FGModuleCat.{u} Rᵐᵒᵖ, toSkeleton M = x ∧ IsBrick M ∧ FGModuleCat.moduleLength M ≤ m) := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  exact ⟨polynomialBrickGrowth_of_isEFinite k, FieldExtension.exists_exponential_brick_finsets_of_not_isEFinite k⟩

end EFiniteCharacterizations
