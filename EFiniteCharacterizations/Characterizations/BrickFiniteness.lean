module

public import EFiniteCharacterizations.Characterizations.ModuleCriteria

/-! # Brick-continuity, the seven pointwise implications, and finite-field growth -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

theorem brickContinuous_iff_exists_generic_right_brick :
    (∃ r : ℕ, 0 < r ∧ (brickClassesOfEndolength (R := Rᵐᵒᵖ) k r).Infinite) ↔
      ∃ M : ModuleCat.{u} Rᵐᵒᵖ, IsGenericBrick k M := by
  classical
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hd,_,_,_,_,hg,_,_⟩ := moduleCriteria k R
  simpa only [not_forall, exists_prop, Classical.not_imp, not_not, Set.Infinite] using
    (hd.symm.trans hg).not

/-- For a fixed algebra all seven hypotheses in the introduction yield
equivalent implications to brick-finiteness. -/
theorem seven_pointwise_implications :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    let C := FGModuleCat.{u} Rᵐᵒᵖ
    let conclusion := (brickClasses (C := C)).Finite
    let demonet := IsEFinite Rᵐᵒᵖ → conclusion
    (demonet ↔ ((∀ s : Set (Skeleton C), IsSemibrick s → s.Finite) → conclusion)) ∧
    (demonet ↔ ((∀ s : Set (Skeleton C), IsSemibrick s → s.Finite →
      s.ncard = (simpleIsomorphismClasses Rᵐᵒᵖ).ncard → s = simpleIsomorphismClasses Rᵐᵒᵖ) → conclusion)) ∧
    (demonet ↔ ((∀ r : ℕ, 0 < r → (brickClassesOfEndolength (R := Rᵐᵒᵖ) k r).Finite) → conclusion)) ∧
    (demonet ↔ ((¬ ∃ M : ModuleCat.{u} Rᵐᵒᵖ, IsGenericBrick k M) → conclusion)) ∧
    (demonet ↔ ((∀ (g : ProjectiveClass Rᵐᵒᵖ) (r : ℕ), 0 < r →
      (stableClassesOfEndolength k (projectiveClassWeight k g) r).Finite) → conclusion)) ∧
    (demonet ↔ ((∀ W : ObjectProperty C, IsWideClass W → FunctoriallyFinite W) → conclusion)) := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  obtain ⟨_,_,_,_,_,_,_,w,_,n,s,d,t,_,_,_,g,_,_⟩ := moduleCriteria k R
  exact ⟨imp_congr s Iff.rfl, imp_congr n Iff.rfl, imp_congr d Iff.rfl,
    imp_congr g Iff.rfl, imp_congr t Iff.rfl, imp_congr w Iff.rfl⟩

theorem finiteField_exponential_bricks_by_dimension [Finite k] (h : ¬ IsEFinite Rᵐᵒᵖ) :
    ∃ (c : ℝ) (m₀ : ℕ), 0 < c ∧ ∀ m ≥ m₀,
      ∃ s : Finset (Skeleton (FGModuleCat.{u} Rᵐᵒᵖ)), Real.exp (c * m) ≤ s.card ∧
        ∀ x ∈ s, ∃ M : FGModuleCat.{u} Rᵐᵒᵖ, toSkeleton M = x ∧ IsBrick M ∧
          Module.finrank k (M.obj : Type u) ≤ m := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  obtain ⟨P, hp⟩ := FieldExtension.exists_missing_terms k h
  obtain ⟨_, c, m₀, hc, hg⟩ := FieldExtension.exists_exponential_ground_witnesses k P hp
  refine ⟨c, m₀, hc, fun m hm ↦ ?_⟩
  obtain ⟨s, hs, hmem⟩ := hg m hm
  refine ⟨s, hs, fun x hx ↦ ?_⟩
  obtain ⟨M, _, he, _, hst, hl, _⟩ := hmem x hx
  exact ⟨M, he, hst.isBrick, hl⟩

end EFiniteCharacterizations
