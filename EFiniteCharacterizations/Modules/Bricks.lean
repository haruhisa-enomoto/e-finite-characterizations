module

public import EFiniteCharacterizations.Modules.CompositionLength

/-! # Bricks, semibricks and equal-class Hom -/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace EFiniteCharacterizations

section ZeroMorphisms

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A nonzero object whose nonzero endomorphisms are invertible. -/
def IsBrick (X : C) : Prop :=
  ¬ IsZero X ∧ ∀ f : X ⟶ X, f ≠ 0 → IsIso f

/-- Every equal nonzero class has a nonzero map in the indicated direction. -/
def EqualClassHom (C : Type u) [Category.{v} C] [HasZeroMorphisms C] : Prop :=
  ∀ X Y : C, GrothendieckGroup.of X = GrothendieckGroup.of Y →
    GrothendieckGroup.of X ≠ 0 → ∃ f : X ⟶ Y, f ≠ 0

/-- Any two bricks with the same class admit a nonzero map in the indicated direction. -/
def EqualClassBrickHom (C : Type u) [Category.{v} C] [HasZeroMorphisms C] : Prop :=
  ∀ X Y : C, IsBrick X → IsBrick Y → GrothendieckGroup.of X = GrothendieckGroup.of Y →
    ∃ f : X ⟶ Y, f ≠ 0

end ZeroMorphisms

theorem equalClassBrickHom_of_equalClassHom {R : Type u} [Ring R] [IsNoetherianRing R]
    [IsArtinianRing R] (h : EqualClassHom (FGModuleCat.{v} R)) : EqualClassBrickHom (FGModuleCat.{v} R) := by
  intro X Y hX _ hclass
  exact h X Y hclass (FGModuleCat.class_ne_zero (R := R) (M := X) hX.1)

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem Weight.IsStable.isBrick {θ : Weight C} {X : C} (h : θ.IsStable X) : IsBrick X :=
  ⟨h.1, fun f hf ↦ Weight.isIso_of_nonzero (C := C) h h f hf⟩

/-- Distinct stable isomorphism classes at one weight are Hom-orthogonal. -/
theorem Weight.hom_eq_zero_of_not_iso {θ : Weight C} {X Y : C}
    (hX : θ.IsStable X) (hY : θ.IsStable Y) (h : ¬ Nonempty (X ≅ Y)) (f : X ⟶ Y) : f = 0 := by
  by_contra hf
  have : IsIso f := Weight.isIso_of_nonzero (C := C) hX hY f hf
  exact h ⟨asIso f⟩

/-- A pair of distinct stable classes of the same Grothendieck class obstructs the brick Hom criterion. -/
theorem Weight.not_equalClassBrickHom {θ : Weight C} {X Y : C}
    (hX : θ.IsStable X) (hY : θ.IsStable Y) (h : ¬ Nonempty (X ≅ Y))
    (hclass : GrothendieckGroup.of X = GrothendieckGroup.of Y) : ¬ EqualClassBrickHom C := by
  intro hHom
  obtain ⟨f, hf⟩ := hHom X Y (Weight.IsStable.isBrick (C := C) hX)
    (Weight.IsStable.isBrick (C := C) hY) hclass
  exact hf (Weight.hom_eq_zero_of_not_iso (C := C) hX hY h f)

end EFiniteCharacterizations
