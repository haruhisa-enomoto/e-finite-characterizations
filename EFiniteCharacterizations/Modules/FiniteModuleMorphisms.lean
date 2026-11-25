/-
Adapted from the pretorsion-image-closed formalization,
PretorsionImageClosed.Modules.FiniteModules
(commit e6e95f6c295649bccf0ca476c9a5b008320e9443, Apache 2.0).
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Monomorphisms, epimorphisms and zero objects of finitely generated modules

For a Noetherian ring `R`, a morphism of `FGModuleCat R` is a monomorphism iff
it is injective, an epimorphism iff it is surjective, and an isomorphism iff it
is bijective; an object is zero iff its carrier is a subsingleton. These
transfer the corresponding facts about `ModuleCat R` along the forgetful
functor, which is fully faithful and preserves finite limits and colimits.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace EFiniteCharacterizations

open CategoryTheory Limits

namespace FGModuleCat

variable {R : Type*} [Ring R] [IsNoetherianRing R]

theorem mono_iff_injective {X Y : FGModuleCat R} (f : X ⟶ Y) : Mono f ↔ Function.Injective f.hom.hom := by
  constructor
  · intro hf
    have : Mono ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 this
  · intro hf
    have : Mono ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) :=
      (ModuleCat.mono_iff_injective _).2 hf
    exact (forget₂ (FGModuleCat R) (ModuleCat R)).mono_of_mono_map this

omit [IsNoetherianRing R] in
theorem epi_iff_surjective {X Y : FGModuleCat R} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f.hom.hom := by
  constructor
  · intro hf
    have : Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) := inferInstance
    exact (ModuleCat.epi_iff_surjective _).1 this
  · intro hf
    have : Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) :=
      (ModuleCat.epi_iff_surjective _).2 hf
    exact (forget₂ (FGModuleCat R) (ModuleCat R)).epi_of_epi_map this

omit [IsNoetherianRing R] in
/-- A morphism out of a finite projective lifts along an epimorphism. -/
theorem exists_lift_of_projective {X Y Z : FGModuleCat R} [Module.Projective R X]
    (g : Y ⟶ Z) [Epi g] (f : X ⟶ Z) : ∃ h : X ⟶ Y, h ≫ g = f := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property g.hom.hom f.hom.hom
    ((epi_iff_surjective g).mp inferInstance)
  exact ⟨FGModuleCat.ofHom h, FGModuleCat.hom_ext hh⟩

theorem isIso_iff_bijective {X Y : FGModuleCat R} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f.hom.hom := by
  constructor
  · intro hf
    exact ⟨(mono_iff_injective f).1 inferInstance, (epi_iff_surjective f).1 inferInstance⟩
  · rintro ⟨hi, hs⟩
    have := (mono_iff_injective f).2 hi
    have := (epi_iff_surjective f).2 hs
    exact isIso_of_mono_of_epi f

omit [IsNoetherianRing R] in
theorem isZero_iff_subsingleton (X : FGModuleCat R) : IsZero X ↔ Subsingleton X := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    refine ⟨fun x y => ?_⟩
    have hx : x = 0 := congrArg (fun g : X ⟶ X => g.hom.hom x) h
    have hy : y = 0 := congrArg (fun g : X ⟶ X => g.hom.hom y) h
    rw [hx, hy]
  · intro h
    ext x
    exact Subsingleton.elim _ _

end FGModuleCat

end EFiniteCharacterizations
