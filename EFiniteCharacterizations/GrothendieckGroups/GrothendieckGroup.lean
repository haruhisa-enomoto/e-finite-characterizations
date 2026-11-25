module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # Grothendieck groups of abelian categories -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

namespace EFiniteCharacterizations

section ZeroMorphisms

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- The relations imposed by short exact sequences. -/
def exactRelations : AddSubgroup (FreeAbelianGroup C) :=
  AddSubgroup.closure
    {r | ∃ S : ShortComplex C, S.ShortExact ∧
      r = FreeAbelianGroup.of S.X₂ - (FreeAbelianGroup.of S.X₁ + FreeAbelianGroup.of S.X₃)}

/-- The Grothendieck group with respect to short exact sequences. -/
abbrev GrothendieckGroup :=
  FreeAbelianGroup C ⧸ exactRelations C

namespace GrothendieckGroup

variable {C}

/-- The class of an object. -/
def of (X : C) : GrothendieckGroup C :=
  QuotientAddGroup.mk (FreeAbelianGroup.of X)

theorem of_shortExact (S : ShortComplex C) (hS : S.ShortExact) :
    of S.X₂ = of S.X₁ + of S.X₃ := by
  apply sub_eq_zero.mp
  change QuotientAddGroup.mk' (exactRelations C)
    (FreeAbelianGroup.of S.X₂ - (FreeAbelianGroup.of S.X₁ + FreeAbelianGroup.of S.X₃)) = 0
  exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.subset_closure ⟨S, hS, rfl⟩)

/-- An additive invariant of short exact sequences defines a homomorphism on the group. -/
def lift {G : Type*} [AddCommGroup G] (f : C → G)
    (hf : ∀ S : ShortComplex C, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃) :
    GrothendieckGroup C →+ G :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift f) <| by
    rw [exactRelations, AddSubgroup.closure_le]
    rintro _ ⟨S, hS, rfl⟩
    simp [hf S hS]

@[simp] theorem lift_of {G : Type*} [AddCommGroup G] (f : C → G)
    (hf : ∀ S : ShortComplex C, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃) (X : C) :
    lift f hf (of X) = f X := by
  simp [lift, of]

/-- The map induced by an exact functor. -/
def map {D : Type*} [Category D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (hF : ∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact) :
    GrothendieckGroup C →+ GrothendieckGroup D :=
  lift (fun X ↦ of (F.obj X)) (fun S hS ↦ of_shortExact (S.map F) (hF S hS))

end GrothendieckGroup

end ZeroMorphisms

namespace GrothendieckGroup

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem of_isZero {X : C} (hX : IsZero X) : GrothendieckGroup.of X = 0 := by
  let S := ShortComplex.mk (𝟙 X) (𝟙 X) (hX.eq_of_src _ _)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    ((S.exact_iff_mono (hX.eq_of_src _ _)).2 (by dsimp [S]; infer_instance))
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  have h : GrothendieckGroup.of X = GrothendieckGroup.of X + GrothendieckGroup.of X :=
    GrothendieckGroup.of_shortExact S hS
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

theorem of_eq_of_iso {X Y : C} (e : X ≅ Y) :
    GrothendieckGroup.of X = GrothendieckGroup.of Y := by
  let S := ShortComplex.mk (0 : (0 : C) ⟶ X) e.hom (zero_comp)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    ((S.exact_iff_mono rfl).2 (by dsimp [S]; infer_instance))
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  have h : GrothendieckGroup.of X = GrothendieckGroup.of (0 : C) + GrothendieckGroup.of Y :=
    GrothendieckGroup.of_shortExact S hS
  simpa only [GrothendieckGroup.of_isZero (isZero_zero C), zero_add] using h

end GrothendieckGroup

end EFiniteCharacterizations
