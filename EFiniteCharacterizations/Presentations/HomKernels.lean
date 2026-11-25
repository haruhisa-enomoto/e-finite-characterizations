module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Hom into kernels and out of cokernels -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace EFiniteCharacterizations

variable (k : Type*) [Ring k] {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- Maps out of a cokernel are the kernel of precomposition by the differential. -/
noncomputable def cokernelHomLinearEquiv {X Y : C} (f : X ⟶ Y) [HasCokernel f] (M : C) :
    (cokernel f ⟶ M) ≃ₗ[k] LinearMap.ker (Linear.leftComp k M f) where
  toFun a := ⟨cokernel.π f ≫ a, by
    change f ≫ cokernel.π f ≫ a = 0
    rw [← Category.assoc, cokernel.condition, zero_comp]⟩
  invFun a := cokernel.desc f a.val a.property
  left_inv a := (cancel_epi (cokernel.π f)).mp (cokernel.π_desc _ _ _)
  right_inv a := Subtype.ext (cokernel.π_desc _ _ _)
  map_add' _ _ := Subtype.ext (Preadditive.comp_add _ _ _ _ _ _)
  map_smul' _ _ := Subtype.ext (Linear.comp_smul _ _ _ _ _ _)

/-- Maps into a kernel are the kernel of postcomposition by the differential. -/
noncomputable def homKernelLinearEquiv {X Y : C} (f : X ⟶ Y) [HasKernel f] (M : C) :
    (M ⟶ kernel f) ≃ₗ[k] LinearMap.ker (Linear.rightComp k M f) where
  toFun a := ⟨a ≫ kernel.ι f, by
    change (a ≫ kernel.ι f) ≫ f = 0
    rw [Category.assoc, kernel.condition, comp_zero]⟩
  invFun a := kernel.lift f a.val a.property
  left_inv a := (cancel_mono (kernel.ι f)).mp (kernel.lift_ι _ _ _)
  right_inv a := Subtype.ext (kernel.lift_ι _ _ _)
  map_add' _ _ := Subtype.ext (Preadditive.add_comp _ _ _ _ _ _)
  map_smul' _ _ := Subtype.ext (Linear.smul_comp _ _ _ _ _ _)

end EFiniteCharacterizations
