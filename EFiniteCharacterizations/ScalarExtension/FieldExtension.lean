module

public import EFiniteCharacterizations.Modules.FiniteModuleMorphisms
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Extension and restriction for finite modules under ground field extension -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]

/-- Extension of the ground field of an algebra, with the field factor first. -/
abbrev ExtendedAlgebra := F ⊗[k] R

/-- The ground and extension field actions on a module over the extended
algebra form a scalar tower. -/
theorem isScalarTower_ground_extension (N : ModuleCat.{u} (ExtendedAlgebra k F R)) :
    IsScalarTower k F N :=
  IsScalarTower.of_algebraMap_smul (fun c n ↦ by
    change (algebraMap F (ExtendedAlgebra k F R) (algebraMap k F c)) • n =
      (algebraMap k (ExtendedAlgebra k F R) c) • n
    rw [← IsScalarTower.algebraMap_apply k F (ExtendedAlgebra k F R)])

/-- The extension of the original algebra action to the scalar-extended
underlying vector space. -/
def representation (M : FGModuleCat.{u} R) :
    ExtendedAlgebra k F R →ₐ[F] Module.End F (F ⊗[k] (M.obj : Type u)) :=
  Algebra.TensorProduct.lift (Algebra.ofId F _)
    ((Module.End.baseChangeHom k F (M.obj : Type u)).comp (Algebra.lsmul k k (M.obj : Type u)))
    (fun c _f ↦ Algebra.commutes c _)

/-- The module structure induced by scalar extension of the action. -/
abbrev extendedModule (M : FGModuleCat.{u} R) :
    Module (ExtendedAlgebra k F R) (F ⊗[k] (M.obj : Type u)) :=
  Module.compHom _ (representation k F R M).toRingHom

theorem representation_tmul (M : FGModuleCat.{u} R) (c : F) (r : R) (z : F ⊗[k] (M.obj : Type u)) :
    representation k F R M (c ⊗ₜ[k] r) z =
      c • ((Algebra.lsmul k k (M.obj : Type u)) r).baseChange F z := by
  change ((algebraMap F (Module.End F (F ⊗[k] (M.obj : Type u))) c) *
    ((Algebra.lsmul k k (M.obj : Type u)) r).baseChange F) z = _
  rw [Module.End.mul_eq_comp, LinearMap.comp_apply, Algebra.algebraMap_eq_smul_one,
    LinearMap.smul_apply, Module.End.one_apply]

variable [Module.Finite k R]

/-- Extend a finite module to the larger ground field. -/
def extendObj (M : FGModuleCat.{u} R) : FGModuleCat.{u} (ExtendedAlgebra k F R) := by
  let _ := extendedModule k F R M
  have : IsScalarTower F (ExtendedAlgebra k F R) (F ⊗[k] (M.obj : Type u)) :=
    IsScalarTower.of_algebraMap_smul (fun c z ↦ congrArg (fun g : Module.End F (F ⊗[k] (M.obj : Type u)) ↦ g z)
      ((representation k F R M).commutes c))
  have : Module.Finite R (M.obj : Type u) := M.property
  have : Module.Finite k (M.obj : Type u) := Module.Finite.trans R _
  have : Module.Finite F (F ⊗[k] (M.obj : Type u)) := inferInstance
  have : Module.Finite (ExtendedAlgebra k F R) (F ⊗[k] (M.obj : Type u)) :=
    Module.Finite.of_restrictScalars_finite F _ _
  exact FGModuleCat.of (ExtendedAlgebra k F R) (F ⊗[k] (M.obj : Type u))

@[simp] theorem extendObj_smul_tmul (M : FGModuleCat.{u} R) (a c : F) (r : R) (m : M) :
    (a ⊗ₜ[k] r : ExtendedAlgebra k F R) •
      (show extendObj k F R M from c ⊗ₜ[k] m) = (a * c) ⊗ₜ[k] (r • m) := by
  change representation k F R M (a ⊗ₜ[k] r) (c ⊗ₜ[k] m) = (a * c) ⊗ₜ[k] (r • m)
  rw [representation_tmul, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  rfl

/-- The scalar extension of a module map. -/
def extendMap {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    extendObj k F R M ⟶ extendObj k F R N := by
  let g := (f.hom.hom.restrictScalars k).baseChange F
  refine ObjectProperty.homMk (ModuleCat.ofHom (X := (extendObj k F R M).obj)
    (Y := (extendObj k F R N).obj) { g.toAddHom with map_smul' := ?_ })
  intro x z
  change F ⊗[k] (M.obj : Type u) at z
  change g ((representation k F R M x) z) = (representation k F R N x) (g z)
  refine TensorProduct.inductionOn x ?_ ?_
  · intro c r
    refine TensorProduct.inductionOn z ?_ ?_
    · intro a m
      simp only [g, representation_tmul, LinearMap.baseChange_tmul, TensorProduct.smul_tmul',
        Algebra.lsmul_coe, LinearMap.restrictScalars_apply, map_smul]
    · intro z w hz hw
      simp only [map_add, hz, hw]
  · intro x y hx hy
    simp only [map_add, LinearMap.add_apply, hx, hy]

@[simp] theorem extendMap_tmul {M N : FGModuleCat.{u} R} (f : M ⟶ N) (c : F) (m : M) :
    (extendMap k F R f).hom.hom (c ⊗ₜ[k] m) = c ⊗ₜ[k] (f.hom.hom m) := rfl

/-- Extend finite modules and their maps to the larger ground field. -/
def extend : FGModuleCat.{u} R ⥤ FGModuleCat.{u} (ExtendedAlgebra k F R) where
  obj := extendObj k F R
  map f := extendMap k F R f
  map_id M := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change F ⊗[k] (M.obj : Type u) at z
    change ((LinearMap.id : (M.obj : Type u) →ₗ[k] M.obj).baseChange F) z = z
    simp only [LinearMap.baseChange_id, LinearMap.id_apply]
  map_comp {M N P} f g := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change F ⊗[k] (M.obj : Type u) at z
    let f' := f.hom.hom.restrictScalars k
    let g' := g.hom.hom.restrictScalars k
    change ((g'.comp f').baseChange F) z = (g'.baseChange F) ((f'.baseChange F) z)
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply]

variable [Module.Finite k F]

/-- The original algebra maps to the ground field extension by (rmapsto 1otimes r). -/
def algebraInclusion : R →ₐ[k] ExtendedAlgebra k F R :=
  Algebra.TensorProduct.includeRight

/-- The underlying ground vector space is unchanged by restriction. -/
def restrictVectorSpaceEquiv (M : ModuleCat.{u} (ExtendedAlgebra k F R)) :
    ((ModuleCat.restrictScalars (algebraInclusion k F R).toRingHom).obj M) ≃ₗ[k] M where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl
  map_smul' c x := by
    change algebraInclusion k F R (algebraMap k R c) • x =
      algebraMap k (ExtendedAlgebra k F R) c • x
    rw [AlgHom.commutes]

/-- Restriction keeps the additive group and restricts the action along
the inclusion of the original algebra. -/
def restrictObj (M : FGModuleCat.{u} (ExtendedAlgebra k F R)) : FGModuleCat.{u} R := by
  let M' := (ModuleCat.restrictScalars (algebraInclusion k F R).toRingHom).obj M.obj
  have : Module.Finite (ExtendedAlgebra k F R) (M.obj : Type u) := M.property
  have : Module.Finite k (M.obj : Type u) := Module.Finite.trans (ExtendedAlgebra k F R) _
  let e := restrictVectorSpaceEquiv k F R M.obj
  have : Module.Finite k M' := Module.Finite.equiv e.symm
  have : Module.Finite R M' := Module.Finite.of_restrictScalars_finite k R M'
  exact FGModuleCat.of R M'

/-- Restriction of scalars from a finite ground field extension. -/
def restrict : FGModuleCat.{u} (ExtendedAlgebra k F R) ⥤ FGModuleCat.{u} R where
  obj := restrictObj k F R
  map f := ObjectProperty.homMk
    ((ModuleCat.restrictScalars (algebraInclusion k F R).toRingHom).map f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

end

end EFiniteCharacterizations.FieldExtension
