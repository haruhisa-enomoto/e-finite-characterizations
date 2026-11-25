module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionHom
public import EFiniteCharacterizations.Modules.ProjectiveBaseChange

/-! # Comparison of field extension and induction -/

@[expose] public section

open CategoryTheory EFiniteCharacterizations.ScalarInduction
open scoped TensorProduct ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FieldExtension

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R]

local notation "B" => ExtendedAlgebra k F R
local notation "f" => (AlgHom.toRingHom (algebraInclusion k F R))

/-- Induction along the canonical inclusion is tensor-product field extension. -/
noncomputable def inductionIso (M : FGModuleCat.{u} R) :
    FGModuleCat.of B (Induced f M) ≅ extendObj k F R M := by
  letI : Module.Finite R M := M.property
  let N := FGModuleCat.of B (Induced f M)
  let p : M →ₛₗ[f] (extendObj k F R M) :=
    { (TensorProduct.mk k F (M.obj : Type u) 1).toAddHom with
      map_smul' := fun a x ↦ by
        change (1 : F) ⊗ₜ[k] (a • x) = (1 ⊗ₜ[k] a : B) •
          (show extendObj k F R M from 1 ⊗ₜ[k] x)
        exact (one_mul (1 : F) ▸ extendObj_smul_tmul k F R M 1 1 a x).symm }
  let q : (M.obj : Type u) →ₗ[R] ((ModuleCat.restrictScalars f).obj N.obj) :=
    { (unit f M).toAddHom with map_smul' := fun a x ↦ (unit f M).map_smulₛₗ a x }
  let g := extendLinearOfRestrict k F R q
  have hg (x : M) : g.hom.hom ((1 : F) ⊗ₜ[k] x) = unit f M x := by
    exact extendLinearOfRestrict_one_tmul k F R q x
  refine ⟨ObjectProperty.homMk (ModuleCat.ofHom (X := N.obj) (Y := (extendObj k F R M).obj) (lift f p)),g,?_,?_⟩
  · apply FGModuleCat.hom_ext
    apply ScalarInduction.hom_ext
    intro x
    change g.hom.hom (lift f p (unit f M x)) = _
    rw [lift_unit]
    exact hg x
  · apply extend_hom_ext k F R
    intro x
    change lift f p (g.hom.hom (1 ⊗ₜ[k] x)) = _
    rw [hg,lift_unit]
    rfl

@[simp] theorem inductionIso_hom_unit (M : FGModuleCat.{u} R) (x : M) :
    (inductionIso k F R M).hom.hom.hom (unit f M x) = (1 : F) ⊗ₜ[k] x :=
  lift_unit _ _ _

/-- The comparison intertwines the induced differential with its tensor extension. -/
theorem inductionIso_differential (P : TwoTerm R) :
    (P.induce f).differential ≫ (inductionIso k F R P.target).hom =
      (inductionIso k F R P.source).hom ≫ extendMap k F R P.differential := by
  apply FGModuleCat.hom_ext
  apply ScalarInduction.hom_ext
  intro x
  change (inductionIso k F R P.target).hom.hom.hom
      (lift f ((unit f P.target).comp P.differential.hom.hom) (unit f P.source x)) =
    (extendMap k F R P.differential).hom.hom ((inductionIso k F R P.source).hom.hom.hom (unit f P.source x))
  rw [lift_unit]
  change (inductionIso k F R P.target).hom.hom.hom (unit f P.target (P.differential.hom.hom x)) = _
  rw [inductionIso_hom_unit, inductionIso_hom_unit]
  rfl

end EFiniteCharacterizations.FieldExtension
