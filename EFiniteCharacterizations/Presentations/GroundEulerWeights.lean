module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionTensorHom
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionWeights
public import EFiniteCharacterizations.Presentations.RepresentProjectiveClass

/-! # Projective weights under arbitrary field extension -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R]

local notation "B" => ExtendedAlgebra k F R

def extendProjective (P : FiniteProjective R) : FiniteProjective B :=
  letI := P.property
  ⟨extendObj k F R P.val, projective_extendObj k F R P.val⟩

/-- Scalar extension on the split Grothendieck group of projectives. -/
def extendProjectiveClass : ProjectiveClass R →+ ProjectiveClass B :=
  ProjectiveClass.lift (fun P ↦ ProjectiveClass.of (extendProjective k F R P))
    (fun P Q e ↦ ProjectiveClass.of_eq_of_iso _ _ ((extend k F R).mapIso e))
    (fun P Q T e ↦ by
      let forgetR := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
      let e' := forgetR.preimageIso (e.trans (FGModuleCat.forgetBiprodIso P.val Q.val).symm)
      let D := extend k F R
      let : D.Additive := inferInstanceAs (extend k F R).Additive
      let : PreservesBinaryBiproducts D := preservesBinaryBiproducts_of_preservesBinaryProducts D
      exact ProjectiveClass.of_eq_add_of_biprod _ _ _
        (((forget₂ (FGModuleCat.{u} B) (ModuleCat.{u} B)).mapIso
          ((D.mapIso e').trans (D.mapBiprod P.val Q.val))).trans
          (FGModuleCat.forgetBiprodIso _ _)))

@[simp] theorem extendProjectiveClass_of (P : FiniteProjective R) :
    extendProjectiveClass k F R (ProjectiveClass.of P) =
      ProjectiveClass.of (extendProjective k F R P) :=
  ProjectiveClass.lift_of _ _ _ _

@[simp] theorem projectiveClass_extendTwoTerm (P : TwoTerm R) :
    (extendTwoTerm k F R P).projectiveClass = extendProjectiveClass k F R P.projectiveClass := by
  simp only [TwoTerm.projectiveClass, map_sub, extendProjectiveClass_of]
  rfl

private def unitVector (X : FGModuleCat.{u} R) (x : X) : extendObj k F R X :=
  (1 : F) ⊗ₜ[k] x

private def extendRegularIso : extendObj k F R (FGModuleCat.of R R) ≅ FGModuleCat.of B B := by
  let G := FGModuleCat.of R R
  let N := FGModuleCat.of B B
  let M := extendObj k F R G
  let incl := (algebraInclusion k F R).toRingHom
  let p : G.obj →ₗ[R] ((ModuleCat.restrictScalars incl).obj N.obj) :=
    { toFun := incl, map_add' := incl.map_add, map_smul' := incl.map_mul }
  let f := extendLinearOfRestrict k F R p
  let v : M := unitVector k F R G 1
  let g : N ⟶ M := ObjectProperty.homMk (ModuleCat.ofHom (X := N.obj) (Y := M.obj)
    { toFun := fun a ↦ a • v, map_add' := fun _ _ ↦ add_smul ..,
      map_smul' := fun a b ↦ mul_smul a b v })
  have hf (r : R) : f.hom.hom (unitVector k F R G r) = incl r :=
    extendLinearOfRestrict_one_tmul k F R p r
  refine ⟨f,g,?_,?_⟩
  · apply extend_hom_ext k F R
    intro r
    change g.hom.hom (f.hom.hom (unitVector k F R G r)) = _
    rw [hf]
    change (1 ⊗ₜ[k] r : B) • v = _
    exact (one_mul (1 : F) ▸ extendObj_smul_tmul k F R G 1 1 r 1).trans
      ((congrArg (unitVector k F R G) (mul_one r)))
  · apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change f.hom.hom (a • v) = a
    rw [map_smul, show f.hom.hom v = incl 1 from hf 1, map_one]
    exact mul_one a

/-- Scalar extension carries the regular module to the extended regular module. -/
theorem nonempty_extend_regular_iso : Nonempty (extendObj k F R (FGModuleCat.of R R) ≅ FGModuleCat.of B B) :=
  ⟨extendRegularIso k F R⟩

variable [IsNoetherianRing (ExtendedAlgebra k F R)]

/-- An integer combination of an extended Euler weight and dimension is
represented by projective terms extended from the ground field. -/
theorem exists_ground_corrected_weight (P : TwoTerm R) (d e : ℤ) :
    ∃ Q : TwoTerm R, (extendTwoTerm k F R Q).eulerWeight F =
      d • (extendTwoTerm k F R P).eulerWeight F - e • dimensionWeight (R := B) F := by
  let reg : FiniteProjective R := ⟨FGModuleCat.of R R, inferInstance⟩
  let regB : FiniteProjective B := ⟨FGModuleCat.of B B, inferInstance⟩
  obtain ⟨Q,hQ⟩ := ProjectiveClass.exists_twoTerm (d • P.projectiveClass - e • ProjectiveClass.of reg)
  have hr : ProjectiveClass.of (extendProjective k F R reg) = ProjectiveClass.of regB :=
    ProjectiveClass.of_eq_of_iso _ _ (extendRegularIso k F R)
  refine ⟨Q,?_⟩
  rw [← TwoTerm.projectiveClassWeight_eq_eulerWeight, projectiveClass_extendTwoTerm, hQ,
    map_sub, map_zsmul, map_zsmul, extendProjectiveClass_of, hr, map_sub, map_zsmul,
    map_zsmul, ← projectiveClass_extendTwoTerm, TwoTerm.projectiveClassWeight_eq_eulerWeight,
    projectiveClassWeight_of]
  rfl

end

end EFiniteCharacterizations.FieldExtension
