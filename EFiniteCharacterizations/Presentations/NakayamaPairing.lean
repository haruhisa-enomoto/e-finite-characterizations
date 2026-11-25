module

public import EFiniteCharacterizations.Presentations.NakayamaKernel

/-! # Nakayama duality on finite module morphisms -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]

variable [Module.Finite k R]

/-- Regard algebra-linear maps into a Nakayama module as maps between finite modules. -/
noncomputable def nakayamaTargetHomEquiv (P M : FGModuleCat.{u} R) :
    ((M.obj : Type u) →ₗ[R] NakayamaModule k R (P.obj : Type u)) ≃ₗ[k]
      (M ⟶ nakayamaObject k P) where
  toFun f := ObjectProperty.homMk (ModuleCat.ofHom f)
  invFun f := f.hom.hom
  left_inv _ := rfl
  right_inv f := FGModuleCat.hom_ext rfl
  map_add' _ _ := rfl
  map_smul' c f := by
    apply FGModuleCat.hom_ext
    ext x
    exact (IsScalarTower.algebraMap_smul R c (f x)).symm

/-- The categorical pairing on Hom from a finite projective module. -/
noncomputable def nakayamaPairing (P M : FGModuleCat.{u} R) [Module.Projective R P] :
    Module.Dual k (P ⟶ M) ≃ₗ[k] (M ⟶ nakayamaObject k P) := by
  have : Module.Finite R (P.obj : Type u) := P.property
  have : Module.Projective R (P.obj : Type u) := ‹Module.Projective R P›
  exact ((finiteModuleHomLinearEquiv k P M).symm.dualMap.trans
    (nakayamaHomEquiv k R (P.obj : Type u) (M.obj : Type u))).trans
    (nakayamaTargetHomEquiv k P M)

theorem nakayamaPairing_dual_leftComp {P Q M : FGModuleCat.{u} R}
    [Module.Projective R P] [Module.Projective R Q] (f : P ⟶ Q)
    (χ : Module.Dual k (P ⟶ M)) :
    nakayamaPairing k Q M ((Linear.leftComp k M f).dualMap χ) =
      nakayamaPairing k P M χ ≫ nakayamaMorphism k f := by
  have : Module.Finite R (P.obj : Type u) := P.property
  have : Module.Finite R (Q.obj : Type u) := Q.property
  have : Module.Projective R (P.obj : Type u) := ‹Module.Projective R P›
  have : Module.Projective R (Q.obj : Type u) := ‹Module.Projective R Q›
  apply FGModuleCat.hom_ext
  let eP := finiteModuleHomLinearEquiv k P M
  let eQ := finiteModuleHomLinearEquiv k Q M
  let χP := eP.symm.dualMap χ
  change nakayamaHomEquiv k R (Q.obj : Type u) (M.obj : Type u)
      (eQ.symm.dualMap ((Linear.leftComp k M f).dualMap χ)) =
    (f.hom.hom.nakayamaMap (k := k)).comp
      (nakayamaHomEquiv k R (P.obj : Type u) (M.obj : Type u) χP)
  rw [← nakayamaHomEquiv_dualMap_lcomp k R f.hom.hom χP]
  congr 1

theorem nakayamaPairing_dual_rightComp {P M N : FGModuleCat.{u} R}
    [Module.Projective R P] (f : M ⟶ N) (χ : Module.Dual k (P ⟶ N)) :
    nakayamaPairing k P M ((Linear.rightComp k P f).dualMap χ) =
      f ≫ nakayamaPairing k P N χ := by
  have : Module.Finite R (P.obj : Type u) := P.property
  have : Module.Projective R (P.obj : Type u) := ‹Module.Projective R P›
  apply FGModuleCat.hom_ext
  let eM := finiteModuleHomLinearEquiv k P M
  let eN := finiteModuleHomLinearEquiv k P N
  let χN := eN.symm.dualMap χ
  change nakayamaHomEquiv k R (P.obj : Type u) (M.obj : Type u)
      (eM.symm.dualMap ((Linear.rightComp k P f).dualMap χ)) =
    (nakayamaHomEquiv k R (P.obj : Type u) (N.obj : Type u) χN).comp f.hom.hom
  rw [← nakayamaHomEquiv_dualMap_compRight k R f.hom.hom χN]
  congr 1

end EFiniteCharacterizations
