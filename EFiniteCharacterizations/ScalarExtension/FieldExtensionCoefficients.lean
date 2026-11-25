module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionTensorHom

/-! # Changing coefficients on extended modules and their maps -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable {k F L R : Type u} [Field k] [Field F] [Field L] [Ring R]
  [Algebra k F] [Algebra k L] [Algebra k R]

/-- Change the field coefficient of an extended module. -/
def coefficientMap (e : F →ₐ[k] L) (M : FGModuleCat.{u} R) :
    (F ⊗[k] (M : Type u)) →ₗ[k] L ⊗[k] (M : Type u) :=
  TensorProduct.map e.toLinearMap LinearMap.id

@[simp] theorem coefficientMap_tmul (e : F →ₐ[k] L) (M : FGModuleCat.{u} R) (c : F) (x : M) :
    coefficientMap e M (c ⊗ₜ[k] x) = e c ⊗ₜ[k] x :=
  TensorProduct.map_tmul _ _ _ _

theorem coefficientMap_smul (e : F →ₐ[k] L) (M : FGModuleCat.{u} R) (c : F) (x : F ⊗[k] (M : Type u)) :
    coefficientMap e M (c • x) = e c • coefficientMap e M x := by
  refine TensorProduct.inductionOn x ?_ ?_
  · intro a m
    rw [TensorProduct.smul_tmul', coefficientMap_tmul, coefficientMap_tmul, TensorProduct.smul_tmul']
    simp only [smul_eq_mul, map_mul]
  · intro x y hx hy
    rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable [Module.Finite k R]

theorem coefficientMap_ground_smul (e : F →ₐ[k] L) (M : FGModuleCat.{u} R) (r : R)
    (x : extendObj k F R M) :
    coefficientMap e M ((1 ⊗ₜ[k] r : ExtendedAlgebra k F R) • x) =
      (1 ⊗ₜ[k] r : ExtendedAlgebra k L R) • (show extendObj k L R M from coefficientMap e M x) := by
  change F ⊗[k] (M : Type u) at x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro a m
    rw [extendObj_smul_tmul, coefficientMap_tmul, coefficientMap_tmul, extendObj_smul_tmul]
    simp only [one_mul]
  · intro x y hx hy
    let rF : ExtendedAlgebra k F R := 1 ⊗ₜ[k] r
    let rL : ExtendedAlgebra k L R := 1 ⊗ₜ[k] r
    let xF : extendObj k F R M := x
    let yF : extendObj k F R M := y
    let xL : extendObj k L R M := coefficientMap e M x
    let yL : extendObj k L R M := coefficientMap e M y
    change coefficientMap e M (rF • (xF + yF)) =
      rL • (show extendObj k L R M from coefficientMap e M (x + y))
    refine (congrArg (coefficientMap e M) (smul_add rF xF yF)).trans ?_
    refine ((coefficientMap e M).map_add _ _).trans ?_
    exact (congrArg₂ (fun a b : L ⊗[k] (M : Type u) ↦ a + b) hx hy).trans
      ((smul_add rL xL yL).symm.trans
        (congrArg (fun z : (extendObj k L R M : Type u) ↦ rL • z) ((coefficientMap e M).map_add x y).symm))

theorem homTensorMap_tmul_apply {X Y : FGModuleCat.{u} R} (a c : F) (f : X ⟶ Y) (x : X) :
    (homTensorMap k F R X Y (a ⊗ₜ[k] f)).hom.hom (c ⊗ₜ[k] x) =
      (a * c) ⊗ₜ[k] f.hom.hom x := by
  rw [homTensorMap_tmul]
  change (algebraMap F (ExtendedAlgebra k F R) a) • (extendMap k F R f).hom.hom (c ⊗ₜ[k] x) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, extendMap_tmul,
    extendObj_smul_tmul, one_smul]

/-- The change of coefficients commutes with realizing a tensor of maps as
a module homomorphism. -/
theorem coefficientMap_naturality (e : F →ₐ[k] L) {X Y : FGModuleCat.{u} R}
    (f : F ⊗[k] (X ⟶ Y)) (x : F ⊗[k] (X : Type u)) :
    coefficientMap e Y ((homTensorMap k F R X Y f).hom.hom x) =
      (homTensorMap k L R X Y (TensorProduct.map e.toLinearMap LinearMap.id f)).hom.hom
        (coefficientMap e X x) := by
  revert x
  refine TensorProduct.inductionOn f ?_ ?_
  · intro a f x
    rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    refine TensorProduct.inductionOn x ?_ ?_
    · intro c x
      rw [homTensorMap_tmul_apply, coefficientMap_tmul, coefficientMap_tmul, homTensorMap_tmul_apply, map_mul]
    · intro x y hx hy
      let p := (homTensorMap k F R X Y (a ⊗ₜ[k] f)).hom.hom
      let q := (homTensorMap k L R X Y (e a ⊗ₜ[k] f)).hom.hom
      refine (congrArg (coefficientMap e Y) (p.map_add x y)).trans ?_
      refine ((coefficientMap e Y).map_add _ _).trans ?_
      refine (congrArg₂ (fun a b : L ⊗[k] (Y : Type u) ↦ a + b) hx hy).trans ?_
      refine (q.map_add _ _).symm.trans ?_
      exact congrArg q ((coefficientMap e X).map_add x y).symm
  · intro f g hf hg x
    simp only [map_add]
    change coefficientMap e Y
      ((homTensorMap k F R X Y f).hom.hom x + (homTensorMap k F R X Y g).hom.hom x) = _
    exact ((coefficientMap e Y).map_add _ _).trans (congrArg₂ (· + ·) (hf x) (hg x))

end

end EFiniteCharacterizations.FieldExtension
