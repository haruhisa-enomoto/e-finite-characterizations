module

public import EFiniteCharacterizations.ScalarExtension.FieldExtension
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Coordinates of a scalar extension after restriction -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F]

/-- Choose a basis of the extension field to identify restriction of a
scalar-extended module with a finite power of that module. -/
def restrictExtendBasisEquiv {n : ℕ} (b : Module.Basis (Fin n) k F) (M : FGModuleCat.{u} R) :
    restrictObj k F R (extendObj k F R M) ≃ₗ[R] (Fin n → M) := by
  let e : F ⊗[k] (M.obj : Type u) ≃ₗ[k] (Fin n → M) :=
    (TensorProduct.comm k F (M.obj : Type u)).trans
      ((TensorProduct.congr (LinearEquiv.refl k (M.obj : Type u)) b.equivFun).trans
        (TensorProduct.piScalarRight k k (M.obj : Type u) (Fin n)))
  have he (c : F) (m : M) : e (c ⊗ₜ[k] m) = fun i ↦ b.equivFun c i • m := by
    simp only [e, LinearEquiv.trans_apply, TensorProduct.comm_tmul, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  refine { e.toEquiv with map_add' := e.map_add, map_smul' := ?_ }
  intro r z
  let a : (F ⊗[k] (M.obj : Type u)) →+ (F ⊗[k] (M.obj : Type u)) :=
    { toFun := fun z ↦ r • (show restrictObj k F R (extendObj k F R M) from z)
      map_add' := fun x y ↦ smul_add r (show restrictObj k F R (extendObj k F R M) from x)
        (show restrictObj k F R (extendObj k F R M) from y)
      map_zero' := by
        change r • (0 : restrictObj k F R (extendObj k F R M)) = 0
        exact smul_zero r }
  change F ⊗[k] (M.obj : Type u) at z
  change e (a z) = r • e z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro c m
    have h : a (c ⊗ₜ[k] m) = c ⊗ₜ[k] (r • m) := by
      change (1 ⊗ₜ[k] r : ExtendedAlgebra k F R) •
        (show extendObj k F R M from c ⊗ₜ[k] m) = c ⊗ₜ[k] (r • m)
      simpa only [one_mul] using extendObj_smul_tmul k F R M 1 c r m
    rw [h, he, he]
    funext i
    exact smul_comm _ _ _
  · intro z w hz hw
    rw [map_add, map_add, map_add, hz, hw, smul_add]

@[simp] theorem restrictExtendBasisEquiv_tmul {n : ℕ} (b : Module.Basis (Fin n) k F)
    (M : FGModuleCat.{u} R) (c : F) (m : M) :
    restrictExtendBasisEquiv k F R b M (c ⊗ₜ[k] m) = fun i ↦ b.equivFun c i • m := by
  change ((TensorProduct.comm k F (M.obj : Type u)).trans
    ((TensorProduct.congr (LinearEquiv.refl k (M.obj : Type u)) b.equivFun).trans
      (TensorProduct.piScalarRight k k (M.obj : Type u) (Fin n)))) (c ⊗ₜ[k] m) = _
  simp only [LinearEquiv.trans_apply, TensorProduct.comm_tmul, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

end

end EFiniteCharacterizations.FieldExtension
