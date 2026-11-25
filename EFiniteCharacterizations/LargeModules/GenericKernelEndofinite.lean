module

public import EFiniteCharacterizations.LargeModules.GenericCopresentation
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # Endofiniteness of the generic kernel -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct

universe u
namespace EFiniteCharacterizations
noncomputable section

variable {k R D : Type u} [Field k] [Ring R] [Algebra k R] [DivisionRing D] [Algebra k D]
  {I J : Type u} [AddCommGroup I] [Module k I] [Module R I] [IsScalarTower k R I]
  [AddCommGroup J] [Module k J] [Module R J] [IsScalarTower k R J]

/-- Right multiplication on the coefficients commutes with the ground module action. -/
def tensorRightAction : Dᵐᵒᵖ →+* Module.End R (I ⊗[k] D) where
  toFun d := AlgebraTensorModule.map LinearMap.id (LinearMap.mulRight k d.unop)
  map_one' := AlgebraTensorModule.ext fun x y ↦ by simp
  map_mul' a b := AlgebraTensorModule.ext fun x y ↦ by simp [Module.End.mul_apply,mul_assoc]
  map_zero' := AlgebraTensorModule.ext fun x y ↦ by simp
  map_add' a b := AlgebraTensorModule.ext fun x y ↦ by simp [mul_add,tmul_add]

private def flipCoefficients : I ⊗[k] D ≃ₗ[k] Dᵐᵒᵖ ⊗[k] I :=
  (TensorProduct.comm k I D).trans (TensorProduct.congr (MulOpposite.opLinearEquiv k) (.refl k I))

private theorem flipCoefficients_action (d : Dᵐᵒᵖ) (z : I ⊗[k] D) :
    flipCoefficients (tensorRightAction (R := R) d z) = d • flipCoefficients z := by
  induction z with
  | tmul x y => simp [tensorRightAction,flipCoefficients]; rfl
  | add x y hx hy => simp [hx,hy,smul_add]

private theorem genericCopresentation_commutes {n : Type u} [Fintype n]
    (h : Module.Basis n k (I →ₗ[R] J)) (g : FreeAlgebra k n →ₐ[k] D) (d : Dᵐᵒᵖ) :
    ModuleCat.ofHom (tensorRightAction (R := R) d) ≫ genericCopresentation h g =
      genericCopresentation h g ≫ ModuleCat.ofHom (tensorRightAction (R := R) d) := by
  apply ModuleCat.hom_ext
  apply AlgebraTensorModule.ext
  intro x v
  simp [tensorRightAction,genericCopresentation,mul_assoc]

private def kernelAction {A B : ModuleCat.{u} R} (f : A ⟶ B)
    (a : D →+* Module.End R A) (b : D →+* Module.End R B)
    (comm : ∀ d, ModuleCat.ofHom (a d) ≫ f = f ≫ ModuleCat.ofHom (b d)) :
    D →+* Module.End R (kernel f : ModuleCat R) := by
  let act (d : D) := kernel.lift f (kernel.ι f ≫ ModuleCat.ofHom (a d)) (by simp [comm])
  have faith {s t : Module.End R (kernel f : ModuleCat R)}
      (e : ModuleCat.ofHom s ≫ kernel.ι f = ModuleCat.ofHom t ≫ kernel.ι f) : s = t :=
    congrArg ModuleCat.Hom.hom ((cancel_mono (kernel.ι f)).1 e)
  refine
    { toFun := fun d ↦ (act d).hom
      map_one' := faith ?_
      map_mul' := fun d e ↦ faith ?_
      map_zero' := faith ?_
      map_add' := fun d e ↦ faith ?_ }
  · change act 1 ≫ kernel.ι f = 𝟙 _ ≫ _
    simp [act]; rfl
  · change act (d * e) ≫ kernel.ι f = (act e ≫ act d) ≫ _
    simp [act,Category.assoc]; rfl
  · change act 0 ≫ kernel.ι f = 0 ≫ _
    simp [act]
  · change act (d + e) ≫ kernel.ι f = (act d + act e) ≫ _
    simp [act,Preadditive.add_comp,Preadditive.comp_add]

/-- The kernel is finite over the opposite coefficient division ring, since it
embeds into the scalar extension of the finite-dimensional ground source. -/
theorem genericCopresentation_kernel_endofinite [Module.Finite k I] {n : Type u} [Fintype n]
    (h : Module.Basis n k (I →ₗ[R] J)) (g : FreeAlgebra k n →ₐ[k] D) :
    IsEndofinite (kernel (genericCopresentation h g)) := by
  let f := genericCopresentation h g
  let N := kernel f
  let action := kernelAction f (tensorRightAction (k := k)) (tensorRightAction (k := k))
    (genericCopresentation_commutes h g)
  let : Module Dᵐᵒᵖ N := Module.compHom N action
  let : Module Dᵐᵒᵖ (Module.End R N) := Module.compHom _ action
  let : IsScalarTower Dᵐᵒᵖ (Module.End R N) N := ⟨fun _ _ _ ↦ rfl⟩
  let inc : N →ₗ[Dᵐᵒᵖ] Dᵐᵒᵖ ⊗[k] I :=
    { toFun := fun x ↦ flipCoefficients ((kernel.ι f).hom x)
      map_add' := fun x y ↦ by simp
      map_smul' := fun d x ↦ by
        have he := kernel.lift_ι f (kernel.ι f ≫ ModuleCat.ofHom (tensorRightAction (R := R) d))
          (by simp [f,genericCopresentation_commutes])
        have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom he) x
        exact (congrArg flipCoefficients hx).trans (flipCoefficients_action (R := R) d _) }
  let := Module.Finite.of_injective inc (flipCoefficients.injective.comp
    ((ModuleCat.mono_iff_injective (kernel.ι f)).mp inferInstance))
  exact isEndofinite_of_scalar_tower N Dᵐᵒᵖ

end
end EFiniteCharacterizations
