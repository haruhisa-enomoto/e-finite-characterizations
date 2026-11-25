module

public import EFiniteCharacterizations.DivisionRings.FreeAlgebraCommutators
public import EFiniteCharacterizations.DivisionRings.FreeTensorBoundary
public import EFiniteCharacterizations.Modules.TensorCoefficientMaps
public import EFiniteCharacterizations.LargeModules.GrainTorsionPair
public import Mathlib.Algebra.Category.ModuleCat.Injective

/-! # The generic copresentation over a division ring localization -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct

universe u
namespace EFiniteCharacterizations

noncomputable section

variable {k R D n : Type u} [Field k] [Ring R] [Algebra k R] [DivisionRing D] [Algebra k D]
  [Fintype n] {I J : Type u} [AddCommGroup I] [Module k I] [Module R I] [IsScalarTower k R I]
  [AddCommGroup J] [Module k J] [Module R J] [IsScalarTower k R J]

/-- Ground module maps with independent free generators as multiplication operators.
Here the coefficient space is a right division-ring space. -/
def genericCopresentation (h : Module.Basis n k (I →ₗ[R] J)) (g : FreeAlgebra k n →ₐ[k] D) :
    ModuleCat.of R (I ⊗[k] D) ⟶ ModuleCat.of R (J ⊗[k] D) :=
  ModuleCat.ofHom (∑ j, AlgebraTensorModule.map (h j) (LinearMap.mulLeft k (g (FreeAlgebra.ι k j))))

theorem genericCopresentation_rigid_of_commutators [Module.Finite R I] (h : Module.Basis n k (I →ₗ[R] J))
    (g : FreeAlgebra k n →ₐ[k] D)
    (hc : HasSurjectiveCommutators k (fun i ↦ g (FreeAlgebra.ι k i))) :
    ∀ f, ∃ a c, f = a ≫ genericCopresentation h g + genericCopresentation h g ≫ c := by
  intro f
  obtain ⟨b,hb⟩ := exists_tensor_operator_coefficients h f.hom
  obtain ⟨T,hT⟩ := hc b
  refine ⟨ModuleCat.ofHom (AlgebraTensorModule.map LinearMap.id (-T)),
    ModuleCat.ofHom (AlgebraTensorModule.map LinearMap.id T),?_⟩
  apply ModuleCat.hom_ext
  apply AlgebraTensorModule.ext
  intro x v
  change f.hom (x ⊗ₜ[k] v) = _ + _
  rw [hb]
  simp [genericCopresentation, hT, tmul_add, Finset.sum_add_distrib,
    tmul_neg, Finset.sum_neg_distrib,sub_eq_add_neg,add_comm]

theorem genericCopresentation_rigid [Module.Finite R I] (h : Module.Basis n k (I →ₗ[R] J))
    (g : FreeAlgebra k n →ₐ[k] D) {ι : Type*} {φ : ι → TwoTerm (FreeAlgebra k n)}
    (loc : IsUniversalLocalization φ g.toRingHom) :
    ∀ f, ∃ a c, f = a ≫ genericCopresentation h g + genericCopresentation h g ≫ c :=
  genericCopresentation_rigid_of_commutators h g (simultaneous_commutators_of_division_localization g loc)

/-- The actual generic differential has a kernel that splits extensions on
its finitely cogenerated modules. -/
theorem genericCopresentation_kernel_splits [IsNoetherianRing R] [Module.Finite R I]
    (injI : Module.Injective R I) (injJ : Module.Injective R J)
    (h : Module.Basis n k (I →ₗ[R] J)) (g : FreeAlgebra k n →ₐ[k] D)
    {ι : Type*} {φ : ι → TwoTerm (FreeAlgebra k n)} (loc : IsUniversalLocalization φ g.toRingHom) :
    SplitsOnCogeneratedModules k (kernel (genericCopresentation h g)) := by
  let := injective_tensor_vectorSpace (k := k) (D := D) injI
  let := injective_tensor_vectorSpace (k := k) (D := D) injJ
  let := Module.injective_object_of_injective_module R (I ⊗[k] D)
  let := Module.injective_object_of_injective_module R (J ⊗[k] D)
  exact splitsOnCogeneratedModules_kernel_of_rigid k _ (genericCopresentation_rigid h g loc)

end
end EFiniteCharacterizations
