module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionWeights
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-! # Scalar extension of finite modules in a tower of fields -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable {k A B : Type u} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

theorem isFG_restrict_equiv (e : A ≃+* B) :
    (ModuleCat.isFG.{u} A).inverseImage (ModuleCat.restrictScalars e.toRingHom) = ModuleCat.isFG B := by
  ext M
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  let v : N →ₛₗ[e.toRingHom] M :=
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let _ : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  exact v.finite_iff_of_bijective Function.bijective_id

/-- Transport finite modules along an isomorphism of algebras by restriction of scalars. -/
def restrictAlgEquivalence (e : A ≃ₐ[k] B) : FGModuleCat.{u} B ≌ FGModuleCat.{u} A := by
  let _ : (ModuleCat.isFG.{u} A).IsClosedUnderIsomorphisms :=
    ⟨fun {X Y} f hf ↦ (Module.Finite.equiv_iff f.toLinearEquiv).1 hf⟩
  exact (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv).congrFullSubcategory
    (isFG_restrict_equiv e.toRingEquiv)

instance (e : A ≃ₐ[k] B) : (restrictAlgEquivalence e).functor.Additive where
  map_add := by intros; rfl

instance (e : A ≃ₐ[k] B) : (restrictAlgEquivalence e).functor.Linear k where
  map_smul {X Y} f c := by
    apply FGModuleCat.hom_ext
    exact congrArg ModuleCat.Hom.hom ((ModuleCat.restrictScalars e.toAlgHom.toRingHom).map_smul c f.hom)

/-- Changing the presentation of the coefficient algebra preserves the vector-space dimension. -/
theorem finrank_restrictAlgEquivalence (e : A ≃ₐ[k] B) (X : FGModuleCat.{u} B) :
    Module.finrank k (((restrictAlgEquivalence e).functor.obj X).obj : Type u) = Module.finrank k (X.obj : Type u) := by
  let v : ((restrictAlgEquivalence e).functor.obj X).obj ≃ₗ[k] X.obj :=
    { Equiv.refl _ with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ congrArg (· • (show X from x)) (e.commutes c) }
  exact v.finrank_eq

variable (k K L R : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [Ring R] [Algebra k R] [Module.Finite k R]

local notation "RK" => ExtendedAlgebra k K R
local notation "RL" => ExtendedAlgebra k L R
local notation "T" => ExtendedAlgebra K L RK

/-- In a tower, the direct and the iterated extensions of the original algebra
are canonically isomorphic, including for noncommutative algebras. -/
def towerAlgebraEquiv : RL ≃ₐ[L] T :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange k K L L R).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))

/-- The category of modules over the algebra extended in two stages identifies with the
category for the direct extension. -/
def towerEquivalence : FGModuleCat.{u} T ≌ FGModuleCat.{u} RL :=
  restrictAlgEquivalence (towerAlgebraEquiv k K L R)

set_option maxHeartbeats 800000 in
/-- Extending a ground module in two stages gives its direct scalar extension
after identifying the two coefficient algebras. -/
def towerExtendIso (X : FGModuleCat.{u} R) :
    extendObj k L R X ≅ (towerEquivalence k K L R).functor.obj (extendObj K L RK (extendObj k K R X)) := by
  let Y := extendObj k K R X
  let direct := extendObj k L R X
  let iter := (towerEquivalence k K L R).functor.obj (extendObj K L RK Y)
  let e := (TensorProduct.AlgebraTensorModule.cancelBaseChange k K L L (X.obj : Type u)).symm.trans
    (LinearEquiv.baseChange K L _ _ (extendVectorSpaceEquiv k K R X).symm)
  let a : direct ≃+ iter := e.toAddEquiv
  have onTensor (c : L) (x : X) : a (c ⊗ₜ[k] x) = c ⊗ₜ[K] (show Y from (1 : K) ⊗ₜ[k] x) := rfl
  let v : direct.obj ≃ₗ[RL] iter.obj :=
    { a with
      map_smul' := by
        intro t z
        change a (t • z) = t • a z
        change RL at t
        refine TensorProduct.inductionOn t ?_ ?_
        · intro b r
          change L ⊗[k] (X.obj : Type u) at z
          refine TensorProduct.inductionOn z ?_ ?_
          · intro c x
            change a ((b ⊗ₜ[k] r : RL) • (show direct from c ⊗ₜ[k] x)) =
              (towerAlgebraEquiv k K L R (b ⊗ₜ[k] r)) • (show extendObj K L RK Y from a (c ⊗ₜ[k] x))
            have hr : towerAlgebraEquiv k K L R (b ⊗ₜ[k] r) = b ⊗ₜ[K] ((1 : K) ⊗ₜ[k] r) := rfl
            rw [hr,extendObj_smul_tmul,onTensor,onTensor,extendObj_smul_tmul,extendObj_smul_tmul,one_mul]
          · intro z w hz hw
            change a ((b ⊗ₜ[k] r : RL) • ((show direct from z) + (show direct from w))) =
              (b ⊗ₜ[k] r : RL) • a ((show direct from z) + (show direct from w))
            let t : RL := b ⊗ₜ[k] r
            exact (congrArg a (smul_add t (show direct from z) (show direct from w))).trans
              ((a.map_add _ _).trans ((congrArg₂ (· + ·) hz hw).trans
                ((smul_add t (a z) (a w)).symm.trans (congrArg (t • ·) (a.map_add _ _).symm))))
        · intro s t hs ht
          simp only [add_smul,map_add,hs,ht] }
  exact v.toFGModuleCatIso

end

end EFiniteCharacterizations.FieldExtension
