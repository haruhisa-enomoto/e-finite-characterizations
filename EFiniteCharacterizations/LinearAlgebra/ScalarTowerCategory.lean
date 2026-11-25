module

public import EFiniteCharacterizations.LinearAlgebra.ScalarCategory
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Composition of scalar extensions of linear categories -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace EFiniteCharacterizations.ScalarCategory

variable {k F L : Type*} [CommRing k] [CommRing F] [CommRing L]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  {C : Type*} [Category C] [Preadditive C] [Linear k C]

local notation "e" => IsScalarTower.toAlgHom k F L

/-- The Hom-space identification for two successive scalar extensions. -/
def towerHomEquiv (X Y : C) :
    (L ⊗[F] (F ⊗[k] (X ⟶ Y))) ≃ₗ[L] L ⊗[k] (X ⟶ Y) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange k F L L _

theorem towerHomEquiv_tmul {X Y : C} (a : L) (f : F ⊗[k] (X ⟶ Y)) :
    towerHomEquiv X Y (a ⊗ₜ[F] f) =
      a • TensorProduct.map (e).toLinearMap LinearMap.id f := by
  refine TensorProduct.inductionOn f ?_ ?_
  · intro b g
    rw [towerHomEquiv, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, TensorProduct.smul_tmul']
    rw [Algebra.smul_def, smul_eq_mul, mul_comm]
    rfl
  · intro f g hf hg
    rw [TensorProduct.tmul_add, map_add, map_add, smul_add, hf, hg]

/-- The scalar extensions along a tower agree with the direct extension. -/
def flatten : ScalarCategory F L (ScalarCategory k F C) ⥤ ScalarCategory k L C where
  obj X := ⟨X.obj.obj⟩
  map {X Y} f := towerHomEquiv X.obj.obj Y.obj.obj f
  map_id X := by
    change towerHomEquiv X.obj.obj X.obj.obj ((1 : L) ⊗ₜ[F] ((1 : F) ⊗ₜ[k] 𝟙 X.obj.obj)) = _
    rw [towerHomEquiv_tmul, TensorProduct.map_tmul, one_smul, AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply]
    rfl
  map_comp {X Y Z} f g := by
    let H := changeScalars (C := C) e
    change towerHomEquiv X.obj.obj Z.obj.obj (compLinear f g) =
      compLinear (towerHomEquiv X.obj.obj Y.obj.obj f) (towerHomEquiv Y.obj.obj Z.obj.obj g)
    revert g
    refine TensorProduct.inductionOn f ?_ ?_
    · intro a f g
      refine TensorProduct.inductionOn g ?_ ?_
      · intro b g
        have he : towerHomEquiv X.obj.obj Z.obj.obj (compLinear (a ⊗ₜ[F] f) (b ⊗ₜ[F] g)) =
            towerHomEquiv X.obj.obj Z.obj.obj ((a * b) ⊗ₜ[F] (f ≫ g)) :=
          congrArg (towerHomEquiv X.obj.obj Z.obj.obj) (tmul_comp_tmul (X := X) (Y := Y) (Z := Z) a b f g)
        rw [he, towerHomEquiv_tmul, towerHomEquiv_tmul, towerHomEquiv_tmul]
        change (a * b) • H.map (f ≫ g) = (a • H.map f) ≫ (b • H.map g)
        rw [H.map_comp, Linear.smul_comp, Linear.comp_smul, smul_smul]
      · intro g₁ g₂ hg₁ hg₂
        simp only [map_add, hg₁, hg₂]
    · intro f₁ f₂ hf₁ hf₂ g
      simp only [map_add, LinearMap.add_apply, hf₁ g, hf₂ g]

instance : (flatten (k := k) (F := F) (L := L) (C := C)).Full where
  map_surjective {X Y} := (towerHomEquiv X.obj.obj Y.obj.obj).surjective

instance : (flatten (k := k) (F := F) (L := L) (C := C)).Faithful where
  map_injective {X Y} := (towerHomEquiv X.obj.obj Y.obj.obj).injective

instance : (flatten (k := k) (F := F) (L := L) (C := C)).Additive where
  map_add {X Y} f g := (towerHomEquiv X.obj.obj Y.obj.obj).map_add f g

theorem flatten_of_map {X Y : ScalarCategory k F C} (f : X ⟶ Y) :
    (flatten (L := L)).map ((of (k := F) (S := L)).map f) = (changeScalars e).map f := by
  change towerHomEquiv X.obj Y.obj ((1 : L) ⊗ₜ[F] f) = _
  rw [towerHomEquiv_tmul, one_smul]
  rfl

end EFiniteCharacterizations.ScalarCategory
