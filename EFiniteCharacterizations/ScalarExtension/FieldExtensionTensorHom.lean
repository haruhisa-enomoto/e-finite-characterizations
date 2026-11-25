module

public import EFiniteCharacterizations.LinearAlgebra.ScalarCategory
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionHom
public import EFiniteCharacterizations.Modules.HomDimension
public import EFiniteCharacterizations.ScalarExtension.RestrictionOfExtension

/-! # Scalar extension of the Hom spaces of finite modules -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R]

local notation "R₊" => ExtendedAlgebra k F R

/-- The base change of module maps is linear over the ground field. -/
def extendMapLinear (M N : FGModuleCat.{u} R) :
    (M ⟶ N) →ₗ[k] (extendObj k F R M ⟶ extendObj k F R N) where
  toFun := extendMap k F R
  map_add' f g := by
    apply extend_hom_ext k F R
    intro x
    change (extendMap k F R (f + g)).hom.hom (1 ⊗ₜ[k] x) =
      (extendMap k F R f).hom.hom (1 ⊗ₜ[k] x) + (extendMap k F R g).hom.hom (1 ⊗ₜ[k] x)
    rw [extendMap_tmul, extendMap_tmul, extendMap_tmul]
    exact TensorProduct.tmul_add _ _ _
  map_smul' c f := by
    apply extend_hom_ext k F R
    intro x
    change (extendMap k F R (c • f)).hom.hom (1 ⊗ₜ[k] x) =
      (algebraMap k R₊ c) • (extendMap k F R f).hom.hom (1 ⊗ₜ[k] x)
    rw [extendMap_tmul, extendMap_tmul, Algebra.TensorProduct.algebraMap_apply']
    exact (one_mul (1 : F) ▸ extendObj_smul_tmul k F R N 1 1 (algebraMap k R c) (f.hom.hom x)).symm

local instance (X Y : FGModuleCat.{u} R₊) : IsScalarTower k F (X ⟶ Y) :=
  isScalarTower_ground_extension_hom k F R X Y

instance : (extend k F R).Additive where
  map_add {X Y} f g := (extendMapLinear k F R X Y).map_add f g

/-- The canonical scalar extension map on Hom spaces. -/
def homTensorMap (M N : FGModuleCat.{u} R) :
    (F ⊗[k] (M ⟶ N)) →ₗ[F] (extendObj k F R M ⟶ extendObj k F R N) :=
  LinearMap.liftBaseChange F (extendMapLinear k F R M N)

@[simp] theorem homTensorMap_tmul {M N : FGModuleCat.{u} R} (a : F) (f : M ⟶ N) :
    homTensorMap k F R M N (a ⊗ₜ[k] f) = a • extendMap k F R f := rfl

open Classical in
private def coordinates {ι V : Type u} [AddCommGroup V] [Module k V] (b : Module.Basis ι k F) :
    F ⊗[k] V ≃ₗ[k] (ι →₀ V) :=
  (b.repr.rTensor V).trans (TensorProduct.finsuppScalarLeft k V ι)

private theorem coordinates_tmul {ι V : Type u} [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k F) (a : F) (x : V) (i : ι) :
    coordinates k F b (a ⊗ₜ[k] x) i = b.repr a i • x :=
  by
    classical
    exact TensorProduct.finsuppScalarLeft_apply_tmul_apply (b.repr a) x i

private theorem coordinates_smul {ι : Type u} (b : Module.Basis ι k F) (N : FGModuleCat.{u} R)
    (r : R) (z : F ⊗[k] (N.obj : Type u)) (i : ι) :
    coordinates k F b ((1 ⊗ₜ[k] r : R₊) • (show extendObj k F R N from z)) i =
      r • coordinates k F b z i := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a x
    rw [extendObj_smul_tmul,one_mul,coordinates_tmul,coordinates_tmul,smul_comm]
  · intro x y hx hy
    erw [smul_add (1 ⊗ₜ[k] r : R₊) (show extendObj k F R N from x) (show extendObj k F R N from y)]
    erw [map_add,Finsupp.add_apply,map_add,Finsupp.add_apply,smul_add]
    exact congrArg₂ (· + ·) hx hy

private def coefficient {ι : Type u} (b : Module.Basis ι k F) {M N : FGModuleCat.{u} R}
    (f : extendObj k F R M ⟶ extendObj k F R N) (i : ι) : M ⟶ N :=
  (finiteModuleHomLinearEquiv k M N).symm
    { toFun x := coordinates k F b (f.hom.hom (1 ⊗ₜ[k] x)) i
      map_add' x y := by
        erw [TensorProduct.tmul_add, f.hom.hom.map_add (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y),map_add,Finsupp.add_apply]
      map_smul' r x := by
        change coordinates k F b (f.hom.hom (1 ⊗ₜ[k] (r • x))) i = _
        have he := extendObj_smul_tmul k F R M 1 1 r x
        rw [one_mul] at he
        rw [← he,map_smul]
        exact coordinates_smul k F R b N r _ i }

/-- A module map after extension has ground module maps as its coefficients
in a basis of the extension field. -/
private theorem coefficient_homTensorMap {ι : Type u} (b : Module.Basis ι k F)
    (M N : FGModuleCat.{u} R) (z : F ⊗[k] (M ⟶ N)) (i : ι) :
    coefficient k F R b (homTensorMap k F R M N z) i = coordinates k F b z i := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change coordinates k F b ((homTensorMap k F R M N z).hom.hom (1 ⊗ₜ[k] x)) i =
    (coordinates k F b z i).hom.hom x
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a f
    rw [homTensorMap_tmul]
    change coordinates k F b ((algebraMap F R₊ a) • (extendMap k F R f).hom.hom (1 ⊗ₜ[k] x)) i = _
    rw [Algebra.TensorProduct.algebraMap_apply,Algebra.algebraMap_self_apply,extendMap_tmul,
      extendObj_smul_tmul,mul_one,one_smul,coordinates_tmul,coordinates_tmul]
    rfl
  · intro z w hz hw
    simp only [map_add,Finsupp.add_apply]
    let ev (t : F ⊗[k] (M ⟶ N)) : F ⊗[k] (N.obj : Type u) := (homTensorMap k F R M N t).hom.hom (1 ⊗ₜ[k] x)
    change coordinates k F b (ev z + ev w) i = (coordinates k F b z i).hom.hom x + (coordinates k F b w i).hom.hom x
    rw [map_add,Finsupp.add_apply]
    exact congrArg₂ (· + ·) hz hw

/-- Hom commutes with arbitrary ground field extensions. Finite generation
of the source bounds the common support of all coefficient maps. -/
theorem homTensorMap_bijective (M N : FGModuleCat.{u} R) :
    Function.Bijective (homTensorMap k F R M N) := by
  classical
  let b := Module.Free.chooseBasis k F
  let E := coordinates (V := M ⟶ N) k F b
  constructor
  · intro z w h
    apply E.injective
    exact Finsupp.ext fun i ↦ (coefficient_homTensorMap k F R b M N z i).symm.trans
      ((congrArg (fun f ↦ coefficient k F R b f i) h).trans (coefficient_homTensorMap k F R b M N w i))
  · intro f
    have : Module.Finite k (M.obj : Type u) := Module.Finite.trans R _
    let d := Module.finBasis k (M.obj : Type u)
    let S := Finset.univ.biUnion fun j ↦ (coordinates k F b (f.hom.hom (1 ⊗ₜ[k] d j))).support
    let c := coefficient k F R b f
    have hS (i) (hi : c i ≠ 0) : i ∈ S := by
      by_contra hn
      apply hi
      apply FGModuleCat.hom_ext
      apply LinearMap.restrictScalars_injective k
      apply d.ext
      intro j
      change coordinates k F b (f.hom.hom (1 ⊗ₜ[k] d j)) i = 0
      apply Finsupp.notMem_support_iff.mp
      exact fun hj ↦ hn (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hj⟩)
    let v := Finsupp.onFinset S c hS
    let z := E.symm v
    refine ⟨z,extend_hom_ext k F R fun x ↦ (coordinates k F b).injective (Finsupp.ext fun i ↦ ?_)⟩
    have he : coefficient k F R b (homTensorMap k F R M N z) i = c i := by
      rw [coefficient_homTensorMap]
      exact congrArg (fun a ↦ a i) (E.apply_symm_apply v)
    exact LinearMap.congr_fun (congrArg (fun g : M ⟶ N ↦ g.hom.hom) he) x

/-- Scalar-extended Hom spaces are the Hom spaces between extended modules. -/
def homTensorEquiv (M N : FGModuleCat.{u} R) :
    (F ⊗[k] (M ⟶ N)) ≃ₗ[F] (extendObj k F R M ⟶ extendObj k F R N) :=
  LinearEquiv.ofBijective (homTensorMap k F R M N) (homTensorMap_bijective k F R M N)

/-- The Hom comparison respects composition in the scalar-extended category. -/
theorem homTensorMap_comp {X Y Z : FGModuleCat.{u} R}
    (f : F ⊗[k] (X ⟶ Y)) (g : F ⊗[k] (Y ⟶ Z)) :
    homTensorMap k F R X Z (ScalarCategory.compLinear f g) =
      homTensorMap k F R X Y f ≫ homTensorMap k F R Y Z g := by
  revert g
  refine TensorProduct.inductionOn f ?_ ?_
  · intro a f g
    refine TensorProduct.inductionOn g ?_ ?_
    · intro b g
      have h : ScalarCategory.compLinear (a ⊗ₜ[k] f) (b ⊗ₜ[k] g) =
          (a * b) ⊗ₜ[k] (f ≫ g) :=
        ScalarCategory.tmul_comp_tmul (X := ⟨X⟩) (Y := ⟨Y⟩) (Z := ⟨Z⟩) a b f g
      rw [h, homTensorMap_tmul, homTensorMap_tmul, homTensorMap_tmul, Linear.smul_comp, Linear.comp_smul, smul_smul]
      congr 1
      exact (extend k F R).map_comp f g
    · intro g h hg hh
      simp only [map_add, hg, hh, Preadditive.comp_add]
  · intro f h hf hh g
    simp only [map_add, LinearMap.add_apply, hf, hh, Preadditive.add_comp]

/-- Realize the scalar-extended Hom category as the full category of
extended objects and their maps in the module category. -/
def extendScalarCategory : ScalarCategory k F (FGModuleCat.{u} R) ⥤ FGModuleCat.{u} R₊ where
  obj X := extendObj k F R X.obj
  map {X Y} f := homTensorMap k F R X.obj Y.obj f
  map_id X := by
    change homTensorMap k F R X.obj X.obj ((1 : F) ⊗ₜ[k] 𝟙 X.obj) = 𝟙 (extendObj k F R X.obj)
    rw [homTensorMap_tmul, one_smul]
    exact (extend k F R).map_id X.obj
  map_comp f g := homTensorMap_comp k F R f g

instance : (extendScalarCategory k F R).Faithful where
  map_injective {X Y} := (homTensorEquiv k F R X.obj Y.obj).injective

instance : (extendScalarCategory k F R).Full where
  map_surjective := (homTensorEquiv k F R _ _).surjective

instance : (extendScalarCategory k F R).Additive where
  map_add {X Y} f g := (homTensorMap k F R X.obj Y.obj).map_add f g

end

end EFiniteCharacterizations.FieldExtension
