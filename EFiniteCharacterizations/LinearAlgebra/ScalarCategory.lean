module

public import EFiniteCharacterizations.LinearAlgebra.TensorBilinear
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Scalar extension of the Hom spaces of a linear category -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace EFiniteCharacterizations

/-- The category with the same objects as `C` and with each Hom space extended
from `k` to `S`. -/
structure ScalarCategory (k S : Type*) (C : Type*) where
  /-- The original object. -/
  obj : C

namespace ScalarCategory

universe u v w s

variable {k : Type w} {S : Type s} {C : Type u} [CommRing k] [CommRing S] [Algebra k S]
  [Category.{v} C] [Preadditive C] [Linear k C]

/-- Composition of scalar-extended morphisms, linear in both inputs. -/
def compLinear {X Y Z : C} :
    (S ⊗[k] (X ⟶ Y)) →ₗ[S] (S ⊗[k] (Y ⟶ Z)) →ₗ[S] S ⊗[k] (X ⟶ Z) :=
  baseChangeBilinear S (Linear.comp X Y Z)

@[simp] private theorem compLinear_tmul {X Y Z : C} (a b : S) (f : X ⟶ Y) (g : Y ⟶ Z) :
    compLinear (a ⊗ₜ[k] f) (b ⊗ₜ[k] g) = (a * b) ⊗ₜ[k] (f ≫ g) :=
  baseChangeBilinear_tmul S (Linear.comp X Y Z) a b f g

theorem id_compLinear {X Y : C} (f : S ⊗[k] (X ⟶ Y)) :
    compLinear ((1 : S) ⊗ₜ[k] 𝟙 X) f = f := by
  refine TensorProduct.inductionOn f (fun a g ↦ by simp) ?_
  intro g h hg hh
  simp only [map_add, hg, hh]

theorem compLinear_id {X Y : C} (f : S ⊗[k] (X ⟶ Y)) :
    compLinear f ((1 : S) ⊗ₜ[k] 𝟙 Y) = f := by
  refine TensorProduct.inductionOn f (fun a g ↦ by simp) ?_
  intro g h hg hh
  simp only [map_add, LinearMap.add_apply, hg, hh]

theorem compLinear_assoc {W X Y Z : C} (f : S ⊗[k] (W ⟶ X))
    (g : S ⊗[k] (X ⟶ Y)) (h : S ⊗[k] (Y ⟶ Z)) :
    compLinear (compLinear f g) h = compLinear f (compLinear g h) := by
  revert g h
  refine TensorProduct.inductionOn f ?_ ?_
  · intro a f g
    refine TensorProduct.inductionOn g ?_ ?_
    · intro b g h
      refine TensorProduct.inductionOn h (fun c h ↦ by simp [Category.assoc, mul_assoc]) ?_
      intro h h' hh hh'
      simp only [map_add, hh, hh']
    · intro g g' hg hg' h
      simp only [map_add, LinearMap.add_apply, hg h, hg' h]
  · intro f f' hf hf' g h
    simp only [map_add, LinearMap.add_apply, hf g h, hf' g h]

instance : Category.{max s v} (ScalarCategory k S C) where
  Hom X Y := S ⊗[k] (X.obj ⟶ Y.obj)
  id X := 1 ⊗ₜ[k] 𝟙 X.obj
  comp := fun {_ _ _} f g ↦ compLinear f g
  id_comp f := id_compLinear f
  comp_id f := compLinear_id f
  assoc f g h := compLinear_assoc f g h

instance : Preadditive (ScalarCategory k S C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (S ⊗[k] (X.obj ⟶ Y.obj)))
  add_comp X Y Z f f' g :=
    DFunLike.congr_fun ((compLinear (X := X.obj) (Y := Y.obj) (Z := Z.obj)).map_add f f') g
  comp_add X Y Z f g g' := (compLinear (X := X.obj) (Y := Y.obj) (Z := Z.obj) f).map_add g g'

instance : Linear S (ScalarCategory k S C) where
  homModule X Y := inferInstanceAs (Module S (S ⊗[k] (X.obj ⟶ Y.obj)))
  smul_comp X Y Z r f g :=
    DFunLike.congr_fun ((compLinear (X := X.obj) (Y := Y.obj) (Z := Z.obj)).map_smul r f) g
  comp_smul X Y Z f r g := (compLinear (X := X.obj) (Y := Y.obj) (Z := Z.obj) f).map_smul r g

/-- The original category maps into its scalar extension by `f ↦ 1 ⊗ f`. -/
def of : C ⥤ ScalarCategory k S C where
  obj := ScalarCategory.mk
  map f := 1 ⊗ₜ[k] f
  map_id _ := rfl
  map_comp f g := by change _ = compLinear (1 ⊗ₜ[k] f) (1 ⊗ₜ[k] g); simp

@[simp] theorem of_map {X Y : C} (f : X ⟶ Y) :
    (of (k := k) (S := S) (C := C)).map f = (1 : S) ⊗ₜ[k] f := rfl

instance : (of (k := k) (S := S) (C := C)).Additive where
  map_add := fun {_ _} f g ↦ TensorProduct.tmul_add (1 : S) f g

@[simp] theorem tmul_comp_tmul {X Y Z : ScalarCategory k S C} (a b : S)
    (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    @CategoryStruct.comp (ScalarCategory k S C) _ X Y Z (a ⊗ₜ[k] f) (b ⊗ₜ[k] g) =
      (a * b) ⊗ₜ[k] (f ≫ g) :=
  compLinear_tmul a b f g

@[simp] theorem one_tmul_comp {X Y Z : ScalarCategory k S C} (f : X.obj ⟶ Y.obj) (g : Y ⟶ Z) :
    (1 ⊗ₜ[k] f : X ⟶ Y) ≫ g = (Linear.leftComp k Z.obj f).baseChange S g :=
  baseChangeBilinear_one_tmul_left S (Linear.comp X.obj Y.obj Z.obj) f g

@[simp] theorem comp_one_tmul {X Y Z : ScalarCategory k S C} (f : X ⟶ Y) (g : Y.obj ⟶ Z.obj) :
    f ≫ (1 ⊗ₜ[k] g : Y ⟶ Z) = (Linear.rightComp k X.obj g).baseChange S f :=
  baseChangeBilinear_one_tmul_right S (Linear.comp X.obj Y.obj Z.obj) f g

/-- Change the coefficients of scalar-extended morphisms along an algebra homomorphism. -/
def changeScalars {T : Type*} [CommRing T] [Algebra k T] (e : S →ₐ[k] T) :
    ScalarCategory k S C ⥤ ScalarCategory k T C where
  obj X := ⟨X.obj⟩
  map f := TensorProduct.map e.toLinearMap LinearMap.id f
  map_id X := by
    change TensorProduct.map e.toLinearMap LinearMap.id (1 ⊗ₜ[k] 𝟙 X.obj) = 1 ⊗ₜ[k] 𝟙 X.obj
    simp
  map_comp {X Y Z} f g := map_baseChangeBilinear S e (Linear.comp X.obj Y.obj Z.obj) f g

@[simp] theorem changeScalars_map_tmul {T : Type*} [CommRing T] [Algebra k T]
    (e : S →ₐ[k] T) {X Y : ScalarCategory k S C} (s : S) (f : X.obj ⟶ Y.obj) :
    (changeScalars (C := C) e).map (show X ⟶ Y from s ⊗ₜ[k] f) =
      (show (changeScalars (C := C) e).obj X ⟶ (changeScalars (C := C) e).obj Y from
        e s ⊗ₜ[k] f) := rfl

instance {T : Type*} [CommRing T] [Algebra k T] (e : S →ₐ[k] T) :
    (changeScalars (C := C) e).Additive where
  map_add {_ _} f g := (TensorProduct.map e.toLinearMap LinearMap.id).map_add f g

/-- Changing coefficients along an algebra isomorphism is bijective on Hom. -/
theorem changeScalars_map_bijective {T : Type*} [CommRing T] [Algebra k T] (e : S ≃ₐ[k] T)
    (X Y : ScalarCategory k S C) :
    Function.Bijective ((changeScalars (C := C) e.toAlgHom).map (X := X) (Y := Y)) :=
  (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl k (X.obj ⟶ Y.obj))).bijective

instance {T : Type*} [CommRing T] [Algebra k T] (e : S ≃ₐ[k] T) :
    (changeScalars (C := C) e.toAlgHom).Full where
  map_surjective := (changeScalars_map_bijective e _ _).2

instance {T : Type*} [CommRing T] [Algebra k T] (e : S ≃ₐ[k] T) :
    (changeScalars (C := C) e.toAlgHom).Faithful where
  map_injective {X Y} := (changeScalars_map_bijective e X Y).1

end ScalarCategory

end EFiniteCharacterizations
