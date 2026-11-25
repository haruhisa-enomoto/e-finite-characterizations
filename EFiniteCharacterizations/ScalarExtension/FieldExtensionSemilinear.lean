module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionCoefficients
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionWeights
public import Mathlib.FieldTheory.Galois.Basic

/-! # Semilinear maps from a field automorphism and a linear isomorphism -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable {k F R : Type u} [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F]

local notation "R₊" => ExtendedAlgebra k F R

/-- Compose the field automorphism on coefficients with an isomorphism of
extended modules. -/
def semilinearEquiv (σ : Gal(F/k)) {M : FGModuleCat.{u} R}
    (a : extendObj k F R M ≅ extendObj k F R M) :
    (extendObj k F R M : Type u) ≃+ (extendObj k F R M : Type u) :=
  (TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl k (M : Type u))).toAddEquiv.trans
    (FGModuleCat.isoToLinearEquiv a).toAddEquiv

omit [Module.Finite k F] in
theorem semilinearEquiv_apply (σ : Gal(F/k)) {M : FGModuleCat.{u} R}
    (a : extendObj k F R M ≅ extendObj k F R M) (x : extendObj k F R M) :
    semilinearEquiv σ a x = a.hom.hom.hom (coefficientMap σ.toAlgHom M x) := rfl

omit [Module.Finite k F] in
theorem semilinearEquiv_field_smul (σ : Gal(F/k)) {M : FGModuleCat.{u} R}
    (a : extendObj k F R M ≅ extendObj k F R M) (c : F) (x : extendObj k F R M) :
    semilinearEquiv σ a (c • x) = σ c • semilinearEquiv σ a x := by
  let b := extendVectorSpaceEquiv k F R M
  have h₁ : coefficientMap σ.toAlgHom M (b (c • x)) =
      σ c • coefficientMap σ.toAlgHom M (b x) := by
    rw [b.map_smul, coefficientMap_smul]
    rfl
  have h₂ := congrArg b.symm h₁
  rw [b.symm.map_smul] at h₂
  change (show extendObj k F R M from coefficientMap σ.toAlgHom M (c • x)) =
    σ c • (show extendObj k F R M from coefficientMap σ.toAlgHom M x) at h₂
  change a.hom.hom.hom (coefficientMap σ.toAlgHom M (c • x)) =
    σ c • a.hom.hom.hom (coefficientMap σ.toAlgHom M x)
  exact (congrArg (fun z : extendObj k F R M ↦ a.hom.hom.hom z) h₂).trans
    ((a.hom.hom.hom.restrictScalars F).map_smul _ _)

omit [Module.Finite k F] in
theorem semilinearEquiv_tensor_smul (σ : Gal(F/k)) {M : FGModuleCat.{u} R}
    (a : extendObj k F R M ≅ extendObj k F R M) (c : F) (x : F ⊗[k] (M : Type u)) :
    (show F ⊗[k] (M : Type u) from semilinearEquiv σ a (c • x)) =
      σ c • (show F ⊗[k] (M : Type u) from semilinearEquiv σ a x) := by
  let b := extendVectorSpaceEquiv k F R M
  have hb : b.symm (c • x) = c • b.symm x := b.symm.map_smul c x
  exact (congrArg (fun z : extendObj k F R M ↦ b (semilinearEquiv σ a z)) hb).trans
    ((congrArg b (semilinearEquiv_field_smul σ a c (b.symm x))).trans (b.map_smul _ _))

omit [Module.Finite k F] in
theorem semilinearEquiv_algebra_smul (σ : Gal(F/k)) {M : FGModuleCat.{u} R}
    (a : extendObj k F R M ≅ extendObj k F R M) (r : R) (x : extendObj k F R M) :
    semilinearEquiv σ a (algebraInclusion k F R r • x) =
      algebraInclusion k F R r • semilinearEquiv σ a x := by
  rw [semilinearEquiv_apply, semilinearEquiv_apply]
  have h := coefficientMap_ground_smul σ.toAlgHom M r x
  exact (congrArg (fun z : (extendObj k F R M : Type u) ↦ a.hom.hom.hom z) h).trans
    (a.hom.hom.hom.map_smul (algebraInclusion k F R r) _)

omit [Module.Finite k F] in
/-- The commutative square with a Frobenius conjugate yields an equivariant
differential for the resulting semilinear maps. -/
theorem semilinearEquiv_commutes (σ : Gal(F/k)) {X Y : ScalarCategory k F (FGModuleCat.{u} R)}
    (p : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
    (h : a.hom ≫ p = (ScalarCategory.changeScalars σ.toAlgHom).map p ≫ b.hom) :
    let G := extendScalarCategory k F R
    ∀ x : G.obj X, (G.map p).hom.hom (semilinearEquiv σ (G.mapIso a) x) =
      semilinearEquiv σ (G.mapIso b) ((G.map p).hom.hom x) := by
  intro G x
  change (G.map p).hom.hom ((G.map a.hom).hom.hom (coefficientMap σ.toAlgHom X.obj x)) =
    (G.map b.hom).hom.hom (coefficientMap σ.toAlgHom Y.obj ((G.map p).hom.hom x))
  let q : X ⟶ Y := (ScalarCategory.changeScalars σ.toAlgHom).map p
  have hmap : G.map a.hom ≫ G.map p = G.map q ≫ G.map b.hom :=
    (G.map_comp a.hom p).symm.trans
      ((congrArg (fun f : X ⟶ Y ↦ G.map f) h).trans (G.map_comp q b.hom))
  have h' := congrArg
    (fun f : G.obj X ⟶ G.obj Y ↦ f.hom.hom (coefficientMap σ.toAlgHom X.obj x)) hmap
  refine h'.trans ?_
  exact congrArg (fun z : G.obj Y ↦ (G.map b.hom).hom.hom z)
    (coefficientMap_naturality σ.toAlgHom p x).symm

variable {L : Type u} [Field L] [Algebra k L] [Module.Finite k L]

omit [Module.Finite k F] [Module.Finite k L] in
/-- The semilinear maps on two successive extensions agree on vectors over
the smaller extension when their field automorphisms agree there. -/
theorem semilinearEquiv_coefficientMap (e : F →ₐ[k] L) (σ : Gal(F/k)) (τ : Gal(L/k))
    (h : ∀ c : F, e (σ c) = τ (e c)) {X : ScalarCategory k F (FGModuleCat.{u} R)}
    (a : X ≅ X) (x : extendObj k F R X.obj) :
    let G := extendScalarCategory k F R
    let H := extendScalarCategory k L R
    let J := ScalarCategory.changeScalars (C := FGModuleCat.{u} R) e
    semilinearEquiv τ (H.mapIso (J.mapIso a)) (coefficientMap e X.obj x) =
      coefficientMap e X.obj (semilinearEquiv σ (G.mapIso a) x) := by
  intro G H J
  have hcomp (z : F ⊗[k] (X.obj : Type u)) :
      coefficientMap τ.toAlgHom X.obj (coefficientMap e X.obj z) =
        coefficientMap e X.obj (coefficientMap σ.toAlgHom X.obj z) := by
    refine TensorProduct.inductionOn z ?_ ?_
    · intro c x
      simp only [coefficientMap_tmul, AlgEquiv.coe_toAlgHom, h]
    · intro z w hz hw
      simp only [map_add, hz, hw]
  change (H.map (J.map a.hom)).hom.hom
      (coefficientMap τ.toAlgHom X.obj (coefficientMap e X.obj x)) =
    coefficientMap e X.obj ((G.map a.hom).hom.hom (coefficientMap σ.toAlgHom X.obj x))
  exact (congrArg (fun z : H.obj (J.obj X) ↦ (H.map (J.map a.hom)).hom.hom z) (hcomp x)).trans
    (coefficientMap_naturality e a.hom (coefficientMap σ.toAlgHom X.obj x)).symm

end

end EFiniteCharacterizations.FieldExtension
