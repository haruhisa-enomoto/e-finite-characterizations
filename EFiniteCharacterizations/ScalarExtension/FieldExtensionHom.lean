module

public import EFiniteCharacterizations.ScalarExtension.FieldExtension
public import EFiniteCharacterizations.Modules.ProjectiveCovers
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! # The Hom adjunction for ground field extension -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F]

local notation "R₊" => ExtendedAlgebra k F R

local instance (N : ModuleCat.{u} R₊) : IsScalarTower k F N :=
  isScalarTower_ground_extension k F R N

omit [Module.Finite k R] [Module.Finite k F] in
/-- The two field actions on extended-algebra Hom spaces form a scalar tower. -/
theorem isScalarTower_ground_extension_hom (X Y : FGModuleCat.{u} R₊) :
    IsScalarTower k F (X ⟶ Y) :=
  IsScalarTower.of_algebraMap_smul (fun c f ↦
    FGModuleCat.hom_ext (LinearMap.ext (fun x ↦ by
      change (algebraMap F R₊ (algebraMap k F c)) • f.hom.hom x =
        (algebraMap k R₊ c) • f.hom.hom x
      rw [← IsScalarTower.algebraMap_apply k F R₊])))

/-- The map to the restriction of the scalar extension is `m ↦ 1 ⊗ m`. -/
def unitMap (M : FGModuleCat.{u} R) : M ⟶ restrictObj k F R (extendObj k F R M) := by
  refine ObjectProperty.homMk (ModuleCat.ofHom (X := M.obj)
    (Y := (restrictObj k F R (extendObj k F R M)).obj)
    { (TensorProduct.mk k F (M.obj : Type u) 1).toAddHom with map_smul' := ?_ })
  intro a x
  change (1 : F) ⊗ₜ[k] (a • x) = (1 ⊗ₜ[k] a : R₊) • (show extendObj k F R M from 1 ⊗ₜ[k] x)
  exact (one_mul (1 : F) ▸ extendObj_smul_tmul k F R M 1 1 a x).symm

@[simp] theorem unitMap_apply (M : FGModuleCat.{u} R) (x : M) :
    (unitMap k F R M).hom.hom x = (1 : F) ⊗ₜ[k] x := rfl

/-- Extend a map into a restricted module along the unit of scalar extension. -/
def extendLinearOfRestrict {M : FGModuleCat.{u} R} {N : FGModuleCat.{u} R₊}
    (f : (M.obj : Type u) →ₗ[R] ((ModuleCat.restrictScalars (algebraInclusion k F R).toRingHom).obj N.obj)) : extendObj k F R M ⟶ N := by
  let f₀ := (restrictVectorSpaceEquiv k F R N.obj).toLinearMap.comp (f.restrictScalars k)
  let l := LinearMap.liftBaseChange F f₀
  refine ObjectProperty.homMk (ModuleCat.ofHom (X := (extendObj k F R M).obj) (Y := N.obj)
    { l.toAddHom with map_smul' := ?_ })
  intro x z
  change F ⊗[k] (M.obj : Type u) at z
  change l (representation k F R M x z) = x • l z
  refine TensorProduct.inductionOn x ?_ ?_
  · intro c a
    refine TensorProduct.inductionOn z ?_ ?_
    · intro d m
      have h : f₀ (a • m) = (1 ⊗ₜ[k] a : R₊) • f₀ m := f.map_smul a m
      rw [representation_tmul, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]
      change (c * d) • f₀ (a • m) = (c ⊗ₜ[k] a : R₊) • (d • f₀ m)
      rw [h, ← IsScalarTower.algebraMap_smul R₊ (c * d), ← mul_smul,
        ← IsScalarTower.algebraMap_smul R₊ d, ← mul_smul]
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    · intro x y hx hy
      simp only [map_add, smul_add, hx, hy]
  · intro x y hx hy
    simp only [map_add, LinearMap.add_apply, add_smul, hx, hy]

omit [Module.Finite k F] in
@[simp] theorem extendLinearOfRestrict_one_tmul {M : FGModuleCat.{u} R} {N : FGModuleCat.{u} R₊}
    (f : (M.obj : Type u) →ₗ[R] ((ModuleCat.restrictScalars (algebraInclusion k F R).toRingHom).obj N.obj))
    (x : M) :
    (extendLinearOfRestrict k F R f).hom.hom ((1 : F) ⊗ₜ[k] x) = (show N from f x) := by
  change (1 : F) • (show N from f x) = _
  exact one_smul F _

/-- The finite-module adjunction map for a finite extension. -/
def extendHomOfRestrict {M : FGModuleCat.{u} R} {N : FGModuleCat.{u} R₊}
    (f : M ⟶ restrictObj k F R N) : extendObj k F R M ⟶ N :=
  extendLinearOfRestrict k F R f.hom.hom

@[simp] theorem extendHomOfRestrict_tmul {M : FGModuleCat.{u} R} {N : FGModuleCat.{u} R₊}
    (f : M ⟶ restrictObj k F R N) (c : F) (x : M) :
    (extendHomOfRestrict k F R f).hom.hom (c ⊗ₜ[k] x) = c •
      (show N from f.hom.hom x) := rfl

omit [Module.Finite k F] in
/-- Two morphisms from a scalar extension are equal if they agree on all
vectors of the form `1 ⊗ m`. -/
theorem extend_hom_ext {M : FGModuleCat.{u} R} {N : FGModuleCat.{u} R₊}
    {f g : extendObj k F R M ⟶ N}
    (h : ∀ x : M, f.hom.hom ((1 : F) ⊗ₜ[k] x) = g.hom.hom ((1 : F) ⊗ₜ[k] x)) : f = g := by
  apply FGModuleCat.hom_ext
  let f' : (F ⊗[k] (M.obj : Type u)) →+ N := f.hom.hom.toAddMonoidHom
  let g' : (F ⊗[k] (M.obj : Type u)) →+ N := g.hom.hom.toAddMonoidHom
  apply LinearMap.ext
  intro z
  change F ⊗[k] (M.obj : Type u) at z
  change f' z = g' z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro c x
    change f.hom.hom (c ⊗ₜ[k] x) = g.hom.hom (c ⊗ₜ[k] x)
    have ht : (c ⊗ₜ[k] (1 : R) : R₊) • (show extendObj k F R M from 1 ⊗ₜ[k] x) = c ⊗ₜ[k] x := by
      simpa only [mul_one, one_smul] using extendObj_smul_tmul k F R M c 1 1 x
    rw [← ht, map_smul, map_smul, h x]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

/-- The Hom equivalence for extension and restriction of the ground field. -/
def homEquiv (M : FGModuleCat.{u} R) (N : FGModuleCat.{u} R₊) :
    (extendObj k F R M ⟶ N) ≃ (M ⟶ restrictObj k F R N) where
  toFun f := unitMap k F R M ≫ (restrict k F R).map f
  invFun f := extendHomOfRestrict k F R f
  left_inv f := extend_hom_ext k F R (fun x ↦ by
    rw [extendHomOfRestrict_tmul, one_smul]
    rfl)
  right_inv f := FGModuleCat.hom_ext (LinearMap.ext (fun x ↦ by
    change (extendHomOfRestrict k F R f).hom.hom ((1 : F) ⊗ₜ[k] x) = (show N from f.hom.hom x)
    rw [extendHomOfRestrict_tmul, one_smul]))

/-- The scalar extension Hom equivalence is linear over the ground field. -/
def homLinearEquiv (M : FGModuleCat.{u} R) (N : FGModuleCat.{u} R₊) :
    (extendObj k F R M ⟶ N) ≃ₗ[k] (M ⟶ restrictObj k F R N) where
  toEquiv := homEquiv k F R M N
  map_add' f g := FGModuleCat.hom_ext (LinearMap.ext (fun _ ↦ rfl))
  map_smul' c f := FGModuleCat.hom_ext (LinearMap.ext (fun x ↦ by
    change (algebraMap k R₊ c) • f.hom.hom ((1 : F) ⊗ₜ[k] x) =
      (algebraInclusion k F R (algebraMap k R c)) • f.hom.hom ((1 : F) ⊗ₜ[k] x)
    rw [AlgHom.commutes]))

/-- Restriction along the ground field inclusion preserves epimorphisms. -/
theorem epi_restrict_map {M N : FGModuleCat.{u} R₊} (f : M ⟶ N) [Epi f] :
    Epi ((restrict k F R).map f) :=
  (FGModuleCat.epi_iff_surjective _).2 ((FGModuleCat.epi_iff_surjective f).1 inferInstance)

omit [Module.Finite k F] in
/-- Scalar extension preserves finite projectives over every field extension. -/
theorem projective_extendObj (M : FGModuleCat.{u} R) [Module.Projective R M] :
    Module.Projective R₊ (extendObj k F R M) := by
  obtain ⟨N, hN, q, hq⟩ := FGModuleCat.exists_projective_epi (extendObj k F R M)
  let G := ModuleCat.restrictScalars (algebraInclusion k F R).toRingHom
  let η : (M.obj : Type u) →ₗ[R] G.obj (extendObj k F R M).obj :=
    { (TensorProduct.mk k F (M.obj : Type u) 1).toAddHom with
      map_smul' := fun r x ↦ (one_mul (1 : F) ▸ extendObj_smul_tmul k F R M 1 1 r x).symm }
  obtain ⟨l,hl⟩ := Module.projective_lifting_property (G.map q.hom).hom η
    ((FGModuleCat.epi_iff_surjective q).1 hq)
  let s := extendLinearOfRestrict k F R (N := N) l
  have hsplit : s ≫ q = 𝟙 (extendObj k F R M) := by
    apply extend_hom_ext k F R
    intro x
    exact (congrArg (fun y : N ↦ q.hom.hom y) (one_smul F (show N from l x))).trans
      (LinearMap.congr_fun hl x)
  exact Module.Projective.of_split s.hom.hom q.hom.hom
    (congrArg (fun f : extendObj k F R M ⟶ extendObj k F R M ↦ f.hom.hom) hsplit)

end

end EFiniteCharacterizations.FieldExtension
