module

public import EFiniteCharacterizations.LinearAlgebra.GaloisDescent
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionHom
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Descent of modules and maps carrying a semilinear Galois action -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F]

local notation "R₊" => ExtendedAlgebra k F R

/-- A Galois action semilinear over the extended field and linear over the
original algebra. -/
structure DescentAction (N : FGModuleCat.{u} R₊) where
  /-- The additive action of the Galois group. -/
  action : Gal(F/k) →* AddMonoid.End N
  /-- The action respects extension scalars through the field automorphism. -/
  map_field_smul : ∀ σ : Gal(F/k), ∀ (c : F) (x : N), action σ (c • x) = σ c • action σ x
  /-- The action commutes with the original algebra action. -/
  map_algebra_smul : ∀ σ : Gal(F/k), ∀ (r : R) (x : N),
    action σ (algebraInclusion k F R r • x) = algebraInclusion k F R r • action σ x

variable {k F R}
variable {M N : FGModuleCat.{u} (ExtendedAlgebra k F R)}

namespace DescentAction

omit [Module.Finite k R] [Module.Finite k F] in
/-- A semilinear map of period dividing the order of a Galois generator
extends to a descent action. -/
theorem exists_of_generator (g : Gal(F/k)) (hg : ∀ σ : Gal(F/k), ∃ n : ℕ, g ^ n = σ)
    (t : AddMonoid.End N) (ht : t ^ orderOf g = 1) (hpos : orderOf g ≠ 0)
    (hF : ∀ (c : F) (x : N), t (c • x) = g c • t x)
    (hR : ∀ (r : R) (x : N),
      t (algebraInclusion k F R r • x) = algebraInclusion k F R r • t x) :
    ∃ ρ : DescentAction k F R N, ρ.action g = t := by
  let uT := Units.ofPowEqOne t (orderOf g) ht hpos
  have hgen (σ : Gal(F/k)) : σ ∈ Subgroup.zpowers g := by
    obtain ⟨n, rfl⟩ := hg σ
    exact Subgroup.npow_mem_zpowers g n
  let ψ := monoidHomOfForallMemZpowers hgen
    (orderOf_dvd_of_pow_eq_one (Units.pow_ofPowEqOne ht hpos))
  let ρ := (Units.coeHom (AddMonoid.End N)).comp ψ
  have hρ : ρ g = t := by
    change (ψ g : AddMonoid.End N) = t
    rw [monoidHomOfForallMemZpowers_apply_gen]
    rfl
  refine ⟨⟨ρ, ?_, ?_⟩, hρ⟩
  · intro σ c x
    obtain ⟨n, rfl⟩ := hg σ
    rw [map_pow, hρ]
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change t ((t ^ n) (c • x)) = g ((g ^ n) c) • t ((t ^ n) x)
      rw [ih, hF]
  · intro σ r x
    obtain ⟨n, rfl⟩ := hg σ
    rw [map_pow, hρ]
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ']
      change t ((t ^ n) (algebraInclusion k F R r • x)) =
        algebraInclusion k F R r • t ((t ^ n) x)
      rw [ih, hR]

/-- The fixed vectors are a submodule over the original algebra. -/
def fixedSubmodule (ρ : DescentAction k F R N) : Submodule R (restrictObj k F R N) where
  carrier := {x : (restrictObj k F R N : Type u) | ∀ σ : Gal(F/k), ρ.action σ (show N from x) = x}
  zero_mem' := fun σ ↦ (ρ.action σ).map_zero
  add_mem' {x y} hx hy := fun σ ↦
    ((ρ.action σ).map_add x y).trans (congrArg₂ (fun a b : N ↦ a + b) (hx σ) (hy σ))
  smul_mem' r x hx := fun σ ↦
    (ρ.map_algebra_smul σ r x).trans (congrArg (fun z : N ↦ algebraInclusion k F R r • z) (hx σ))

/-- The descended module consists of the fixed vectors. -/
def fixedObj (ρ : DescentAction k F R N) : FGModuleCat.{u} R := by
  let _ := IsNoetherianRing.of_finite k R
  exact FGModuleCat.of R ρ.fixedSubmodule

/-- The inclusion of the fixed vectors in the restricted module. -/
def fixedι (ρ : DescentAction k F R N) : ρ.fixedObj ⟶ restrictObj k F R N :=
  ObjectProperty.homMk (ModuleCat.ofHom ρ.fixedSubmodule.subtype)

/-- A map commuting with the descent actions restricts to the fixed modules. -/
def fixedMap (ρ : DescentAction k F R M) (τ : DescentAction k F R N) (f : M ⟶ N)
    (hf : ∀ (σ : Gal(F/k)) (x : M), f.hom.hom (ρ.action σ x) = τ.action σ (f.hom.hom x)) :
    ρ.fixedObj ⟶ τ.fixedObj :=
  ObjectProperty.homMk (ModuleCat.ofHom
    (((restrict k F R).map f).hom.hom.restrict (p := ρ.fixedSubmodule) (q := τ.fixedSubmodule) (fun x hx σ ↦ by
      change τ.action σ (f.hom.hom x) = f.hom.hom x
      exact (hf σ (show M from x)).symm.trans (congrArg (fun v : M ↦ f.hom.hom v) (hx σ)))))

variable [IsGalois k F]

/-- Scalar extension of the fixed module recovers the given module. -/
def fixedIso (ρ : DescentAction k F R N) : extendObj k F R ρ.fixedObj ≅ N := by
  let _ := IsNoetherianRing.of_finite F R₊
  let _ := isScalarTower_ground_extension k F R N.obj
  let A := GaloisDescent.fixedSubmodule ρ.action ρ.map_field_smul
  let e : (ρ.fixedObj : Type u) ≃ₗ[k] A :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ Subtype.ext ((restrictVectorSpaceEquiv k F R N.obj).map_smul c x.val) }
  let f : extendObj k F R ρ.fixedObj ⟶ N := extendHomOfRestrict k F R ρ.fixedι
  let a : F ⊗[k] A →ₗ[F] (N : Type u) := LinearMap.liftBaseChange F A.subtype
  let b : F ⊗[k] (ρ.fixedObj : Type u) ≃ₗ[F] F ⊗[k] A :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl F F) e
  let f₀ := (restrictVectorSpaceEquiv k F R N.obj).toLinearMap.comp (ρ.fixedι.hom.hom.restrictScalars k)
  let g := LinearMap.liftBaseChange F f₀
  let _ : Module.Finite F (N : Type u) := Module.Finite.trans R₊ N
  have h : g = a.comp b.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c x
    change LinearMap.liftBaseChange F f₀ (c ⊗ₜ[k] x) =
      a (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl F F) e (c ⊗ₜ[k] x))
    rw [LinearMap.liftBaseChange_tmul, TensorProduct.AlgebraTensorModule.congr_tmul]
    change c • f₀ x = LinearMap.liftBaseChange F A.subtype (c ⊗ₜ[k] e x)
    rw [LinearMap.liftBaseChange_tmul]
    rfl
  have hf : Function.Bijective f.hom.hom := by
    change Function.Bijective g
    rw [h]
    exact (GaloisDescent.bijective_liftBaseChange_fixedSubmodule ρ.action ρ.map_field_smul).comp b.bijective
  letI : IsIso f := (FGModuleCat.isIso_iff_bijective f).2 hf
  exact asIso f

/-- The scalar extension isomorphisms commute with the descended map. -/
theorem fixedIso_naturality (ρ : DescentAction k F R M) (τ : DescentAction k F R N)
    (f : M ⟶ N) (hf : ∀ (σ : Gal(F/k)) (x : M), f.hom.hom (ρ.action σ x) = τ.action σ (f.hom.hom x)) :
    extendMap k F R (ρ.fixedMap τ f hf) ≫ τ.fixedIso.hom = ρ.fixedIso.hom ≫ f := by
  apply extend_hom_ext
  intro x
  change (extendHomOfRestrict k F R τ.fixedι).hom.hom
    ((extendMap k F R (ρ.fixedMap τ f hf)).hom.hom (1 ⊗ₜ[k] x)) =
    f.hom.hom ((extendHomOfRestrict k F R ρ.fixedι).hom.hom (1 ⊗ₜ[k] x))
  rw [extendMap_tmul, extendHomOfRestrict_tmul, extendHomOfRestrict_tmul, one_smul, one_smul]
  rfl

end DescentAction

end

end EFiniteCharacterizations.FieldExtension
