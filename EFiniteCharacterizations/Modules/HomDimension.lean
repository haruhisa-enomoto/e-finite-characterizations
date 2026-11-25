module

public import EFiniteCharacterizations.Modules.FiniteModuleMorphisms
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Dimensions of Hom spaces of finite modules -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]

/-- Dimension of the space of homomorphisms between finite modules. -/
noncomputable def homFinrank (X Y : FGModuleCat.{u} R) : ℕ :=
  Module.finrank k (X.obj ⟶ Y.obj)

/-- Finite-module morphisms as linear maps. -/
def finiteModuleHomLinearEquiv (X Y : FGModuleCat.{u} R) :
    (X ⟶ Y) ≃ₗ[k] ((X.obj : Type u) →ₗ[R] (Y.obj : Type u)) :=
  (InducedCategory.homLinearEquiv (R := k) (F := (·.obj)) (X := X) (Y := Y)).trans
    ModuleCat.homLinearEquiv

theorem finiteModuleHom_isFinite [Module.Finite k R] (X Y : FGModuleCat.{u} R) :
    Module.Finite k (X ⟶ Y) := by
  have : Module.Finite R (X.obj : Type u) := X.property
  have : Module.Finite R (Y.obj : Type u) := Y.property
  have : Module.Finite k (X.obj : Type u) := Module.Finite.trans R _
  have : Module.Finite k (Y.obj : Type u) := Module.Finite.trans R _
  exact Module.Finite.equiv (finiteModuleHomLinearEquiv k X Y).symm

theorem homFinrank_eq_finrank (X Y : FGModuleCat.{u} R) :
    homFinrank k X Y = Module.finrank k (X ⟶ Y) := by
  let e : (X ⟶ Y) ≃ₗ[k] (X.obj ⟶ Y.obj) := InducedCategory.homLinearEquiv
  exact e.symm.finrank_eq

theorem homFinrank_pos_iff [Module.Finite k R] (X Y : FGModuleCat.{u} R) :
    0 < homFinrank k X Y ↔ ∃ f : X ⟶ Y, f ≠ 0 := by
  have := finiteModuleHom_isFinite k X Y
  rw [homFinrank_eq_finrank, Module.finrank_pos_iff_exists_ne_zero]

theorem homFinrank_eq_zero_iff [Module.Finite k R] (X Y : FGModuleCat.{u} R) :
    homFinrank k X Y = 0 ↔ ∀ f : X ⟶ Y, f = 0 := by
  constructor
  · intro hz f
    by_contra hf
    have hpos := (homFinrank_pos_iff k X Y).2 ⟨f, hf⟩
    omega
  · intro h
    by_contra hz
    obtain ⟨f, hf⟩ := (homFinrank_pos_iff k X Y).1 (Nat.pos_of_ne_zero hz)
    exact hf (h f)

/-- Algebra-linear maps form a subspace of the maps over the ground field. -/
theorem homFinrank_le_mul [Module.Finite k R] (X Y : FGModuleCat.{u} R) :
    homFinrank k X Y ≤ Module.finrank k (X.obj : Type u) * Module.finrank k (Y.obj : Type u) := by
  have : Module.Finite R (X.obj : Type u) := X.property
  have : Module.Finite R (Y.obj : Type u) := Y.property
  have : Module.Finite k (X.obj : Type u) := Module.Finite.trans R _
  have : Module.Finite k (Y.obj : Type u) := Module.Finite.trans R _
  let f := LinearMap.restrictScalarsₗ k R (X.obj : Type u) (Y.obj : Type u) k
  rw [homFinrank_eq_finrank, (finiteModuleHomLinearEquiv k X Y).finrank_eq]
  exact (LinearMap.finrank_le_finrank_of_injective (f := f)
      (LinearMap.restrictScalars_injective k)).trans_eq (Module.finrank_linearMap ..)

/-- A quotient cannot increase dimension over the ground field. -/
theorem groundFinrank_le_of_epi [Module.Finite k R] {X Y : FGModuleCat.{u} R}
    (f : X ⟶ Y) [Epi f] :
    Module.finrank k (Y.obj : Type u) ≤ Module.finrank k (X.obj : Type u) := by
  have : Module.Finite R (X.obj : Type u) := X.property
  have : Module.Finite k (X.obj : Type u) := Module.Finite.trans R _
  exact LinearMap.finrank_le_finrank_of_surjective (f := f.hom.hom.restrictScalars k)
    ((FGModuleCat.epi_iff_surjective f).mp inferInstance)

end EFiniteCharacterizations
