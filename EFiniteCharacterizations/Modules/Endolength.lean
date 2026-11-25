module

public import EFiniteCharacterizations.Modules.Bricks
public import EFiniteCharacterizations.Modules.HomDimension
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Endolength of a finite brick -/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]

/-- On bricks, the ratio of ground-field dimensions is the dimension over the
division ring of endomorphisms. -/
noncomputable def endolength (M : FGModuleCat.{u} R) : ℕ :=
  Module.finrank k (M.obj : Type u) / homFinrank k M M

theorem endolength_le_groundFinrank (M : FGModuleCat.{u} R) :
    endolength k M ≤ Module.finrank k (M.obj : Type u) := Nat.div_le_self _ _

variable [Module.Finite k R]

/-- The endomorphism ring of a finite brick is a division ring. -/
@[instance_reducible]
noncomputable def IsBrick.endomorphismDivisionRing {M : FGModuleCat.{u} R} (h : IsBrick M) :
    DivisionRing (Module.End R (M.obj : Type u)) := by
  let D := Module.End R (M.obj : Type u)
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp
    (fun hs ↦ h.1 ((FGModuleCat.isZero_iff_subsingleton M).2 hs))
  haveI : IsDomain D := by
    rw [isDomain_iff_noZeroDivisors_and_nontrivial]
    refine ⟨⟨?_⟩, inferInstance⟩
    intro f g hfg
    by_cases hf : f = 0
    · exact Or.inl hf
    · let f' := (finiteModuleHomLinearEquiv k M M).symm f
      have hf' : f' ≠ 0 := by simpa [f'] using hf
      have := h.2 f' hf'
      have hi : Function.Injective f := by
        have hl (x : M.obj) : (inv f').hom.hom (f x) = x := by
          change (f' ≫ inv f').hom.hom x = x
          rw [IsIso.hom_inv_id]
          rfl
        exact Function.LeftInverse.injective hl
      right
      ext x
      apply hi
      change f (g x) = f 0
      rw [map_zero]
      exact LinearMap.congr_fun hfg x
  have : Module.Finite k (M.obj : Type u) :=
    letI := M.property
    Module.Finite.trans R _
  exact divisionRingOfFiniteDimensional k D

theorem IsBrick.endolength_eq_finrank {M : FGModuleCat.{u} R} (h : IsBrick M) :
    letI := h.endomorphismDivisionRing k
    endolength k M = Module.finrank (Module.End R (M.obj : Type u)) (M.obj : Type u) := by
  let D := Module.End R (M.obj : Type u)
  let _ : DivisionRing D := h.endomorphismDivisionRing k
  have : Module.Finite k (M.obj : Type u) :=
    letI := M.property
    Module.Finite.trans R _
  change endolength k M = Module.finrank D (M.obj : Type u)
  rw [endolength, homFinrank_eq_finrank, (finiteModuleHomLinearEquiv k M M).finrank_eq]
  exact Module.finrank_div_finrank_cancel_left_of_nontrivial k D (M.obj : Type u)

theorem IsBrick.endolength_pos {M : FGModuleCat.{u} R} (h : IsBrick M) : 0 < endolength k M := by
  let D := Module.End R (M.obj : Type u)
  let _ : DivisionRing D := h.endomorphismDivisionRing k
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp
    (fun hs ↦ h.1 ((FGModuleCat.isZero_iff_subsingleton M).2 hs))
  have : Module.Finite k (M.obj : Type u) :=
    letI := M.property
    Module.Finite.trans R _
  have := Module.Finite.of_restrictScalars_finite k D (M.obj : Type u)
  rw [h.endolength_eq_finrank k]
  exact Module.finrank_pos

end EFiniteCharacterizations
