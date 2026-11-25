module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Two-term projective complexes

A complex is specified by its differential in degrees −1 and 0. The degree-one
Hom group in the homotopy category is the cokernel of the map encoding the two
possible homotopies.
-/

@[expose] public section

open CategoryTheory

universe u

namespace EFiniteCharacterizations

/-- A two-term complex of finitely generated projective modules. -/
structure TwoTerm (R : Type u) [Ring R] where
  source : FGModuleCat.{u} R
  target : FGModuleCat.{u} R
  projective_source : Module.Projective R source
  projective_target : Module.Projective R target
  differential : source ⟶ target

namespace TwoTerm

variable {R : Type u} [Ring R]

/-- A differential between two fixed finite projectives. -/
abbrev ofDifferential {P₁ P₀ : FGModuleCat.{u} R}
    [Module.Projective R P₁] [Module.Projective R P₀] (p : P₁ ⟶ P₀) : TwoTerm R :=
  ⟨P₁, P₀, inferInstance, inferInstance, p⟩

/-- Boundaries in the degree-one Hom group from `P` to `Q`. -/
def homotopyBoundary (P Q : TwoTerm R) :
    ((P.source ⟶ Q.source) × (P.target ⟶ Q.target)) →+
      (P.source ⟶ Q.target) where
  toFun ab := ab.1 ≫ Q.differential - P.differential ≫ ab.2
  map_zero' := by simp
  map_add' a b := by
    change (a.1 + b.1) ≫ Q.differential - P.differential ≫ (a.2 + b.2) =
      (a.1 ≫ Q.differential - P.differential ≫ a.2) +
        (b.1 ≫ Q.differential - P.differential ≫ b.2)
    simp only [Preadditive.add_comp, Preadditive.comp_add]
    abel

/-- Maps from `P` to `Q[1]`, modulo null-homotopic maps. -/
abbrev ShiftedHom (P Q : TwoTerm R) :=
  (P.source ⟶ Q.target) ⧸ (homotopyBoundary P Q).range

/-- Every map to the shift of the complex is null-homotopic. -/
def IsPresilting (P : TwoTerm R) : Prop :=
  Function.Surjective (homotopyBoundary P P)

theorem surjective_boundary_iff_subsingleton_shiftedHom (P Q : TwoTerm R) :
    Function.Surjective (homotopyBoundary P Q) ↔ Subsingleton (P.ShiftedHom Q) := by
  constructor
  · intro h
    have hz (f : P.source ⟶ Q.target) : (f : P.ShiftedHom Q) = 0 :=
      (QuotientAddGroup.eq_zero_iff f).2 (h f)
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
    exact (hz a).trans (hz b).symm
  · intro h f
    exact (QuotientAddGroup.eq_zero_iff f).1 (h.elim _ _)

theorem isPresilting_iff_subsingleton_shiftedHom (P : TwoTerm R) :
    P.IsPresilting ↔ Subsingleton (P.ShiftedHom P) :=
  surjective_boundary_iff_subsingleton_shiftedHom P P

/-- The two-term complex concentrated in degree zero at a finite projective. -/
def inDegreeZero (P : FGModuleCat.{u} R) [Module.Projective R P] : TwoTerm R where
  source := FGModuleCat.of R PUnit
  target := P
  projective_source := inferInstance
  projective_target := inferInstance
  differential := 0

theorem isPresilting_inDegreeZero (P : FGModuleCat.{u} R) [Module.Projective R P] :
    (inDegreeZero P).IsPresilting := by
  intro f
  use (0, 0)
  change homotopyBoundary (inDegreeZero P) (inDegreeZero P) 0 = f
  rw [map_zero]
  apply FGModuleCat.hom_ext
  ext x
  have hx : x = 0 := by
    exact @Subsingleton.elim PUnit inferInstance x 0
  rw [hx, map_zero, map_zero]

end TwoTerm

end EFiniteCharacterizations
