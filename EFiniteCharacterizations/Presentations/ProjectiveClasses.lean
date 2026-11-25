module

public import EFiniteCharacterizations.Presentations.TwoTerm
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Split Grothendieck group of finite projectives and E-finiteness

Defines the category `FiniteProjective R` of finitely generated projective modules,
its split Grothendieck group `ProjectiveClass R = K₀(proj R)`, the `g`-vector
`P.projectiveClass = [P⁰] - [P⁻¹]` of a two-term complex `P`, and the predicate
`IsEFinite R` asserting that every class in `ProjectiveClass R` is represented by a
two-term presilting complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable (R : Type u) [Ring R]

/-- Finite projective modules as a full subcategory of finite modules. -/
abbrev FiniteProjective :=
  { P : FGModuleCat.{u} R // Module.Projective R P }

/-- Isomorphisms and finite direct sums give the relations in the split
Grothendieck group of finite projectives. -/
def projectiveClassRelations : AddSubgroup (FreeAbelianGroup (FiniteProjective R)) :=
  AddSubgroup.closure
    ({x | ∃ P Q : FiniteProjective R, Nonempty (P.val ≅ Q.val) ∧
        x = FreeAbelianGroup.of P - FreeAbelianGroup.of Q} ∪
      {x | ∃ P Q T : FiniteProjective R, Nonempty (T.val.obj ≅ P.val.obj ⊞ Q.val.obj) ∧
        x = FreeAbelianGroup.of T - (FreeAbelianGroup.of P + FreeAbelianGroup.of Q)})

/-- The split Grothendieck group of finite projectives. -/
abbrev ProjectiveClass :=
  FreeAbelianGroup (FiniteProjective R) ⧸ projectiveClassRelations R

namespace ProjectiveClass

variable {R}

/-- The class of a finite projective module. -/
def of (P : FiniteProjective R) : ProjectiveClass R :=
  QuotientAddGroup.mk (FreeAbelianGroup.of P)

theorem of_eq_of_iso (P Q : FiniteProjective R) (e : P.val ≅ Q.val) : of P = of Q := by
  apply sub_eq_zero.mp
  change QuotientAddGroup.mk' (projectiveClassRelations R)
    (FreeAbelianGroup.of P - FreeAbelianGroup.of Q) = 0
  exact (QuotientAddGroup.eq_zero_iff _).mpr
    (AddSubgroup.subset_closure (Or.inl ⟨P, Q, ⟨e⟩, rfl⟩))

theorem of_eq_add_of_biprod (P Q T : FiniteProjective R) (e : T.val.obj ≅ P.val.obj ⊞ Q.val.obj) :
    of T = of P + of Q := by
  apply sub_eq_zero.mp
  change QuotientAddGroup.mk' (projectiveClassRelations R)
    (FreeAbelianGroup.of T - (FreeAbelianGroup.of P + FreeAbelianGroup.of Q)) = 0
  exact (QuotientAddGroup.eq_zero_iff _).mpr
    (AddSubgroup.subset_closure (Or.inr ⟨P, Q, T, ⟨e⟩, rfl⟩))

/-- An invariant additive under direct sums evaluates on integral projective classes. -/
def lift {G : Type*} [AddCommGroup G] (f : FiniteProjective R → G)
    (hiso : ∀ P Q : FiniteProjective R, (P.val ≅ Q.val) → f P = f Q)
    (hsum : ∀ P Q T : FiniteProjective R, (T.val.obj ≅ P.val.obj ⊞ Q.val.obj) →
      f T = f P + f Q) : ProjectiveClass R →+ G :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift f) <| by
    rw [projectiveClassRelations, AddSubgroup.closure_le]
    rintro _ (⟨P, Q, ⟨e⟩, rfl⟩ | ⟨P, Q, T, ⟨e⟩, rfl⟩)
    · simp [hiso P Q e]
    · simp [hsum P Q T e]

@[simp] theorem lift_of {G : Type*} [AddCommGroup G] (f : FiniteProjective R → G)
    (hiso : ∀ P Q : FiniteProjective R, (P.val ≅ Q.val) → f P = f Q)
    (hsum : ∀ P Q T : FiniteProjective R, (T.val.obj ≅ P.val.obj ⊞ Q.val.obj) →
      f T = f P + f Q) (P : FiniteProjective R) :
    lift f hiso hsum (of P) = f P := by
  simp [lift, of]

end ProjectiveClass

variable {R}

/-- The class of a complex is the class of its target minus the class of its source. -/
def TwoTerm.projectiveClass (P : TwoTerm R) : ProjectiveClass R :=
  ProjectiveClass.of ⟨P.target, P.projective_target⟩ -
    ProjectiveClass.of ⟨P.source, P.projective_source⟩

variable (R)

/-- Every integral class of finite projectives has a two-term presilting representative. -/
def IsEFinite : Prop :=
  ∀ g : ProjectiveClass R, ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = g

end EFiniteCharacterizations
