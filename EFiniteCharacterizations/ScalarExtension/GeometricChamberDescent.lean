module

public import EFiniteCharacterizations.Silting.Fans.ChamberCone
public import EFiniteCharacterizations.ScalarExtension.AbsoluteFrobeniusCorrespondence
public import EFiniteCharacterizations.ScalarExtension.GeometricPresiltingDescent
public import EFiniteCharacterizations.Presentations.RigidTerms

/-! # Descent of the integral realization criterion along algebraic field extensions -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations.FieldExtension

variable (k L R : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [Ring R]
  [Algebra k R] [Module.Finite k R] [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k L R)]

local notation "A" => ExtendedAlgebra k L R

omit [IsNoetherianRing R] in
/-- Realizability of a ground projective class by a presilting complex is invariant
under algebraic scalar extension. The extended representative may have arbitrary terms. -/
theorem presilting_class_iff_of_algebraic_extension (g : ProjectiveClass R) :
    (∃ Q : TwoTerm A, Q.IsPresilting ∧ Q.projectiveClass = extendProjectiveClass k L R g) ↔
      ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = g := by
  constructor
  · rintro ⟨Q,hq,he⟩
    obtain ⟨P,rfl⟩ := ProjectiveClass.exists_twoTerm g
    let T := extendTwoTerm k L R P
    let _ := T.projective_source
    let _ := T.projective_target
    have hT : Q.projectiveClass = T.projectiveClass := he.trans (projectiveClass_extendTwoTerm k L R P).symm
    let _ : IsArtinianRing A := IsArtinianRing.of_finite L A
    obtain ⟨p,hp,_⟩ := Q.exists_representative_on_terms L hq T.source T.target hT
    by_contra hn
    exact no_presilting_differential_over_algebraic_extension P hn p hp
  · rintro ⟨P,hp,rfl⟩
    exact ⟨extendTwoTerm k L R P,(isPresilting_extendTwoTerm_iff k L R P).2 hp,projectiveClass_extendTwoTerm k L R P⟩

/-- Vanishing of the semistable category at an integral weight is invariant under algebraic
extension. A geometric counterexample has a stable subobject giving a ground stable module. -/
theorem zero_semistable_iff_of_algebraic_extension (g : ProjectiveClass R) :
    (∀ X, (projectiveClassWeight L (extendProjectiveClass k L R g)).IsSemistable X → IsZero X) ↔
      ∀ X, (projectiveClassWeight k g).IsSemistable X → IsZero X := by
  obtain ⟨P,rfl⟩ := ProjectiveClass.exists_twoTerm g
  rw [← projectiveClass_extendTwoTerm,(extendTwoTerm k L R P).projectiveClassWeight_eq_eulerWeight L,
    P.projectiveClassWeight_eq_eulerWeight k]
  constructor
  · intro h X hx
    by_contra hn
    have hz := h _ (isSemistable_extendObj_of_algebraic k L P X hx)
    have h0 := (dimensionWeight (R := A) L).eval_isZero hz
    have hpos := dimensionWeight_pos k X hn
    rw [dimensionWeight_eval,finrank_extendObj] at h0
    rw [dimensionWeight_eval] at hpos
    omega
  · intro h X hx
    by_contra hn
    obtain ⟨S,_,_,hs⟩ := hx.exists_stable_subobject L hn
    obtain ⟨B,hB,_⟩ := exists_ground_of_geometric_stable k L R P S hs
    exact hB.1 (h B hB.isSemistable)

/-- For the fixed-weight criterion over an arbitrary field it suffices to realize integral
weights with zero semistable category after passage to the algebraic closure. -/
theorem fixedWeightTorsionCriteria_of_geometric_realization
    (realize : ∀ g : ProjectiveClass A, (∀ X, (projectiveClassWeight L g).IsSemistable X → IsZero X) →
      ∃ Q : TwoTerm A, Q.IsPresilting ∧ Q.projectiveClass = g) (v : RealProjectiveSpace R) :
    FixedWeightTorsionCriteria k v := by
  apply fixedWeightTorsionCriteria_of_integral_realization
  intro g hg
  exact (presilting_class_iff_of_algebraic_extension k L R g).1
    (realize _ ((zero_semistable_iff_of_algebraic_extension k L R g).2 hg))

end EFiniteCharacterizations.FieldExtension
