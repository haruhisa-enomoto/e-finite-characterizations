module

public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickInversion
public import EFiniteCharacterizations.RingEpimorphisms.GroundLocalization

/-!
# Equivalence of E-finiteness with presilting generation of two-term thick subcategories

Assembles `isEFinite_iff_twoTermThickGeneration` (Theorem 7.8, `(E-fin) ⇔ (thick-gen)`).
For the converse `(thick-gen) ⇒ (E-fin)`, generating the thick subcategory of a
single differential `P` by a presilting complex `U` identifies the modules inverting
`P` with those inverting `U` (`exists_presilting_same_inversions`), forcing the
singleton universal localization at `P` to be finite-dimensional and ruling out
missing integral weights.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

/-- Every two-term thick subcategory is the two-term part of the thick
closure of a presilting complex. -/
def TwoTermThickGeneration (R : Type u) [Ring R] [IsNoetherianRing R] : Prop :=
  ∀ H : TwoTerm R → Prop, TwoTerm.IsTwoTermThick H →
    ∃ U : TwoTerm R, U.IsPresilting ∧ ∀ X : TwoTerm R, H X ↔ TwoTerm.InThick U X

namespace TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R]

private theorem isTwoTermThick_inThick (P : TwoTerm R) : IsTwoTermThick (InThick P) where
  zero := (ObjectProperty.singleton P.homotopyObject).triangEnvelope.prop_of_isZero (isZero_contractible _)
  triangles := twoOutOfThree_inThick P
  retracts _ _ r := (ObjectProperty.singleton P.homotopyObject).triangEnvelope.prop_of_retract r

/-- Every differential has the same inverting modules as some presilting
differential if every two-term thick subcategory has a presilting generator. -/
theorem exists_presilting_same_inversions (h : TwoTermThickGeneration R) (P : TwoTerm R) :
    ∃ U : TwoTerm R, U.IsPresilting ∧ ∀ N : ModuleCat.{u} R, P.InvertedOn N ↔ U.InvertedOn N := by
  obtain ⟨U,hu,hU⟩ := h (InThick P) (isTwoTermThick_inThick P)
  have hPU := (hU U).2 (inThick_self U)
  have hUP := (hU P).1 (inThick_self P)
  exact ⟨U,hu,fun N ↦ ⟨invertedOn_of_inThick hPU N,invertedOn_of_inThick hUP N⟩⟩

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [IsArtinianRing R]

/-- Localization at any presilting differential has a finite-dimensional
model over the original field. -/
theorem exists_finite_singleton_localization_of_presilting (P : TwoTerm R) (hp : P.IsPresilting) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B) (f : R →ₐ[k] B),
      IsUniversalLocalization (fun _ : Unit ↦ P) f.toRingHom := by
  obtain ⟨L,e,hL,he⟩ := exists_pointed_perpendicular_of_presilting k P hp
  let A : PointedReflection P := ⟨L,e,hL,he⟩
  refine ⟨A.Target,inferInstance,inferInstance,A.finite_target k,A.algebraMapToTarget k,?_,?_⟩
  · exact fun _ ↦ (P.isIso_induce_iff_regular A.ringMap).2 A.invertedOn_regular
  · intro T _ g hg
    exact (A.factor_iff_inverted g).2 ((P.invertedOn_restrictions_iff_regular g).2
      ((P.isIso_induce_iff_regular g).1 (hg ())))

end TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

include k in
/-- The arbitrary-field thick-generation criterion for E-finiteness. -/
theorem isEFinite_iff_twoTermThickGeneration : IsEFinite R ↔ TwoTermThickGeneration R := by
  constructor
  · intro he H hH
    obtain ⟨U,_,hu,h⟩ := TwoTerm.exists_presilting_thick_generator k he hH
    exact ⟨U,hu,h⟩
  · intro h
    by_contra hn
    let F := AlgebraicClosure k
    let := IsNoetherianRing.of_finite F (FieldExtension.ExtendedAlgebra k F R)
    let := IsArtinianRing.of_finite k R
    obtain ⟨P,hP⟩ := exists_infinite_extended_stable_chart_of_not_isEFinite k hn
    obtain ⟨U,hu,hi⟩ := TwoTerm.exists_presilting_same_inversions h P
    obtain ⟨B,_,_,hb,g,hg⟩ := U.exists_finite_singleton_localization_of_presilting k hu
    have eq (T : Type u) [Ring T] (f : R →+* T) :
        IsIso (P.induce f).differential ↔ IsIso (U.induce f).differential := by
      rw [P.isIso_induce_iff_regular f, U.isIso_induce_iff_regular f]
      let := Module.compHom T f
      exact hi (ModuleCat.of R T)
    have loc : IsUniversalLocalization (fun _ : Unit ↦ P) g.toRingHom :=
      ⟨fun _ ↦ (eq B g.toRingHom).2 (hg.inverts ()), fun T _ f hf ↦ hg.desc T f (fun _ ↦ (eq T f).1 (hf ()))⟩
    exact FieldExtension.infinite_localization_of_infinite_extended_stable_chart k F P g loc hP hb

end EFiniteCharacterizations
