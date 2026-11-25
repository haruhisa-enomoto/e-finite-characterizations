module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionDescent
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionRigidity
public import EFiniteCharacterizations.Presentations.StableRigidComparison

/-! # Descent of presilting differentials carrying a Galois action -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FieldExtension

variable {k F R : Type u} [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F] [IsGalois k F]

local notation "R₊" => ExtendedAlgebra k F R

/-- A presilting differential compatible with descent actions descends to
a presilting two-term complex. -/
theorem exists_presilting_of_descent (P : TwoTerm R₊) (hP : P.IsPresilting)
    (ρ : DescentAction k F R P.source) (τ : DescentAction k F R P.target)
    (hf : ∀ (σ : Gal(F/k)) (x : P.source),
      P.differential.hom.hom (ρ.action σ x) = τ.action σ (P.differential.hom.hom x)) :
    ∃ Q : TwoTerm R, Q.IsPresilting ∧
      Nonempty (extendObj k F R Q.source ≅ P.source) ∧ Nonempty (extendObj k F R Q.target ≅ P.target) := by
  let _ := P.projective_source
  let _ := P.projective_target
  let _ : Module.Projective R₊ (extendObj k F R ρ.fixedObj) :=
    Module.Projective.of_equiv' (FGModuleCat.isoToLinearEquiv ρ.fixedIso).symm
  let _ : Module.Projective R₊ (extendObj k F R τ.fixedObj) :=
    Module.Projective.of_equiv' (FGModuleCat.isoToLinearEquiv τ.fixedIso).symm
  let _ := projective_of_projective_extendObj k F R ρ.fixedObj
  let _ := projective_of_projective_extendObj k F R τ.fixedObj
  let Q := TwoTerm.ofDifferential (ρ.fixedMap τ P.differential hf)
  have h := TwoTerm.isPresilting_iff_of_term_isos F (extendTwoTerm k F R Q) P ρ.fixedIso τ.fixedIso
    (ρ.fixedIso_naturality τ P.differential hf).symm
  exact ⟨Q, (isPresilting_extendTwoTerm_iff k F R Q).1 (h.2 hP), ⟨ρ.fixedIso⟩, ⟨τ.fixedIso⟩⟩

/-- Descent of a presilting differential on extended projective terms
produces their ground projective class. -/
theorem exists_presilting_of_extended_terms_of_descent (P : TwoTerm R₊) (hP : P.IsPresilting)
    (ρ : DescentAction k F R P.source) (τ : DescentAction k F R P.target)
    (hf : ∀ (σ : Gal(F/k)) (x : P.source),
      P.differential.hom.hom (ρ.action σ x) = τ.action σ (P.differential.hom.hom x))
    (A B : FiniteProjective R) (a : P.source ≅ extendObj k F R A.val) (b : P.target ≅ extendObj k F R B.val) :
    ∃ Q : TwoTerm R, Q.IsPresilting ∧ Q.projectiveClass = ProjectiveClass.of B - ProjectiveClass.of A := by
  let _ := IsNoetherianRing.of_finite k R
  obtain ⟨Q, hQ, ⟨i⟩, ⟨j⟩⟩ := exists_presilting_of_descent P hP ρ τ hf
  refine ⟨Q, hQ, ?_⟩
  change ProjectiveClass.of ⟨Q.target, Q.projective_target⟩ -
    ProjectiveClass.of ⟨Q.source, Q.projective_source⟩ = ProjectiveClass.of B - ProjectiveClass.of A
  rw [projectiveClass_eq_of_extendObj_iso k F R ⟨Q.target, Q.projective_target⟩ B (j.trans b),
    projectiveClass_eq_of_extendObj_iso k F R ⟨Q.source, Q.projective_source⟩ A (i.trans a)]

end EFiniteCharacterizations.FieldExtension
