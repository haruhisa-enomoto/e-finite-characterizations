module

public import EFiniteCharacterizations.LargeModules.LargeNumericalTests
public import EFiniteCharacterizations.Presentations.IntegralEulerWeights

/-! # Euler dimensions over a commuting division ring -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] (D : Type u) [DivisionRing D]
variable (M : ModuleCat.{u} R) [Module D M] [SMulCommClass R D M] [Module.Finite D M]

/-- Evaluation on generators embeds Hom into a finite product of copies of M. -/
theorem finite_hom_over_division (P : FGModuleCat.{u} R) : Module.Finite D (P →ₗ[R] M) := by
  obtain ⟨s,hs⟩ := P.property.fg_top
  let ev : (P →ₗ[R] M) →ₗ[D] (s → M) :=
    { toFun := fun f i ↦ f i.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Finite.of_injective ev (fun f g he ↦ LinearMap.ext_on hs fun x hx ↦ congrFun he ⟨x,hx⟩)

/-- Pairing a projective class with a module of finite dimension over a
commuting division ring. -/
noncomputable def divisionEuler : ProjectiveClass R →+ ℤ := by
  refine ProjectiveClass.lift (fun P ↦ (Module.finrank D (P.val →ₗ[R] M) : ℤ)) ?_ ?_
  · intro P Q e
    let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
    exact_mod_cast (LinearEquiv.congrLeft M D (F.mapIso e).toLinearEquiv).finrank_eq
  · intro P Q T e
    have := finite_hom_over_division D M P.val
    have := finite_hom_over_division D M Q.val
    let l := (e.trans (ModuleCat.biprodIsoProd P.val.obj Q.val.obj)).toLinearEquiv
    let w := (LinearEquiv.congrLeft M D l).trans (LinearMap.coprodEquiv D).symm
    exact_mod_cast w.finrank_eq.trans Module.finrank_prod

@[simp] theorem divisionEuler_of (P : FiniteProjective R) :
    divisionEuler D M (ProjectiveClass.of P) = Module.finrank D (P.val →ₗ[R] M) := by
  apply ProjectiveClass.lift_of

theorem divisionEuler_twoTerm (P : TwoTerm R) :
    divisionEuler D M P.projectiveClass =
      (Module.finrank D (P.target →ₗ[R] M) : ℤ) - Module.finrank D (P.source →ₗ[R] M) := by
  simp [TwoTerm.projectiveClass]

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

theorem divisionEuler_nonpos_of_submodule_tests (P : TwoTerm R) (hp : P.IsPresilting)
    (h : ∀ (N : FGModuleCat.{u} R) (i : N.obj ⟶ M), Function.Injective i.hom →
      (P.eulerWeight k).eval N ≤ 0) : divisionEuler D M P.projectiveClass ≤ 0 := by
  have := finite_hom_over_division D M P.source
  have hi := P.injective_precomposition_of_finite_submodule_tests k hp M h
  rw [divisionEuler_twoTerm,sub_nonpos]
  exact_mod_cast LinearMap.finrank_le_finrank_of_injective (f := P.differential.hom.hom.lcomp D M) hi

theorem divisionEuler_nonneg_of_quotient_tests (P : TwoTerm R) (hp : P.IsPresilting)
    (h : ∀ (Q : FGModuleCat.{u} R) (q : M ⟶ Q.obj), Function.Surjective q.hom →
      0 ≤ (P.eulerWeight k).eval Q) : 0 ≤ divisionEuler D M P.projectiveClass := by
  have := finite_hom_over_division D M P.target
  have hs := P.surjective_precomposition_of_finite_quotient_tests k hp M h
  rw [divisionEuler_twoTerm,sub_nonneg]
  exact_mod_cast LinearMap.finrank_le_finrank_of_surjective (f := P.differential.hom.hom.lcomp D M) hs

end EFiniteCharacterizations
