module

public import EFiniteCharacterizations.Stability.ProjectiveSubspacePairs
public import EFiniteCharacterizations.ScalarExtension.FieldWitnessFibres
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionRigidity

/-!
# Preservation of semistability under algebraic field extensions

Lemma A.2(1) (`lem:frob-dict`) of Appendix A: if a finite-dimensional `R`-module `M`
is semistable at an integral projective weight over `k`, then `F ⊗_k M` remains
semistable at the extended weight over every algebraic field extension `F / k`,
including `k̄` (`isSemistable_extendObj_of_algebraic`).
-/

@[expose] public section
open CategoryTheory Module
open scoped ModuleCat.Algebra TensorProduct

universe u
namespace EFiniteCharacterizations.FieldExtension

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

private noncomputable def homBasis {X Y : FGModuleCat.{u} R} {ι : Type*} (b : Basis ι k (X ⟶ Y)) :
    Basis ι F (extendObj k F R X ⟶ extendObj k F R Y) :=
  (Algebra.TensorProduct.basis F b).map (homTensorEquiv k F R X Y)

private theorem homBasis_apply {X Y : FGModuleCat.{u} R} {ι : Type*} (b : Basis ι k (X ⟶ Y)) (i : ι) :
    homBasis k F b i = (extend k F R).map (b i) := by
  rw [homBasis,Basis.map_apply,Algebra.TensorProduct.basis_apply]
  change homTensorMap k F R X Y (1 ⊗ₜ[k] b i) = _
  rw [homTensorMap_tmul,one_smul]
  rfl

private theorem homBasis_repr {X Y : FGModuleCat.{u} R} {ι : Type*} (b : Basis ι k (X ⟶ Y))
    (f : X ⟶ Y) (i : ι) :
    (homBasis k F b).repr ((extend k F R).map f) i = algebraMap k F (b.repr f i) := by
  let e := homTensorEquiv k F R X Y
  have eq : e (1 ⊗ₜ[k] f) = (extend k F R).map f := (one_smul F _)
  rw [← eq,homBasis,Basis.map_repr]
  change (Algebra.TensorProduct.basis F b).repr (e.symm (e _)) i = _
  rw [e.symm_apply_apply,Algebra.TensorProduct.basis_repr_tmul,one_smul]
  rfl

private theorem matrix_precomposition_extend {X Y Z : FGModuleCat.{u} R}
    {ι ν : Type*} [Fintype ι] [Finite ν] [DecidableEq ι]
    (u : Basis ι k (Y ⟶ Z)) (v : Basis ν k (X ⟶ Z)) (f : X ⟶ Y) :
    LinearMap.toMatrix (homBasis k F u) (homBasis k F v)
      (Linear.leftComp F (extendObj k F R Z) ((extend k F R).map f)) =
      (LinearMap.toMatrix u v (Linear.leftComp k Z f)).map (algebraMap k F) := by
  ext i j
  rw [LinearMap.toMatrix_apply,homBasis_apply]
  change ((homBasis k F v).repr ((extend k F R).map f ≫ (extend k F R).map (u j))) i = _
  simp only [Matrix.map_apply,LinearMap.toMatrix_apply,Linear.leftComp_apply]
  exact (congrArg (fun g ↦ (homBasis k F v).repr g i) ((extend k F R).map_comp f (u j)).symm).trans
    (homBasis_repr k F v (f ≫ u j) i)

private theorem extended_hom_test_iff_pairs (P : TwoTerm R) (M : FGModuleCat.{u} R)
    {a n m : Type*} [Fintype a] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (b : Basis a k (P.source ⟶ P.target)) (u : Basis n k (P.target ⟶ M)) (v : Basis m k (P.source ⟶ M))
    (test : ℕ → ℕ → Prop) :
    (∀ (U : Submodule F (extendObj k F R P.target ⟶ extendObj k F R M))
      (V : Submodule F (extendObj k F R P.source ⟶ extendObj k F R M)),
      (∀ (p : extendObj k F R P.source ⟶ extendObj k F R P.target) (f : U), p ≫ f.val ∈ V) →
        test (Module.finrank F U) (Module.finrank F V)) ↔
    ∀ r s, HasMatrixSubspacePair
      (fun j ↦ (LinearMap.toMatrix u v (Linear.leftComp k M (b j))).map (algebraMap k F)) r s → test r s := by
  let be := homBasis k F b
  let ue := homBasis k F u
  let ve := homBasis k F v
  have h := (extendTwoTerm k F R P).hom_subspace_test_iff_matrix_pairs F (extendObj k F R M) be ue ve test
  have eq (j : a) : LinearMap.toMatrix ue ve (Linear.leftComp F (extendObj k F R M) (be j)) = _ :=
    (homBasis_apply k F b j) ▸ matrix_precomposition_extend k F u v (b j)
  exact h.trans (iff_of_eq (congrArg (fun D ↦ ∀ r s, HasMatrixSubspacePair D r s → test r s) (funext eq)))

/-- A numerical test on pairs of projective Hom subspaces holds over an algebraic
extension if it holds over every finite intermediate field. -/
theorem hom_subspace_test_of_finite_models [Algebra.IsAlgebraic k F] (P : TwoTerm R)
    (M : FGModuleCat.{u} R) (test : ℕ → ℕ → Prop)
    (h : ∀ (E : IntermediateField k F) [Module.Finite k E],
      ∀ (U : Submodule E (extendObj k E R P.target ⟶ extendObj k E R M))
        (V : Submodule E (extendObj k E R P.source ⟶ extendObj k E R M)),
        (∀ (p : extendObj k E R P.source ⟶ extendObj k E R P.target) (f : U), p ≫ f.val ∈ V) →
          test (Module.finrank E U) (Module.finrank E V)) :
    ∀ (U : Submodule F (extendObj k F R P.target ⟶ extendObj k F R M))
      (V : Submodule F (extendObj k F R P.source ⟶ extendObj k F R M)),
      (∀ (p : extendObj k F R P.source ⟶ extendObj k F R P.target) (f : U), p ≫ f.val ∈ V) →
        test (Module.finrank F U) (Module.finrank F V) := by
  classical
  have := finiteModuleHom_isFinite k P.source P.target
  have := finiteModuleHom_isFinite k P.target M
  have := finiteModuleHom_isFinite k P.source M
  let b := Module.finBasis k (P.source ⟶ P.target)
  let u := Module.finBasis k (P.target ⟶ M)
  let v := Module.finBasis k (P.source ⟶ M)
  apply (extended_hom_test_iff_pairs k F P M b u v test).2
  intro r s hp
  obtain ⟨E,hE,he⟩ := matrixSubspacePair_finite_model _ r s hp
  exact ((extended_hom_test_iff_pairs k E P M b u v test).1 (h E)) r s he

variable [IsNoetherianRing R]

/-- Semistability at an integral projective weight ascends to every
algebraic field extension, including the algebraic closure. -/
theorem isSemistable_extendObj_of_algebraic [Algebra.IsAlgebraic k F]
    [IsNoetherianRing (ExtendedAlgebra k F R)] (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (hs : (P.eulerWeight k).IsSemistable M) :
    ((extendTwoTerm k F R P).eulerWeight F).IsSemistable (extendObj k F R M) := by
  apply ((extendTwoTerm k F R P).isSemistable_iff_no_shrunk_subspace F _).2
  refine ⟨?_,hom_subspace_test_of_finite_models k F P M (· ≤ ·) ?_⟩
  · simpa only [extendTwoTerm,homFinrank_extendObj] using ((P.isSemistable_iff_no_shrunk_subspace k M).1 hs).1
  · intro E hE
    let _ := IsNoetherianRing.of_finite E (ExtendedAlgebra k E R)
    exact (((extendTwoTerm k E R P).isSemistable_iff_no_shrunk_subspace E _).1
      (isSemistable_extendObj k E R P M hs)).2

end EFiniteCharacterizations.FieldExtension
