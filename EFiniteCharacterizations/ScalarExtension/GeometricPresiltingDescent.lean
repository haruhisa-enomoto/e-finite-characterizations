module

public import EFiniteCharacterizations.ScalarExtension.FinitePresiltingDescent
public import EFiniteCharacterizations.LinearAlgebra.SurjectiveSpecialization
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Presilting differentials on ground projective terms over an algebraic closure -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

variable {k F R : Type u} [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R]

private theorem finite_field_of_definition {V : Type u} [AddCommGroup V] [Module k V]
    [Algebra.IsAlgebraic k F] (z : F ⊗[k] V) :
    ∃ E : IntermediateField k F, Module.Finite k E ∧
      ∃ w : E ⊗[k] V, TensorProduct.map E.val.toLinearMap LinearMap.id w = z := by
  classical
  obtain ⟨a,ha⟩ := TensorProduct.exists_finsupp_left z
  let E := IntermediateField.adjoin k (a.support : Set F)
  have hE : Module.Finite k E := IntermediateField.finiteDimensional_adjoin
    fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let c (i : a.support) : E := ⟨i,IntermediateField.subset_adjoin k _ i.property⟩
  refine ⟨E,hE,∑ i : a.support, c i ⊗ₜ[k] a i,?_⟩
  rw [ha,map_sum]
  simp [Finsupp.sum,c]

/-- Over an algebraic extension of a finite field, a rigid differential
on extended terms gives a ground presilting representative of their class. -/
theorem exists_presilting_class_of_algebraic_extension_of_finite [Fintype k]
    [Algebra.IsAlgebraic k F] (P : TwoTerm R)
    (p : (extendTwoTerm k F R P).source ⟶ (extendTwoTerm k F R P).target)
    (hp : ({ extendTwoTerm k F R P with differential := p }).IsPresilting) :
    ∃ Q : TwoTerm R, Q.IsPresilting ∧ Q.projectiveClass = P.projectiveClass := by
  let H := extendScalarCategory k F R
  obtain ⟨d,hd⟩ := (homTensorEquiv k F R P.source P.target).surjective p
  obtain ⟨E,hE,w,hw⟩ := finite_field_of_definition d
  let X : ScalarCategory k E (FGModuleCat.{u} R) := ⟨P.source⟩
  let Y : ScalarCategory k E (FGModuleCat.{u} R) := ⟨P.target⟩
  let q : X ⟶ Y := w
  let G := ScalarCategory.changeScalars (C := FGModuleCat.{u} R) E.val
  have hmap : H.map (G.map q) = p := by
    change homTensorMap k F R _ _ (TensorProduct.map E.val.toLinearMap LinearMap.id w) = p
    rw [hw]
    exact hd
  have hrigid : Function.Surjective (boundaryLinear E q q) := by
    apply (boundaryLinear_changeScalars_surjective_iff E.val q).1
    apply (boundaryLinear_map_surjective_iff F F H (G.map q) (G.map q)).1
    rw [hmap]
    exact hp
  have : Finite E := Module.finite_of_finite k
  let J := extendScalarCategory k E R
  exact exists_presilting_class_of_finite_extension P (J.map q)
    ((boundaryLinear_map_surjective_iff E E J q q).2 hrigid)

private def selfBoundaryLinear (K : Type*) [Field K] {C : Type*} [Category C]
    [Preadditive C] [Linear K C] (X Y : C) :
    (X ⟶ Y) →ₗ[K] ((X ⟶ X) × (Y ⟶ Y)) →ₗ[K] (X ⟶ Y) where
  toFun p := boundaryLinear K p p
  map_add' p q := by apply LinearMap.ext; intro x; simp [sub_add_sub_comm]
  map_smul' a p := by apply LinearMap.ext; intro x; simp [Linear.smul_comp,Linear.comp_smul,smul_sub]

/-- Over an infinite ground field a geometric presilting differential
specializes to one on the very same ground projective terms. -/
theorem exists_presilting_differential_of_extension_of_infinite [Infinite k] (P : TwoTerm R)
    (p : (extendTwoTerm k F R P).source ⟶ (extendTwoTerm k F R P).target)
    (hp : ({ extendTwoTerm k F R P with differential := p }).IsPresilting) :
    ∃ q : P.source ⟶ P.target, ({P with differential := q}).IsPresilting := by
  classical
  let X := extendObj k F R P.source
  let Y := extendObj k F R P.target
  have := finiteModuleHom_isFinite k P.source P.target
  have := finiteModuleHom_isFinite F X Y
  let b := Module.finBasis k (P.source ⟶ P.target)
  let e := homTensorEquiv k F R P.source P.target
  let b' := (Algebra.TensorProduct.basis F b).map e
  have hb (i) : b' i = extendMap k F R (b i) := by
    change e ((Algebra.TensorProduct.basis F b) i) = _
    rw [Algebra.TensorProduct.basis_apply]
    exact (homTensorMap_tmul k F R 1 (b i)).trans (one_smul F _)
  let L := selfBoundaryLinear F X Y
  let D i := L (b' i)
  have hs : Function.Surjective (∑ i, b'.repr p i • D i : _ →ₗ[F] _) := by
    have he := congrArg L (b'.sum_repr p)
    simp only [map_sum,map_smul] at he
    change Function.Surjective (∑ i, b'.repr p i • L (b' i) : _ →ₗ[F] _)
    rw [he]
    exact hp
  obtain ⟨c,hc⟩ := exists_surjective_ground_coefficients k F D _ hs
  let q := ∑ i, c i • b i
  refine ⟨q,(isPresilting_extendTwoTerm_iff k F R {P with differential := q}).1 ?_⟩
  have he : extendMap k F R q = ∑ i, algebraMap k F (c i) • b' i := by
    change extendMapLinear k F R _ _ (∑ i, c i • b i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,hb]
    have := isScalarTower_ground_extension_hom k F R X Y
    exact (IsScalarTower.algebraMap_smul F (c i) (extendMap k F R (b i))).symm
  change Function.Surjective (L (extendMap k F R q))
  simpa only [he,map_sum,map_smul] using hc

/-- A missing ground projective class never acquires a presilting
differential on its extended terms over an algebraic closure. -/
theorem no_presilting_differential_over_algebraic_extension [Algebra.IsAlgebraic k F]
    (P : TwoTerm R) (h : ¬ ∃ Q : TwoTerm R, Q.IsPresilting ∧ Q.projectiveClass = P.projectiveClass)
    (p : (extendTwoTerm k F R P).source ⟶ (extendTwoTerm k F R P).target) :
    ¬ ({extendTwoTerm k F R P with differential := p}).IsPresilting := by
  intro hp
  apply h
  rcases finite_or_infinite k with hk | hk
  · let := Fintype.ofFinite k
    exact exists_presilting_class_of_algebraic_extension_of_finite P p hp
  · obtain ⟨q,hq⟩ := exists_presilting_differential_of_extension_of_infinite P p hp
    exact ⟨{P with differential := q},hq,rfl⟩

end EFiniteCharacterizations.FieldExtension
