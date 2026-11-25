module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionTower
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Finite fields of definition inside an algebraic extension -/

@[expose] public section

open CategoryTheory Module
open scoped TensorProduct ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FieldExtension

variable (K L D : Type u) [Field K] [Field L] [Algebra K L] [Ring D] [Algebra K D] [Module.Finite K D]

private theorem model_of_invariant_basis (Y : FGModuleCat.{u} (ExtendedAlgebra K L D))
    {ι : Type*} [Fintype ι] (b : Basis ι L (Y.obj : Type u))
    (h : ∀ (r : D) (j : ι), (algebraInclusion K L D r) • b j ∈ Submodule.span K (Set.range b)) :
    ∃ X : FGModuleCat.{u} D, Nonempty (extendObj K L D X ≅ Y) := by
  classical
  let _ := IsNoetherianRing.of_finite L (ExtendedAlgebra K L D)
  let _ := isScalarTower_ground_extension K L D Y.obj
  let H := Submodule.span K (Set.range b)
  let Z := (ModuleCat.restrictScalars (algebraInclusion K L D).toRingHom).obj Y.obj
  let i := restrictVectorSpaceEquiv K L D Y.obj
  have closed (r : D) {y : Y} (hy : y ∈ H) : (algebraInclusion K L D r) • y ∈ H := by
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨j,rfl⟩ := hx; exact h r j
    | zero => simpa only [smul_zero] using H.zero_mem
    | add x z _ _ hx hz => rw [smul_add]; exact H.add_mem hx hz
    | smul c x _ hx =>
      rw [smul_comm (algebraInclusion K L D r) c]
      exact H.smul_mem c hx
  let W : Submodule D Z :=
    { carrier := {z | i z ∈ H}
      zero_mem' := H.zero_mem
      add_mem' := fun hx hy ↦ H.add_mem hx hy
      smul_mem' := fun r _ hx ↦ closed r hx }
  let w : W ≃ₗ[K] H :=
    { toFun := fun z ↦ ⟨i z,z.property⟩
      invFun := fun y ↦ ⟨i.symm y,y.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c z ↦ Subtype.ext (i.map_smul c z.val) }
  let bw := (b.restrictScalars K).map w.symm
  let _ : Module.Finite K W := Module.Finite.of_basis bw
  let _ : Module.Finite D W := Module.Finite.of_restrictScalars_finite K D W
  let X := FGModuleCat.of D W
  let vw : W ≃ₗ[K] X.obj := { Equiv.refl _ with map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let bx := bw.map vw
  let f : extendObj K L D X ⟶ Y := extendLinearOfRestrict K L D (M := X) W.subtype
  let be := (Algebra.TensorProduct.basis L bx).map (extendVectorSpaceEquiv K L D X).symm
  let e := be.equiv b (Equiv.refl ι)
  have eq : f.hom.hom.restrictScalars L = e.toLinearMap := by
    apply be.ext
    intro j
    rw [LinearEquiv.coe_coe,Basis.equiv_apply]
    change f.hom.hom ((Algebra.TensorProduct.basis L bx) j) = b j
    rw [Algebra.TensorProduct.basis_apply]
    exact (extendLinearOfRestrict_one_tmul K L D (M := X) W.subtype (bx j)).trans (b.restrictScalars_apply K j)
  let _ : IsIso f := (FGModuleCat.isIso_iff_bijective f).2 (show Function.Bijective (f.hom.hom.restrictScalars L) from eq ▸ e.bijective)
  exact ⟨X,⟨asIso f⟩⟩

private theorem invariant_under_tensor_algebra {k F L R : Type u} [Field k] [Field F] [Field L] [Algebra k F]
    [Algebra F L] [Ring R] [Algebra k R] (Y : FGModuleCat.{u} (ExtendedAlgebra F L (ExtendedAlgebra k F R)))
    (H : Submodule F (Y.obj : Type u)) (y : Y) (h : ∀ r : R, algebraInclusion F L (ExtendedAlgebra k F R)
      ((1 : F) ⊗ₜ[k] r) • y ∈ H) (d : ExtendedAlgebra k F R) :
    algebraInclusion F L (ExtendedAlgebra k F R) d • y ∈ H := by
  let i := algebraInclusion F L (ExtendedAlgebra k F R)
  refine TensorProduct.inductionOn d ?_ ?_
  · intro c r
    have hc : c ⊗ₜ[k] r = c • ((1 : F) ⊗ₜ[k] r) := by rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    change i _ • y ∈ H
    rw [hc,Algebra.smul_def,map_mul,AlgHom.commutes,mul_smul]
    exact H.smul_mem c (h r)
  · intro a d ha hd
    rw [map_add,add_smul]
    exact H.add_mem ha hd

section Descent

variable (k L R : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
  [Ring R] [Algebra k R] [Module.Finite k R]

private theorem exists_field_of_matrix_coefficients {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : R →ₐ[k] Matrix I I L) : ∃ E : IntermediateField k L, Module.Finite k E ∧
      ∀ (r : R) (i j : I), ρ r i j ∈ E := by
  classical
  let br := Module.finBasis k R
  let J := Fin (Module.finrank k R)
  let coeff (p : J × I × I) := ρ (br p.1) p.2.1 p.2.2
  let E := IntermediateField.adjoin k (Set.range coeff)
  let _ : Module.Finite k E := IntermediateField.finiteDimensional_adjoin fun c _ ↦
    (Algebra.IsAlgebraic.isAlgebraic (R := k) c).isIntegral
  refine ⟨E,inferInstance,fun r i j ↦ ?_⟩
  rw [← br.sum_repr r,map_sum,Matrix.sum_apply]
  apply E.sum_mem
  intro t _
  rw [map_smul,Matrix.smul_apply,Algebra.smul_def]
  exact E.mul_mem (E.algebraMap_mem _) (IntermediateField.subset_adjoin k _ ⟨(t,i,j),rfl⟩)

/-- A finite module over an algebraic extension of a finite-dimensional algebra
is obtained from a finite intermediate field of definition. -/
theorem exists_finite_field_of_definition (X : FGModuleCat.{u} (ExtendedAlgebra k L R)) :
    ∃ E : IntermediateField k L, Module.Finite k E ∧
      ∃ B : FGModuleCat.{u} (ExtendedAlgebra k E R), Nonempty
        ((towerEquivalence k E L R).functor.obj (extendObj E L (ExtendedAlgebra k E R) B) ≅ X) := by
  classical
  let _ : Module.Finite L (X.obj : Type u) := Module.Finite.trans (ExtendedAlgebra k L R) _
  let b := Module.finBasis L (X.obj : Type u)
  let I := Fin (Module.finrank L (X.obj : Type u))
  let ρ : R →ₐ[k] Matrix I I L :=
    (((LinearMap.toMatrixAlgEquiv b).toAlgHom.comp
      (Algebra.lsmul L L (X.obj : Type u))).restrictScalars k).comp (algebraInclusion k L R)
  obtain ⟨E,hE,mem⟩ := exists_field_of_matrix_coefficients k L R ρ
  let RK := ExtendedAlgebra k E R
  let G := towerEquivalence k E L R
  let Y := G.inverse.obj X
  let v : Y.obj ≃ₗ[L] X.obj :=
    { Equiv.refl _ with map_add' := fun _ _ ↦ rfl
                        map_smul' := fun c x ↦ congrArg (· • (show X from x)) ((towerAlgebraEquiv k E L R).symm.commutes c) }
  let bY := b.map v.symm
  let _ := isScalarTower_ground_extension E L RK Y.obj
  have ground (r : R) (j : I) :
      (algebraInclusion E L RK ((1 : E) ⊗ₜ[k] r)) • bY j ∈ Submodule.span E (Set.range bY) := by
    apply (bY.mem_span_iff_repr_mem E _).2
    intro i
    refine ⟨⟨ρ r i j,mem r i j⟩,?_⟩
    change ρ r i j = (b.map v.symm).repr _ i
    rw [Basis.map_repr,LinearEquiv.trans_apply]
    change (LinearMap.toMatrixAlgEquiv b _ i j) = _
    rw [LinearMap.toMatrixAlgEquiv_apply]
    apply congrArg (fun x ↦ b.repr x i)
    change (algebraInclusion k L R r) • b j =
      (towerAlgebraEquiv k E L R).symm ((1 : L) ⊗ₜ[E] ((1 : E) ⊗ₜ[k] r)) • b j
    rw [show (towerAlgebraEquiv k E L R).symm ((1 : L) ⊗ₜ[E] ((1 : E) ⊗ₜ[k] r)) =
      (1 : E) • (1 : L) ⊗ₜ[k] r from rfl,one_smul]
    rfl
  obtain ⟨B,⟨e⟩⟩ := model_of_invariant_basis E L RK Y bY (fun d j ↦
    invariant_under_tensor_algebra Y (Submodule.span E (Set.range bY)) (bY j) (fun r ↦ ground r j) d)
  exact ⟨E,inferInstance,B,⟨(G.functor.mapIso e).trans (G.counitIso.app X)⟩⟩

end Descent

end EFiniteCharacterizations.FieldExtension
