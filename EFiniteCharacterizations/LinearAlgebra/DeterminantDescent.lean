module

public import Mathlib.Data.Matrix.Composition
public import EFiniteCharacterizations.LinearAlgebra.MatrixBlowup
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Specialization of geometric determinants to finite ground matrices -/

@[expose] public section

open scoped TensorProduct

namespace EFiniteCharacterizations

variable (k : Type*) {F : Type*} [Field k] [Field F] [Algebra k F] [Algebra.IsAlgebraic k F]

/-- A geometric polynomial can be made a unit by substituting elements
from a finite ground extension into the second factor of its scalar extension.
The ground multiple has invertible value already in the second factor. -/
theorem exists_unit_tensor_evaluation [Infinite F] {ι : Type*} [Finite ι]
    (p : MvPolynomial ι F) (hp : p ≠ 0) :
    ∃ (E : IntermediateField k F) (_ : Module.Finite k E) (c : ι → E),
      IsUnit (MvPolynomial.aeval (R := F) (fun i ↦ (1 : F) ⊗ₜ[k] c i) p) := by
  classical
  obtain ⟨q,hq,hd⟩ := MvPolynomial.exists_dvd_map_of_isAlgebraic (R := k) hp
  have hq' : q.map (algebraMap k F) ≠ 0 := (map_ne_zero_iff _
    (MvPolynomial.map_injective (algebraMap k F) (algebraMap k F).injective)).2 hq
  obtain ⟨z,hz⟩ : ∃ z : ι → F, MvPolynomial.eval z (q.map (algebraMap k F)) ≠ 0 := by
    by_contra! h
    exact hq' (MvPolynomial.funext fun z ↦ (h z).trans (map_zero _).symm)
  let E := IntermediateField.adjoin k (Set.range z)
  have hE : Module.Finite k E := IntermediateField.finiteDimensional_adjoin
    fun u _ ↦ (Algebra.IsAlgebraic.isAlgebraic u).isIntegral
  let c (i : ι) : E := ⟨z i,IntermediateField.subset_adjoin k _ ⟨i,rfl⟩⟩
  let incl : E →ₐ[k] F ⊗[k] E := Algebra.TensorProduct.includeRight
  let ev := MvPolynomial.aeval (R := F) (fun i ↦ incl (c i))
  have hval : MvPolynomial.aeval c q ≠ 0 := by
    intro h
    apply hz
    have he : (MvPolynomial.eval z).comp (MvPolynomial.map (algebraMap k F)) =
        E.val.toRingHom.comp (MvPolynomial.aeval c).toRingHom := by
      apply MvPolynomial.ringHom_ext'
      · ext; simp
      · intro i; simp [c]
    exact (DFunLike.congr_fun he q).trans (by simp [h])
  have hmap : ev.toRingHom.comp (MvPolynomial.map (algebraMap k F)) =
      incl.toRingHom.comp (MvPolynomial.aeval c).toRingHom := by
    apply MvPolynomial.ringHom_ext'
    · ext x
      simp only [RingHom.comp_apply,MvPolynomial.map_C,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,MvPolynomial.aeval_C,ev]
      exact (IsScalarTower.algebraMap_apply k F (F ⊗[k] E) x).symm.trans (incl.commutes x).symm
    · intro i
      simp [ev]
  refine ⟨E,hE,c,?_⟩
  change IsUnit (ev p)
  have hu : IsUnit (ev (MvPolynomial.map (algebraMap k F) q)) := by
    rw [show ev (MvPolynomial.map (algebraMap k F) q) = incl (MvPolynomial.aeval c q) from DFunLike.congr_fun hmap q]
    exact (isUnit_iff_ne_zero.mpr hval).map incl.toRingHom.toMonoidHom
  exact isUnit_of_dvd_unit (α := F ⊗[k] E) (x := ev p) (y := ev _) (map_dvd ev.toRingHom.toMonoidHom hd) hu

omit [Algebra.IsAlgebraic k F] in
private theorem leftMulMatrix_tmul {E : Type*} [Field E] [Algebra k E] {m : Type*}
    [Fintype m] [DecidableEq m] (b : Module.Basis m k E) (c : E) (d : F) (i j : m) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis F b) (d ⊗ₜ[k] c) i j =
      algebraMap k F (b.repr (c * b j) i) * d := by
  simp [Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.tmul_mul_tmul,mul_comm]

set_option maxHeartbeats 1600000 in
/-- An invertible geometric block matrix can be replaced by a larger block
matrix whose coefficients are in the ground field. The entries of the
matrix family itself may be geometric. -/
theorem exists_ground_invertible_block [Infinite F] {a n : Type*} [Fintype a] [Fintype n]
    [DecidableEq n] (D : a → Matrix n n F) {t : ℕ} (ht : 0 < t)
    (z : Fin t × (a × Fin t) → F) (hz : (blockFamily D z).det ≠ 0) :
    ∃ (m : ℕ) (_ : 0 < m) (x : Fin m × (a × Fin m) → k),
      (blockFamily D (fun j ↦ algebraMap k F (x j))).det ≠ 0 := by
  classical
  let A : Matrix (Fin t × n) (Fin t × n) (MvPolynomial (Fin t × (a × Fin t)) F) :=
    Matrix.of fun i j ↦ ∑ l, MvPolynomial.X (i.1,l,j.1) * MvPolynomial.C (D l i.2 j.2)
  have hA : A.det ≠ 0 := by
    intro h
    apply hz
    have he : A.map (MvPolynomial.eval z) = blockFamily D z := by
      ext i j
      simp [A,Matrix.map_apply,blockFamily]
    rw [← he]
    exact (RingHom.map_det (MvPolynomial.eval z) A).symm.trans (by rw [h,map_zero])
  obtain ⟨E,hE,c,hu⟩ := exists_unit_tensor_evaluation k A.det hA
  let ev := MvPolynomial.aeval (R := F) (fun i ↦ (1 : F) ⊗ₜ[k] c i)
  have heval : ev A.det = (A.map ev).det := by
    let f : MvPolynomial (Fin t × (a × Fin t)) F →+* (F ⊗[k] E) := ev.toRingHom
    exact RingHom.map_det (S := F ⊗[k] E) f A
  have hunit : IsUnit (ev A.det) := hu
  rw [heval] at hunit
  have hmat : IsUnit (A.map ev) := (Matrix.isUnit_iff_isUnit_det _).2 hunit
  let q := Module.finrank k E
  let b := Module.finBasis k E
  let ρ := Algebra.leftMulMatrix (R := F) (S := F ⊗[k] E) (Algebra.TensorProduct.basis F b)
  let φ := ρ.toRingHom.mapMatrix (m := Fin t × n)
  let flat := Matrix.compRingEquiv (Fin t × n) (Fin q) F
  let pair : Fin t × Fin q ≃ Fin (t*q) := finProdFinEquiv
  let e : (Fin t × n) × Fin q ≃ Fin (t*q) × n :=
    { toFun := fun ((i,l),j) ↦ (pair (i,j),l)
      invFun := fun (v,l) ↦ ((pair.symm v |>.1,l), (pair.symm v).2)
      left_inv := fun ((i,l),j) ↦ by simp
      right_inv := fun (v,l) ↦ by simp }
  let x (p : Fin (t*q) × (a × Fin (t*q))) :=
    let i := pair.symm p.1
    let j := pair.symm p.2.2
    b.repr (c (i.1,p.2.1,j.1) * b j.2) i.2
  refine ⟨t*q,Nat.mul_pos ht Module.finrank_pos,x,?_⟩
  have H := (hmat.map φ.toMonoidHom).map flat.toRingHom.toMonoidHom
  have H' := H.map (Matrix.reindexRingEquiv F e).toRingHom.toMonoidHom
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).1
  convert H' using 1
  ext ⟨i,l⟩ ⟨j,m⟩
  change (∑ v, algebraMap k F (x (i,v,j)) * D v l m) =
    ρ (ev (∑ v, MvPolynomial.X ((pair.symm i).1,v,(pair.symm j).1) *
      MvPolynomial.C (D v l m))) (pair.symm i).2 (pair.symm j).2
  simp only [ev,map_sum,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro v _
  rw [← map_mul ρ]
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]
  exact (leftMulMatrix_tmul k b _ _ _ _).symm

end EFiniteCharacterizations
