module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Lifting a null vector of a surjective specialization -/

@[expose] public section

open Matrix

namespace EFiniteCharacterizations

/-- A null vector at a surjective specialization lifts to a polynomial null vector
with the prescribed value at zero. The determinant and adjugate of the matrix
obtained from a right inverse give a lift over the polynomial ring. -/
theorem exists_polynomial_kernel_lift {k m n : Type*} [CommRing k]
    [Fintype m] [DecidableEq m] [Fintype n]
    (A : Matrix m n (Polynomial k)) (C : Matrix n m k)
    (hC : A.map (Polynomial.evalRingHom 0) * C = 1)
    (v : n → k) (hv : A.map (Polynomial.evalRingHom 0) *ᵥ v = 0) :
    ∃ w : n → Polynomial k, A *ᵥ w = 0 ∧ (Polynomial.evalRingHom 0) ∘ w = v := by
  let e := Polynomial.evalRingHom (0 : k)
  let v' := Polynomial.C ∘ v
  let C' := C.map Polynomial.C
  let L := A * C'
  let w := L.det • v' - C' *ᵥ (L.adjugate *ᵥ (A *ᵥ v'))
  refine ⟨w, ?_, ?_⟩
  · dsimp only [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      show A * C' = L from rfl, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hv' : e ∘ v' = v := by
    funext i
    simp [e, v', Function.comp_apply]
  have hC' : C'.map e = C := by
    apply Matrix.ext
    intro i j
    simp [e, C', Matrix.map_apply]
  have hL : L.map e = 1 := by
    dsimp only [L]
    rw [Matrix.map_mul, hC']
    exact hC
  have hd : e L.det = 1 := by
    rw [RingHom.map_det]
    change (L.map e).det = 1
    rw [hL, Matrix.det_one]
  have hz : e ∘ (A *ᵥ v') = 0 := by
    funext i
    change e ((A *ᵥ v') i) = 0
    rw [RingHom.map_mulVec, hv']
    exact congrFun hv i
  have hz' : e ∘ (L.adjugate *ᵥ (A *ᵥ v')) = 0 := by
    funext i
    change e ((L.adjugate *ᵥ (A *ᵥ v')) i) = 0
    rw [RingHom.map_mulVec, hz, Matrix.mulVec_zero, Pi.zero_apply]
  funext i
  change e (w i) = v i
  simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
  rw [hd, one_mul, RingHom.map_mulVec, hz', Matrix.mulVec_zero, Pi.zero_apply, sub_zero]
  exact congrFun hv' i

/-- The polynomial matrix of the pencil `A + t • B`. -/
noncomputable def affineMatrix {k m n : Type*} [CommRing k] (A B : Matrix m n k) :
    Matrix m n (Polynomial k) :=
  A.map Polynomial.C + (Polynomial.X : Polynomial k) • B.map Polynomial.C

theorem affineMatrix_eval {k m n : Type*} [CommRing k] (A B : Matrix m n k) (t : k) :
    (affineMatrix A B).map (Polynomial.evalRingHom t) = A + t • B := by
  ext i j
  simp [affineMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
  exact mul_comm _ _

/-- A null vector at the constant term of a linear-map pencil lifts to a
polynomial null vector in any chosen bases. -/
theorem exists_affine_kernel_lift {k V W m n : Type*} [Field k]
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (bV : Module.Basis n k V) (bW : Module.Basis m k W)
    (A B : V →ₗ[k] W) (hA : Function.Surjective A) (v : V) (hv : A v = 0) :
    ∃ w : n → Polynomial k,
      affineMatrix (LinearMap.toMatrix bV bW A) (LinearMap.toMatrix bV bW B) *ᵥ w = 0 ∧
      (Polynomial.evalRingHom 0) ∘ w = bV.equivFun v := by
  have : Module.Free k W := Module.Free.of_basis bW
  obtain ⟨r, hr⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA)
  apply exists_polynomial_kernel_lift _ (LinearMap.toMatrix bW bV r)
  · rw [affineMatrix_eval, zero_smul, add_zero, ← LinearMap.toMatrix_comp, hr, LinearMap.toMatrix_id]
  · rw [affineMatrix_eval, zero_smul, add_zero]
    change LinearMap.toMatrix bV bW A *ᵥ (bV.repr v : n → k) = 0
    rw [LinearMap.toMatrix_mulVec_repr, hv, map_zero]
    rfl

end EFiniteCharacterizations
