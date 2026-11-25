module

public import EFiniteCharacterizations.LinearAlgebra.MatrixRankSpecialization
public import EFiniteCharacterizations.LinearAlgebra.PolynomialTensor

/-! # Rank bounds for a pencil of linear maps -/

@[expose] public section

open Matrix

namespace EFiniteCharacterizations

variable {k F U V : Type*} [Field k] [Field F] [Algebra k F]
  [AddCommGroup U] [AddCommGroup V] [Module k U] [Module k V]
  [Module.Finite k U] [Module.Finite k V]

private theorem rank_toMatrix {K W Z m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq n] [AddCommGroup W] [AddCommGroup Z] [Module K W] [Module K Z]
    (bW : Module.Basis n K W) (bZ : Module.Basis m K Z) (f : W →ₗ[K] Z) :
    (LinearMap.toMatrix bW bZ f).rank = Module.finrank K (LinearMap.range f) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ bZ bW, Matrix.toLin_toMatrix]

/-- Extension of scalars preserves the rank of a linear map over a field. -/
theorem finrank_range_baseChange (A : U →ₗ[k] V) :
    Module.finrank F (LinearMap.range (A.baseChange F)) = Module.finrank k (LinearMap.range A) := by
  classical
  let bU := Module.finBasis k U
  let bV := Module.finBasis k V
  rw [← rank_toMatrix bU bV A, ← rank_toMatrix (bU.baseChange F) (bV.baseChange F),
    toMatrix_baseChange, matrix_rank_map_from_field]

/-- The rank of a pencil at any ground-field parameter is at most its rank
where the parameter is transcendental. -/
theorem affine_finrank_range_eval_le (e : Polynomial k →ₐ[k] F) (he : Function.Injective e)
    (A B : U →ₗ[k] V) (t : k) :
    Module.finrank k (LinearMap.range (A + t • B)) ≤
      Module.finrank F (LinearMap.range (A.baseChange F + (e Polynomial.X) • B.baseChange F)) := by
  classical
  let bU := Module.finBasis k U
  let bV := Module.finBasis k V
  let a := LinearMap.toMatrix bU bV A
  let b := LinearMap.toMatrix bU bV B
  have h := matrix_rank_specialization_le_of_injective (Polynomial.evalRingHom t) Polynomial.C
    (by ext x; simp) e.toRingHom he (affineMatrix a b)
  rw [affineMatrix_eval] at h
  have hbase (D : U →ₗ[k] V) :
      (LinearMap.toMatrix bU bV D).map (e.toRingHom.comp Polynomial.C) =
        LinearMap.toMatrix (bU.baseChange F) (bV.baseChange F) (D.baseChange F) := by
    rw [toMatrix_baseChange]
    ext i j
    exact e.commutes _
  have hmatrix : (affineMatrix a b).map e.toRingHom =
      LinearMap.toMatrix (bU.baseChange F) (bV.baseChange F)
        (A.baseChange F + (e Polynomial.X) • B.baseChange F) := by
    ext i j
    have ha := congrArg (fun M : Matrix _ _ F ↦ M i j) (hbase A)
    have hb := congrArg (fun M : Matrix _ _ F ↦ M i j) (hbase B)
    simp only [Matrix.map_apply, RingHom.comp_apply] at ha hb
    simp only [affineMatrix, a, b, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_smul, map_mul]
    rw [ha, hb]
    rfl
  rw [hmatrix, rank_toMatrix] at h
  rw [← rank_toMatrix bU bV]
  simpa [a, b] using h

end EFiniteCharacterizations
