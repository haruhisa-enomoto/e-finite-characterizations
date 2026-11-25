module

public import EFiniteCharacterizations.LinearAlgebra.PolynomialKernelLift
public import EFiniteCharacterizations.LinearAlgebra.TensorBilinear
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Polynomial solutions of linear systems in scalar extensions -/

@[expose] public section

open scoped TensorProduct
open Matrix

namespace EFiniteCharacterizations

variable {k S V W : Type*} [CommRing k] [AddCommGroup V] [AddCommGroup W]
  [Module k V] [Module k W]

/-- Evaluate the polynomial coefficients of a scalar extension of a module. -/
noncomputable def polynomialEval (t : k) : Polynomial k ⊗[k] V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap.comp
    (TensorProduct.map (Polynomial.aeval t).toLinearMap LinearMap.id)

@[simp] theorem polynomialEval_tmul (t : k) (p : Polynomial k) (v : V) :
    polynomialEval t (p ⊗ₜ[k] v) = p.eval t • v := by
  simp [polynomialEval, Polynomial.aeval_def, Polynomial.eval₂_id]

theorem polynomialEval_baseChange (t : k) (f : V →ₗ[k] W) (z : Polynomial k ⊗[k] V) :
    polynomialEval t (f.baseChange (Polynomial k) z) = f (polynomialEval t z) := by
  refine TensorProduct.inductionOn z (fun p v ↦ by simp) ?_
  intro x y hx hy
  simp [hx, hy]

theorem polynomialEval_baseChangeBilinear {U : Type*} [AddCommGroup U] [Module k U]
    (t : k) (f : U →ₗ[k] V →ₗ[k] W) (u : Polynomial k ⊗[k] U) (v : Polynomial k ⊗[k] V) :
    polynomialEval t (baseChangeBilinear (Polynomial k) f u v) =
      f (polynomialEval t u) (polynomialEval t v) := by
  revert v
  refine TensorProduct.inductionOn u ?_ ?_
  · intro p a v
    refine TensorProduct.inductionOn v (fun q b ↦ by simp [smul_smul, mul_comm]) ?_
    intro b b' hb hb'
    simp only [map_add, hb, hb']
  · intro a a' ha ha' v
    simp only [map_add, LinearMap.add_apply, ha v, ha' v]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
  (bV : Module.Basis n k V) (bW : Module.Basis m k W)

theorem toMatrix_baseChange [CommRing S] [Algebra k S] (f : V →ₗ[k] W) :
    LinearMap.toMatrix (bV.baseChange S) (bW.baseChange S) (f.baseChange S) =
      (LinearMap.toMatrix bV bW f).map (algebraMap k S) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.map_apply, Algebra.smul_def]

omit [Fintype n] [DecidableEq n] in
theorem polynomialEval_coord (t : k) (z : Polynomial k ⊗[k] V) (i : n) :
    bV.repr (polynomialEval t z) i = ((bV.baseChange (Polynomial k)).repr z i).eval t := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro p v
    simp only [polynomialEval_tmul, map_smul, Finsupp.smul_apply, Module.Basis.baseChange_repr_tmul,
      smul_eq_mul, Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_comm _ _
  · intro x y hx hy
    simp [hx, hy]

omit [Fintype n] [DecidableEq n] in
theorem baseChange_coord_map [CommRing S] [Algebra k S] {T : Type*} [CommRing T] [Algebra k T]
    (e : S →ₐ[k] T) (z : S ⊗[k] V) (i : n) :
    (bV.baseChange T).repr (TensorProduct.map e.toLinearMap LinearMap.id z) i =
      e ((bV.baseChange S).repr z i) := by
  refine TensorProduct.inductionOn z (fun s v ↦ by simp [Algebra.smul_def, e.commutes]) ?_
  intro x y hx hy
  simp [hx, hy]

/-- A null vector of a surjective constant term lifts to the polynomial scalar extension. -/
theorem exists_tensor_affine_kernel_lift {k V W : Type*} [Field k]
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W]
    [Module.Finite k V] [Module.Finite k W]
    (A B : V →ₗ[k] W) (hA : Function.Surjective A) (v : V) (hv : A v = 0) :
    ∃ w : Polynomial k ⊗[k] V,
      (A.baseChange (Polynomial k) + (Polynomial.X : Polynomial k) • B.baseChange (Polynomial k)) w = 0 ∧
      polynomialEval (0 : k) w = v := by
  classical
  let bV := Module.finBasis k V
  let bW := Module.finBasis k W
  let bV' := bV.baseChange (Polynomial k)
  let bW' := bW.baseChange (Polynomial k)
  obtain ⟨w, hw, hw₀⟩ := exists_affine_kernel_lift bV bW A B hA v hv
  let z := bV'.equivFun.symm w
  have hz : (bV'.repr z : _ → Polynomial k) = w := bV'.equivFun.apply_symm_apply w
  let f := A.baseChange (Polynomial k) + (Polynomial.X : Polynomial k) • B.baseChange (Polynomial k)
  have hf : LinearMap.toMatrix bV' bW' f =
      affineMatrix (LinearMap.toMatrix bV bW A) (LinearMap.toMatrix bV bW B) := by
    simp only [f, map_add, map_smul]
    rw [toMatrix_baseChange bV bW, toMatrix_baseChange bV bW]
    rfl
  refine ⟨z, ?_, ?_⟩
  · apply bW'.repr.injective
    apply Finsupp.ext
    intro i
    change bW'.repr (f z) i = bW'.repr 0 i
    rw [← LinearMap.toMatrix_mulVec_repr bV' bW', hf, hz, hw, map_zero]
    rfl
  · apply bV.repr.injective
    apply Finsupp.ext
    intro i
    change bV.repr (polynomialEval 0 z) i = bV.repr v i
    rw [polynomialEval_coord, show bV.baseChange (Polynomial k) = bV' from rfl]
    exact (congrArg (Polynomial.eval 0) (congrFun hz i)).trans (congrFun hw₀ i)

end EFiniteCharacterizations
