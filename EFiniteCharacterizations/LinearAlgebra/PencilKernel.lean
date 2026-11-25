module

public import EFiniteCharacterizations.LinearAlgebra.PolynomialTensor
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Polynomial kernels of pencils on arbitrary vector spaces -/

@[expose] public section

open scoped TensorProduct

namespace EFiniteCharacterizations

variable {k V W : Type*} [Field k] [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W]

/-- The coefficient of degree n in the expansion at one. -/
private noncomputable def atOneCoeff (n : ℕ) : Polynomial k ⊗[k] V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap.comp
    (TensorProduct.map ((Polynomial.lcoeff k n).comp (Polynomial.taylor 1)) LinearMap.id)

private theorem atOneCoeff_tmul (n : ℕ) (p : Polynomial k) (v : V) :
    atOneCoeff n (p ⊗ₜ[k] v) = ((Polynomial.taylor 1 p).coeff n) • v := rfl

private theorem atOneCoeff_map (n : ℕ) (f : V →ₗ[k] W) (z : Polynomial k ⊗[k] V) :
    atOneCoeff n (f.baseChange (Polynomial k) z) = f (atOneCoeff n z) := by
  refine TensorProduct.inductionOn z (fun p v ↦ by simp [atOneCoeff_tmul]) ?_
  intro _ _ ha hb
  simp [ha,hb]

private theorem atOneCoeff_X_zero (z : Polynomial k ⊗[k] V) :
    atOneCoeff 0 ((Polynomial.X : Polynomial k) • z) = atOneCoeff 0 z := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro p v
    simp [TensorProduct.smul_tmul',atOneCoeff_tmul,smul_eq_mul,Polynomial.taylor_mul]
  · intro _ _ ha hb
    simp [smul_add,ha,hb]

private theorem atOneCoeff_X_succ (n : ℕ) (z : Polynomial k ⊗[k] V) :
    atOneCoeff (n+1) ((Polynomial.X : Polynomial k) • z) = atOneCoeff n z + atOneCoeff (n+1) z := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro p v
    simp [TensorProduct.smul_tmul',atOneCoeff_tmul,smul_eq_mul,Polynomial.taylor_mul,
      add_mul,Polynomial.coeff_X_mul,add_smul]
  · intro _ _ ha hb
    simp only [smul_add,map_add,ha,hb]
    abel

/-- If a pencil is injective at one, it has no nonzero polynomial kernel
vectors. The source and target may have arbitrary dimension. -/
theorem polynomial_pencil_injective (A B : V →ₗ[k] W) (h : Function.Injective (A + B)) :
    Function.Injective (A.baseChange (Polynomial k) + (Polynomial.X : Polynomial k) • B.baseChange (Polynomial k)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.2
  intro z hz
  have hc (n : ℕ) : atOneCoeff n z = 0 := by
    induction n with
    | zero =>
      apply h
      simpa only [LinearMap.add_apply,LinearMap.smul_apply,map_zero,map_add,atOneCoeff_X_zero,atOneCoeff_map]
        using congrArg (atOneCoeff 0) hz
    | succ n ih =>
      apply h
      simpa only [LinearMap.add_apply,LinearMap.smul_apply,map_zero,map_add,atOneCoeff_X_succ,
        atOneCoeff_map,ih,zero_add] using congrArg (atOneCoeff (n+1)) hz
  classical
  let b := Module.Free.chooseBasis k V
  apply (b.baseChange (Polynomial k)).repr.injective
  ext i n
  have he (q : Polynomial k ⊗[k] V) (j : ℕ) :
      (Polynomial.taylor 1 (((b.baseChange (Polynomial k)).repr q) i)).coeff j =
        b.repr (atOneCoeff j q) i := by
    refine TensorProduct.inductionOn q ?_ ?_
    · intro p v
      simp [Module.Basis.baseChange_repr_tmul,atOneCoeff_tmul,Polynomial.smul_eq_C_mul,Polynomial.taylor_mul,mul_comm]
    · intro x y hx hy
      simp [map_add,hx,hy]
  have hp : Polynomial.taylor 1 (((b.baseChange (Polynomial k)).repr z) i) = 0 := by
    ext j
    simp [he,hc]
  have hp' := (Polynomial.taylorEquiv (1 : k)).injective (hp.trans (map_zero _).symm)
  simp [hp']

/-- Transport a null vector of a finite-dimensional surjective pencil at
zero to another pencil. If the second pencil is injective at one, the
transported vector at zero vanishes, even when its space is infinite-dimensional. -/
theorem eq_zero_of_pencil_intertwiner {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module k E] [Module k F] [Module.Finite k E] [Module.Finite k F]
    (d t : E →ₗ[k] F) (hd : Function.Surjective d) (v : E) (hv : d v = 0)
    (A B : V →ₗ[k] W) (hi : Function.Injective (A + B))
    (m : E →ₗ[k] V) (n : F →ₗ[k] W) (hA : A.comp m = n.comp d) (hB : B.comp m = n.comp t) :
    m v = 0 := by
  obtain ⟨w,hw,h₀⟩ := exists_tensor_affine_kernel_lift d t hd v hv
  have h (a : E →ₗ[k] F) (b : V →ₗ[k] W) (he : b.comp m = n.comp a) :
      b.baseChange (Polynomial k) (m.baseChange (Polynomial k) w) = n.baseChange (Polynomial k) (a.baseChange (Polynomial k) w) := by
    simpa only [LinearMap.baseChange_comp,LinearMap.comp_apply] using
      DFunLike.congr_fun (congrArg (LinearMap.baseChange (Polynomial k)) he) w
  have hz : m.baseChange (Polynomial k) w = 0 := by
    apply polynomial_pencil_injective A B hi
    simp only [LinearMap.add_apply,LinearMap.smul_apply,h d A hA,h t B hB,map_zero]
    simpa only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,map_zero] using
      congrArg (n.baseChange (Polynomial k)) hw
  simpa only [polynomialEval_baseChange,h₀,map_zero] using congrArg (polynomialEval (0 : k)) hz

end EFiniteCharacterizations
