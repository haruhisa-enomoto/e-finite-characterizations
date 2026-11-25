module

public import EFiniteCharacterizations.LinearAlgebra.PolynomialTensor
public import Mathlib.Algebra.Polynomial.Module.TensorProduct

/-! # Coefficients of polynomial lifts at a rigid point of a pencil -/

@[expose] public section
open scoped TensorProduct
open PolynomialModule

namespace EFiniteCharacterizations

variable {k V W : Type*} [Field k] [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W]

/-- Expand a polynomial vector in the parameter t = 1 − s. -/
private noncomputable def expand (z : Polynomial k ⊗[k] V) :=
  PolynomialModule.comp (1 - Polynomial.X) (polynomialTensorProductLEquivPolynomialModule k V z)

private theorem expand_tmul (p : Polynomial k) (v : V) :
    expand (p ⊗ₜ[k] v) = p.comp (1 - Polynomial.X) • single k 0 v := by
  change PolynomialModule.comp _ (p • single k 0 v) = _
  rw [comp_smul, comp_single, pow_zero, one_smul]

private theorem expand_add (a b : Polynomial k ⊗[k] V) :
    expand (a + b) = expand a + expand b := by simp only [expand, _root_.map_add]

private theorem expand_X (a : Polynomial k ⊗[k] V) :
    expand ((Polynomial.X : Polynomial k) • a) = (1 - Polynomial.X : Polynomial k) • expand a := by
  simp only [expand, _root_.map_smul, comp_smul, Polynomial.X_comp]

private theorem expand_map (f : V →ₗ[k] W) (z : Polynomial k ⊗[k] V) :
    expand (f.baseChange (Polynomial k) z) = PolynomialModule.map k f (expand z) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro p v
    rw [LinearMap.baseChange_tmul, expand_tmul, expand_tmul, PolynomialModule.map_smul, map_single]
    simp
  · intro a b ha hb
    simpa only [expand_add, _root_.map_add] using congrArg₂ (· + ·) ha hb

private theorem expand_eval (z : Polynomial k ⊗[k] V) :
    PolynomialModule.eval (1 : k) (expand z) = polynomialEval 0 z := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro p v
    rw [expand_tmul, eval_smul, eval_single, polynomialEval_tmul, Polynomial.eval_comp]
    simp
  · intro a b ha hb
    simpa only [expand_add, _root_.map_add] using congrArg₂ (· + ·) ha hb

/-- A null vector at the parameter one lifts to a polynomial solution over
the ground field, expressed in the parameter vanishing at the special fiber. -/
theorem exists_affine_polynomial_solution [Module.Finite k V] [Module.Finite k W]
    (A B : V →ₗ[k] W) (h : Function.Surjective (A + B)) (v : V) (hv : (A + B) v = 0) :
    ∃ z : PolynomialModule k V, PolynomialModule.eval 1 z = v ∧
      PolynomialModule.map k A z + (Polynomial.X : Polynomial k) • PolynomialModule.map k B z = 0 := by
  obtain ⟨w, hw, h₀⟩ := exists_tensor_affine_kernel_lift (A + B) (-B) h v hv
  refine ⟨expand w, (expand_eval w).trans h₀, ?_⟩
  have he := congrArg expand hw
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.baseChange_add,
    LinearMap.baseChange_neg, LinearMap.neg_apply, smul_neg] at he
  have expand_neg (b : Polynomial k ⊗[k] W) : expand (-b) = -expand b := by
    simp only [expand, map_neg]
  have expand_zero : expand (0 : Polynomial k ⊗[k] W) = 0 := by simp only [expand, map_zero]
  rw [expand_add, expand_add, expand_neg, expand_X, expand_map, expand_map, expand_zero,
    sub_smul, one_smul] at he
  abel_nf at he ⊢
  exact he

/-- A polynomial lift gives a finite sequence satisfying the pencil recurrence.
Its sum recovers the prescribed vector at the rigid point. -/
theorem exists_finite_pencil_coefficients [Module.Finite k V] [Module.Finite k W]
    (A B : V →ₗ[k] W) (h : Function.Surjective (A + B)) (v : V) (hv : (A + B) v = 0) :
    ∃ (n : ℕ) (a : ℕ → V), (∀ i, n ≤ i → a i = 0) ∧ ∑ i ∈ Finset.range n, a i = v ∧
      A (a 0) = 0 ∧ ∀ i, A (a (i+1)) + B (a i) = 0 := by
  classical
  obtain ⟨z, he, hz⟩ := exists_affine_polynomial_solution A B h v hv
  let n := z.coeff.support.sup id + 1
  have hs : z.coeff.support ⊆ Finset.range n := fun i hi ↦
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have coeff_map (f : V →ₗ[k] W) (i : ℕ) : (PolynomialModule.map k f z).coeff i = f (z.coeff i) := rfl
  have hc (i : ℕ) := congrArg (fun x : PolynomialModule k W ↦ x.coeff i) hz
  refine ⟨n, z.coeff, fun i hi ↦ Finsupp.notMem_support_iff.mp
    (fun hmem ↦ (Finset.mem_range.1 (hs hmem)).not_ge hi), ?_, ?_, ?_⟩
  · rw [← he, PolynomialModule.eval_apply]
    simp only [one_pow, one_smul, Finsupp.sum]
    exact (Finset.sum_subset hs (fun i _ hi ↦ Finsupp.notMem_support_iff.mp hi)).symm
  · simpa [← Polynomial.monomial_one_one_eq_X, coeff_map] using hc 0
  · intro i
    simpa [← Polynomial.monomial_one_one_eq_X, coeff_map] using hc (i+1)

/-- Partial sums of a finite polynomial lift satisfy the same recurrence and
stabilize at the prescribed vector. -/
theorem exists_stable_pencil_coefficients [Module.Finite k V] [Module.Finite k W]
    (A B : V →ₗ[k] W) (h : Function.Surjective (A + B)) (v : V) (hv : (A + B) v = 0) :
    ∃ (n : ℕ) (a : ℕ → V), (∀ i, n ≤ i → a i = v) ∧
      A (a 0) = 0 ∧ ∀ i, A (a (i+1)) + B (a i) = 0 := by
  obtain ⟨n, c, hc, hs, h₀, hr⟩ := exists_finite_pencil_coefficients A B h v hv
  let a (i : ℕ) := ∑ j ∈ Finset.range (i+1), c j
  have ha (i : ℕ) : a (i+1) = a i + c (i+1) := Finset.sum_range_succ _ _
  have ha₀ : a 0 = c 0 := by simp [a]
  refine ⟨n, a, ?_, ha₀ ▸ h₀, ?_⟩
  · intro i hi
    rw [← hs]
    exact (Finset.sum_subset (Finset.range_mono (by omega : n ≤ i+1))
      (fun j _ hj ↦ hc j (by simpa using hj))).symm
  · intro i
    induction i with
    | zero => rw [ha, ha₀, map_add, h₀, zero_add, hr]
    | succ i ih =>
      rw [ha (i+1), map_add, ha i, map_add] at *
      have hh := hr (i+1)
      abel_nf at ih hh ⊢
      grind

end EFiniteCharacterizations
