module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-! # Finite covers by polynomial zero loci -/

@[expose] public section

namespace EFiniteCharacterizations

open MvPolynomial

variable {k : Type*} [Field k]

private theorem product_eval_zero {ι β : Type*} [Fintype β]
    (D : β → MvPolynomial ι k) (h : ∀ x : ι → k, ∃ i, eval x (D i) = 0)
    (x : ι → k) : eval x (∏ i, D i) = 0 := by
  classical
  obtain ⟨i, hi⟩ := h x
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- A finite family of nonzero polynomials cannot vanish at every point over
an infinite field. -/
theorem not_polynomial_zero_cover_of_infinite [Infinite k] {ι β : Type*}
    [Finite β] (D : β → MvPolynomial ι k) (hne : ∀ i, D i ≠ 0) :
    ¬ (∀ x : ι → k, ∃ i, eval x (D i) = 0) := by
  classical
  let := Fintype.ofFinite β
  intro h
  apply Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hne i)
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  exact product_eval_zero D h x

/-- A nonzero multivariable polynomial vanishing at every rational point over a
finite field has total degree at least the cardinality of the field. -/
theorem field_card_le_totalDegree_of_eval_zero [Fintype k] {n : ℕ}
    {D : MvPolynomial (Fin n) k} (hne : D ≠ 0) (h : ∀ x, eval x D = 0) :
    Fintype.card k ≤ D.totalDegree := by
  classical
  have hgrid : Fintype.piFinset (fun _ : Fin n ↦ (Finset.univ : Finset k)) = Finset.univ := by
    ext x
    simp
  have hs := schwartz_zippel_totalDegree hne (Finset.univ : Finset k)
  simp only [hgrid, h, Finset.filter_true, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow] at hs
  have hpos : (0 : ℚ≥0) < (Fintype.card k : ℚ≥0) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card k)
  rw [div_self (pow_ne_zero _ hpos.ne')] at hs
  have hc := (le_div_iff₀ hpos).mp hs
  simpa using hc

/-- A zero-locus cover by nonzero polynomials of degree at most `d` has at least
`#k / d` members, in the form `#k ≤ #β * d`. -/
theorem field_card_le_card_mul_degree_of_polynomial_zero_cover [Fintype k]
    {n d : ℕ} {β : Type*} [Fintype β] (D : β → MvPolynomial (Fin n) k)
    (hne : ∀ i, D i ≠ 0) (hdeg : ∀ i, (D i).totalDegree ≤ d)
    (h : ∀ x : Fin n → k, ∃ i, eval x (D i) = 0) : Fintype.card k ≤ Fintype.card β * d := by
  classical
  have hne' : (∏ i, D i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hne i)
  calc
    Fintype.card k ≤ (∏ i, D i).totalDegree :=
      field_card_le_totalDegree_of_eval_zero hne' (product_eval_zero D h)
    _ ≤ ∑ i, (D i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ Fintype.card β * d := by
      simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hdeg i)

end EFiniteCharacterizations
