module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Nat.Find
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.Ring

/-! # Polynomial minors of linear families -/

@[expose] public section

open scoped BigOperators

namespace EFiniteCharacterizations

open Module

variable {k ι T V W : Type*} [Field k] [Fintype ι]
  [AddCommGroup T] [Module k T] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

noncomputable def linearFormPolynomial (b : Basis ι k T) (l : Dual k T) :
    MvPolynomial ι k :=
  ∑ i, MvPolynomial.C (l (b i)) * MvPolynomial.X i

private theorem linearFormPolynomial_degree (b : Basis ι k T) (l : Dual k T) :
    (linearFormPolynomial b l).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

private theorem eval_linearFormPolynomial (b : Basis ι k T) (l : Dual k T) (p : T) :
    MvPolynomial.eval (b.repr p) (linearFormPolynomial b l) = l p := by
  have h := congrArg l (b.sum_repr p)
  simpa only [linearFormPolynomial, map_sum, map_smul, smul_eq_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, map_mul, mul_comm] using h

private noncomputable def pencilSubstitution (b : Basis ι k T) (p h : T) :
    MvPolynomial ι k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C fun i ↦
    Polynomial.C (b.repr p i) + Polynomial.X * Polynomial.C (b.repr h i)

private theorem pencilSubstitution_linearForm (b : Basis ι k T) (l : Dual k T) (p h : T) :
    pencilSubstitution b p h (linearFormPolynomial b l) =
      Polynomial.C (l p) + Polynomial.X * Polynomial.C (l h) := by
  have hp : ∑ i, l (b i) * b.repr p i = l p := by
    simpa only [linearFormPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X] using eval_linearFormPolynomial b l p
  have hh : ∑ i, l (b i) * b.repr h i = l h := by
    simpa only [linearFormPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X] using eval_linearFormPolynomial b l h
  rw [← hp, ← hh]
  simp only [linearFormPolynomial, pencilSubstitution, map_sum, map_mul,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The determinant of a linear family evaluated on fixed vectors and tested by fixed covectors. -/
noncomputable def polynomialMinor (b : Basis ι k T) (Φ : T →ₗ[k] V →ₗ[k] W)
    {n : ℕ} (v : Fin n → V) (l : Fin n → Dual k W) : MvPolynomial ι k :=
  (Matrix.of fun i j ↦
    linearFormPolynomial b ((l i).comp ((LinearMap.applyₗ (R := k) (M₂ := W) (v j)).comp Φ))).det

private theorem polynomialMinor_degree (b : Basis ι k T) (Φ : T →ₗ[k] V →ₗ[k] W)
    {n : ℕ} (v : Fin n → V) (l : Fin n → Dual k W) :
    (polynomialMinor b Φ v l).totalDegree ≤ n := by
  rw [polynomialMinor, Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [← map_intCast (MvPolynomial.C : k →+* MvPolynomial ι k), MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    linearFormPolynomial_degree b ((l (e i)).comp ((LinearMap.applyₗ (R := k) (M₂ := W) (v i)).comp Φ)))

theorem eval_polynomialMinor (b : Basis ι k T) (Φ : T →ₗ[k] V →ₗ[k] W)
    {n : ℕ} (v : Fin n → V) (l : Fin n → Dual k W) (p : T) :
    MvPolynomial.eval (b.repr p) (polynomialMinor b Φ v l) =
      (Matrix.of fun i j ↦ l i (Φ p (v j))).det := by
  rw [polynomialMinor, RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact eval_linearFormPolynomial b _ p

theorem eval₂_polynomialMinor {F : Type*} [Field F] [Algebra k F] (b : Basis ι k T)
    (Φ : T →ₗ[k] V →ₗ[k] W) {n : ℕ} (v : Fin n → V) (l : Fin n → Dual k W) (x : ι → F) :
    MvPolynomial.eval₂Hom (algebraMap k F) x (polynomialMinor b Φ v l) =
      (Matrix.of fun i j ↦ ∑ t, algebraMap k F (l i (Φ (b t) (v j))) * x t).det := by
  rw [polynomialMinor,RingHom.map_det]
  congr 1
  ext i j
  simp [linearFormPolynomial]

private theorem pencilSubstitution_polynomialMinor (b : Basis ι k T) (Φ : T →ₗ[k] V →ₗ[k] W)
    {n : ℕ} (v : Fin n → V) (l : Fin n → Dual k W) (p h : T) :
    pencilSubstitution b p h (polynomialMinor b Φ v l) =
      (Matrix.of fun i j ↦ Polynomial.C (l i (Φ p (v j))) +
        Polynomial.X * Polynomial.C (l i (Φ h (v j)))).det := by
  rw [polynomialMinor, RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact pencilSubstitution_linearForm b _ p h

private theorem matrixProbes_card_le [Module.Finite k W] {n : ℕ}
    (w : Fin n → W) (l : Fin n → Dual k W)
    (h : (Matrix.of fun i j ↦ l i (w j)).det ≠ 0) : n ≤ finrank k W := by
  have hi := Matrix.linearIndependent_cols_of_det_ne_zero h
  have hind : LinearIndependent k w := LinearIndependent.of_comp (LinearMap.pi l) hi
  simpa using hind.fintype_card_le_finrank

private theorem det_border (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (h : ∀ j : Fin n, A 0 j.succ = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [h]

/-- A direction taking a kernel vector outside the image gives a nonzero polynomial
minor one order larger than any chosen nonzero minor at that point. -/
theorem exists_larger_polynomialMinor [Module.Finite k W] (b : Basis ι k T)
    (Φ : T →ₗ[k] V →ₗ[k] W) {r : ℕ} {v : Fin r → V} {l : Fin r → Dual k W}
    {p h : T} {u : V} (hu : Φ p u = 0) (hw' : Φ h u ∉ LinearMap.range (Φ p))
    (hdet : (Matrix.of fun i j ↦ l i (Φ p (v j))).det ≠ 0) :
    r + 1 ≤ finrank k W ∧ ∃ (v' : Fin (r+1) → V) (l' : Fin (r+1) → Dual k W),
      polynomialMinor b Φ v' l' ≠ 0 := by
  classical
  let w := Φ h u
  have hh : Φ h u = w := rfl
  obtain ⟨l₀, hhit, hann⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw' inferInstance
  have hp (x : V) : l₀ (Φ p x) = 0 := by
    have hmem : l₀ (Φ p x) ∈ (LinearMap.range (Φ p)).map l₀ :=
      Submodule.mem_map_of_mem ⟨x, rfl⟩
    simpa [hann] using hmem
  let v' : Fin (r + 1) → V := Fin.cons u v
  let l' : Fin (r + 1) → Dual k W := Fin.cons l₀ l
  let w' : Fin (r + 1) → W := Fin.cons w (fun j ↦ Φ p (v j))
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) k := Matrix.of fun i j ↦ l' i (w' j)
  have hB : B.det ≠ 0 := by
    rw [det_border r B (by intro j; simpa [B, l', w'] using hp (v j))]
    exact mul_ne_zero hhit hdet
  have hrnext : r + 1 ≤ finrank k W := matrixProbes_card_le w' l' hB
  refine ⟨hrnext,v',l',?_⟩
  intro hz
  have he := congrArg (pencilSubstitution b p h) hz
  rw [pencilSubstitution_polynomialMinor, map_zero] at he
  let N : Matrix (Fin (r + 1)) (Fin (r + 1)) (Polynomial k) := Matrix.of fun i j ↦
    Fin.cons (α := fun _ ↦ Polynomial k) (Polynomial.C (l' i w))
      (fun a ↦ Polynomial.C (l' i (Φ p (v a))) +
        Polynomial.X * Polynomial.C (l' i (Φ h (v a)))) j
  let t : Fin (r + 1) → Polynomial k := Fin.cons Polynomial.X (fun _ ↦ 1)
  have hfac :
      (Matrix.of fun i j ↦ Polynomial.C (l' i (Φ p (v' j))) +
        Polynomial.X * Polynomial.C (l' i (Φ h (v' j)))) = N * Matrix.diagonal t := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_diagonal]
    refine Fin.cases ?_ (fun a ↦ ?_) j
    · simp only [Matrix.of_apply, N, t, v', Fin.cons_zero, hu, hh, map_zero, zero_add]
      exact mul_comm _ _
    · simp only [Matrix.of_apply, N, t, v', Fin.cons_succ, mul_one]
  have hN : N.det ≠ 0 := by
    intro hNz
    have hEval := congrArg (Polynomial.evalRingHom (0 : k)) hNz
    rw [RingHom.map_det, map_zero] at hEval
    apply hB
    convert hEval using 1
    congr 1
    apply Matrix.ext
    intro i j
    refine Fin.cases ?_ (fun a ↦ ?_) j
    · simp [N, B, w']
    · simp [N, B, w']
  have ht : (Matrix.diagonal t).det ≠ 0 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_succ]
    simp [t]
  rw [hfac, Matrix.det_mul] at he
  exact mul_ne_zero hN ht he

/-- One nonzero polynomial, of degree at most the dimension of the target, vanishes
at every parameter where a kernel vector gives surjective evaluation in the family
and the specialized map itself is not surjective. -/
theorem exists_polynomial_vanishing_at_defective_pencil [Module.Finite k W]
    (b : Basis ι k T) (Φ : T →ₗ[k] V →ₗ[k] W) :
    ∃ D : MvPolynomial ι k, D ≠ 0 ∧ D.totalDegree ≤ finrank k W ∧
      ∀ (p : T) (u : V), Φ p u = 0 → (∀ w : W, ∃ h : T, Φ h u = w) →
        ¬ Function.Surjective (Φ p) → MvPolynomial.eval (b.repr p) D = 0 := by
  classical
  let A (n : ℕ) : Prop := ∃ (v : Fin n → V) (l : Fin n → Dual k W),
    polynomialMinor b Φ v l ≠ 0
  have hzero : A 0 := by
    refine ⟨Fin.elim0, Fin.elim0, ?_⟩
    simp [polynomialMinor]
  let r := Nat.findGreatest A (finrank k W)
  obtain ⟨v, l, hminor⟩ := Nat.findGreatest_spec (Nat.zero_le _) hzero
  have hr : r ≤ finrank k W := Nat.findGreatest_le _
  refine ⟨polynomialMinor b Φ v l, hminor, (polynomialMinor_degree b Φ v l).trans hr, ?_⟩
  intro p u hu hsurj hnonsurj
  by_contra hpd
  have hdet : (Matrix.of fun i j ↦ l i (Φ p (v j))).det ≠ 0 := by
    rwa [eval_polynomialMinor] at hpd
  obtain ⟨w, hw⟩ := not_forall.mp hnonsurj
  have hw' : w ∉ LinearMap.range (Φ p) := hw
  obtain ⟨h, hh⟩ := hsurj w
  obtain ⟨hrnext,hnext⟩ := exists_larger_polynomialMinor b Φ hu (hh.symm ▸ hw') hdet
  exact (Nat.findGreatest_is_greatest (Nat.lt_succ_self r) hrnext) hnext

end EFiniteCharacterizations
