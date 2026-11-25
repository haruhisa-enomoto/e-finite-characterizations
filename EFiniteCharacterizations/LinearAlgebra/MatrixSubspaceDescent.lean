module

public import EFiniteCharacterizations.LinearAlgebra.MatrixRankSpecialization
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Specializing simultaneous subspaces of a matrix family -/

@[expose] public section

namespace EFiniteCharacterizations

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k]

/-- A finite list of coefficients in an extension of an algebraically closed
field lies in a ground algebra admitting a specialization to that field. -/
private theorem exists_specialization_on (s : Set K) (hs : s.Finite) :
    ∃ S : Subalgebra k K, s ⊆ S ∧ Nonempty (S →ₐ[k] k) := by
  let := hs.to_subtype
  let f := MvPolynomial.aeval (R := k) (fun i : s ↦ i.val)
  let g := f.rangeRestrict
  let I := RingHom.ker g.toRingHom
  obtain ⟨J,hJ,hIJ⟩ := I.exists_le_maximal (RingHom.ker_ne_top _)
  obtain ⟨v,hv⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hJ
  let e := MvPolynomial.aeval (R := k) v
  have he : I ≤ RingHom.ker e.toRingHom := by
    intro p hp
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff v p).1 (hv ▸ hIJ hp)
  refine ⟨f.range,fun x hx ↦ ⟨MvPolynomial.X ⟨x,hx⟩,by simp [f]⟩,?_⟩
  exact ⟨AlgHom.liftOfSurjective g f.rangeRestrict_surjective e he⟩

/-- Columns of two split injections specify subspaces of the stated
dimensions. The intertwining equations say all the matrices send the first
subspace into the second. -/
def HasMatrixSubspacePair {L : Type*} [Field L] {a n m : Type*} [Fintype n] [Fintype m]
    (D : a → Matrix m n L) (r s : ℕ) : Prop :=
  ∃ (X : Matrix n (Fin r) L) (Y : Matrix m (Fin s) L)
    (LX : Matrix (Fin r) n L) (LY : Matrix (Fin s) m L) (B : a → Matrix (Fin s) (Fin r) L),
    LX * X = 1 ∧ LY * Y = 1 ∧ ∀ i, D i * X = Y * B i

private def entries {i j : Type*} (A : Matrix i j K) := Set.range (fun p : i × j ↦ A p.1 p.2)

private def liftEntries {i j : Type*} (S : Subalgebra k K) (A : Matrix i j K)
    (hA : entries A ⊆ S) : Matrix i j S := Matrix.of fun u v ↦ ⟨A u v,hA ⟨(u,v),rfl⟩⟩

omit [IsAlgClosed k] in
private theorem map_val_injective {i j : Type*} (S : Subalgebra k K) :
    Function.Injective (fun A : Matrix i j S ↦ A.map S.val) :=
  fun _ _ h ↦ Matrix.ext fun u v ↦ Subtype.ext (congrFun (congrFun h u) v)

omit [IsAlgClosed k] in
private theorem matrixSubspacePair_coefficients {a n m : Type*} [Finite a] [Fintype n] [Fintype m]
    (D : a → Matrix m n k) (r s : ℕ)
    (h : HasMatrixSubspacePair (fun i ↦ (D i).map (algebraMap k K)) r s) :
    ∃ t : Set K, t.Finite ∧ ∀ (S : Subalgebra k K), t ⊆ S →
      ∀ {L : Type*} [Field L] [Algebra k L], (S →ₐ[k] L) →
        HasMatrixSubspacePair (fun i ↦ (D i).map (algebraMap k L)) r s := by
  classical
  obtain ⟨X,Y,LX,LY,B,hX,hY,hD⟩ := h
  let t := entries X ∪ entries Y ∪ entries LX ∪ entries LY ∪ ⋃ i, entries (B i)
  have ht : t.Finite := by
    dsimp [t,entries]
    exact ((((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)).union (Set.finite_iUnion fun _ ↦ Set.finite_range _)
  refine ⟨t,ht,?_⟩
  intro S hS L _ _ e
  let X' := liftEntries S X (Set.Subset.trans (by dsimp [t]; grind) hS)
  let Y' := liftEntries S Y (Set.Subset.trans (by dsimp [t]; grind) hS)
  let LX' := liftEntries S LX (Set.Subset.trans (by dsimp [t]; grind) hS)
  let LY' := liftEntries S LY (Set.Subset.trans (by dsimp [t]; grind) hS)
  let B' i := liftEntries S (B i) ((Set.subset_iUnion _ i).trans (Set.subset_union_right.trans hS))
  have hX' : LX' * X' = 1 := by
    apply map_val_injective S
    dsimp only
    rw [Matrix.map_mul (f := S.val)]
    simp
    exact hX
  have hY' : LY' * Y' = 1 := by
    apply map_val_injective S
    dsimp only
    rw [Matrix.map_mul (f := S.val)]
    simp
    exact hY
  have hD' i : (D i).map (algebraMap k S) * X' = Y' * B' i := by
    apply map_val_injective S
    dsimp only
    rw [Matrix.map_mul (f := S.val),Matrix.map_mul (f := S.val)]
    exact hD i
  refine ⟨X'.map e,Y'.map e,LX'.map e,LY'.map e,fun i ↦ (B' i).map e,?_,?_,fun i ↦ ?_⟩
  · simpa [Matrix.map_mul] using congrArg (Matrix.map · e) hX'
  · simpa [Matrix.map_mul] using congrArg (Matrix.map · e) hY'
  · simpa [Matrix.map_mul,Matrix.map_map,Function.comp_def] using congrArg (Matrix.map · e) (hD' i)

/-- Over an algebraically closed field, extending scalars introduces no new
dimension pairs of simultaneous subspaces. -/
theorem matrixSubspacePair_descends {a n m : Type*} [Finite a] [Fintype n] [Fintype m]
    (D : a → Matrix m n k) (r s : ℕ)
    (h : HasMatrixSubspacePair (fun i ↦ (D i).map (algebraMap k K)) r s) :
    HasMatrixSubspacePair D r s := by
  obtain ⟨t,ht,hh⟩ := matrixSubspacePair_coefficients D r s h
  obtain ⟨S,hS,⟨e⟩⟩ := exists_specialization_on (k := k) t ht
  simpa using hh S hS e

omit [IsAlgClosed k] in
/-- A simultaneous pair over an algebraic extension is defined over a finite
intermediate field with the same two dimensions. -/
theorem matrixSubspacePair_finite_model [Algebra.IsAlgebraic k K]
    {a n m : Type*} [Finite a] [Fintype n] [Fintype m] (D : a → Matrix m n k) (r s : ℕ)
    (h : HasMatrixSubspacePair (fun i ↦ (D i).map (algebraMap k K)) r s) :
    ∃ E : IntermediateField k K, Module.Finite k E ∧
      HasMatrixSubspacePair (fun i ↦ (D i).map (algebraMap k E)) r s := by
  obtain ⟨t,ht,hh⟩ := matrixSubspacePair_coefficients D r s h
  let E := IntermediateField.adjoin k t
  let := ht.to_subtype
  refine ⟨E, IntermediateField.finiteDimensional_adjoin (fun x _ ↦
    (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral),?_⟩
  exact hh E.toSubalgebra (IntermediateField.subset_adjoin k t) (AlgHom.id k E)

/-- Columns of all images of the columns of Z, in one rectangular matrix. -/
def matrixImages {L a n m t : Type*} [Field L] [Fintype n] (D : a → Matrix m n L)
    (Z : Matrix n t L) : Matrix m (a × t) L :=
  Matrix.of fun i j ↦ (D j.1 * Z) i j.2

/-- The column space and its simultaneous image have a split matrix
presentation of dimensions equal to their respective ranks. -/
theorem matrixSubspacePair_of_columns {L a n m t : Type*} [Field L]
    [Fintype a] [Fintype n] [Fintype m] [Fintype t] (D : a → Matrix m n L) (Z : Matrix n t L) :
    HasMatrixSubspacePair D Z.rank (matrixImages D Z).rank := by
  classical
  obtain ⟨X,C,LX,H,hXC,hLX,hCH⟩ := exists_matrix_rank_factorization Z
  obtain ⟨Y,E,LY,_,hYE,hLY,_⟩ := exists_matrix_rank_factorization (matrixImages D Z)
  have hX : Z * H = X := (congrArg (· * H) hXC.symm).trans (by rw [Matrix.mul_assoc,hCH,Matrix.mul_one])
  let E' i := E.submatrix id (fun j ↦ (i,j))
  have hE i : Y * E' i = D i * Z := Matrix.ext fun l j ↦ congrFun (congrFun hYE l) (i,j)
  refine ⟨X,Y,LX,LY,fun i ↦ E' i * H,hLX,hLY,fun i ↦ ?_⟩
  rw [← Matrix.mul_assoc Y, hE,← hX,Matrix.mul_assoc]

end EFiniteCharacterizations
