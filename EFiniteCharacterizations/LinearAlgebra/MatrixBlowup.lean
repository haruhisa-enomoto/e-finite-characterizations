module

public import EFiniteCharacterizations.LinearAlgebra.RankSeparation
public import EFiniteCharacterizations.LinearAlgebra.IndependentMatrixRelations
public import EFiniteCharacterizations.LinearAlgebra.MatrixSubspaceDescent
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Invertible block matrices from strict subspace expansion -/

@[expose] public section

open Matrix

namespace EFiniteCharacterizations

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
  {a m n t : Type*} [Fintype a] [Fintype m] [Fintype n] [Fintype t]

/-- The matrix on t copies with each block a linear combination of the
matrices in the given family. -/
def blockFamily (D : a → Matrix m n k) (x : t × (a × t) → k) : Matrix (t × m) (t × n) k :=
  Matrix.of fun i j ↦ ∑ b, x (i.1,b,j.1) * D b i.2 j.2

omit [Fintype m] in
private theorem block_kernel_equations (D : a → Matrix m n K) (x : t × (a × t) → K)
    (z : t × n → K) (h : (blockFamily D x).mulVec z = 0) (u : t) (v : m) :
    ∑ j : a × t, matrixImages D (Matrix.of fun i l ↦ z (l,i)) v j * x (u,j) = 0 := by
  have he := congrFun h (u,v)
  change (∑ j : t × n, (∑ b, x (u,b,j.1) * D b v j.2) * z j) = 0 at he
  simp only [matrixImages,Matrix.of_apply,Matrix.mul_apply,Fintype.sum_prod_type,Finset.sum_mul]
  simp only [Fintype.sum_prod_type,Finset.sum_mul] at he
  rw [Finset.sum_comm]
  convert he using 1
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem image_rank_bound (D : a → Matrix m n k) (Z : Matrix n t K)
    (x : t × (a × t) → K) (hx : AlgebraicIndependent k x)
    (h : ∀ u v, ∑ j, matrixImages (fun b ↦ (D b).map (algebraMap k K)) Z v j * x (u,j) = 0)
    (s : Finset K) (hs : ∀ i j, Z i j ∈ IntermediateField.adjoin k (s : Set K)) :
    Fintype.card t * (matrixImages (fun b ↦ (D b).map (algebraMap k K)) Z).rank ≤ s.card := by
  let E := IntermediateField.adjoin k (s : Set K)
  let Z' : Matrix n t E := Matrix.of fun i j ↦ ⟨Z i j,hs i j⟩
  let A := matrixImages (fun b ↦ (D b).map (algebraMap k E)) Z'
  have he : A.map E.val = matrixImages (fun b ↦ (D b).map (algebraMap k K)) Z := by
    ext i j
    simp [A,matrixImages,Z',Matrix.mul_apply,Matrix.map_apply]
  rw [← he,show (A.map E.val).rank = A.rank from matrix_rank_map_from_field E.val.toRingHom A]
  exact rank_mul_le_parameters x hx s A (fun u v ↦ by
    have hv := h u v
    rw [← he] at hv
    exact hv)

private def entriesFinset {L i j : Type*} [DecidableEq L] [Fintype i] [Fintype j]
    (Z : Matrix i j L) := Finset.univ.image (fun p : i × j ↦ Z p.1 p.2)

private theorem card_entriesFinset {L i j : Type*} [DecidableEq L] [Fintype i] [Fintype j]
    (Z : Matrix i j L) : (entriesFinset Z).card ≤ Fintype.card i * Fintype.card j := by
  simpa only [entriesFinset,Finset.card_univ,Fintype.card_prod] using (Finset.card_image_le
    (s := Finset.univ) (f := fun p : i × j ↦ Z p.1 p.2))

private theorem mem_entriesFinset {L i j : Type*} [DecidableEq L] [Fintype i] [Fintype j]
    (Z : Matrix i j L) (u : i) (v : j) : Z u v ∈ entriesFinset Z :=
  Finset.mem_image.mpr ⟨(u,v),Finset.mem_univ _,rfl⟩

private theorem generic_kernel_impossible [IsAlgClosed k] (D : a → Matrix m n k)
    (hD : ∀ r s, HasMatrixSubspacePair D r s → 0 < r →
      (r < Fintype.card n → r < s) ∧ (r = Fintype.card n → r ≤ s))
    (ht : Fintype.card n ^ 2 < Fintype.card t)
    (x : t × (a × t) → K) (hx : AlgebraicIndependent k x)
    (Z : Matrix n t K) (i : n) (j : t) (hij : Z i j = 1)
    (h : ∀ u v, ∑ p, matrixImages (fun b ↦ (D b).map (algebraMap k K)) Z v p * x (u,p) = 0) : False := by
  classical
  let D' b := (D b).map (algebraMap k K)
  let W := matrixImages D' Z
  have hr : 0 < Z.rank := by
    apply Nat.pos_of_ne_zero
    intro hz
    obtain ⟨U,C,_,_,hc,_,_⟩ := exists_matrix_rank_factorization Z
    have : IsEmpty (Fin Z.rank) := ⟨fun l ↦ by have := l.isLt; omega⟩
    have he := congrFun (congrFun hc i) j
    simp [Matrix.mul_apply,hij] at he
  have hle := Z.rank_le_card_height
  have hd := hD Z.rank W.rank (matrixSubspacePair_descends D _ _ (matrixSubspacePair_of_columns D' Z)) hr
  rcases lt_or_eq_of_le hle with hlt | he
  · obtain ⟨U,C,_,_,hUC,_,_⟩ := exists_matrix_rank_factorization Z
    let s := entriesFinset U ∪ entriesFinset C
    let E := IntermediateField.adjoin k (s : Set K)
    have hmem u v : Z u v ∈ E := by
      have hz := congrFun (congrFun hUC u) v
      rw [← hz,Matrix.mul_apply]
      apply E.sum_mem
      intro l _
      exact E.mul_mem (IntermediateField.subset_adjoin k _ (Finset.mem_union_left _ (mem_entriesFinset U u l)))
        (IntermediateField.subset_adjoin k _ (Finset.mem_union_right _ (mem_entriesFinset C l v)))
    have hb : Fintype.card t * W.rank ≤ s.card := image_rank_bound D Z x hx h s hmem
    have hc : s.card ≤ Fintype.card n * Z.rank + Z.rank * Fintype.card t := by
      apply (Finset.card_union_le _ _).trans
      simpa using Nat.add_le_add (card_entriesFinset U) (card_entriesFinset C)
    have hbig := Nat.mul_le_mul_left (Fintype.card t) (hd.1 hlt)
    have hsmall := Nat.mul_le_mul_left (Fintype.card n) hle
    nlinarith only [hb,hc,hbig,hsmall,ht]
  · let p := (i,j)
    let s := (Finset.univ.erase p).image (fun q : n × t ↦ Z q.1 q.2)
    have hmem u v : Z u v ∈ IntermediateField.adjoin k (s : Set K) := by
      by_cases hp : (u,v) = p
      · have hz := congrArg (fun q : n × t ↦ Z q.1 q.2) hp
        rw [show Z u v = 1 from hz.trans hij]
        exact one_mem _
      · exact IntermediateField.subset_adjoin k _ (Finset.mem_image.mpr
          ⟨(u,v),Finset.mem_erase.mpr ⟨hp,Finset.mem_univ _⟩,rfl⟩)
    have hb : Fintype.card t * W.rank ≤ s.card := image_rank_bound D Z x hx h s hmem
    have hc : s.card < Fintype.card n * Fintype.card t := by
      apply Finset.card_image_le.trans_lt
      simpa using Finset.card_erase_lt_of_mem (Finset.mem_univ p)
    have hbig := Nat.mul_le_mul_left (Fintype.card t) (hd.2 he)
    nlinarith only [he,hbig,hb,hc]

/-- Over an algebraically closed field, a rectangular family strictly expanding
proper nonzero subspaces has an injective blowup on a nonempty principal open set
at every size greater than the square of its source dimension. -/
theorem polynomial_of_block_expansion [IsAlgClosed k] (D : a → Matrix m n k)
    (hD : ∀ r s, HasMatrixSubspacePair D r s → 0 < r →
      (r < Fintype.card n → r < s) ∧ (r = Fintype.card n → r ≤ s))
    (ht : Fintype.card n ^ 2 < Fintype.card t) :
    ∃ p : MvPolynomial (t × (a × t)) k, p ≠ 0 ∧ ∀ x, MvPolynomial.eval x p ≠ 0 →
      Function.Injective (blockFamily D x).mulVec := by
  classical
  let S := MvPolynomial (t × (a × t)) k
  let L := FractionRing S
  let q := algebraMap S L
  let x (i : t × (a × t)) := q (MvPolynomial.X i)
  let D' b := (D b).map (algebraMap k L)
  let B := blockFamily D' x
  have hx : AlgebraicIndependent k x :=
    (MvPolynomial.algebraicIndependent_X _ k).map' (f := IsScalarTower.toAlgHom k S L)
      (IsFractionRing.injective S L)
  have hinj : Function.Injective B.mulVecLin := by
    apply (injective_iff_map_eq_zero _).2
    intro z hker
    by_contra hz
    obtain ⟨⟨j,i⟩,hij⟩ := Function.ne_iff.mp hz
    change z (j,i) ≠ 0 at hij
    let w := (z (j,i))⁻¹ • z
    have hw : B.mulVec w = 0 := by
      change B.mulVec z = 0 at hker
      simp [w,Matrix.mulVec_smul,hker]
    exact generic_kernel_impossible D hD ht x hx (Matrix.of fun l b ↦ w (b,l)) i j
      (inv_mul_cancel₀ hij) (block_kernel_equations D' x w hw)
  have hr : B.rank = Fintype.card (t × n) := by
    rw [Matrix.rank,LinearMap.finrank_range_of_inj hinj,Module.finrank_pi]
  let A : Matrix (t × m) (t × n) S := Matrix.of fun i j ↦
    ∑ b, MvPolynomial.X (i.1,b,j.1) * MvPolynomial.C (D b i.2 j.2)
  have he : A.map q = B := by
    ext i j
    change q (∑ b, _) = ∑ b, _
    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ ↦ map_mul q _ _
  obtain ⟨r,c,hdet⟩ := exists_nonzero_rank_minor B
  let p := (A.submatrix r c).det
  have hq : q p = (B.submatrix r c).det := by
    calc
      q p = ((A.map q).submatrix r c).det := RingHom.map_det q _
      _ = _ := congrArg (fun Z : Matrix (t × m) (t × n) L ↦ (Z.submatrix r c).det) he
  refine ⟨p,fun h ↦ hdet (by rw [← hq,h,map_zero]),?_⟩
  intro y hy
  let C := blockFamily D y
  have hC : A.map (MvPolynomial.eval y) = C := by
    ext i j
    simp [C,A,Matrix.map_apply,blockFamily]
  have hd : (C.submatrix r c).det ≠ 0 := by
    have eq : MvPolynomial.eval y p = (C.submatrix r c).det :=
      (RingHom.map_det (MvPolynomial.eval y) (A.submatrix r c)).trans
        (congrArg (fun Z : Matrix (t × m) (t × n) k ↦ (Z.submatrix r c).det) hC)
    exact eq ▸ hy
  have hle := C.rank_submatrix_le r c
  rw [Matrix.rank_of_det_ne_zero hd,Fintype.card_fin,hr] at hle
  have hsum := C.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank,Module.finrank_pi] at hsum
  change Function.Injective C.mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

/-- Strict expansion on proper nonzero subspaces gives an invertible block
matrix at every size greater than the square of the source dimension. -/
theorem exists_invertible_blockFamily [DecidableEq t] [DecidableEq n] [IsAlgClosed k] (D : a → Matrix n n k)
    (hD : ∀ r s, HasMatrixSubspacePair D r s → 0 < r →
      (r < Fintype.card n → r < s) ∧ (r = Fintype.card n → r ≤ s))
    (ht : Fintype.card n ^ 2 < Fintype.card t) :
    ∃ x : t × (a × t) → k, (blockFamily D x).det ≠ 0 := by
  obtain ⟨p,hp,h⟩ := polynomial_of_block_expansion D hD ht
  obtain ⟨x,hx⟩ : ∃ x, MvPolynomial.eval x p ≠ 0 := by
    by_contra! hz
    exact hp (MvPolynomial.funext (fun x ↦ (hz x).trans (map_zero _).symm))
  exact ⟨x,Matrix.nonsingular_iff_det_ne_zero.1
    (Matrix.Nonsingular.of_linearIndependent_col (Matrix.mulVec_injective_iff.1 (h x hx)))⟩

end EFiniteCharacterizations
