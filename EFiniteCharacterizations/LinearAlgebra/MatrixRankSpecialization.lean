module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Rank under specialization of a matrix -/

@[expose] public section

open Matrix

namespace EFiniteCharacterizations

/-- A rectangular matrix over a field factors through a space of dimension its rank.
The two factors admit a left inverse and a right inverse respectively. -/
theorem exists_matrix_rank_factorization {k m n : Type*} [Field k]
    [Fintype m] [Fintype n] (A : Matrix m n k) :
    ∃ (B : Matrix m (Fin A.rank) k) (C : Matrix (Fin A.rank) n k)
      (L : Matrix (Fin A.rank) m k) (R : Matrix n (Fin A.rank) k),
      B * C = A ∧ L * B = 1 ∧ C * R = 1 := by
  classical
  let f := A.mulVecLin
  let I := LinearMap.range f
  let b : Module.Basis (Fin A.rank) k I := Module.finBasis k I
  let bm := Pi.basisFun k m
  let bn := Pi.basisFun k n
  obtain ⟨l, hl⟩ := I.subtype.exists_leftInverse_of_injective I.ker_subtype
  obtain ⟨r, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    f.range_rangeRestrict
  refine ⟨LinearMap.toMatrix b bm I.subtype, LinearMap.toMatrix bn b f.rangeRestrict,
    LinearMap.toMatrix bm b l, LinearMap.toMatrix b bn r, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp, LinearMap.subtype_comp_rangeRestrict]
    simpa [bm, bn, f, Matrix.toLin_eq_toLin', Matrix.toLin'_apply'] using
      (LinearMap.toMatrix_toLin bn bm A)
  · rw [← LinearMap.toMatrix_comp, hl, LinearMap.toMatrix_id]
  · rw [← LinearMap.toMatrix_comp, hr, LinearMap.toMatrix_id]

/-- A matrix with coefficients in a field has the same rank after embedding the
coefficients in a commutative domain. -/
theorem matrix_rank_map_from_field {k S m n : Type*} [Field k] [CommRing S] [IsDomain S]
    [Fintype m] [Fintype n] (e : k →+* S) (A : Matrix m n k) :
    (A.map e).rank = A.rank := by
  classical
  obtain ⟨B, C, L, R, hA, hl, hr⟩ := exists_matrix_rank_factorization A
  have hA' : A.map e = B.map e * C.map e := by rw [← Matrix.map_mul, hA]
  have hl' : L.map e * B.map e = 1 := by rw [← Matrix.map_mul, hl]; simp
  have hr' : C.map e * R.map e = 1 := by rw [← Matrix.map_mul, hr]; simp
  apply le_antisymm
  · rw [hA']
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa using (B.map e).rank_le_card_width)
  · have hI : L.map e * A.map e * R.map e = 1 := by
      rw [hA', ← Matrix.mul_assoc (L.map e), hl', Matrix.one_mul, hr']
    have h := (Matrix.rank_mul_le_left (L.map e * A.map e) (R.map e)).trans
      (Matrix.rank_mul_le_right _ _)
    rw [hI, Matrix.rank_one, Fintype.card_fin] at h
    exact h

/-- The rank after specialization is bounded by the rank in any domain into
which the coefficient ring embeds. -/
theorem matrix_rank_specialization_le_of_injective {k S T m n : Type*}
    [Field k] [CommRing S] [CommRing T] [IsDomain T] [Fintype m] [Fintype n]
    (e : S →+* k) (c : k →+* S) (h : e.comp c = RingHom.id k)
    (f : S →+* T) (hf : Function.Injective f) (A : Matrix m n S) : (A.map e).rank ≤ (A.map f).rank := by
  classical
  obtain ⟨B, C, L, R, hA, hl, hr⟩ := exists_matrix_rank_factorization (A.map e)
  let D := L.map c * A * R.map c
  have he (x : k) : e (c x) = x := congrFun (congrArg DFunLike.coe h) x
  have hd : D.map e = 1 := by
    simp only [D, Matrix.map_mul, Matrix.map_map, Function.comp_def, he]
    change L * A.map e * R = 1
    calc
      L * A.map e * R = L * (B * C) * R := congrArg (fun M ↦ L * M * R) hA.symm
      _ = 1 := by rw [← Matrix.mul_assoc L, hl, Matrix.one_mul, hr]
  have hd' : D.det ≠ 0 := by
    intro hz
    have hh : e D.det = 1 := by
      rw [RingHom.map_det]
      change (D.map e).det = 1
      rw [hd, Matrix.det_one]
    rw [hz, map_zero] at hh
    exact zero_ne_one hh
  have hdet : (D.map f).det ≠ 0 := by
    have hm : f D.det = (D.map f).det := RingHom.map_det f D
    exact hm ▸ fun hz ↦ hd' (hf (hz.trans (map_zero f).symm))
  have hrank : (D.map f).rank = (A.map e).rank := by
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin]
  rw [← hrank]
  simp only [D, Matrix.map_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Specialization of the coefficients to a field cannot increase rank. -/
theorem matrix_rank_specialization_le {k S m n : Type*} [Field k] [CommRing S] [IsDomain S]
    [Fintype m] [Fintype n] (e : S →+* k) (c : k →+* S)
    (h : e.comp c = RingHom.id k) (A : Matrix m n S) : (A.map e).rank ≤ A.rank := by
  simpa using matrix_rank_specialization_le_of_injective e c h (RingHom.id S) Function.injective_id A

end EFiniteCharacterizations
