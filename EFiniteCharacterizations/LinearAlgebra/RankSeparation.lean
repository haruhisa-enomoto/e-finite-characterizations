module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.RingTheory.Polynomial.Basic

/-! # Separating field-valued points by matrix ranks -/

@[expose] public section

namespace EFiniteCharacterizations

open Matrix

private theorem exists_independent_columns {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) :
    ∃ c : Fin A.rank → n, LinearIndependent K (fun i ↦ A.col (c i)) := by
  obtain ⟨f,hf,_,hi⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
  rw [A.rank_eq_finrank_span_cols]
  choose c hc using hf
  exact ⟨c,by simpa only [hc] using hi⟩

/-- There is a square minor of size equal to the rank and with nonzero determinant. -/
theorem exists_nonzero_rank_minor {K m n : Type*} [Field K] [Fintype m] [Fintype n] (A : Matrix m n K) :
    ∃ (r : Fin A.rank → m) (c : Fin A.rank → n), (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨c,hc⟩ := exists_independent_columns A
  let B := (A.submatrix id c).transpose
  have hi : LinearIndependent K B.row := hc
  have hb : B.rank = A.rank := by simpa using hi.rank_matrix
  obtain ⟨r,hr⟩ : ∃ r : Fin A.rank → m, LinearIndependent K (fun i ↦ B.col (r i)) := by
    obtain ⟨r,hr⟩ := exists_independent_columns B
    let e := finCongr hb.symm
    exact ⟨r ∘ e, hr.comp e e.injective⟩
  exact ⟨r,c,Matrix.nonsingular_iff_det_ne_zero.1 (Matrix.Nonsingular.of_linearIndependent_row hr)⟩

/-- A family of field-valued points of a Noetherian ring is finite if each point
can be distinguished from all the others by a single nonvanishing function. -/
theorem finite_of_separating_ring_elements {A I : Type*} [CommRing A] [IsNoetherianRing A]
    {K : I → Type*} [∀ i, Field (K i)] (ev : ∀ i, A →+* K i) (f : I → A)
    (hn : ∀ i, ev i (f i) ≠ 0) (hz : ∀ i j, i ≠ j → ev j (f i) = 0) : Finite I := by
  classical
  let J := Ideal.span (Set.range f)
  obtain ⟨s,hs,he⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := A) (Set.range f)).1
    (show J.FG from Ideal.fg_of_isNoetherianRing J)
  choose g hg using fun x : s ↦ hs x.property
  apply Finite.of_surjective g
  intro j
  by_contra h
  have hle : J ≤ RingHom.ker (ev j) := by
    rw [show J = Ideal.span (↑s : Set A) from he, Ideal.span_le]
    intro x hx
    let a : s := ⟨x,hx⟩
    exact (congrArg (ev j) (hg a).symm).trans (hz (g a) j (fun eq ↦ h ⟨a,eq⟩))
  exact hn j (hle (Ideal.subset_span (Set.mem_range_self j)))

/-- At each point suppose some matrix over the parameter ring has strictly
larger rank there than at every other point. The residue fields and the test
matrix may both depend on the point. -/
theorem finite_of_separating_matrix_ranks {A I : Type*} [CommRing A] [IsNoetherianRing A]
    {K : I → Type*} [∀ i, Field (K i)] (ev : ∀ i, A →+* K i)
    (m n : I → Type*) [∀ i, Fintype (m i)] [∀ i, Fintype (n i)]
    (M : ∀ i, Matrix (m i) (n i) A)
    (h : ∀ i j, i ≠ j → ((M i).map (ev j)).rank < ((M i).map (ev i)).rank) : Finite I := by
  classical
  choose r c hc using fun i ↦ exists_nonzero_rank_minor ((M i).map (ev i))
  let f (i : I) := ((M i).submatrix (r i) (c i)).det
  have he (i j : I) : ev j (f i) = (((M i).map (ev j)).submatrix (r i) (c i)).det :=
    RingHom.map_det _ _
  refine finite_of_separating_ring_elements ev f (fun i ↦ (he i i) ▸ hc i) (fun i j hn ↦ ?_)
  rw [he]
  by_contra hdet
  have hle := ((M i).map (ev j)).rank_submatrix_le (r i) (c i)
  rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hle
  exact (h i j hn).not_ge hle

end EFiniteCharacterizations
