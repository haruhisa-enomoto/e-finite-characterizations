module

public import EFiniteCharacterizations.LinearAlgebra.DeterminantDescent
public import EFiniteCharacterizations.LinearAlgebra.StrictMatrixExpansion
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Descent of simultaneous rectangular block ranks -/

@[expose] public section
open Matrix Module
namespace EFiniteCharacterizations

variable {k E : Type*} [Field k] [Field E] [Algebra k E]
  {a m n : Type*} [Fintype a] [Fintype m] [Fintype n]

private noncomputable def expandedVectors {q t : ℕ} (b : Basis (Fin q) k E) (s : Type*) :
    (Fin t × s → E) ≃ (Fin (t*q) × s → k) where
  toFun z p := b.equivFun (z ((finProdFinEquiv.symm p.1).1,p.2)) (finProdFinEquiv.symm p.1).2
  invFun z p := b.equivFun.symm (fun j ↦ z (finProdFinEquiv (p.1,j),p.2))
  left_inv z := by funext ⟨i,l⟩; simp
  right_inv z := by
    funext ⟨i,l⟩
    obtain ⟨⟨j,h⟩,rfl⟩ := (finProdFinEquiv (m := t) (n := q)).surjective i
    simp only [Equiv.symm_apply_apply,LinearEquiv.apply_symm_apply]

private noncomputable def expandedCoefficients {q t : ℕ} (b : Basis (Fin q) k E)
    (z : Fin t × (a × Fin t) → E) (p : Fin (t*q) × (a × Fin (t*q))) : k :=
  let i := finProdFinEquiv.symm p.1
  let j := finProdFinEquiv.symm p.2.2
  b.equivFun (z (i.1,p.2.1,j.1) * b j.2) i.2

omit [Fintype m] in
private theorem expanded_mulVec {t q : ℕ} (b : Basis (Fin q) k E) (z : Fin t × (a × Fin t) → E)
    (D : a → Matrix m n k) (v : Fin t × n → E) :
    (blockFamily D (expandedCoefficients b z)).mulVec (expandedVectors b n v) =
      expandedVectors b m ((blockFamily (fun j ↦ (D j).map (algebraMap k E)) z).mulVec v) := by
  classical
  funext ⟨p,l⟩
  obtain ⟨⟨i,h⟩,rfl⟩ := (finProdFinEquiv (m := t) (n := q)).surjective p
  change (∑ j : Fin (t*q) × n, (∑ u, expandedCoefficients b z (finProdFinEquiv (i,h),u,j.1) * D u l j.2) *
      expandedVectors b n v j) = _
  rw [Fintype.sum_prod_type,← finProdFinEquiv.sum_comp,Fintype.sum_prod_type]
  simp only [expandedVectors,Equiv.coe_fn_mk,Equiv.symm_apply_apply]
  change _ = b.equivFun (∑ j : Fin t × n, (∑ u, z (i,u,j.1) * algebraMap k E (D u l j.2)) * v j)
    h
  simp only [expandedCoefficients,Equiv.symm_apply_apply,Fintype.sum_prod_type,
    map_sum,Finset.sum_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  have hc := congrFun (Algebra.leftMulMatrix_mulVec_repr b (z (i,u,j)) (v (j,c))) h
  change (∑ f, Algebra.leftMulMatrix b (z (i,u,j)) h f * b.equivFun (v (j,c)) f) =
    b.equivFun (z (i,u,j) * v (j,c)) h at hc
  rw [show z (i,u,j) * algebraMap k E (D u l c) * v (j,c) = D u l c • (z (i,u,j) * v (j,c)) by
    rw [Algebra.smul_def]; ring,map_smul,Pi.smul_apply,smul_eq_mul,← hc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change (b.repr (z (i,u,j) * b f) h * D u l c * b.equivFun (v (j,c)) f) = _
  ring

private theorem inj_of_map {F : Type*} [Field F] (e : E →+* F) (A : Matrix m n E)
    (h : Function.Injective (A.map e).mulVec) : Function.Injective A.mulVecLin := by
  have he := LinearMap.finrank_range_of_inj (f := (A.map e).mulVecLin) h
  rw [← Matrix.rank,matrix_rank_map_from_field,Module.finrank_pi] at he
  have ht := A.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank,he,Module.finrank_pi] at ht
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

private theorem surj_of_map {F : Type*} [Field F] (e : E →+* F) (A : Matrix m n E)
    (h : Function.Surjective (A.map e).mulVec) : Function.Surjective A.mulVecLin := by
  have he : (A.map e).rank = Fintype.card m := by
    rw [Matrix.rank,LinearMap.range_eq_top.mpr h,finrank_top,Module.finrank_pi]
  rw [matrix_rank_map_from_field] at he
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (he.trans (Module.finrank_pi E).symm))

omit [Fintype m] in
private theorem map_ground_block {F : Type*} [Field F] [Algebra k F]
    (S : IntermediateField k F) {t : ℕ} (c : Fin t × (a × Fin t) → S) (A : a → Matrix m n k) :
    (blockFamily (fun j ↦ (A j).map (algebraMap k S)) c).map S.val =
      blockFamily (fun j ↦ (A j).map (algebraMap k F)) (fun i ↦ (c i : F)) := by
  ext i j
  simp [Matrix.map_apply,blockFamily]

/-- A coefficient tuple giving simultaneous full column and row rank over an
algebraic extension yields one ground tuple, possibly of larger block size.
Restriction of scalars uses the same regular representation on both families. -/
theorem exists_ground_block_rank_pair {F : Type*} [Field F] [Algebra k F] [Algebra.IsAlgebraic k F]
    {m' n' : Type*} [Fintype m'] [Fintype n']
    (D : a → Matrix m n k) (H : a → Matrix m' n' k) {t : ℕ} (ht : 0 < t)
    (z : Fin t × (a × Fin t) → F)
    (hi : Function.Injective (blockFamily (fun j ↦ (D j).map (algebraMap k F)) z).mulVec)
    (hs : Function.Surjective (blockFamily (fun j ↦ (H j).map (algebraMap k F)) z).mulVec) :
    ∃ (q : ℕ) (_ : 0 < q) (x : Fin q × (a × Fin q) → k),
      Function.Injective (blockFamily D x).mulVec ∧ Function.Surjective (blockFamily H x).mulVec := by
  classical
  let E := IntermediateField.adjoin k (Set.range z)
  have : Module.Finite k E := IntermediateField.finiteDimensional_adjoin
    (fun v _ ↦ (Algebra.IsAlgebraic.isAlgebraic v).isIntegral)
  let c i : E := ⟨z i,IntermediateField.subset_adjoin k _ ⟨i,rfl⟩⟩
  have h₁ := inj_of_map E.val.toRingHom _ ((map_ground_block E c D).symm ▸ hi)
  have h₂ := surj_of_map E.val.toRingHom _ ((map_ground_block E c H).symm ▸ hs)
  let b := Module.finBasis k E
  refine ⟨_,Nat.mul_pos ht Module.finrank_pos,expandedCoefficients b c,?_,?_⟩
  · intro x y hxy
    obtain ⟨v,rfl⟩ := (expandedVectors b n).surjective x
    obtain ⟨w,rfl⟩ := (expandedVectors b n).surjective y
    rw [expanded_mulVec,expanded_mulVec] at hxy
    exact congrArg _ (h₁ ((expandedVectors b m).injective hxy))
  · intro x
    obtain ⟨v,rfl⟩ := (expandedVectors b m').surjective x
    obtain ⟨w,hw⟩ := h₂ v
    exact ⟨expandedVectors b n' w,(expanded_mulVec b c H w).trans (congrArg _ hw)⟩

/-- Two strictly expanding families, one on columns and one on transpose
columns, have a common block substitution of full column and row ranks. -/
theorem exists_simultaneous_block_ranks {m' n' : Type*} [Fintype m'] [Fintype n']
    (D : a → Matrix m n k) (H : a → Matrix m' n' k)
    (hd : ∀ r s, HasMatrixSubspacePair D r s → 0 < r → r < s)
    (hh : ∀ r s, HasMatrixSubspacePair (fun j ↦ (H j).transpose) r s → 0 < r → r < s) :
    ∃ (q : ℕ) (_ : 0 < q) (x : Fin q × (a × Fin q) → k),
      Function.Injective (blockFamily D x).mulVec ∧ Function.Surjective (blockFamily H x).mulVec := by
  classical
  let F := AlgebraicClosure k
  let D' j := (D j).map (algebraMap k F)
  let H' j := (H j).map (algebraMap k F)
  let t := max (Fintype.card n ^ 2) (Fintype.card m' ^ 2) + 1
  obtain ⟨p,hp,hcol⟩ := polynomial_of_block_expansion (t := Fin t) D' (fun r s pair hr ↦ by
    have h := strict_matrix_expansion_of_algebraic D hd pair hr
    exact ⟨fun _ ↦ h,fun _ ↦ h.le⟩) (by simpa only [Fintype.card_fin] using Nat.lt_succ_of_le (le_max_left ..))
  obtain ⟨q,hq,hrow⟩ := polynomial_of_block_expansion (t := Fin t) (fun j ↦ (H' j).transpose)
    (fun r s pair hr ↦ by
      have h := strict_matrix_expansion_of_algebraic (fun j ↦ (H j).transpose) hh (E := F) pair hr
      exact ⟨fun _ ↦ h,fun _ ↦ h.le⟩) (by simpa only [Fintype.card_fin] using Nat.lt_succ_of_le (le_max_right ..))
  let flip : Fin t × (a × Fin t) → Fin t × (a × Fin t) := fun ⟨i,j,l⟩ ↦ (l,j,i)
  have hf : Function.Involutive flip := fun ⟨_,_,_⟩ ↦ rfl
  have hq' : MvPolynomial.rename flip q ≠ 0 := fun hz ↦ hq
    (MvPolynomial.rename_injective _ hf.injective (hz.trans (map_zero _).symm))
  obtain ⟨z,hz⟩ : ∃ z, MvPolynomial.eval z (p * MvPolynomial.rename flip q) ≠ 0 := by
    by_contra! h
    exact mul_ne_zero hp hq' (MvPolynomial.funext (fun z ↦ (h z).trans (map_zero _).symm))
  rw [map_mul,MvPolynomial.eval_rename] at hz
  let A := blockFamily H' z
  have ht : Function.Injective A.transpose.mulVecLin := hrow (z ∘ flip) (right_ne_zero_of_mul hz)
  have hr : A.rank = Module.finrank F (Fin t × m' → F) := by
    rw [← Matrix.rank_transpose,Matrix.rank,LinearMap.finrank_range_of_inj ht]
  exact exists_ground_block_rank_pair D H (Nat.succ_pos _) z (hcol _ (left_ne_zero_of_mul hz))
    (LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq hr))

end EFiniteCharacterizations
