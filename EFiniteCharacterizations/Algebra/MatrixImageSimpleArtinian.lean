module

public import EFiniteCharacterizations.Algebra.MatrixSandwichOperators
public import Mathlib.RingTheory.SimpleRing.Congr
public import Mathlib.RingTheory.Artinian.Module

/-! # Simplicity and the Artinian condition over the matrix coefficient field -/

@[expose] public section

namespace EFiniteCharacterizations

variable {B K n ι : Type*} [Ring B] [Field K] [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype ι] (q : B →+* Matrix n n K) (b : Module.Basis ι K (Matrix n n K))
    (hb : Set.range b ⊆ Set.range q)

local notation "L" => matrixCoefficientField q b
local notation "H" => matrixImageAlgebra q b

include hb in
theorem matrixImage_simple : IsSimpleRing H := by
  classical
  refine isSimpleRing_iff_isTwoSided_imp.mpr ⟨inferInstance, fun I hI ↦ ?_⟩
  by_cases h : I = ⊥
  · exact Or.inl h
  obtain ⟨x,hx,hne⟩ := I.ne_bot_iff.mp h
  let β := matrixImageBasis q b hb
  obtain ⟨i,hi⟩ : ∃ i, β.repr x i ≠ 0 := by
    by_contra! hall
    exact hne (β.repr.injective (by ext j; simp [hall]))
  let f := (β.coord i).smulRight ((β.repr x i)⁻¹ • (1 : H))
  have hf : f x = 1 := by simp [f, Module.Basis.coord_apply, smul_smul, hi]
  obtain ⟨c,hc⟩ := matrixImage_operator_expansion q b hb f
  apply Or.inr
  apply I.eq_top_iff_one.mpr
  rw [← hf, ← hc x]
  apply I.sum_mem
  intro p _
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ (I.mul_mem_right _ (I.mul_mem_left _ hx))

include hb in
omit [Nonempty n] in
theorem matrixImage_artinian : IsArtinianRing H := by
  let : Module.Finite L H := Module.Finite.of_basis (matrixImageBasis q b hb)
  exact isArtinian_of_tower L inferInstance

end EFiniteCharacterizations
