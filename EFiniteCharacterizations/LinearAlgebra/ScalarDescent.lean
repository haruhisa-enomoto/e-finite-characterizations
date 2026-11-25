module

public import EFiniteCharacterizations.LinearAlgebra.AddClosure
public import EFiniteCharacterizations.LinearAlgebra.ScalarCategory
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Descending factorizations from scalar-extended Hom spaces -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace EFiniteCharacterizations.ScalarCategory

variable {k : Type*} [Field k] (F : Type*) [Field F] [Algebra k F]
  {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- A retraction through `Y` after scalar extension puts `X` in the additive
closure of `Y` over the ground field. -/
theorem isInAdd_of_scalar_retraction {X Y : C}
    (f : (of (k := k) (S := F)).obj X ⟶ (of (k := k) (S := F)).obj Y)
    (g : (of (k := k) (S := F)).obj Y ⟶ (of (k := k) (S := F)).obj X)
    (h : f ≫ g = 𝟙 ((of (k := k) (S := F)).obj X)) :
    IsInAdd X Y := by
  let s : Set (X ⟶ X) := {z | ∃ (a : X ⟶ Y) (b : Y ⟶ X), a ≫ b = z}
  let W := Submodule.span k s
  have hm : 𝟙 X ∈ W := by
    let π := W.mkQ
    have hzero (a : F ⊗[k] (X ⟶ Y)) (b : F ⊗[k] (Y ⟶ X)) :
        π.baseChange F (compLinear a b) = 0 := by
      revert b
      refine TensorProduct.inductionOn a ?_ ?_
      · intro r a b
        refine TensorProduct.inductionOn b ?_ ?_
        · intro t b
          have hz : π (a ≫ b) = 0 := (Submodule.Quotient.mk_eq_zero W).2
            (Submodule.subset_span (show a ≫ b ∈ s from ⟨a, b, rfl⟩))
          simp [compLinear, hz]
        · intro b b' hb hb'
          simp only [map_add, hb, hb', add_zero]
      · intro a a' ha ha' b
        simp only [map_add, LinearMap.add_apply, ha b, ha' b, add_zero]
    change compLinear f g = (1 : F) ⊗ₜ[k] 𝟙 X at h
    have h1 : π.baseChange F ((1 : F) ⊗ₜ[k] 𝟙 X) = 0 :=
      (congrArg (π.baseChange F) h).symm.trans (hzero f g)
    rw [LinearMap.baseChange_tmul] at h1
    obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : F) ≠ 0)
    let test := (TensorProduct.lid k ((X ⟶ X) ⧸ W)).toLinearMap.comp
      (TensorProduct.map ℓ (LinearMap.id : ((X ⟶ X) ⧸ W) →ₗ[k] ((X ⟶ X) ⧸ W)))
    have hz := congrArg test h1
    have hπ : π (𝟙 X) = 0 := by simpa [test, hℓ] using hz
    exact (Submodule.Quotient.mk_eq_zero W).1 hπ
  refine Submodule.span_induction (p := fun z _ ↦
    ∃ l : List ((X ⟶ Y) × (Y ⟶ X)), (l.map (fun p ↦ p.1 ≫ p.2)).sum = z)
    ?_ ?_ ?_ ?_ hm
  · rintro z ⟨a, b, rfl⟩
    exact ⟨[(a, b)], by simp⟩
  · exact ⟨[], rfl⟩
  · rintro x y _ _ ⟨l, rfl⟩ ⟨t, rfl⟩
    exact ⟨l ++ t, by simp⟩
  · rintro c x hx ⟨l, rfl⟩
    clear hx
    refine ⟨l.map (fun p ↦ (c • p.1, p.2)), ?_⟩
    induction l with
    | nil => simp
    | cons p l ih => simp only [List.map_cons, List.sum_cons, Linear.smul_comp, smul_add, ih]

/-- A scalar-extended isomorphism gives finite identity factorizations in
both directions over the ground field. -/
theorem isInAdd_of_scalar_iso {X Y : C}
    (e : (of (k := k) (S := F)).obj X ≅ (of (k := k) (S := F)).obj Y) :
    IsInAdd X Y ∧ IsInAdd Y X :=
  ⟨isInAdd_of_scalar_retraction F e.hom e.inv e.hom_inv_id,
    isInAdd_of_scalar_retraction F e.inv e.hom e.inv_hom_id⟩

end EFiniteCharacterizations.ScalarCategory
