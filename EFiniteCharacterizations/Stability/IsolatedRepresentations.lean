module

public import EFiniteCharacterizations.Modules.FreeHomCoordinates

/-! # Hom separation for bricks with bounded coordinates -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

private theorem rank_lt_of_kernel_and_exact {D E a b c : Type*} [Field D] [Field E]
    [Fintype a] [Fintype b] [Fintype c]
    (U : Matrix b a D) (V : Matrix c b D) (U' : Matrix b a E) (V' : Matrix c b E)
    (hn : ¬ Function.Injective U.mulVecLin) (he : LinearMap.ker V.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hi : Function.Injective U'.mulVecLin) (hz : LinearMap.range U'.mulVecLin ≤ LinearMap.ker V'.mulVecLin) :
    V'.rank < V.rank := by
  have hk : 0 < Module.finrank D (LinearMap.ker U.mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr (fun h ↦ hn (LinearMap.ker_eq_bot.mp h))
  have h₁ := U.mulVecLin.finrank_range_add_finrank_ker
  have h₂ := V.mulVecLin.finrank_range_add_finrank_ker
  have h₃ := V'.mulVecLin.finrank_range_add_finrank_ker
  have h₄ := Submodule.finrank_mono he
  have h₅ := Submodule.finrank_mono hz
  rw [LinearMap.finrank_range_of_inj hi, Module.finrank_pi] at h₅
  simp only [Module.finrank_pi] at h₁ h₂ h₃
  change Module.finrank E (LinearMap.range V'.mulVecLin) < Module.finrank D (LinearMap.range V.mulVecLin)
  omega

namespace FreeHom

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

/-- Suppose each target has a three-term free complex giving nonzero Hom
and vanishing first cohomology at that target, and zero Hom at every other
target. If the targets have one fixed dimension over commuting coefficient
fields, the family is finite. -/
theorem finite_of_isolating_complexes (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
    {I : Type*} (X : I → FGModuleCat.{u} R) (D : I → Type u) [∀ i, Field (D i)]
    [∀ i, Algebra k (D i)] [∀ i, Module (D i) ((X i).obj : Type u)]
    [∀ i, SMulCommClass R (D i) ((X i).obj : Type u)] [∀ i, IsScalarTower k (D i) ((X i).obj : Type u)]
    {d : ℕ} (bX : ∀ i, Module.Basis (Fin d) (D i) ((X i).obj : Type u))
    (h : ∀ i, ∃ (a b c : ℕ) (f : freeModule R b ⟶ freeModule R a) (g : freeModule R c ⟶ freeModule R b),
      g ≫ f = 0 ∧ (∃ p : freeModule R a ⟶ X i, p ≠ 0 ∧ f ≫ p = 0) ∧
      (∀ q : freeModule R b ⟶ X i, g ≫ q = 0 → ∃ p, f ≫ p = q) ∧
      ∀ j, i ≠ j → ∀ p : freeModule R a ⟶ X j, f ≫ p = 0 → p = 0) : Finite I := by
  classical
  choose a b c f g hw hp hfac hz using h
  let bR := Module.finBasis k R
  let ev i := evalAction bR (bX i)
  let U i := precomposeMatrix bR d (f i)
  let V i := precomposeMatrix bR d (g i)
  apply finite_of_separating_matrix_ranks ev _ _ V
  intro i j hij
  apply rank_lt_of_kernel_and_exact ((U i).map (ev i)) _ ((U i).map (ev j))
  · intro hi
    obtain ⟨p,hp₀,hh⟩ := hp i
    have hval := precomposeMatrix_mulVec bR (bX i) (f i) p
    rw [hh,coordinates_zero] at hval
    have hn := LinearMap.ker_eq_bot'.mp (LinearMap.ker_eq_bot.mpr hi) _ hval
    exact hp₀ ((coordinates (bX i)).injective (hn.trans (coordinates_zero _ _).symm))
  · intro z hzero
    obtain ⟨q,rfl⟩ := (coordinates (bX i)).surjective z
    change ((V i).map (ev i)).mulVec _ = 0 at hzero
    rw [precomposeMatrix_mulVec, ← coordinates_zero (bX i) (c i)] at hzero
    obtain ⟨p,hp⟩ := hfac i q ((coordinates (bX i)).injective hzero)
    exact ⟨coordinates (bX i) p,(precomposeMatrix_mulVec bR (bX i) (f i) p).trans (congrArg _ hp)⟩
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z he
    obtain ⟨p,rfl⟩ := (coordinates (bX j)).surjective z
    change ((U i).map (ev j)).mulVec _ = 0 at he
    rw [precomposeMatrix_mulVec, ← coordinates_zero (bX j) (b i)] at he
    rw [hz i j hij p ((coordinates (bX j)).injective he),coordinates_zero]
  · rintro _ ⟨z,rfl⟩
    obtain ⟨p,rfl⟩ := (coordinates (bX j)).surjective z
    change ((V i).map (ev j)).mulVec (((U i).map (ev j)).mulVec _) = 0
    rw [precomposeMatrix_mulVec,precomposeMatrix_mulVec,← Category.assoc,hw,zero_comp,coordinates_zero]

end FreeHom
end EFiniteCharacterizations
