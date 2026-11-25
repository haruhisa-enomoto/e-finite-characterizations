module

public import EFiniteCharacterizations.Modules.ProjectiveBiproducts

/-! # Representing integral projective classes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.ProjectiveClass

variable {R : Type u} [Ring R]

/-- Every class is a difference of classes of two finite projective modules. -/
theorem exists_sub (g : ProjectiveClass R) :
    ∃ P Q : FiniteProjective R, of P - of Q = g := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective g
  change ∃ P Q : FiniteProjective R, of P - of Q = QuotientAddGroup.mk' _ x
  induction x using FreeAbelianGroup.induction_on with
  | zero => exact ⟨zeroProjective R, zeroProjective R, by simp⟩
  | of P =>
    refine ⟨biprod P (zeroProjective R), zeroProjective R, ?_⟩
    change of (biprod P (zeroProjective R)) - of (zeroProjective R) = of P
    rw [of_biprod, add_sub_cancel_right]
  | neg P h =>
    obtain ⟨S, T, heq⟩ := h
    exact ⟨T, S, by rw [map_neg, ← heq, neg_sub]⟩
  | add x y hx hy =>
    obtain ⟨P, Q, hp⟩ := hx
    obtain ⟨S, T, hs⟩ := hy
    refine ⟨biprod P S, biprod Q T, ?_⟩
    rw [map_add, ← hp, ← hs, of_biprod, of_biprod]
    abel

/-- Every integral projective class is the class of a two-term complex. -/
theorem exists_twoTerm (g : ProjectiveClass R) : ∃ P : TwoTerm R, P.projectiveClass = g := by
  obtain ⟨P, Q, heq⟩ := exists_sub g
  exact ⟨⟨Q.val, P.val, Q.property, P.property, 0⟩, heq⟩

end EFiniteCharacterizations.ProjectiveClass
