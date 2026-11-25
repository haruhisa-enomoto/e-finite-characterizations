module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Length

/-! # Finite modules over a finite-dimensional algebra -/

@[expose] public section

universe u

namespace EFiniteCharacterizations

/-- Finite right modules, viewed as left modules over the opposite ring. -/
abbrev FiniteRightModule (A : Type u) [Ring A] := FGModuleCat.{u} Aᵐᵒᵖ

/-- All right modules, in the same convention. -/
abbrev RightModule (A : Type u) [Ring A] := ModuleCat.{u} Aᵐᵒᵖ

variable (k A : Type u) [Field k] [Ring A] [Algebra k A] [Module.Finite k A]

include k in
theorem isArtinianRing_op : IsArtinianRing Aᵐᵒᵖ := by
  exact IsArtinianRing.of_finite k Aᵐᵒᵖ

variable {A} in
include k in
theorem finiteRightModule_isFiniteLength (M : FiniteRightModule A) :
    IsFiniteLength Aᵐᵒᵖ M := by
  have := isArtinianRing_op k A
  have := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end EFiniteCharacterizations
