module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionRigidity
public import EFiniteCharacterizations.ScalarExtension.AlgebraicSemistability

/-! # Reflection of stability under extension of scalars -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FieldExtension

variable (k L R : Type u) [Field k] [Field L] [Algebra k L] [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k L R)]

/-- Stability descends along every field extension. -/
theorem isStable_of_extendObj (P : TwoTerm R) {M : FGModuleCat.{u} R}
    (h : ((extendTwoTerm k L R P).eulerWeight L).IsStable (extendObj k L R M)) : (P.eulerWeight k).IsStable M := by
  have he (X : FGModuleCat.{u} R) : ((extendTwoTerm k L R P).eulerWeight L).eval (extendObj k L R X) =
      (P.eulerWeight k).eval X := by
    simp only [TwoTerm.eulerWeight_eval,extendTwoTerm,homFinrank_extendObj]
  refine ⟨fun hz ↦ h.1 ((extend k L R).map_isZero hz),(he M).symm.trans h.2.1,?_⟩
  intro T i hi ht hp
  let j := extendMap k L R i
  let _ : Mono j := (FGModuleCat.mono_iff_injective j).2 (Module.Flat.lTensor_preserves_injective_linearMap
    (M := L) (i.hom.hom.restrictScalars k) ((FGModuleCat.mono_iff_injective i).1 hi))
  have hT : ¬ IsZero (extendObj k L R T) := by
    intro hz
    have h0 := (dimensionWeight (R := ExtendedAlgebra k L R) L).eval_isZero hz
    have hpos := dimensionWeight_pos k T ht
    rw [dimensionWeight_eval,finrank_extendObj] at h0
    rw [dimensionWeight_eval] at hpos
    omega
  rw [← he]
  apply h.2.2 j hT
  intro hj
  have _ : Epi i := (epi_extendMap_iff k L R i).1 (inferInstanceAs (Epi j))
  exact hp (isIso_of_mono_of_epi i)

end EFiniteCharacterizations.FieldExtension
