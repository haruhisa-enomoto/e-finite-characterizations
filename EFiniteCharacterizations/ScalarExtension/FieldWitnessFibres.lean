module

public import EFiniteCharacterizations.ScalarExtension.RestrictionOfExtension
public import EFiniteCharacterizations.ScalarExtension.FieldRestriction
public import EFiniteCharacterizations.Stability.SemistablePowers
public import EFiniteCharacterizations.Stability.StableFiniteness

/-! # Bounding the fibres of restriction witnesses at a fixed weight -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F] [IsNoetherianRing R]
  [IsNoetherianRing (ExtendedAlgebra k F R)]

local notation "R₊" => ExtendedAlgebra k F R

/-- Extending a semistable ground module preserves semistability for the
extended Euler weight. -/
theorem isSemistable_extendObj (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (hM : (P.eulerWeight k).IsSemistable M) :
    ((extendTwoTerm k F R P).eulerWeight F).IsSemistable (extendObj k F R M) := by
  apply (isSemistable_restrictObj_iff k F R P _).1
  let b := Module.finBasis k F
  let e := restrictExtendBasisEquiv k F R b M
  exact (hM.finPower _).of_iso e.symm.toFGModuleCatIso

/-- Ground Hom from a semistable module to the restriction of a stable
extension module produces a stable quotient of the extended ground module. -/
theorem exists_epi_of_hom_restrictObj (P : TwoTerm R) {M : FGModuleCat.{u} R} {N : FGModuleCat.{u} R₊}
    (hM : (P.eulerWeight k).IsSemistable M) (hN : ((extendTwoTerm k F R P).eulerWeight F).IsStable N)
    (f : M ⟶ restrictObj k F R N) (hf : f ≠ 0) : ∃ g : extendObj k F R M ⟶ N, Epi g := by
  let e := (homLinearEquiv k F R M N).symm
  have hf' : e f ≠ 0 := fun h ↦ hf (e.injective (h.trans (map_zero e).symm))
  exact ⟨e f, Weight.epi_of_isSemistable_of_isStable (isSemistable_extendObj k F R P M hM) hN _ hf'⟩

/-- Stable extension classes whose restriction receives a nonzero map
from a fixed ground module at the corresponding weight. -/
def stableExtensionClassesOver (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    Set (Skeleton (FGModuleCat.{u} R₊)) :=
  {x | ((extendTwoTerm k F R P).eulerWeight F).IsStable ((fromSkeleton _).obj x) ∧
    ∃ f : M ⟶ restrictObj k F R ((fromSkeleton _).obj x), f ≠ 0}

/-- A ground module of dimension d attracts at most d stable extension
classes at a fixed extended weight. -/
theorem finite_and_ncard_stableExtensionClassesOver (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (hM : (P.eulerWeight k).IsSemistable M) :
    (stableExtensionClassesOver k F R P M).Finite ∧
      (stableExtensionClassesOver k F R P M).ncard ≤ Module.finrank k (M.obj : Type u) := by
  let W := (extendTwoTerm k F R P).eulerWeight F
  have hE := isSemistable_extendObj k F R P M hM
  have hsub : stableExtensionClassesOver k F R P M ⊆ stableQuotientClasses W (extendObj k F R M) := by
    rintro x ⟨hN, f, hf⟩
    let g := (homLinearEquiv k F R M ((fromSkeleton _).obj x)).symm
    exact ⟨hN, g f, fun h ↦ hf (g.injective (h.trans (map_zero g).symm))⟩
  obtain ⟨hfin, hcard⟩ := finite_and_ncard_stableQuotientClasses F W _ hE
  exact ⟨hfin.subset hsub, ((Set.ncard_le_ncard hsub hfin).trans hcard).trans_eq (finrank_extendObj k F R M)⟩

end

end EFiniteCharacterizations.FieldExtension
