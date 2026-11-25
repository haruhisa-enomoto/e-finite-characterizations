module

public import EFiniteCharacterizations.Presentations.TwoTerm
public import Mathlib.Algebra.Category.FGModuleCat.Colimits

/-! # Applying Hom to a projective differential -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R]

/-- The map induced by the differential on Hom into a finite module. -/
def precompose (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    (P.target ⟶ M) →+ (P.source ⟶ M) where
  toFun f := P.differential ≫ f
  map_zero' := comp_zero
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _

/-- The kernel of the differential on Hom consists of the maps out of its cokernel. -/
noncomputable def cokernelHomEquiv (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    (cokernel P.differential ⟶ M) ≃+ (P.precompose M).ker where
  toFun f := ⟨cokernel.π P.differential ≫ f, by
    change P.differential ≫ cokernel.π P.differential ≫ f = 0
    rw [← Category.assoc, cokernel.condition, zero_comp]⟩
  invFun f := cokernel.desc P.differential f.val f.property
  left_inv f := by
    apply (cancel_epi (cokernel.π P.differential)).mp
    exact cokernel.π_desc _ _ _
  right_inv f := Subtype.ext (cokernel.π_desc _ _ _)
  map_add' f g := Subtype.ext (Preadditive.comp_add _ _ _ _ _ _)

end EFiniteCharacterizations.TwoTerm
