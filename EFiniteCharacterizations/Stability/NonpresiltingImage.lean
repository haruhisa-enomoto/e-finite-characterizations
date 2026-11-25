module

public import EFiniteCharacterizations.Presentations.Nonpresilting
public import EFiniteCharacterizations.Presentations.ProjectiveHomWeight
public import EFiniteCharacterizations.Presentations.TwoTermEuler
public import EFiniteCharacterizations.Stability.StableImage

/-! # Stable bricks from nonpresilting presentations -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R] [IsArtinianRing R]

/-- A nonpresilting differential gives a stable brick by correcting its Euler weight
using the dimension of the image over the ground field. -/
theorem exists_stable_image_of_not_isPresilting (P : TwoTerm R) (hP : ¬ P.IsPresilting) :
    ∃ f : cokernel P.differential ⟶ P.nakayamaKernel k, f ≠ 0 ∧ IsBrick (image f) ∧
      ((P.eulerWeight k).corrected (dimensionWeight (R := R) k) (image f)).IsStable (image f) :=
  exists_stable_image_of_hom_difference k (P.eulerWeight k) (dimensionWeight (R := R) k)
    (dimensionWeight_pos k)
    (fun M ↦ (P.eulerWeight_eval k M).trans (P.euler_eq_hom_difference k M))
    (P.exists_nonzero_hom_of_not_isPresilting k hP)

end EFiniteCharacterizations.TwoTerm
