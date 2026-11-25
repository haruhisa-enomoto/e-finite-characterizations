module

public import EFiniteCharacterizations.ScalarExtension.GeometricPresiltingDescent
public import EFiniteCharacterizations.Stability.CommonStableClass
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # A geometric stable family at a weight defined over the ground field -/

@[expose] public section

open CategoryTheory

universe u

namespace EFiniteCharacterizations.FieldExtension

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Algebra.IsAlgebraic k F]
  [Infinite F] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

/-- A missing ground class gives infinitely many stable modules of one
geometric composition class. Their common weight is a ground Euler weight
and the regular weight combined with integer coefficients. -/
theorem exists_infinite_geometric_stable_family (h : ¬ IsEFinite R) :
    letI := IsNoetherianRing.of_finite F (ExtendedAlgebra k F R)
    ∃ (P : TwoTerm R) (d : ℕ) (e : ℤ) (c : GrothendieckGroup (FGModuleCat.{u} (ExtendedAlgebra k F R))),
      (stableClassesOfClass ((d : ℤ) • (extendTwoTerm k F R P).eulerWeight F -
        e • dimensionWeight (R := ExtendedAlgebra k F R) F) c).Infinite := by
  classical
  let := IsNoetherianRing.of_finite F (ExtendedAlgebra k F R)
  let := IsArtinianRing.of_finite F (ExtendedAlgebra k F R)
  obtain ⟨g,hg⟩ := not_forall.mp h
  obtain ⟨P,hP⟩ := g.exists_twoTerm
  let U := extendTwoTerm k F R P
  have := U.projective_source
  have := U.projective_target
  have hw (p : U.source ⟶ U.target) : ∃ M, (TwoTerm.ofDifferential p).IsStableImageWitness F M :=
    (TwoTerm.ofDifferential p).exists_stableImageWitness_of_not_isPresilting F
      (no_presilting_differential_over_algebraic_extension P (hP.symm ▸ hg) p)
  choose B hB using hw
  obtain ⟨d,e,hi⟩ := exists_infinite_stableClassesOfDimension_at_corrected_weight F B hB
  obtain ⟨c,hc⟩ := exists_infinite_stableClassesOfClass_of_infinite_dimension F hi
  exact ⟨P,d,e,c,hc⟩

end EFiniteCharacterizations.FieldExtension
