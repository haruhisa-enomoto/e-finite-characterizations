module

public import EFiniteCharacterizations.Geometry.InversionCover
public import EFiniteCharacterizations.ScalarExtension.GeometricStableFamily
public import EFiniteCharacterizations.RingEpimorphisms.GeometricLocalizationCharts
public import EFiniteCharacterizations.Stability.GroundStableDeterminant

/-! # The universal localization criterion over arbitrary fields -/

@[expose] public section

open CategoryTheory

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

/-- A missing class gives a single ground differential whose geometric
inversion locus contains infinitely many stable classes. -/
theorem exists_infinite_fixed_class_extended_chart_of_not_isEFinite (hn : ¬ IsEFinite R) :
    let F := AlgebraicClosure k
    let B := FieldExtension.ExtendedAlgebra k F R
    letI := IsNoetherianRing.of_finite F B
    ∃ (T : TwoTerm R) (θ : Weight (FGModuleCat.{u} B)) (c : GrothendieckGroup (FGModuleCat.{u} B)),
      ((T.induce (FieldExtension.algebraInclusion k F R).toRingHom).stableInvertingClasses F ∩ stableClassesOfClass θ c).Infinite := by
  classical
  let F := AlgebraicClosure k
  let B := FieldExtension.ExtendedAlgebra k F R
  let := IsNoetherianRing.of_finite F B
  obtain ⟨P,d,e,c,hc⟩ := FieldExtension.exists_infinite_geometric_stable_family k F hn
  obtain ⟨Q,hQ⟩ := FieldExtension.exists_ground_corrected_weight k F R P d e
  rw [← hQ] at hc
  let J := Σ m : ℕ, (0 < m) ×' (Fin m → Fin m → (Q.source ⟶ Q.target))
  let T (j : J) := Q.blockDifferentialOnCopies j.2.2
  let U (j : J) := (T j).induce (FieldExtension.algebraInclusion k F R).toRingHom
  obtain ⟨j,hj⟩ := exists_infinite_fixed_class_chart_of_pointwise_inversion F _ c hc U
    (fun j M hs ↦ by
      change (((Q.blockDifferentialOnCopies j.2.2).induce
        (FieldExtension.algebraInclusion k F R).toRingHom).eulerWeight F).IsStable M
      rw [FieldExtension.eulerWeight_induce_block k F R]
      exact (stable_nsmul_iff _ M j.2.1).2 hs)
    (fun M _ hs ↦ by
      obtain ⟨m,hm,p,hp⟩ := FieldExtension.exists_ground_block_invertedOn k F R Q M hs
      exact ⟨⟨m,hm,p⟩,hp⟩)
  exact ⟨T j,_,c,hj⟩

/-- A missing class gives a single ground differential whose geometric
inversion locus contains infinitely many stable classes. -/
theorem exists_infinite_extended_stable_chart_of_not_isEFinite (hn : ¬ IsEFinite R) :
    let F := AlgebraicClosure k
    let B := FieldExtension.ExtendedAlgebra k F R
    letI := IsNoetherianRing.of_finite F B
    ∃ T : TwoTerm R,
      ((T.induce (FieldExtension.algebraInclusion k F R).toRingHom).stableInvertingClasses F).Infinite := by
  obtain ⟨T,θ,c,h⟩ := exists_infinite_fixed_class_extended_chart_of_not_isEFinite k hn
  exact ⟨T,h.mono Set.inter_subset_left⟩

/-- In the right-module convention, testing each single differential suffices. -/
theorem isEFinite_iff_singleton_localizations_finite :
    IsEFinite Rᵐᵒᵖ ↔ ∀ (P : TwoTerm Rᵐᵒᵖ) (B : Type u) [Ring B] [Algebra k B]
      (g : Rᵐᵒᵖ →ₐ[k] B), IsUniversalLocalization (fun _ : Unit ↦ P) g.toRingHom → Module.Finite k B := by
  refine ⟨fun he P _ _ _ g hg ↦ finite_right_singleton_localization k
    (rightUniversalLocalizationsFinite_of_isEFinite k he) P g hg, fun h ↦ ?_⟩
  by_contra hn
  let F := AlgebraicClosure k
  let := IsNoetherianRing.of_finite F (FieldExtension.ExtendedAlgebra k F Rᵐᵒᵖ)
  obtain ⟨P,hP⟩ := exists_infinite_extended_stable_chart_of_not_isEFinite k hn
  obtain ⟨B,_,_,g,hg⟩ := exists_algebra_universalLocalization k (fun _ : PUnit.{u+1} ↦ P)
  have hu : IsUniversalLocalization (fun _ : Unit ↦ P) g.toRingHom :=
    ⟨fun _ ↦ hg.inverts PUnit.unit,fun T _ f hf ↦ hg.desc T f (fun _ ↦ hf ())⟩
  exact FieldExtension.infinite_localization_of_infinite_extended_stable_chart k F P g hu hP
    (h P B g hu)

/-- The right-module universal localization equivalence of Theorem A′. -/
theorem isEFinite_iff_rightUniversalLocalizationsFinite :
    IsEFinite Rᵐᵒᵖ ↔ RightUniversalLocalizationsFinite k R := by
  refine ⟨rightUniversalLocalizationsFinite_of_isEFinite k, fun h ↦ ?_⟩
  apply (isEFinite_iff_singleton_localizations_finite k).2
  exact fun P _ _ _ g hg ↦ finite_right_singleton_localization k h P g hg

end EFiniteCharacterizations
