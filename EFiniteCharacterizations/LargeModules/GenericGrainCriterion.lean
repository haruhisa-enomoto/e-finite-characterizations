module

public import EFiniteCharacterizations.DivisionRings.FreeGroupBiorder
public import EFiniteCharacterizations.DivisionRings.OrderedGroupSeries
public import EFiniteCharacterizations.Stability.FiniteCogeneratorWeights
public import EFiniteCharacterizations.LargeModules.GenericBrickExclusion

/-!
# Generic grains at missing integral weights

Proposition 7.6 (`prop:grain`) and the `(E-fin) ⇔ (no-gen-grain)` equivalence of
Theorem 7.8 (`isEFinite_iff_no_genericGrain`). Whereas the manuscript constructs
generic grains over Cohn's universal skew field, Lean constructs the required
division ring self-containedly from Malcev–Neumann well-ordered power series on a
bi-ordered finitely generated free group (`DivisionRings/`), producing an endofinite
module `N` realizing the numerical torsion pair at a missing weight whose
indecomposable summands include a generic grain (`exists_weight_with_generic_grain_kernel`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations

/-- Division coefficients with an injective free tensor boundary exist in every characteristic. -/
theorem exists_division_injective_boundary (k ι : Type u) [Field k] [Fintype ι] :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra k D) (a : ι → D),
      Function.Injective (freeTensorBoundary k a) := by
  obtain ⟨o,hl,hr⟩ := FreeGroupBiorder.exists_biorder ι
  exact @OrderedGroupSeries.exists_injective_boundary_of_biorder k ι _ _ o hl hr

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

/-- Every integral weight admits an endofinite module realizing both halves of its
numerical torsion pair and splitting extensions on the cogenerated class. -/
theorem exists_endofinite_kernel_for_weight [IsNoetherianRing R] [IsArtinianRing R]
    (γ : ProjectiveClass R) :
    ∃ N : ModuleCat.{u} R, IsEndofinite N ∧ SplitsOnCogeneratedModules k N ∧
      perpendicularToModule N = (projectiveClassWeight k γ).weakTorsionClass ∧
      cogeneratedByModule N = (fun X ↦ ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X) [Mono i],
        ¬ IsZero U → (projectiveClassWeight k γ).eval U < 0) := by
  apply exists_endofinite_kernel_of_commutators _ γ
  intro V _
  obtain ⟨D,_,_,a,ha⟩ := exists_division_injective_boundary k V
  exact ⟨D,inferInstance,inferInstance,a,simultaneous_commutators_of_injective_boundary k a ha⟩

/-- Some integral weight outside the presilting fan has a splitting endofinite kernel
with a generic grain as a direct summand. -/
theorem exists_weight_with_generic_grain_kernel [IsNoetherianRing R] [IsArtinianRing R]
    (hn : ¬ IsEFinite R) :
    ∃ γ : ProjectiveClass R, (¬ ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = γ) ∧
      ∃ N : ModuleCat.{u} R, IsEndofinite N ∧ SplitsOnCogeneratedModules k N ∧
        perpendicularToModule N = (projectiveClassWeight k γ).weakTorsionClass ∧
        cogeneratedByModule N = (fun X ↦ ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X) [Mono i],
          ¬ IsZero U → (projectiveClassWeight k γ).eval U < 0) ∧
        ∃ G : ModuleCat.{u} R, Nonempty (Retract G N) ∧ IsGenericGrain k G := by
  obtain ⟨γ,hγ,h⟩ := exists_weight_forcing_grain_retract k hn
  obtain ⟨N,he,hs,hp,hc⟩ := exists_endofinite_kernel_for_weight k γ
  exact ⟨γ,hγ,N,he,hs,hp,hc,h N he hs hc⟩

/-- E-finiteness is equivalent to absence of a generic grain over every field. -/
theorem isEFinite_iff_no_genericGrain :
    IsEFinite R ↔ ¬ ∃ N : ModuleCat.{u} R, IsGenericGrain k N := by
  let := IsNoetherianRing.of_finite k R
  let := IsArtinianRing.of_finite k R
  refine ⟨no_genericGrain_of_isEFinite k,fun h ↦ ?_⟩
  by_contra hn
  exact h (exists_generic_grain_of_injective_boundaries k (fun V _ ↦ exists_division_injective_boundary k V) hn)

end EFiniteCharacterizations
