module

public import EFiniteCharacterizations.LargeModules.GenericGrainCriterion
public import EFiniteCharacterizations.ScalarExtension.GeometricChamberDescent

/-! # Generic-grain summands at prescribed integral weights -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

omit [IsArtinianRing R] in
/-- A finite cogenerator for the weak numerical torsion pair makes its real weak
torsion class cocompact. -/
theorem realWeak_cocompact_of_finite_perpendicular (γ : ProjectiveClass R)
    (M : FGModuleCat.{u} R)
    (hm : (projectiveClassWeight k γ).weakTorsionClass = perpendicularToModule M.obj) :
    ∀ X, realWeakTorsion k (realProjectiveClass R γ) X ↔ Subsingleton (X ⟶ M) := by
  have h := (integral_classes_of_multiple k (n := 1) (g := γ) zero_lt_one (one_smul ℕ _)).2
  rw [← h,hm]
  intro X
  exact ⟨fun hx ↦ ⟨fun a b ↦ InducedCategory.hom_ext ((hx a.hom).trans (hx b.hom).symm)⟩,
    fun hs f ↦ congrArg InducedCategory.Hom.hom (hs.elim (InducedCategory.homMk f) 0)⟩

include k in
omit [IsArtinianRing R] in
/-- A differential is presilting if precomposition is surjective on a generator
of a torsion class and injective on a module cutting out that class. -/
theorem TwoTerm.isPresilting_of_torsion_pair_tests (P : TwoTerm R) (B M : FGModuleCat.{u} R)
    (pair : ∀ X, generatedTorsionClass B X ↔ Subsingleton (X ⟶ M))
    (surj : Function.Surjective (P.precompose B)) (inj : Function.Injective (P.precompose M)) :
    P.IsPresilting := by
  have C := (pair _).2 ((P.injective_precompose_iff_no_hom_cokernel k M).1 inj)
  have K := (P.surjective_precompose_iff_no_hom_nakayamaKernel k B).1 surj
  apply (P.isPresilting_iff_no_hom_nakayamaKernel k).2
  exact ⟨fun f g ↦ (C _ (fun a ↦ K.elim a 0) f).trans (C _ (fun a ↦ K.elim a 0) g).symm⟩

/-- At every prescribed weight outside the fan, the fixed-weight torsion criterion
implies the grain proposition with its two numerical classes and direct summand. -/
theorem exists_generic_grain_kernel_of_fixedWeightTorsionCriteria (γ : ProjectiveClass R)
    (hγ : ¬ ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = γ)
    (criterion : FixedWeightTorsionCriteria k (realProjectiveClass R γ)) :
    ∃ N : ModuleCat.{u} R, IsEndofinite N ∧ SplitsOnCogeneratedModules k N ∧
      perpendicularToModule N = (projectiveClassWeight k γ).weakTorsionClass ∧
      cogeneratedByModule N = (fun X ↦ ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X) [Mono i],
        ¬ IsZero U → (projectiveClassWeight k γ).eval U < 0) ∧
      ∃ G : ModuleCat.{u} R, Nonempty (Retract G N) ∧ IsGenericGrain k G := by
  obtain ⟨N,he,hs,hp,hc⟩ := exists_endofinite_kernel_for_weight k γ
  refine ⟨N,he,hs,hp,hc,(finite_cogenerator_or_grain_retract k he hs).resolve_left ?_⟩
  rintro ⟨M,hm,_⟩
  apply hγ
  apply (TwoTerm.mem_fanSupport_iff_exists_presilting k γ).1
  have cc : ∃ M : FGModuleCat.{u} R, ∀ X, realWeakTorsion k (realProjectiveClass R γ) X ↔
      Subsingleton (X ⟶ M) := ⟨M,realWeak_cocompact_of_finite_perpendicular k γ M (hp.symm.trans hm)⟩
  exact (criterion.out 6 1 (a := _) (b := _) rfl rfl).1 cc

end EFiniteCharacterizations
