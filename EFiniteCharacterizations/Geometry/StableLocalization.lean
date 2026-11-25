module

public import EFiniteCharacterizations.LinearAlgebra.SimpleModuleDensity
public import EFiniteCharacterizations.Geometry.InversionCover
public import EFiniteCharacterizations.Stability.StableDeterminant
public import EFiniteCharacterizations.RingEpimorphisms.LocalizationCharts

/-! # The universal localization criterion over an algebraically closed field -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] [IsAlgClosed k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

/-- A missing integral class over an algebraically closed field produces one
projective differential with infinitely many stable inverting classes. -/
theorem exists_infinite_fixed_class_chart_of_not_isEFinite [IsNoetherianRing R] (h : ¬ IsEFinite R) :
    ∃ (P : TwoTerm R) (θ : Weight (FGModuleCat.{u} R)) (c : GrothendieckGroup (FGModuleCat.{u} R)), (P.stableInvertingClasses k ∩ stableClassesOfClass θ c).Infinite := by
  classical
  let := IsArtinianRing.of_finite k R
  obtain ⟨c,g,hc⟩ := exists_infinite_stableClassesOfClass_at_projectiveWeight_of_not_isEFinite k h
  obtain ⟨P,hg⟩ := g.exists_twoTerm
  let J := Σ t : ℕ, (0 < t) ×' (Fin t → Fin t → (P.source ⟶ P.target))
  let Q (j : J) := P.blockDifferentialOnCopies j.2.2
  have hw : projectiveClassWeight k g = P.eulerWeight k := hg ▸ P.projectiveClassWeight_eq_eulerWeight k
  obtain ⟨j,hj⟩ := exists_infinite_fixed_class_chart_of_pointwise_inversion k _ c hc Q
    (fun j M hM ↦ by
      rw [← (Q j).projectiveClassWeight_eq_eulerWeight k]
      change (projectiveClassWeight k (P.blockDifferentialOnCopies j.2.2).projectiveClass).IsStable M
      rw [TwoTerm.projectiveClass_blockDifferentialOnCopies,map_nsmul,hg]
      exact (stable_nsmul_iff _ M j.2.1).2 hM)
    (fun M _ hM ↦ by
      let n := (homFinrank k P.target M)^2
      obtain ⟨p,hp⟩ := P.exists_inverting_power_of_stable k M (hw ▸ hM) (n+1) (Nat.lt_succ_self n)
      exact ⟨⟨n+1,Nat.succ_pos _,p⟩,hp⟩)
  exact ⟨Q j,_,c,hj⟩

theorem exists_infinite_stable_chart_of_not_isEFinite [IsNoetherianRing R] (h : ¬ IsEFinite R) :
    ∃ P : TwoTerm R, (P.stableInvertingClasses k).Infinite := by
  obtain ⟨P,_,_,hP⟩ := exists_infinite_fixed_class_chart_of_not_isEFinite k h
  exact ⟨P,hP.mono Set.inter_subset_left⟩

/-- A single projective differential inverts two stable nonisomorphic
modules with identical Grothendieck class. -/
theorem exists_stable_inverting_pair [IsNoetherianRing R] (h : ¬ IsEFinite R) :
    ∃ (P : TwoTerm R) (X Y : FGModuleCat.{u} R),
      GrothendieckGroup.of X = GrothendieckGroup.of Y ∧ toSkeleton X ≠ toSkeleton Y ∧
      (P.eulerWeight k).IsStable X ∧ P.InvertedOn X.obj ∧
      (P.eulerWeight k).IsStable Y ∧ P.InvertedOn Y.obj := by
  obtain ⟨P,θ,c,hP⟩ := exists_infinite_fixed_class_chart_of_not_isEFinite k h
  obtain ⟨a,ha,b,hb,hab⟩ := hP.nontrivial
  obtain ⟨X,hX,hsX,hiX⟩ := ha.1
  obtain ⟨Y,hY,hsY,hiY⟩ := hb.1
  have hc {M : FGModuleCat.{u} R} (hm : toSkeleton M ∈ stableClassesOfClass θ c) :
      GrothendieckGroup.of M = c := by
    obtain ⟨N,hN,he,_⟩ := hm
    obtain ⟨f⟩ := toSkeleton_eq_toSkeleton_iff.1 hN.symm
    exact (GrothendieckGroup.of_eq_of_iso f).trans he
  exact ⟨P,X,Y,(hc (hX.symm ▸ ha.2)).trans (hc (hY.symm ▸ hb.2)).symm,
    hX.symm ▸ hY.symm ▸ hab,hsX,hiX,hsY,hiY⟩

/-- Compatible actions of a common universal localization on two distinct
stable modules are separated by a trace. -/
theorem exists_separating_localized_actions [IsNoetherianRing R]
    (P : TwoTerm R) {B : Type u} [Ring B] [Algebra k B] (g : R →ₐ[k] B)
    (hg : IsUniversalLocalization (fun _ : Unit ↦ P) g.toRingHom)
    (X Y : FGModuleCat.{u} R) (hne : toSkeleton X ≠ toSkeleton Y)
    (hsX : (P.eulerWeight k).IsStable X) (hiX : P.InvertedOn X.obj)
    (hsY : (P.eulerWeight k).IsStable Y) (hiY : P.InvertedOn Y.obj) :
    ∃ (mX : Module B X) (mY : Module B Y), letI := mX; letI := mY
      ∃ (_ : IsScalarTower k B X) (_ : IsScalarTower k B Y),
        (∀ r (x : X), g r • x = r • x) ∧ (∀ r (y : Y), g r • y = r • y) ∧
        ∃ z : B, LinearMap.trace k X (Algebra.lsmul k k X z) = 1 ∧
          LinearMap.trace k Y (Algebra.lsmul k k Y z) = 0 := by
  obtain ⟨mX,sX,tX,hX⟩ := hg.exists_simple_action k P g X hsX hiX
  obtain ⟨mY,sY,tY,hY⟩ := hg.exists_simple_action k P g Y hsY hiY
  let := mX
  let := mY
  let := sX
  let := sY
  let := tX
  let := tY
  let : Module.Finite k X := Module.Finite.trans R _
  let : Module.Finite k Y := Module.Finite.trans R _
  refine ⟨mX,mY,tX,tY,hX,hY,exists_distinct_simple_traces ⟨fun f ↦ ?_⟩⟩
  let l : X ≃ₗ[R] Y :=
    { f.toAddEquiv with
      map_smul' := fun r x ↦ by
        change f (r • x) = r • f x
        rw [← hX,← hY,f.map_smul] }
  exact hne (congr_toSkeleton_of_iso l.toFGModuleCatIso)

/-- The right-module universal localization equivalence of Theorem A. -/
theorem isEFinite_iff_rightUniversalLocalizationsFinite_of_isAlgClosed :
    IsEFinite Rᵐᵒᵖ ↔ RightUniversalLocalizationsFinite k R := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  refine ⟨rightUniversalLocalizationsFinite_of_isEFinite k,fun h ↦ ?_⟩
  by_contra hn
  obtain ⟨P,hP⟩ := exists_infinite_stable_chart_of_not_isEFinite k hn
  exact hP (finite_right_stable_charts_of_finite_localizations k h P)

end EFiniteCharacterizations
