module

public import EFiniteCharacterizations.Silting.Reduction.PerpendicularGenerator
public import EFiniteCharacterizations.Stability.Semibricks

/-! # Finiteness of the stable classes at covered weights -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

/-- Stable isomorphism classes receiving a nonzero map from a fixed module. -/
def stableQuotientClasses (θ : Weight (FGModuleCat.{u} R)) (M : FGModuleCat.{u} R) :
    Set (Skeleton (FGModuleCat.{u} R)) :=
  {x | θ.IsStable ((fromSkeleton _).obj x) ∧ ∃ f : M ⟶ (fromSkeleton _).obj x, f ≠ 0}

include k in
/-- A semistable module has at most its ground dimension many stable quotients
up to isomorphism. -/
theorem finite_and_ncard_stableQuotientClasses (θ : Weight (FGModuleCat.{u} R)) (M : FGModuleCat.{u} R)
    (hM : θ.IsSemistable M) :
    (stableQuotientClasses θ M).Finite ∧
      (stableQuotientClasses θ M).ncard ≤ Module.finrank k (M.obj : Type u) := by
  classical
  generalize hn : Module.finrank k (M.obj : Type u) = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hnon : (stableQuotientClasses θ M).Nonempty
    · obtain ⟨x, hx, f, hf⟩ := hnon
      let Z := (fromSkeleton _).obj x
      have hZ : θ.IsStable Z := hx
      let _ := Weight.epi_of_isSemistable_of_isStable hM hZ f hf
      have hk := hM.kernel_of_epi hZ.isSemistable f
      let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel f)
        (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
      have hd := (dimensionWeight (R := R) k).eval_shortExact S hS
      change (dimensionWeight (R := R) k).eval M =
        (dimensionWeight (R := R) k).eval (kernel f) + (dimensionWeight (R := R) k).eval Z at hd
      have hpos := dimensionWeight_pos k Z hZ.1
      rw [dimensionWeight_eval, dimensionWeight_eval, dimensionWeight_eval, hn] at hd
      rw [dimensionWeight_eval, Int.natCast_pos] at hpos
      have hlt : Module.finrank k ((kernel f).obj : Type u) < n := by omega
      have hsub : stableQuotientClasses θ M ⊆ insert x (stableQuotientClasses θ (kernel f)) := by
        rintro y ⟨hy, g, hg⟩
        by_cases hxy : x = y
        · exact Or.inl hxy.symm
        · refine Or.inr ⟨hy, kernel.ι f ≫ g, ?_⟩
          intro hz
          let a := Abelian.epiDesc f g hz
          have ha : f ≫ a = g := Abelian.comp_epiDesc f g hz
          have hna : a ≠ 0 := by
            intro he
            apply hg
            rw [← ha, he, comp_zero]
          let _ := Weight.isIso_of_nonzero hZ hy a hna
          exact hxy ((toSkeleton_fromSkeleton_obj x).symm.trans
            ((congr_toSkeleton_of_iso (asIso a)).trans (toSkeleton_fromSkeleton_obj y)))
      obtain ⟨hfin, hcard⟩ := ih _ hlt (kernel f) hk rfl
      refine ⟨(hfin.insert x).subset hsub, (Set.ncard_le_ncard hsub (hfin.insert x)).trans ?_⟩
      exact (Set.ncard_insert_le _ _).trans (by omega)
    · simp [Set.not_nonempty_iff_eq_empty.mp hnon]

include k in
/-- The stable quotients of a semistable module form a finite set of isomorphism classes. -/
theorem finite_stableQuotientClasses (θ : Weight (FGModuleCat.{u} R)) (M : FGModuleCat.{u} R)
    (hM : θ.IsSemistable M) : (stableQuotientClasses θ M).Finite :=
  (finite_and_ncard_stableQuotientClasses k θ M hM).1

/-- The stable classes of a covered weight are finite. -/
theorem TwoTerm.finite_stableClasses_eulerWeight (P : TwoTerm R) (hP : P.IsPresilting) :
    (stableClasses (P.eulerWeight k)).Finite := by
  obtain ⟨G, hG, hgen, _⟩ := P.exists_semistable_projective_generator k hP
  apply (finite_stableQuotientClasses k (P.eulerWeight k) G hG).subset
  intro x hx
  exact ⟨hx, (hgen _ hx.isSemistable).exists_nonzero_hom hx.1⟩

/-- Finiteness of the stable classes at every integral projective weight. -/
def StableFiniteAtAllIntegralWeights : Prop :=
  ∀ g : ProjectiveClass R, (stableClasses (projectiveClassWeight (R := R) k g)).Finite

/-- The forward semistable-finiteness implication over any field. -/
theorem stableFiniteAtAllIntegralWeights_of_isEFinite (h : IsEFinite R) :
    StableFiniteAtAllIntegralWeights (R := R) k := by
  intro g
  obtain ⟨P, hP, hg⟩ := h g
  rw [← hg, P.projectiveClassWeight_eq_eulerWeight k]
  exact P.finite_stableClasses_eulerWeight k hP

variable [Infinite k] [IsArtinianRing R]

/-- Over an infinite field, finiteness at all integral weights is equivalent to E-finiteness. -/
theorem isEFinite_iff_stableFiniteAtAllIntegralWeights :
    IsEFinite R ↔ StableFiniteAtAllIntegralWeights (R := R) k := by
  refine ⟨stableFiniteAtAllIntegralWeights_of_isEFinite k, fun h ↦ ?_⟩
  by_contra hn
  obtain ⟨d, g, hg⟩ := exists_infinite_stableClassesOfDimension_at_projectiveWeight_of_not_isEFinite k hn
  exact hg ((h g).subset (stableClassesOfDimension_subset k _ d))

end EFiniteCharacterizations
