module

public import EFiniteCharacterizations.Stability.CommonStableWeight
public import EFiniteCharacterizations.Modules.CompositionFactors
public import Mathlib.Data.Set.Card

/-! # Semibricks from common stability -/

@[expose] public section

open CategoryTheory

universe u v

namespace EFiniteCharacterizations

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The set of brick isomorphism classes. -/
def brickClasses : Set (Skeleton C) := {x | IsBrick ((fromSkeleton C).obj x)}

/-- A set of brick isomorphism classes with zero Hom between distinct classes. -/
def IsSemibrick (s : Set (Skeleton C)) : Prop :=
  s ⊆ brickClasses ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ f : (fromSkeleton C).obj x ⟶ (fromSkeleton C).obj y, f = 0

theorem IsSemibrick.subset {s t : Set (Skeleton C)} (ht : IsSemibrick t) (hs : s ⊆ t) :
    IsSemibrick s :=
  ⟨fun _ hx ↦ ht.1 (hs hx), fun x hx y hy ↦ ht.2 x (hs hx) y (hs hy)⟩

/-- All isomorphism classes that are stable for a given weight. -/
def stableClasses (θ : Weight C) : Set (Skeleton C) :=
  {x | θ.IsStable ((fromSkeleton C).obj x)}

theorem isSemibrick_stableClasses (θ : Weight C) : IsSemibrick (stableClasses θ) := by
  refine ⟨fun _ hx ↦ hx.isBrick, ?_⟩
  rintro x hx y hy hxy f
  refine Weight.hom_eq_zero_of_not_iso hx hy ?_ f
  rintro ⟨e⟩
  exact hxy ((toSkeleton_fromSkeleton_obj x).symm.trans
    ((congr_toSkeleton_of_iso e).trans (toSkeleton_fromSkeleton_obj y)))

end Abelian

variable {R : Type u} [Ring R] [IsNoetherianRing R]

theorem stableClasses_zero : stableClasses (0 : Weight (FGModuleCat.{u} R)) = simpleIsomorphismClasses R := by
  ext x
  constructor
  · intro hx
    exact ⟨_, toSkeleton_fromSkeleton_obj x, (Weight.isStable_zero_iff_simple _).mp hx⟩
  · rintro ⟨M, hM, hsimple⟩
    obtain ⟨e⟩ := toSkeleton_eq_iff.mp hM
    exact ((Weight.isStable_zero_iff_simple M).mpr hsimple).of_iso e

theorem isSemibrick_simpleIsomorphismClasses : IsSemibrick (simpleIsomorphismClasses R) := by
  rw [← stableClasses_zero]
  exact isSemibrick_stableClasses 0

variable (k : Type u) [Field k] [Algebra k R]

theorem stableClassesOfDimension_subset (θ : Weight (FGModuleCat.{u} R)) (d : ℕ) :
    stableClassesOfDimension k θ d ⊆ stableClasses θ := by
  rintro x ⟨M, hM, _, hstable⟩
  obtain ⟨e⟩ := toSkeleton_eq_iff.mp hM
  exact hstable.of_iso e

variable [Infinite k] [Module.Finite k R] [IsArtinianRing R]

include k in
/-- A missing integral presilting class gives an infinite semibrick. -/
theorem exists_infinite_semibrick_of_not_isEFinite (h : ¬ IsEFinite R) :
    ∃ s : Set (Skeleton (FGModuleCat.{u} R)), IsSemibrick s ∧ s.Infinite := by
  obtain ⟨d, θ, hθ⟩ := exists_infinite_stableClassesOfDimension_of_not_isEFinite k h
  exact ⟨stableClasses θ, isSemibrick_stableClasses θ,
    hθ.mono (stableClassesOfDimension_subset k θ d)⟩

include k in
theorem isEFinite_of_finite_semibricks
    (h : ∀ s : Set (Skeleton (FGModuleCat.{u} R)), IsSemibrick s → s.Finite) : IsEFinite R := by
  by_contra h'
  obtain ⟨s, hs, hi⟩ := exists_infinite_semibrick_of_not_isEFinite k h'
  exact hi (h s hs)

include k in
theorem isEFinite_of_finite_brickClasses
    (h : (brickClasses (C := FGModuleCat.{u} R)).Finite) : IsEFinite R :=
  isEFinite_of_finite_semibricks k (fun _ hs ↦ h.subset hs.1)

omit [Infinite k] [IsArtinianRing R] in
include k in
theorem finite_semibricks_of_unique_fullSize_semibrick
    (h : ∀ t : Set (Skeleton (FGModuleCat.{u} R)), IsSemibrick t → t.Finite →
      t.ncard = (simpleIsomorphismClasses R).ncard → t = simpleIsomorphismClasses R)
    (s : Set (Skeleton (FGModuleCat.{u} R))) (hs : IsSemibrick s) : s.Finite := by
  by_contra hi
  change s.Infinite at hi
  have hfin : (simpleIsomorphismClasses R).Finite := finite_simpleIsomorphismClasses k
  have hsimp : (simpleIsomorphismClasses R).Nonempty := by
    obtain ⟨x, hx⟩ := hi.nonempty
    exact simpleIsomorphismClasses_nonempty_of_not_isZero k (hs.1 hx).1
  obtain ⟨t, hts, htcard⟩ := (hi.sdiff hfin).exists_subset_card_eq (simpleIsomorphismClasses R).ncard
  have ht := h t (hs.subset (fun _ hx ↦ (hts hx).1)) t.finite_toSet
    (by simpa using htcard)
  obtain ⟨x, hx⟩ := hsimp
  have hxt : x ∈ (t : Set (Skeleton (FGModuleCat.{u} R))) := ht ▸ hx
  exact (hts hxt).2 hx

include k in
/-- Uniqueness of the semibrick of size equal to the number of simple modules
implies E-finiteness over an infinite field. -/
theorem isEFinite_of_unique_fullSize_semibrick
    (h : ∀ s : Set (Skeleton (FGModuleCat.{u} R)), IsSemibrick s → s.Finite →
      s.ncard = (simpleIsomorphismClasses R).ncard → s = simpleIsomorphismClasses R) : IsEFinite R := by
  exact isEFinite_of_finite_semibricks k (finite_semibricks_of_unique_fullSize_semibrick k h)

end EFiniteCharacterizations
