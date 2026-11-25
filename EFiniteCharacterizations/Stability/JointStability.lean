module

public import EFiniteCharacterizations.Stability.Semibricks
public import EFiniteCharacterizations.Presentations.ProjectiveClassSeparation
public import EFiniteCharacterizations.LinearAlgebra.IntegralSeparation

/-! # Finite subobject inequalities for joint stability -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v

namespace EFiniteCharacterizations

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Ambient classes of nonzero proper subobjects of one object. -/
def properSubobjectClasses (B : C) : Set (GrothendieckGroup C) :=
  {c | ∃ (U : C) (i : U ⟶ B), Mono i ∧ ¬ IsZero U ∧ ¬ IsIso i ∧ GrothendieckGroup.of U = c}

theorem IsSemibrick.hom_to_proper_subobject {s : Set (Skeleton C)} (hs : IsSemibrick s)
    {x y : Skeleton C} (hx : x ∈ s) (hy : y ∈ s) {U : C} (i : U ⟶ (fromSkeleton C).obj y)
    [Mono i] (hi : ¬ IsIso i) (f : (fromSkeleton C).obj x ⟶ U) : f = 0 := by
  by_contra hf
  have hfi : f ≫ i ≠ 0 := fun h ↦ hf ((cancel_mono i).mp (by simpa using h))
  by_cases he : x = y
  · subst y
    have := (hs.1 hx).2 (f ≫ i) hfi
    have := epi_of_epi f i
    exact hi (isIso_of_mono_of_epi i)
  · exact hfi (hs.2 x hx y hy he _)

theorem joint_stability_iff_subobject_inequalities {s : Set (Skeleton C)} (hs : IsSemibrick s)
    (θ : Weight C) :
    s ⊆ stableClasses θ ↔
      (∀ x ∈ s, θ.eval ((fromSkeleton C).obj x) = 0) ∧
      ∀ c ∈ ⋃ x ∈ s, properSubobjectClasses ((fromSkeleton C).obj x), θ c < 0 := by
  constructor
  · intro h
    refine ⟨fun _ hx ↦ (h hx).2.1, ?_⟩
    intro c hc
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hc
    obtain ⟨hm, U, i, hi, hn, hp, rfl⟩ := Set.mem_iUnion.mp hx
    exact (h hm).2.2 i hn hp
  · rintro ⟨hz, hneg⟩ x hx
    refine ⟨(hs.1 hx).1, hz x hx, fun {U} i hi hn hp ↦ ?_⟩
    exact hneg _ (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, U, i, hi, hn, hp, rfl⟩⟩)

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

include k in
theorem finite_properSubobjectClasses (B : FGModuleCat.{u} R) : (properSubobjectClasses B).Finite := by
  have : Module.Finite k (B.obj : Type u) := Module.Finite.trans R _
  apply (finite_classes_of_groundFinrank_le (R := R) k (Module.finrank k (B.obj : Type u))).subset
  rintro c ⟨U, i, hi, _, _, rfl⟩
  exact ⟨U, LinearMap.finrank_le_finrank_of_injective (f := i.hom.hom.restrictScalars k)
    ((FGModuleCat.mono_iff_injective i).1 hi), rfl⟩

include k in
theorem finite_joint_subobject_classes {s : Set (Skeleton (FGModuleCat.{u} R))} (hs : s.Finite) :
    (⋃ x ∈ s, properSubobjectClasses ((fromSkeleton (FGModuleCat.{u} R)).obj x)).Finite :=
  hs.biUnion fun _ _ ↦ finite_properSubobjectClasses k _

/-- For a finite semibrick, either all members are stable at one integral
projective weight, or proper subobject classes give a nonnegative,
nontrivial integral relation modulo the member classes. -/
theorem joint_projective_stability_or_relation_on (s : Finset (Skeleton (FGModuleCat.{u} R)))
    (hs : IsSemibrick (C := FGModuleCat.{u} R) ↑s)
    (t : Finset (Skeleton (FGModuleCat.{u} R)))
    (hspan : ∀ w : Weight (FGModuleCat.{u} R),
      (∀ x ∈ t, w.eval ((fromSkeleton _).obj x) = 0) → ∀ x ∈ s, w.eval ((fromSkeleton _).obj x) = 0) :
    let U := ⋃ x ∈ (s : Set _), properSubobjectClasses ((fromSkeleton (FGModuleCat.{u} R)).obj x)
    letI : Fintype U := (finite_joint_subobject_classes k s.finite_toSet).fintype
    (∃ g : ProjectiveClass R, (s : Set _) ⊆ stableClasses (C := FGModuleCat.{u} R) (projectiveClassWeight k g)) ∨
    ∃ (a : U → ℤ) (c : t → ℤ), (∀ j, 0 ≤ a j) ∧ (∃ j, 0 < a j) ∧
      (∑ j : U, a j • j.val) =
      ∑ i : t, c i • GrothendieckGroup.of ((fromSkeleton (FGModuleCat.{u} R)).obj i.val) := by
  classical
  let U := ⋃ x ∈ (s : Set _), properSubobjectClasses ((fromSkeleton (FGModuleCat.{u} R)).obj x)
  let hu : U.Finite := finite_joint_subobject_classes k s.finite_toSet
  let := hu.fintype
  obtain ⟨n, g, hg⟩ := exists_injective_projective_weight_coordinates (R := R) k
  rcases Farkas.integral_separation_of_injective_coordinates (fun t ↦ projectiveClassWeight k (g t)) hg
      (fun i : t ↦ GrothendieckGroup.of ((fromSkeleton (FGModuleCat.{u} R)).obj i.val)) (fun j : U ↦ j.val) with
      ⟨w, hw, hneg⟩ | ⟨a, c, ha, hp, he⟩
  · left
    refine ⟨∑ t, w t • g t, (joint_stability_iff_subobject_inequalities hs _).2 ?_⟩
    simp only [map_sum, map_zsmul]
    exact ⟨hspan _ (fun x hx ↦ hw ⟨x, hx⟩), fun x hx ↦ hneg ⟨x, hx⟩⟩
  · right
    refine ⟨a, c, ha, ?_, ?_⟩
    · by_contra! h
      exact hp.not_ge (Finset.sum_nonpos fun i _ ↦ h i)
    · exact he

/-- For a finite semibrick, either all members are stable at one integral
projective weight, or proper subobject classes give a nonnegative,
nontrivial integral relation modulo the member classes. -/
theorem joint_projective_stability_or_relation (s : Finset (Skeleton (FGModuleCat.{u} R)))
    (hs : IsSemibrick (C := FGModuleCat.{u} R) ↑s) :
    let U := ⋃ x ∈ (s : Set _), properSubobjectClasses ((fromSkeleton (FGModuleCat.{u} R)).obj x)
    letI : Fintype U := (finite_joint_subobject_classes k s.finite_toSet).fintype
    (∃ g : ProjectiveClass R, (s : Set _) ⊆ stableClasses (C := FGModuleCat.{u} R) (projectiveClassWeight k g)) ∨
    ∃ (a : U → ℤ) (c : s → ℤ), (∀ j, 0 ≤ a j) ∧ (∃ j, 0 < a j) ∧
      (∑ j : U, a j • j.val) =
      ∑ i : s, c i • GrothendieckGroup.of ((fromSkeleton (FGModuleCat.{u} R)).obj i.val) := by
  exact joint_projective_stability_or_relation_on k s hs s (fun _ h ↦ h)

end EFiniteCharacterizations
