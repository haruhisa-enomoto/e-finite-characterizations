module

public import EFiniteCharacterizations.ScalarExtension.FiniteFieldGrowth
public import EFiniteCharacterizations.Stability.CommonStableClass
public import EFiniteCharacterizations.Subcategories.TorsionPairs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import EFiniteCharacterizations.Stability.StableFiniteness

/-! # Consequences of a missing class over an arbitrary ground field -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

/-- Failure of E-finiteness over any field yields infinitely many stable
classes at one integral weight and one positive endolength. -/
theorem exists_infinite_stableClassesOfEndolength_allFields (h : ¬ IsEFinite R) :
    ∃ (g : ProjectiveClass R) (r : ℕ), 0 < r ∧
      (stableClassesOfEndolength k (projectiveClassWeight k g) r).Infinite := by
  rcases finite_or_infinite k with hfin | hinf
  · exact FieldExtension.exists_infinite_stableClassesOfEndolength_of_not_isEFinite k h
  · exact exists_infinite_stableClassesOfEndolength_at_projectiveWeight_of_not_isEFinite k h

/-- Finiteness of the stable classes at every integral weight characterizes
E-finiteness over every field. -/
theorem isEFinite_iff_stableFiniteAtAllIntegralWeights_allFields :
    IsEFinite R ↔ StableFiniteAtAllIntegralWeights (R := R) k := by
  refine ⟨stableFiniteAtAllIntegralWeights_of_isEFinite k, fun h ↦ ?_⟩
  by_contra hn
  obtain ⟨g, r, _, hs⟩ := exists_infinite_stableClassesOfEndolength_allFields k hn
  exact hs ((h g).subset (stableClassesOfEndolength_subset_stableClasses k _ r))

theorem isEFinite_of_finite_stableClassesOfEndolength_allFields
    (h : ∀ (g : ProjectiveClass R) (r : ℕ), 0 < r →
      (stableClassesOfEndolength k (projectiveClassWeight k g) r).Finite) : IsEFinite R := by
  by_contra hn
  obtain ⟨g, r, hr, hs⟩ := exists_infinite_stableClassesOfEndolength_allFields k hn
  exact hs (h g r hr)

/-- Stable-brick discreteness at fixed integral weight and positive
endolength characterizes E-finiteness over every field. -/
theorem isEFinite_iff_endo_stab :
    IsEFinite R ↔ ∀ (g : ProjectiveClass R) (r : ℕ), 0 < r →
      (stableClassesOfEndolength k (projectiveClassWeight k g) r).Finite :=
  ⟨fun h g r _ ↦ ((stableFiniteAtAllIntegralWeights_of_isEFinite k h) g).subset
      (stableClassesOfEndolength_subset_stableClasses k _ r),
    isEFinite_of_finite_stableClassesOfEndolength_allFields k⟩

theorem isEFinite_of_finite_brickClassesOfEndolength_allFields
    (h : ∀ r : ℕ, 0 < r → (brickClassesOfEndolength (R := R) k r).Finite) : IsEFinite R :=
  isEFinite_of_finite_stableClassesOfEndolength_allFields k (fun g r hr ↦
    (h r hr).subset (stableClassesOfEndolength_subset_brickClassesOfEndolength k (projectiveClassWeight k g) r))

include k in
/-- A missing projective class over any field forces an infinite semibrick. -/
theorem exists_infinite_semibrick_of_not_isEFinite_allFields (h : ¬ IsEFinite R) :
    ∃ s : Set (Skeleton (FGModuleCat.{u} R)), IsSemibrick s ∧ s.Infinite := by
  obtain ⟨g, r, _, hs⟩ := exists_infinite_stableClassesOfEndolength_allFields k h
  exact ⟨_, isSemibrick_stableClasses _, hs.mono (stableClassesOfEndolength_subset_stableClasses k _ r)⟩

include k in
theorem isEFinite_of_finite_semibricks_allFields
    (h : ∀ s : Set (Skeleton (FGModuleCat.{u} R)), IsSemibrick s → s.Finite) : IsEFinite R := by
  by_contra hn
  obtain ⟨s, hs, hi⟩ := exists_infinite_semibrick_of_not_isEFinite_allFields k hn
  exact hi (h s hs)

include k in
/-- Brick-finiteness implies E-finiteness in every rank over every field. -/
theorem isEFinite_of_finite_brickClasses_allFields
    (h : (brickClasses (C := FGModuleCat.{u} R)).Finite) : IsEFinite R :=
  isEFinite_of_finite_semibricks_allFields k (fun _ hs ↦ h.subset hs.1)

include k in
theorem isEFinite_of_unique_fullSize_semibrick_allFields
    (h : ∀ s : Set (Skeleton (FGModuleCat.{u} R)), IsSemibrick s → s.Finite →
      s.ncard = (simpleIsomorphismClasses R).ncard → s = simpleIsomorphismClasses R) : IsEFinite R :=
  isEFinite_of_finite_semibricks_allFields k (finite_semibricks_of_unique_fullSize_semibrick k h)

theorem exists_exp_gt_polynomial_bound (A n m₀ : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ m ≥ m₀, (A : ℝ) * ((m : ℝ) + 1) ^ n < Real.exp (c * m) := by
  let B : ℝ := (A + 1 : ℝ) * 2 ^ n
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.1
    ((isLittleO_pow_exp_pos_mul_atTop n hc).bound (inv_pos.mpr hB))
  obtain ⟨j, hj⟩ := exists_nat_gt r
  let m := max (max m₀ 1) j
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (le_max_right m₀ 1).trans (le_max_left _ j)
  have hb := hr (m : ℝ) (hj.le.trans (by exact_mod_cast le_max_right (max m₀ 1) j))
  simp only [Real.norm_eq_abs, abs_pow, abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
    abs_of_pos (Real.exp_pos _)] at hb
  have he : B * (m : ℝ) ^ n ≤ Real.exp (c * m) := by
    calc
      _ ≤ B * (B⁻¹ * Real.exp (c * m)) := mul_le_mul_of_nonneg_left hb hB.le
      _ = Real.exp (c * m) := by rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
  refine ⟨m, (le_max_left m₀ 1).trans (le_max_left _ j), lt_of_lt_of_le ?_ he⟩
  calc
    _ < ((A : ℝ) + 1) * ((m : ℝ) + 1) ^ n := by gcongr; linarith
    _ ≤ ((A : ℝ) + 1) * (2 * (m : ℝ)) ^ n := by gcongr; linarith
    _ = _ := by simp [B, mul_pow, mul_assoc]

omit [IsArtinianRing R] in
/-- Over a finite field, a missing projective class gives two distinct
stable modules of equal ambient class at the same integral weight. -/
theorem exists_equalClass_stable_pair_of_not_isEFinite [Finite k] (hn : ¬ IsEFinite R) :
    ∃ (g : ProjectiveClass R) (X Y : FGModuleCat.{u} R),
      (projectiveClassWeight k g).IsStable X ∧ (projectiveClassWeight k g).IsStable Y ∧
      ¬ Nonempty (X ≅ Y) ∧ GrothendieckGroup.of X = GrothendieckGroup.of Y := by
  classical
  obtain ⟨P, hp⟩ := FieldExtension.exists_missing_terms k hn
  obtain ⟨G, c, m₀, hc, hg⟩ := FieldExtension.exists_exponential_ground_witnesses k P hp
  obtain ⟨m, hm, hex⟩ := exists_exp_gt_polynomial_bound G.card (simpleIsomorphismClasses R).ncard m₀ hc
  obtain ⟨S, hSc, hS⟩ := exists_bounded_class_cover (R := R) k m
  obtain ⟨s, hs, hw⟩ := hg m hm
  choose M g he hG hst hd _ using fun x : s ↦ hw x.val x.property
  let f (x : s) : ↥G × ↥S := (⟨g x, hG x⟩, ⟨_, hS (M x) (hd x)⟩)
  have hf : ¬ Function.Injective f := by
    intro hi
    have hcard : s.card ≤ G.card * S.card := by simpa using Fintype.card_le_of_injective f hi
    have hupper := hcard.trans (Nat.mul_le_mul_left _ hSc)
    exact (not_lt_of_ge (hs.trans (by exact_mod_cast hupper))) hex
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hf
  have hg' : g x = g y := congrArg (fun z : ↥G × ↥S ↦ z.1.val) hxy
  refine ⟨g x, M x, M y, hst x, hg'.symm ▸ hst y, ?_,
    congrArg (fun z : ↥G × ↥S ↦ z.2.val) hxy⟩
  rintro ⟨e⟩
  exact hne (Subtype.ext ((he x).symm.trans ((congr_toSkeleton_of_iso e).trans (he y))))

include k in
theorem exists_equalClass_stable_pair_allFields (hn : ¬ IsEFinite R) :
    ∃ (g : ProjectiveClass R) (X Y : FGModuleCat.{u} R),
      (projectiveClassWeight k g).IsStable X ∧ (projectiveClassWeight k g).IsStable Y ∧
      ¬ Nonempty (X ≅ Y) ∧ GrothendieckGroup.of X = GrothendieckGroup.of Y := by
  rcases finite_or_infinite k with hfin | hinf
  · exact exists_equalClass_stable_pair_of_not_isEFinite k hn
  obtain ⟨c,g,hi⟩ := exists_infinite_stableClassesOfClass_at_projectiveWeight_of_not_isEFinite k hn
  obtain ⟨x,hx⟩ := hi.nonempty
  obtain ⟨y,hy,hyx⟩ := hi.exists_notMem_finite (Set.finite_singleton x)
  obtain ⟨X,ex,hcX,hsX⟩ := hx
  obtain ⟨Y,ey,hcY,hsY⟩ := hy
  exact ⟨g,X,Y,hsX,hsY,fun ⟨e⟩ ↦ hyx (Set.mem_singleton_iff.mpr
    (ey.symm.trans ((congr_toSkeleton_of_iso e).symm.trans ex))),hcX.trans hcY.symm⟩

include k in
theorem isEFinite_of_equalClassBrickHom_allFields
    (h : EqualClassBrickHom (FGModuleCat.{u} R)) : IsEFinite R := by
  by_contra hn
  obtain ⟨_, _, _, hX, hY, hne, hcl⟩ := exists_equalClass_stable_pair_allFields k hn
  exact Weight.not_equalClassBrickHom hX hY hne hcl h

include k in
theorem isEFinite_of_equalClassHom_allFields
    (h : EqualClassHom (FGModuleCat.{u} R)) : IsEFinite R :=
  isEFinite_of_equalClassBrickHom_allFields k (equalClassBrickHom_of_equalClassHom h)

include k in
theorem isEFinite_of_numericallyDisjointTorsionPairs
    (h : NumericallyDisjointTorsionPairs (FGModuleCat.{u} R)) : IsEFinite R :=
  isEFinite_of_equalClassHom_allFields k (equalClassHom_of_numericallyDisjointTorsionPairs h)

end EFiniteCharacterizations
