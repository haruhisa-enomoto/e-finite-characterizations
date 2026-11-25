module

public import EFiniteCharacterizations.Modules.CompositionFactors
public import EFiniteCharacterizations.Stability.CommonStableWeight

/-! # Common Grothendieck classes in infinite stable families -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Isomorphism classes of bricks of a fixed ambient Grothendieck class. -/
def brickClassesOfClass (c : GrothendieckGroup (FGModuleCat.{u} R)) :
    Set (Skeleton (FGModuleCat.{u} R)) :=
  {x | ∃ M : FGModuleCat.{u} R, toSkeleton M = x ∧ GrothendieckGroup.of M = c ∧ IsBrick M}

/-- Isomorphism classes of modules of a fixed ambient Grothendieck class
which are stable for the given weight. -/
def stableClassesOfClass (θ : Weight (FGModuleCat.{u} R))
    (c : GrothendieckGroup (FGModuleCat.{u} R)) : Set (Skeleton (FGModuleCat.{u} R)) :=
  {x | ∃ M : FGModuleCat.{u} R, toSkeleton M = x ∧ GrothendieckGroup.of M = c ∧ θ.IsStable M}

theorem stableClassesOfClass_subset_brickClassesOfClass (θ : Weight (FGModuleCat.{u} R))
    (c : GrothendieckGroup (FGModuleCat.{u} R)) : stableClassesOfClass θ c ⊆ brickClassesOfClass c := by
  rintro x ⟨M, hM, hclass, hstable⟩
  exact ⟨M, hM, hclass, hstable.isBrick⟩

variable (k : Type u) [Field k] [Infinite k] [Algebra k R] [Module.Finite k R] [IsArtinianRing R]

omit [Infinite k] [IsArtinianRing R] in
theorem exists_infinite_stableClassesOfClass_of_infinite_dimension
    {θ : Weight (FGModuleCat.{u} R)} {d : ℕ} (hθ : (stableClassesOfDimension k θ d).Infinite) :
    ∃ c, (stableClassesOfClass θ c).Infinite := by
  classical
  let s := {c : GrothendieckGroup (FGModuleCat.{u} R) | ∃ M : FGModuleCat.{u} R,
    Module.finrank k (M.obj : Type u) ≤ d ∧ GrothendieckGroup.of M = c}
  have : Finite s := finite_classes_of_groundFinrank_le (R := R) k d
  have hsubset : stableClassesOfDimension k θ d ⊆ ⋃ c : s, stableClassesOfClass θ c.val := by
    rintro x ⟨M, hM, hdim, hstab⟩
    exact Set.mem_iUnion.mpr ⟨⟨GrothendieckGroup.of M, M, hdim.le, rfl⟩, M, hM, rfl, hstab⟩
  by_contra habs
  have hall (c : s) : (stableClassesOfClass θ c.val).Finite := by
    by_contra h'
    exact habs ⟨c.val, h'⟩
  exact hθ ((Set.finite_iUnion hall).subset hsubset)

include k in
/-- Over an infinite field, failure of integral presilting coverage gives an
infinite family stable at one weight and with one ambient Grothendieck class. -/
theorem exists_infinite_stableClassesOfClass_at_projectiveWeight_of_not_isEFinite (h : ¬ IsEFinite R) :
    ∃ (c : GrothendieckGroup (FGModuleCat.{u} R)) (g : ProjectiveClass R),
      (stableClassesOfClass (projectiveClassWeight k g) c).Infinite := by
  obtain ⟨d,g,hd⟩ := exists_infinite_stableClassesOfDimension_at_projectiveWeight_of_not_isEFinite k h
  obtain ⟨c,hc⟩ := exists_infinite_stableClassesOfClass_of_infinite_dimension k hd
  exact ⟨c,g,hc⟩

include k in
/-- Over an infinite field, failure of integral presilting coverage gives an
infinite family stable at one weight and with one ambient Grothendieck class. -/
theorem exists_infinite_stableClassesOfClass_of_not_isEFinite (h : ¬ IsEFinite R) :
    ∃ (c : GrothendieckGroup (FGModuleCat.{u} R)) (θ : Weight (FGModuleCat.{u} R)),
      (stableClassesOfClass θ c).Infinite := by
  obtain ⟨c, g, hs⟩ := exists_infinite_stableClassesOfClass_at_projectiveWeight_of_not_isEFinite k h
  exact ⟨c, projectiveClassWeight k g, hs⟩

include k in
/-- Finiteness at each class and each weight implies E-finiteness over an infinite field. -/
theorem isEFinite_of_finite_stableClassesOfClass
    (h : ∀ (θ : Weight (FGModuleCat.{u} R)) (c : GrothendieckGroup (FGModuleCat.{u} R)),
      (stableClassesOfClass θ c).Finite) : IsEFinite R := by
  by_contra h'
  obtain ⟨c, θ, hθ⟩ := exists_infinite_stableClassesOfClass_of_not_isEFinite k h'
  exact hθ (h θ c)

include k in
theorem isEFinite_of_finite_brickClassesOfClass
    (h : ∀ c : GrothendieckGroup (FGModuleCat.{u} R), (brickClassesOfClass c).Finite) : IsEFinite R :=
  isEFinite_of_finite_stableClassesOfClass k
    (fun θ c ↦ (h c).subset (stableClassesOfClass_subset_brickClassesOfClass θ c))

include k in
/-- The equal-class brick Hom condition implies E-finiteness over an infinite field. -/
theorem isEFinite_of_equalClassBrickHom (h : EqualClassBrickHom (FGModuleCat.{u} R)) :
    IsEFinite R := by
  by_contra h'
  obtain ⟨c, θ, hθ⟩ := exists_infinite_stableClassesOfClass_of_not_isEFinite k h'
  obtain ⟨x, hx⟩ := hθ.nonempty
  obtain ⟨y, hy, hyx⟩ := hθ.exists_notMem_finite (Set.finite_singleton x)
  obtain ⟨X, hX, hcX, hsX⟩ := hx
  obtain ⟨Y, hY, hcY, hsY⟩ := hy
  have hne : ¬ Nonempty (X ≅ Y) := by
    rintro ⟨e⟩
    apply hyx
    apply Set.mem_singleton_iff.mpr
    exact hY.symm.trans ((congr_toSkeleton_of_iso e).symm.trans hX)
  exact Weight.not_equalClassBrickHom (C := FGModuleCat.{u} R) hsX hsY hne (hcX.trans hcY.symm) h

end EFiniteCharacterizations
