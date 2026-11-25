module

public import EFiniteCharacterizations.Characterizations.FixedClassFiniteness

/-! # Families of bricks of prescribed ground-field dimension -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

/-- Isomorphism classes of bricks whose underlying vector space has dimension `r`. -/
def brickClassesOfDimension (r : ℕ) : Set (Skeleton (FGModuleCat.{u} R)) :=
  {x | ∃ M : FGModuleCat.{u} R, toSkeleton M = x ∧ Module.finrank k (M.obj : Type u) = r ∧ IsBrick M}

/-- Over every field, E-finiteness gives brick discreteness at each composition
vector. At each vector, discreteness of bricks implies discreteness of stable bricks. -/
theorem dimensionVectorFiniteness :
    (IsEFinite R → ∀ d, (brickClassesOfClass (classOfCompositionVector (R := R) k d)).Finite) ∧
    ((∀ d, (brickClassesOfClass (classOfCompositionVector (R := R) k d)).Finite) →
      ∀ (g : ProjectiveClass R) d, (stableClassesOfClass (projectiveClassWeight k g) (classOfCompositionVector k d)).Finite) := by
  exact ⟨fun h _ ↦ finite_brickClassesOfClass_of_isEFinite k h _,
    fun h _ d ↦ (h d).subset (stableClassesOfClass_subset_brickClassesOfClass _ _)⟩

/-- An infinite family of bricks in one ground-field dimension gives an infinite
family of stable bricks at one integral weight and one positive dimension. -/
theorem exists_infinite_stable_of_infinite_bricks [Infinite k] {r : ℕ}
    (h : (brickClassesOfDimension (R := R) k r).Infinite) :
    ∃ (g : ProjectiveClass R) (s : ℕ), 0 < s ∧
      (stableClassesOfDimension k (projectiveClassWeight k g) s).Infinite := by
  classical
  have hn : ¬ IsEFinite R := by
    intro he
    let D := {c : GrothendieckGroup (FGModuleCat.{u} R) | ∃ M : FGModuleCat.{u} R,
      Module.finrank k (M.obj : Type u) ≤ r ∧ GrothendieckGroup.of M = c}
    have : Finite D := finite_classes_of_groundFinrank_le k r
    apply h
    apply (Set.finite_iUnion (fun c : D ↦ finite_brickClassesOfClass_of_isEFinite k he c.val)).subset
    rintro x ⟨M, hx, hd, hb⟩
    exact Set.mem_iUnion.mpr ⟨⟨_, M, hd.le, rfl⟩, M, hx, rfl, hb⟩
  obtain ⟨s, g, hs⟩ := exists_infinite_stableClassesOfDimension_at_projectiveWeight_of_not_isEFinite k hn
  obtain ⟨_, M, _, hd, hm⟩ := hs.nonempty
  have : Nontrivial (M.obj : Type u) :=
    not_subsingleton_iff_nontrivial.mp (hm.1 ∘ (FGModuleCat.isZero_iff_subsingleton M).2)
  have : Module.Finite k (M.obj : Type u) := Module.Finite.trans R _
  exact ⟨g, s, hd ▸ Module.finrank_pos, hs⟩

end EFiniteCharacterizations
