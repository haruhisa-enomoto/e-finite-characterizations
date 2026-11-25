module

public import EFiniteCharacterizations.Characterizations.FixedClassFiniteness

/-!
# Bricks of prescribed dimension vector and ground-field dimension

Corollaries 5.4 and 5.5 of the manuscript:

* `dimensionVectorFiniteness` (**Corollary 5.4**, forward implications over any field):
  `(E-fin)` implies `(dim-brick)` (finitely many bricks of each dimension vector),
  which implies `(dim-stab)`.
* `exists_infinite_stable_of_infinite_bricks` (**Corollary 5.5**): over an infinite
  field, if infinitely many nonisomorphic bricks have `k`-dimension `r`, then some
  integral weight `g` and positive `k`-dimension `s` admit infinitely many
  nonisomorphic `g`-stable bricks.
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

/-- Isomorphism classes of bricks in `mod R` of `k`-dimension `r`. -/
def brickClassesOfDimension (r : ℕ) : Set (Skeleton (FGModuleCat.{u} R)) :=
  {x | ∃ M : FGModuleCat.{u} R, toSkeleton M = x ∧ Module.finrank k (M.obj : Type u) = r ∧ IsBrick M}

/-- **Corollary 5.4** (arbitrary-field implications): E-finiteness implies finiteness of bricks of
each dimension vector `(dim-brick)`, which in turn implies finiteness of stable bricks of each
dimension vector `(dim-stab)`. -/
theorem dimensionVectorFiniteness :
    (IsEFinite R → ∀ d, (brickClassesOfClass (classOfCompositionVector (R := R) k d)).Finite) ∧
    ((∀ d, (brickClassesOfClass (classOfCompositionVector (R := R) k d)).Finite) →
      ∀ (g : ProjectiveClass R) d, (stableClassesOfClass (projectiveClassWeight k g) (classOfCompositionVector k d)).Finite) := by
  exact ⟨fun h _ ↦ finite_brickClassesOfClass_of_isEFinite k h _,
    fun h _ d ↦ (h d).subset (stableClassesOfClass_subset_brickClassesOfClass _ _)⟩

/-- **Corollary 5.5:** Over an infinite field, if infinitely many nonisomorphic bricks have a fixed
`k`-dimension `r`, then there exist an integral weight `g` and an integer `s > 0` with infinitely
many nonisomorphic `g`-stable bricks of `k`-dimension `s`. -/
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
