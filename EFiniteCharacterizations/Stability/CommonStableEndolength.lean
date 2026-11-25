module

public import EFiniteCharacterizations.Modules.Endolength
public import EFiniteCharacterizations.Stability.CommonStableWeight
public import EFiniteCharacterizations.Stability.Semibricks

/-! # Infinitely many stable bricks at one endolength -/

@[expose] public section

open CategoryTheory

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [IsNoetherianRing R]

/-- Isomorphism classes of bricks of a fixed endolength. -/
def brickClassesOfEndolength (r : ℕ) : Set (Skeleton (FGModuleCat.{u} R)) :=
  {x | ∃ M : FGModuleCat.{u} R, toSkeleton M = x ∧ endolength k M = r ∧ IsBrick M}

/-- Isomorphism classes of stable modules of a fixed endolength at a given weight. -/
def stableClassesOfEndolength (θ : Weight (FGModuleCat.{u} R)) (r : ℕ) :
    Set (Skeleton (FGModuleCat.{u} R)) :=
  {x | ∃ M : FGModuleCat.{u} R, toSkeleton M = x ∧ endolength k M = r ∧ θ.IsStable M}

theorem stableClassesOfEndolength_subset_brickClassesOfEndolength
    (θ : Weight (FGModuleCat.{u} R)) (r : ℕ) :
    stableClassesOfEndolength k θ r ⊆ brickClassesOfEndolength (R := R) k r := by
  rintro x ⟨M, hM, hr, hstable⟩
  exact ⟨M, hM, hr, hstable.isBrick⟩

theorem stableClassesOfEndolength_subset_stableClasses
    (θ : Weight (FGModuleCat.{u} R)) (r : ℕ) :
    stableClassesOfEndolength k θ r ⊆ stableClasses θ := by
  rintro x ⟨M, hM, _, hstable⟩
  obtain ⟨e⟩ := toSkeleton_eq_iff.mp hM
  exact hstable.of_iso e

variable [Infinite k] [Module.Finite k R] [IsArtinianRing R]

/-- Over an infinite field, a missing presilting class yields infinitely many
modules stable at one integral weight and of one endolength. -/
theorem exists_infinite_stableClassesOfEndolength_at_projectiveWeight_of_not_isEFinite (h : ¬ IsEFinite R) :
    ∃ (g : ProjectiveClass R) (r : ℕ), 0 < r ∧
      (stableClassesOfEndolength k (projectiveClassWeight k g) r).Infinite := by
  classical
  obtain ⟨d, g, hθ⟩ := exists_infinite_stableClassesOfDimension_at_projectiveWeight_of_not_isEFinite k h
  let θ := projectiveClassWeight k g
  have hsub : stableClassesOfDimension k θ d ⊆
      ⋃ r : Fin (d + 1), stableClassesOfEndolength k θ r.val := by
    rintro x ⟨M, hM, hd, hstable⟩
    have hr := (endolength_le_groundFinrank k M).trans_eq hd
    exact Set.mem_iUnion.mpr ⟨⟨endolength k M, Nat.lt_succ_of_le hr⟩, M, hM, rfl, hstable⟩
  by_contra habs
  have hall (r : Fin (d + 1)) : (stableClassesOfEndolength k θ r.val).Finite := by
    by_contra hf
    have hinf : (stableClassesOfEndolength k θ r.val).Infinite := hf
    obtain ⟨_, M, _, hM, hs⟩ := hinf.nonempty
    exact habs ⟨g, r.val, hM ▸ hs.isBrick.endolength_pos k, hf⟩
  exact hθ ((Set.finite_iUnion hall).subset hsub)

/-- Over an infinite field, a missing presilting class yields infinitely many
modules stable at one weight and of one endolength. -/
theorem exists_infinite_stableClassesOfEndolength_of_not_isEFinite (h : ¬ IsEFinite R) :
    ∃ (r : ℕ) (θ : Weight (FGModuleCat.{u} R)), 0 < r ∧
      (stableClassesOfEndolength k θ r).Infinite := by
  obtain ⟨g, r, hr, hs⟩ := exists_infinite_stableClassesOfEndolength_at_projectiveWeight_of_not_isEFinite k h
  exact ⟨r, projectiveClassWeight k g, hr, hs⟩

/-- Finiteness at each endolength and weight implies E-finiteness over an infinite field. -/
theorem isEFinite_of_finite_stableClassesOfEndolength
    (h : ∀ (θ : Weight (FGModuleCat.{u} R)) (r : ℕ),
      0 < r → (stableClassesOfEndolength k θ r).Finite) : IsEFinite R := by
  by_contra h'
  obtain ⟨r, θ, hr, hθ⟩ := exists_infinite_stableClassesOfEndolength_of_not_isEFinite k h'
  exact hθ (h θ r hr)

theorem isEFinite_of_finite_brickClassesOfEndolength
    (h : ∀ r : ℕ, 0 < r → (brickClassesOfEndolength (R := R) k r).Finite) : IsEFinite R :=
  isEFinite_of_finite_stableClassesOfEndolength k
    (fun θ r hr ↦ (h r hr).subset (stableClassesOfEndolength_subset_brickClassesOfEndolength k θ r))

end EFiniteCharacterizations
