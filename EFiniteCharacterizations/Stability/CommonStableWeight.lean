module

public import EFiniteCharacterizations.Presentations.IntegralEulerWeights
public import EFiniteCharacterizations.Presentations.RepresentProjectiveClass
public import EFiniteCharacterizations.Stability.PresentationBricks
public import Mathlib.Data.Set.Finite.Lattice

/-! # Infinitely many stable bricks at one weight and dimension -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

/-- The isomorphism classes of finite modules of a fixed ground-field dimension
that are stable for the given weight. -/
def stableClassesOfDimension (θ : Weight (FGModuleCat.{u} R)) (d : ℕ) :
    Set (Skeleton (FGModuleCat.{u} R)) :=
  {c | ∃ M : FGModuleCat.{u} R,
    toSkeleton M = c ∧ Module.finrank k (M.obj : Type u) = d ∧ θ.IsStable M}

variable [Infinite k]

/-- Infinitely many isomorphism classes among the presentation witnesses
share a dimension and a stability weight. -/
theorem exists_infinite_stableClassesOfDimension_at_corrected_weight
    {P₁ P₀ : FGModuleCat.{u} R} [Module.Projective R P₁] [Module.Projective R P₀]
    (B : (P₁ ⟶ P₀) → FGModuleCat.{u} R)
    (hB : ∀ p, (TwoTerm.ofDifferential p).IsStableImageWitness k (B p)) :
    ∃ (d : ℕ) (e : ℤ),
      (stableClassesOfDimension k ((d : ℤ) • (TwoTerm.ofDifferential (0 : P₁ ⟶ P₀)).eulerWeight k -
        e • dimensionWeight (R := R) k) d).Infinite := by
  classical
  let d₀ := Module.finrank k (P₀.obj : Type u)
  let d₁ := Module.finrank k (P₁.obj : Type u)
  let T := Fin (d₀ + 1) × Fin (d₀ * d₀ + 1) × Fin (d₁ * d₀ + 1)
  let U := TwoTerm.ofDifferential (0 : P₁ ⟶ P₀)
  let G : FiniteProjective R := ⟨FGModuleCat.of R R, inferInstance⟩
  have hG : projectiveClassWeight k (ProjectiveClass.of G) = dimensionWeight (R := R) k := by
    rw [projectiveClassWeight_of]
    rfl
  let f (t : T) : ProjectiveClass R :=
    (t.1.val : ℤ) • U.projectiveClass -
      ((t.2.1.val : ℤ) - (t.2.2.val : ℤ)) • ProjectiveClass.of G
  have hmem : Set.range (toSkeleton ∘ B) ⊆
      ⋃ t : T, stableClassesOfDimension k (projectiveClassWeight k (f t)) t.1.val := by
    rintro x ⟨p, rfl⟩
    obtain ⟨q, hq, _⟩ := (hB p).quotient
    have hdim : Module.finrank k ((B p).obj : Type u) ≤ d₀ := groundFinrank_le_of_epi k q
    have h₀ : homFinrank k P₀ (B p) ≤ d₀ * d₀ :=
      (homFinrank_le_mul k P₀ (B p)).trans (Nat.mul_le_mul_left _ hdim)
    have h₁ : homFinrank k P₁ (B p) ≤ d₁ * d₀ :=
      (homFinrank_le_mul k P₁ (B p)).trans (Nat.mul_le_mul_left _ hdim)
    let t : T := ⟨⟨_, Nat.lt_succ_of_le hdim⟩,
      ⟨_, Nat.lt_succ_of_le h₀⟩, ⟨_, Nat.lt_succ_of_le h₁⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨t, B p, rfl, rfl, ?_⟩
    have hs := (hB p).stable
    unfold Weight.corrected at hs
    rw [dimensionWeight_eval, TwoTerm.eulerWeight_eval] at hs
    dsimp only [f]
    rw [map_sub, map_zsmul, map_zsmul, U.projectiveClassWeight_eq_eulerWeight k, hG]
    exact hs
  by_contra h
  have hall (t : T) : (stableClassesOfDimension k (projectiveClassWeight k (f t)) t.1.val).Finite := by
    by_contra hf
    apply h
    refine ⟨t.1.val, (t.2.1.val : ℤ) - t.2.2.val, ?_⟩
    change ¬ (stableClassesOfDimension k ((t.1.val : ℤ) • U.eulerWeight k - _ • dimensionWeight (R := R) k) t.1.val).Finite
    simpa only [f,map_sub,map_zsmul,U.projectiveClassWeight_eq_eulerWeight k,hG] using hf
  exact TwoTerm.infinite_stable_image_witnesses k B hB ((Set.finite_iUnion hall).subset hmem)

/-- The common corrected weight belongs to the integral projective lattice. -/
theorem exists_infinite_stableClassesOfDimension_at_projectiveWeight
    {P₁ P₀ : FGModuleCat.{u} R} [Module.Projective R P₁] [Module.Projective R P₀]
    (B : (P₁ ⟶ P₀) → FGModuleCat.{u} R)
    (hB : ∀ p, (TwoTerm.ofDifferential p).IsStableImageWitness k (B p)) :
    ∃ (d : ℕ) (g : ProjectiveClass R),
      (stableClassesOfDimension k (projectiveClassWeight k g) d).Infinite := by
  obtain ⟨d,e,h⟩ := exists_infinite_stableClassesOfDimension_at_corrected_weight k B hB
  let P := TwoTerm.ofDifferential (0 : P₁ ⟶ P₀)
  let G : FiniteProjective R := ⟨FGModuleCat.of R R,inferInstance⟩
  refine ⟨d,(d : ℤ) • P.projectiveClass - e • ProjectiveClass.of G,?_⟩
  rw [map_sub,map_zsmul,map_zsmul,P.projectiveClassWeight_eq_eulerWeight k,projectiveClassWeight_of]
  exact h

/-- The common weight of the presentation witnesses, viewed as an additive weight. -/
theorem exists_infinite_stableClassesOfDimension
    {P₁ P₀ : FGModuleCat.{u} R} [Module.Projective R P₁] [Module.Projective R P₀]
    (B : (P₁ ⟶ P₀) → FGModuleCat.{u} R)
    (hB : ∀ p, (TwoTerm.ofDifferential p).IsStableImageWitness k (B p)) :
    ∃ (d : ℕ) (θ : Weight (FGModuleCat.{u} R)), (stableClassesOfDimension k θ d).Infinite := by
  obtain ⟨d, g, hg⟩ := exists_infinite_stableClassesOfDimension_at_projectiveWeight k B hB
  exact ⟨d, projectiveClassWeight k g, hg⟩

/-- Failure of integral presilting coverage gives infinitely many stable bricks
at one integral projective weight and one ground-field dimension. -/
theorem exists_infinite_stableClassesOfDimension_at_projectiveWeight_of_not_isEFinite [IsArtinianRing R]
    (h : ¬ IsEFinite R) : ∃ (d : ℕ) (g : ProjectiveClass R),
      (stableClassesOfDimension k (projectiveClassWeight k g) d).Infinite := by
  classical
  obtain ⟨g, hg⟩ := not_forall.mp h
  obtain ⟨P₀, P₁, hp⟩ := ProjectiveClass.exists_sub g
  have := P₀.property
  have := P₁.property
  have hw (p : P₁.val ⟶ P₀.val) : ∃ M, (TwoTerm.ofDifferential p).IsStableImageWitness k M :=
    (TwoTerm.ofDifferential p).exists_stableImageWitness_of_not_isPresilting k
      (fun hs ↦ hg ⟨TwoTerm.ofDifferential p, hs, hp⟩)
  choose B hB using hw
  exact exists_infinite_stableClassesOfDimension_at_projectiveWeight k B hB

theorem exists_infinite_stableClassesOfDimension_of_not_isEFinite [IsArtinianRing R]
    (h : ¬ IsEFinite R) : ∃ (d : ℕ) (θ : Weight (FGModuleCat.{u} R)),
      (stableClassesOfDimension k θ d).Infinite := by
  obtain ⟨d, g, hg⟩ := exists_infinite_stableClassesOfDimension_at_projectiveWeight_of_not_isEFinite k h
  exact ⟨d, projectiveClassWeight k g, hg⟩

end EFiniteCharacterizations
