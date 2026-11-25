module

public import EFiniteCharacterizations.ScalarExtension.GaloisWitnessFibres
public import Mathlib.FieldTheory.Finite.GaloisField
public import EFiniteCharacterizations.Stability.PresentationBricks

/-! # Uniform ground witness counts from nonpresilting extended terms -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FieldExtension

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

/-- If fixed projective terms admit no presilting differential over a
finite extension, the field cardinality bounds the number of ground brick
witnesses from below after division by a uniform constant and the degree.
All witnesses have bounded endolength and use a fixed finite list of weights. -/
theorem exists_sharp_ground_witness_bound (P : TwoTerm R) :
    ∃ G : Finset (ProjectiveClass R),
      ∀ (F : Type u) [Field F] [Algebra k F] [Fintype F] [Module.Finite k F],
        (∀ p : (extendTwoTerm k F R P).source ⟶ (extendTwoTerm k F R P).target,
          ¬ ({ extendTwoTerm k F R P with differential := p }).IsPresilting) →
        ∃ s : Finset (Skeleton (FGModuleCat.{u} R)),
          Fintype.card F ≤ max 1 (Module.finrank k (P.target.obj : Type u) * Module.finrank k (P.source.obj : Type u)) *
            Module.finrank k F * s.card ∧
          ∀ c ∈ s, ∃ (M : FGModuleCat.{u} R) (g : ProjectiveClass R), toSkeleton M = c ∧ g ∈ G ∧
            (projectiveClassWeight k g).IsStable M ∧
            Module.finrank k (M.obj : Type u) ≤ Module.finrank k F * Module.finrank k (P.target.obj : Type u) ∧
            endolength k M ≤ Module.finrank k (P.target.obj : Type u) := by
  classical
  let d₀ := Module.finrank k (P.target.obj : Type u)
  let d₁ := Module.finrank k (P.source.obj : Type u)
  let J := Fin (d₀ + 1) × Fin (d₀ * d₀ + 1) × Fin (d₁ * d₀ + 1)
  let R₀ : FiniteProjective R := ⟨FGModuleCat.of R R, inferInstance⟩
  let g (t : J) : ProjectiveClass R :=
    (t.1.val : ℤ) • P.projectiveClass -
      ((t.2.1.val : ℤ) - (t.2.2.val : ℤ)) • ProjectiveClass.of R₀
  let G := Finset.univ.image g
  choose Q hQ using fun t : J ↦ ProjectiveClass.exists_twoTerm (g t)
  have hg (t : J) : (Q t).eulerWeight k =
      (t.1.val : ℤ) • P.eulerWeight k -
        ((t.2.1.val : ℤ) - (t.2.2.val : ℤ)) • dimensionWeight (R := R) k := by
    rw [← (Q t).projectiveClassWeight_eq_eulerWeight k, hQ t]
    dsimp only [g]
    rw [map_sub, map_zsmul, map_zsmul, P.projectiveClassWeight_eq_eulerWeight k, projectiveClassWeight_of]
    rfl
  refine ⟨G,?_⟩
  intro F _ _ _ _ hmissing
  let A := ExtendedAlgebra k F R
  let _ := IsArtinianRing.of_finite F A
  let _ := IsNoetherianRing.of_finite F A
  let U := extendTwoTerm k F R P
  let _ := U.projective_source
  let _ := U.projective_target
  have h (p : U.source ⟶ U.target) :
      ∃ M, (TwoTerm.ofDifferential p).IsStableImageWitness F M :=
    (TwoTerm.ofDifferential p).exists_stableImageWitness_of_not_isPresilting F (hmissing p)
  choose B hB using h
  let I := Set.range (toSkeleton ∘ B)
  have := finiteModuleHom_isFinite F U.source U.target
  have : Finite (U.source ⟶ U.target) := Module.finite_of_finite F
  let _ := Fintype.ofFinite I
  have hnum := TwoTerm.card_le_mul_number_stable_image_witnesses F B hB
  rw [Nat.card_eq_fintype_card] at hnum
  have hU₀ : Module.finrank F (U.target.obj : Type u) = d₀ := finrank_extendObj k F R P.target
  have hU₁ : Module.finrank F (U.source.obj : Type u) = d₁ := finrank_extendObj k F R P.source
  rw [hU₀, hU₁] at hnum
  choose p hp using fun i : I ↦ i.property
  let N (i : I) := B (p i)
  have hI : Function.Injective (toSkeleton ∘ N) := by
    intro x y he
    exact Subtype.ext ((hp x).symm.trans (he.trans (hp y)))
  have hdim (i : I) : Module.finrank F ((N i).obj : Type u) ≤ d₀ := by
    obtain ⟨f, hf, _⟩ := (hB (p i)).quotient
    exact (groundFinrank_le_of_epi F f).trans_eq hU₀
  have hw (i : I) : ∃ t : J, ((extendTwoTerm k F R (Q t)).eulerWeight F).IsStable (N i) := by
    have h₀ := (homFinrank_le_mul F U.target (N i)).trans (Nat.mul_le_mul_left _ (hdim i))
    have h₁ := (homFinrank_le_mul F U.source (N i)).trans (Nat.mul_le_mul_left _ (hdim i))
    rw [hU₀] at h₀
    rw [hU₁] at h₁
    let t : J := ⟨⟨_, Nat.lt_succ_of_le (hdim i)⟩, ⟨_, Nat.lt_succ_of_le h₀⟩, ⟨_, Nat.lt_succ_of_le h₁⟩⟩
    refine ⟨t, ?_⟩
    rw [eulerWeight_extend_eq_of_eulerWeight_eq k F R P (Q t) _ _ (hg t)]
    have ht := (hB (p i)).stable
    unfold Weight.corrected at ht
    rw [dimensionWeight_eval, TwoTerm.eulerWeight_eval] at ht
    exact ht
  choose tag hstable using hw
  obtain ⟨s, hs, hground⟩ := exists_ground_witness_finset_galois k F R (Q ∘ tag) N d₀ hI hstable hdim
  refine ⟨s, ?_, ?_⟩
  · calc
      Fintype.card F ≤ Fintype.card I * (d₁ * d₀) := hnum
      _ ≤ (Module.finrank k F * s.card) * max 1 (d₀ * d₁) :=
        Nat.mul_le_mul hs ((Nat.mul_comm d₁ d₀).le.trans (le_max_right _ _))
      _ = _ := by change _ = max 1 (d₀*d₁) * Module.finrank k F * s.card; ring
  · intro c hc
    obtain ⟨M, t, heq, hst, hd, he⟩ := hground c hc
    refine ⟨M, g (tag t), heq, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_, hd, he⟩
    rw [← hQ (tag t), (Q (tag t)).projectiveClassWeight_eq_eulerWeight k]
    exact hst

/-- The uniform bound with an existential constant used in the asymptotic growth estimates. -/
theorem exists_uniform_ground_witness_bound (P : TwoTerm R) :
    ∃ (C : ℕ) (G : Finset (ProjectiveClass R)), 0 < C ∧
      ∀ (F : Type u) [Field F] [Algebra k F] [Fintype F] [Module.Finite k F],
        (∀ p : (extendTwoTerm k F R P).source ⟶ (extendTwoTerm k F R P).target,
          ¬ ({ extendTwoTerm k F R P with differential := p }).IsPresilting) →
        ∃ s : Finset (Skeleton (FGModuleCat.{u} R)),
          Fintype.card F ≤ C * Module.finrank k F * s.card ∧
          ∀ c ∈ s, ∃ (M : FGModuleCat.{u} R) (g : ProjectiveClass R), toSkeleton M = c ∧ g ∈ G ∧
            (projectiveClassWeight k g).IsStable M ∧
            Module.finrank k (M.obj : Type u) ≤ Module.finrank k F * Module.finrank k (P.target.obj : Type u) ∧
            endolength k M ≤ Module.finrank k (P.target.obj : Type u) := by
  obtain ⟨G,h⟩ := exists_sharp_ground_witness_bound k P
  exact ⟨_,G,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _),h⟩

end EFiniteCharacterizations.FieldExtension
