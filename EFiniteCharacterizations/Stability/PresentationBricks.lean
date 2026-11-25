module

public import EFiniteCharacterizations.LinearAlgebra.PolynomialCover
public import EFiniteCharacterizations.Presentations.PresentationPolynomial
public import EFiniteCharacterizations.Stability.NonpresiltingImage
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Data.Set.Finite.Range

/-! # Families of stable bricks from projective presentations -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

/-- The stable-brick witnesses tracked for each presentation. -/
structure IsStableImageWitness (P : TwoTerm R) (M : FGModuleCat.{u} R) : Prop where
  brick : IsBrick M
  stable : ((P.eulerWeight k).corrected (dimensionWeight (R := R) k) M).IsStable M
  quotient : ∃ q : P.target ⟶ M, Epi q ∧ P.differential ≫ q = 0
  toNakayamaKernel : ∃ f : M ⟶ P.nakayamaKernel k, f ≠ 0

theorem exists_stableImageWitness_of_not_isPresilting [IsArtinianRing R]
    (P : TwoTerm R) (hP : ¬ P.IsPresilting) :
    ∃ M : FGModuleCat.{u} R, P.IsStableImageWitness k M := by
  obtain ⟨f, hf, hb, hs⟩ := P.exists_stable_image_of_not_isPresilting k hP
  have hi : image.ι f ≠ 0 := by
    intro hz
    apply hf
    rw [← image.fac f, hz, comp_zero]
  refine ⟨image f, hb, hs, ⟨cokernel.π P.differential ≫ factorThruImage f, inferInstance, ?_⟩,
    ⟨image.ι f, hi⟩⟩
  rw [← Category.assoc, cokernel.condition, zero_comp]

variable {P₁ P₀ : FGModuleCat.{u} R} [Module.Projective R P₁] [Module.Projective R P₀]

/-- Give a polynomial to each isomorphism class in a family of stable witnesses. -/
theorem exists_polynomial_cover_of_stable_image_witnesses {n : ℕ}
    (b : Module.Basis (Fin n) k (P₁ ⟶ P₀)) (B : (P₁ ⟶ P₀) → FGModuleCat.{u} R)
    (hB : ∀ p, (ofDifferential p).IsStableImageWitness k (B p)) :
    ∃ D : Set.range (toSkeleton ∘ B) → MvPolynomial (Fin n) k,
      (∀ x, D x ≠ 0) ∧
        (∀ x, (D x).totalDegree ≤
          Module.finrank k (P₁.obj : Type u) * Module.finrank k (P₀.obj : Type u)) ∧
        ∀ a : Fin n → k, ∃ x, MvPolynomial.eval a (D x) = 0 := by
  classical
  have each (x : Set.range (toSkeleton ∘ B)) :
      ∃ D : MvPolynomial (Fin n) k, D ≠ 0 ∧
        D.totalDegree ≤ Module.finrank k (P₁.obj : Type u) * Module.finrank k (P₀.obj : Type u) ∧
        ∀ p : P₁ ⟶ P₀, toSkeleton (B p) = x.val → MvPolynomial.eval (b.repr p) D = 0 := by
    obtain ⟨q, hq⟩ := x.property
    obtain ⟨D, hne, hdeg, hzero⟩ :=
      exists_polynomial_vanishing_at_presentation_occurrences k P₁ P₀ (B q) b
    obtain ⟨e, he, _⟩ := (hB q).quotient
    have hm := groundFinrank_le_of_epi k e
    refine ⟨D, hne, hdeg.trans ((homFinrank_le_mul k P₁ (B q)).trans
      (Nat.mul_le_mul_left _ hm)), ?_⟩
    intro p hp
    let i : B p ≅ B q := Skeleton.isoOfEq (hp.trans hq.symm)
    obtain ⟨f, hf, hz⟩ := (hB p).quotient
    obtain ⟨g, hg⟩ := (hB p).toNakayamaKernel
    refine hzero p (f ≫ i.hom) (epi_comp f i.hom) ?_ ⟨i.inv ≫ g, ?_⟩
    · rw [← Category.assoc, hz, zero_comp]
    · intro hz'
      apply hg
      exact (cancel_epi i.inv).mp (hz'.trans (comp_zero).symm)
  choose D hne hdeg hz using each
  refine ⟨D, hne, hdeg, ?_⟩
  intro a
  let p := b.equivFun.symm a
  refine ⟨⟨toSkeleton (B p), p, rfl⟩, ?_⟩
  have ha : (fun i ↦ b.repr p i) = a := b.equivFun.apply_symm_apply a
  rw [← ha]
  exact hz _ p rfl

/-- Over an infinite field, a family of presentation witnesses has infinitely
many isomorphism classes. -/
theorem infinite_stable_image_witnesses [Infinite k]
    (B : (P₁ ⟶ P₀) → FGModuleCat.{u} R)
    (hB : ∀ p, (ofDifferential p).IsStableImageWitness k (B p)) :
    (Set.range (toSkeleton ∘ B)).Infinite := by
  intro h
  have : Finite (Set.range (toSkeleton ∘ B)) := h
  have := finiteModuleHom_isFinite k P₁ P₀
  obtain ⟨D, hne, _, hcover⟩ :=
    exists_polynomial_cover_of_stable_image_witnesses k (Module.finBasis k _) B hB
  exact not_polynomial_zero_cover_of_infinite D hne hcover

/-- Over a finite field, the number of isomorphism classes in a family of
presentation witnesses is at least the field size divided by the uniform
degree bound. -/
theorem card_le_mul_number_stable_image_witnesses [Fintype k]
    (B : (P₁ ⟶ P₀) → FGModuleCat.{u} R)
    (hB : ∀ p, (ofDifferential p).IsStableImageWitness k (B p)) :
    Fintype.card k ≤ Nat.card (Set.range (toSkeleton ∘ B)) *
      (Module.finrank k (P₁.obj : Type u) * Module.finrank k (P₀.obj : Type u)) := by
  have := finiteModuleHom_isFinite k P₁ P₀
  let b := Module.finBasis k (P₁ ⟶ P₀)
  have : Finite (P₁ ⟶ P₀) := Finite.of_injective b.equivFun b.equivFun.injective
  let := Fintype.ofFinite (Set.range (toSkeleton ∘ B))
  obtain ⟨D, hne, hdeg, hcover⟩ := exists_polynomial_cover_of_stable_image_witnesses k b B hB
  rw [Nat.card_eq_fintype_card]
  exact field_card_le_card_mul_degree_of_polynomial_zero_cover D hne hdeg hcover

end EFiniteCharacterizations.TwoTerm
