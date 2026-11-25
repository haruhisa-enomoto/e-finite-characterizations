module

public import EFiniteCharacterizations.LinearAlgebra.PolynomialMinor
public import EFiniteCharacterizations.Presentations.TwoTermEuler

/-! # Polynomial bounds on occurrences of a module in projective presentations -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

/-- A module can occur as a quotient of the cokernel with a nonzero map to the
Nakayama kernel only on the zero set of a polynomial of bounded degree. -/
theorem exists_polynomial_vanishing_at_presentation_occurrences
    {ι : Type v} [Fintype ι]
    (P₁ P₀ M : FGModuleCat.{u} R) [Module.Projective R P₁] [Module.Projective R P₀]
    (b : Module.Basis ι k (P₁ ⟶ P₀)) :
    ∃ D : MvPolynomial ι k, D ≠ 0 ∧ D.totalDegree ≤ homFinrank k P₁ M ∧
      ∀ (p : P₁ ⟶ P₀) (q : P₀ ⟶ M), Epi q → p ≫ q = 0 →
        (∃ g : M ⟶ (TwoTerm.ofDifferential p).nakayamaKernel k, g ≠ 0) →
        MvPolynomial.eval (b.repr p) D = 0 := by
  have := finiteModuleHom_isFinite k P₁ M
  let Φ := Linear.comp (S := k) P₁ P₀ M
  obtain ⟨D, hD, hdeg, hv⟩ := exists_polynomial_vanishing_at_defective_pencil b Φ
  refine ⟨D, hD, by rwa [homFinrank_eq_finrank], ?_⟩
  rintro p q hq hp ⟨g, hg⟩
  have hsup : ∀ w : P₁ ⟶ M, ∃ h : P₁ ⟶ P₀, Φ h q = w := by
    intro w
    exact FGModuleCat.exists_lift_of_projective q w
  have hnonsurj : ¬ Function.Surjective (Φ p) := by
    intro hs
    let P := TwoTerm.ofDifferential p
    let e := P.dualKerEquiv k M
    let χ := e.symm g
    have hz : (χ : Module.Dual k (P₁ ⟶ M)) = 0 := by
      apply LinearMap.dualMap_injective_of_surjective (f := Linear.leftComp k M p) hs
      exact χ.property.trans (map_zero _).symm
    apply hg
    have hχ : χ = 0 := Subtype.ext hz
    calc
      g = e χ := (e.apply_symm_apply g).symm
      _ = 0 := by rw [hχ, map_zero]
  exact hv p q hp hsup hnonsurj

end EFiniteCharacterizations
