module

public import EFiniteCharacterizations.LinearAlgebra.PolynomialTensor
public import EFiniteCharacterizations.LinearAlgebra.ScalarCategory
public import EFiniteCharacterizations.Modules.HomDimension
public import EFiniteCharacterizations.Presentations.TwoTerm
public import Mathlib.LinearAlgebra.Prod

/-! # Polynomial comparison of differentials on fixed terms -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace EFiniteCharacterizations

variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- The linear map giving null-homotopic maps from a two-term differential to
the shift of another two-term differential. -/
def boundaryLinear {P₁ P₀ Q₁ Q₀ : C} (p : P₁ ⟶ P₀) (q : Q₁ ⟶ Q₀) :
    ((P₁ ⟶ Q₁) × (P₀ ⟶ Q₀)) →ₗ[k] (P₁ ⟶ Q₀) :=
  (Linear.rightComp k P₁ q).comp (LinearMap.fst k _ _) -
    (Linear.leftComp k Q₀ p).comp (LinearMap.snd k _ _)

@[simp] theorem boundaryLinear_apply {P₁ P₀ Q₁ Q₀ : C} (p : P₁ ⟶ P₀) (q : Q₁ ⟶ Q₀)
    (a : (P₁ ⟶ Q₁) × (P₀ ⟶ Q₀)) : boundaryLinear k p q a = a.1 ≫ q - p ≫ a.2 := rfl

/-- A fully faithful additive functor preserves and reflects surjectivity of
the boundary map. The Hom spaces may have different scalar fields. -/
theorem boundaryLinear_map_surjective_iff (F : Type*) [Field F] {D : Type*}
    [Category D] [Preadditive D] [Linear F D] (G : C ⥤ D) [G.Full] [G.Faithful] [G.Additive]
    {P₁ P₀ Q₁ Q₀ : C} (p : P₁ ⟶ P₀) (q : Q₁ ⟶ Q₀) :
    Function.Surjective (boundaryLinear F (G.map p) (G.map q)) ↔
      Function.Surjective (boundaryLinear k p q) := by
  constructor
  · intro h f
    obtain ⟨⟨a, b⟩, hab⟩ := h (G.map f)
    refine ⟨(G.preimage a, G.preimage b), G.map_injective ?_⟩
    simpa only [boundaryLinear_apply, G.map_sub, G.map_comp, G.map_preimage] using hab
  · intro h f
    obtain ⟨⟨a, b⟩, hab⟩ := h (G.preimage f)
    refine ⟨(G.map a, G.map b), ?_⟩
    simpa only [boundaryLinear_apply, G.map_sub, G.map_comp, G.map_preimage] using congrArg G.map hab

/-- A line through the two differentials in the scalar-extended category. -/
noncomputable def differentialPencil {X Y : C} (u σ : X ⟶ Y) :
    (ScalarCategory.mk X : ScalarCategory k (Polynomial k) C) ⟶ ScalarCategory.mk Y :=
  (1 : Polynomial k) ⊗ₜ[k] u + (Polynomial.X : Polynomial k) • ((1 : Polynomial k) ⊗ₜ[k] (σ - u))

/-- A rigid differential determines a polynomial chain map from every pencil
through it, with both components equal to the identity at the rigid point. -/
theorem exists_polynomial_chain_map {X Y : C} (u σ : X ⟶ Y)
    [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]
    (h : Function.Surjective (boundaryLinear k u u)) :
    ∃ (a : (ScalarCategory.mk X : ScalarCategory k (Polynomial k) C) ⟶ ScalarCategory.mk X)
      (b : (ScalarCategory.mk Y : ScalarCategory k (Polynomial k) C) ⟶ ScalarCategory.mk Y),
      a ≫ ((1 : Polynomial k) ⊗ₜ[k] u : ScalarCategory.mk X ⟶ ScalarCategory.mk Y) =
        differentialPencil k u σ ≫ b ∧
      polynomialEval (0 : k) a = 𝟙 X ∧ polynomialEval (0 : k) b = 𝟙 Y := by
  let d := boundaryLinear k u u
  let d' := - (Linear.leftComp k Y (σ - u)).comp (LinearMap.snd k (X ⟶ X) (Y ⟶ Y))
  have hv : d (𝟙 X, 𝟙 Y) = 0 := by simp [d]
  obtain ⟨w, hw, h₀⟩ := exists_tensor_affine_kernel_lift d d' h (𝟙 X, 𝟙 Y) hv
  let a : (ScalarCategory.mk X : ScalarCategory k (Polynomial k) C) ⟶ ScalarCategory.mk X :=
    (LinearMap.fst k (X ⟶ X) (Y ⟶ Y)).baseChange (Polynomial k) w
  let b : (ScalarCategory.mk Y : ScalarCategory k (Polynomial k) C) ⟶ ScalarCategory.mk Y :=
    (LinearMap.snd k (X ⟶ X) (Y ⟶ Y)).baseChange (Polynomial k) w
  have hd : d.baseChange (Polynomial k) w =
      a ≫ ((1 : Polynomial k) ⊗ₜ[k] u : ScalarCategory.mk X ⟶ ScalarCategory.mk Y) -
        ((1 : Polynomial k) ⊗ₜ[k] u : ScalarCategory.mk X ⟶ ScalarCategory.mk Y) ≫ b := by
    rw [ScalarCategory.comp_one_tmul (X := ⟨X⟩) (Y := ⟨X⟩) (Z := ⟨Y⟩),
      ScalarCategory.one_tmul_comp (X := ⟨X⟩) (Y := ⟨Y⟩) (Z := ⟨Y⟩)]
    simp only [d, boundaryLinear, LinearMap.baseChange_sub, LinearMap.baseChange_comp,
      LinearMap.sub_apply, LinearMap.comp_apply, a, b]
  have hd' : d'.baseChange (Polynomial k) w =
      - (((1 : Polynomial k) ⊗ₜ[k] (σ - u) : ScalarCategory.mk X ⟶ ScalarCategory.mk Y) ≫ b) := by
    rw [ScalarCategory.one_tmul_comp (X := ⟨X⟩) (Y := ⟨Y⟩) (Z := ⟨Y⟩)]
    simp only [d', LinearMap.baseChange_neg, LinearMap.baseChange_comp, LinearMap.neg_apply,
      LinearMap.comp_apply, b]
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rw [differentialPencil, Preadditive.add_comp, Linear.smul_comp, ← sub_eq_zero, ← sub_sub]
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, hd, hd', smul_neg, sub_eq_add_neg] using hw
  · simp [a, polynomialEval_baseChange, h₀]
  · simp [b, polynomialEval_baseChange, h₀]

universe u

theorem TwoTerm.isPresilting_iff_boundaryLinear_surjective {k R : Type u} [Field k] [Ring R]
    [Algebra k R] (P : TwoTerm R) : P.IsPresilting ↔
      Function.Surjective (boundaryLinear k P.differential P.differential) := Iff.rfl

end EFiniteCharacterizations
