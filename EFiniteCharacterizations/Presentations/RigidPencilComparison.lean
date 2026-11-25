module

public import EFiniteCharacterizations.LinearAlgebra.AffineRank
public import EFiniteCharacterizations.Presentations.BoundaryRank
public import EFiniteCharacterizations.Presentations.RigidPencilIsomorphism
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Shifted Hom dimensions at a rigid differential -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace EFiniteCharacterizations

section LinearCategory

variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  [∀ X Y : C, Module.Finite k (X ⟶ Y)]

private theorem finite_boundary_rank_scalarExtension {F : Type*} [Field F] [Algebra k F]
    {X Y A B : C} (p : X ⟶ Y) (q : A ⟶ B) :
    let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
    Module.finrank F (LinearMap.range (boundaryLinear F (G.map p) (G.map q))) =
      Module.finrank k (LinearMap.range (boundaryLinear k p q)) := by
  have hr := boundaryLinear_scalarExtension_affine_range k F p p q q (0 : F)
  dsimp only at hr
  simp only [zero_smul, add_zero] at hr
  dsimp only
  rw [hr]
  exact finrank_range_baseChange (boundaryLinear k p q)

/-- A rigid differential maximizes the rank of the homotopy boundary on
fixed terms, in either variable. The comparison holds over finite fields as well. -/
theorem boundaryLinear_rank_le_at_rigid {X Y A B : C} (u σ : X ⟶ Y) (q : A ⟶ B)
    (hu : Function.Surjective (boundaryLinear k u u)) :
    Module.finrank k (LinearMap.range (boundaryLinear k σ q)) ≤
      Module.finrank k (LinearMap.range (boundaryLinear k u q)) ∧
    Module.finrank k (LinearMap.range (boundaryLinear k q σ)) ≤
      Module.finrank k (LinearMap.range (boundaryLinear k q u)) := by
  let F := RatFunc k
  let e : Polynomial k →ₐ[k] F := IsScalarTower.toAlgHom k (Polynomial k) F
  have he : Function.Injective e := IsFractionRing.injective (Polynomial k) F
  let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
  let t := e Polynomial.X
  let p := G.map u + t • G.map (σ - u)
  obtain ⟨a, b, hab⟩ := exists_generic_affine_iso k u σ e he hu
  have h₁ : u + (1 : k) • (σ - u) = σ := by simp only [one_smul]; abel
  constructor
  · have hk : boundaryLinear k u q + (1 : k) • boundaryLinear k (σ - u) 0 = boundaryLinear k σ q := by
      rw [← boundaryLinear_add_smul, h₁, smul_zero, add_zero]
    have hF : LinearMap.range (boundaryLinear F p (G.map q)) =
        LinearMap.range ((boundaryLinear k u q).baseChange F + t • (boundaryLinear k (σ - u) 0).baseChange F) := by
      have e' := boundaryLinear_scalarExtension_affine_range k F u (σ - u) q 0 t
      dsimp only at e'
      simp only [Functor.map_zero, smul_zero, add_zero] at e'
      exact e'
    calc
      _ ≤ Module.finrank F (LinearMap.range (boundaryLinear F p (G.map q))) := by
        rw [← hk, hF]
        exact affine_finrank_range_eval_le e he _ _ 1
      _ = Module.finrank F (LinearMap.range (boundaryLinear F (G.map u) (G.map q))) :=
        boundaryLinear_rank_eq_of_source_iso F p (G.map u) (G.map q) a b hab
      _ = _ := finite_boundary_rank_scalarExtension k u q
  · have hk : boundaryLinear k q u + (1 : k) • boundaryLinear k 0 (σ - u) = boundaryLinear k q σ := by
      rw [← boundaryLinear_add_smul, h₁, smul_zero, add_zero]
    have hF : LinearMap.range (boundaryLinear F (G.map q) p) =
        LinearMap.range ((boundaryLinear k q u).baseChange F + t • (boundaryLinear k 0 (σ - u)).baseChange F) := by
      have e' := boundaryLinear_scalarExtension_affine_range k F q 0 u (σ - u) t
      dsimp only at e'
      simp only [Functor.map_zero, smul_zero, add_zero] at e'
      exact e'
    calc
      _ ≤ Module.finrank F (LinearMap.range (boundaryLinear F (G.map q) p)) := by
        rw [← hk, hF]
        exact affine_finrank_range_eval_le e he _ _ 1
      _ = Module.finrank F (LinearMap.range (boundaryLinear F (G.map q) (G.map u))) :=
        (boundaryLinear_rank_eq_of_target_iso F p (G.map u) (G.map q) a b hab).symm
      _ = _ := finite_boundary_rank_scalarExtension k q u

end LinearCategory

namespace TwoTerm

universe u

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]

/-- The dimension of the space of maps to the shift, modulo homotopy. -/
noncomputable def shiftedHomFinrank (P Q : TwoTerm R) : ℕ :=
  Module.finrank k ((P.source ⟶ Q.target) ⧸ (boundaryLinear k P.differential Q.differential).range)

variable [Module.Finite k R]

theorem shiftedHomFinrank_eq_zero_iff (P Q : TwoTerm R) :
    P.shiftedHomFinrank k Q = 0 ↔ Function.Surjective (homotopyBoundary P Q) := by
  have := finiteModuleHom_isFinite k P.source Q.target
  rw [shiftedHomFinrank, Module.finrank_eq_zero_iff_of_free,
    Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
  rfl

/-- On the terms of a presilting differential, changing the differential can
only increase either shifted Hom dimension against a fixed complex. -/
theorem shiftedHomFinrank_le_of_rigid {X Y : FGModuleCat.{u} R}
    [Module.Projective R X] [Module.Projective R Y] {u σ : X ⟶ Y}
    (hu : (ofDifferential u).IsPresilting) (Q : TwoTerm R) :
    (ofDifferential u).shiftedHomFinrank k Q ≤ (ofDifferential σ).shiftedHomFinrank k Q ∧
      Q.shiftedHomFinrank k (ofDifferential u) ≤ Q.shiftedHomFinrank k (ofDifferential σ) := by
  have (M N : FGModuleCat.{u} R) : Module.Finite k (M ⟶ N) := finiteModuleHom_isFinite k M N
  have h := boundaryLinear_rank_le_at_rigid k u σ Q.differential
    ((isPresilting_iff_boundaryLinear_surjective (k := k) (ofDifferential u)).mp hu)
  change Module.finrank k ((X ⟶ Q.target) ⧸ (boundaryLinear k u Q.differential).range) ≤
      Module.finrank k ((X ⟶ Q.target) ⧸ (boundaryLinear k σ Q.differential).range) ∧
    Module.finrank k ((Q.source ⟶ Y) ⧸ (boundaryLinear k Q.differential u).range) ≤
      Module.finrank k ((Q.source ⟶ Y) ⧸ (boundaryLinear k Q.differential σ).range)
  have hdim {U V : Type u} [AddCommGroup U] [AddCommGroup V] [Module k U] [Module k V]
      [Module.Finite k V] (a b : U →ₗ[k] V)
      (hr : Module.finrank k b.range ≤ Module.finrank k a.range) :
      Module.finrank k (V ⧸ a.range) ≤ Module.finrank k (V ⧸ b.range) := by
    have ha := Submodule.finrank_quotient_add_finrank a.range
    have hb := Submodule.finrank_quotient_add_finrank b.range
    omega
  exact ⟨hdim _ _ h.1, hdim _ _ h.2⟩

end TwoTerm

end EFiniteCharacterizations
