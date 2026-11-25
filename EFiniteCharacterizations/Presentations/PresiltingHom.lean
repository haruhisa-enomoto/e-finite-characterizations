module

public import EFiniteCharacterizations.Modules.FiniteModuleMorphisms
public import EFiniteCharacterizations.Presentations.Cokernel
public import EFiniteCharacterizations.Presentations.TwoTermEuler
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The Hom criterion for two-term presilting complexes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- A map from a projective into the middle term of an exact pair lifts
along the first map if its composite with the second map is zero. -/
theorem exists_lift_of_exact {X A B C : FGModuleCat.{u} R} [Module.Projective R X]
    {f : A ⟶ B} {g : B ⟶ C} (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).Exact) (v : X ⟶ B) (hv : v ≫ g = 0) :
    ∃ a : X ⟶ A, a ≫ f = v := by
  let S := ShortComplex.mk f g hfg
  let w := S.liftCycles v hv
  have : Epi S.toCycles := h.epi_toCycles
  obtain ⟨a, ha⟩ := FGModuleCat.exists_lift_of_projective S.toCycles w
  refine ⟨a, ?_⟩
  change a ≫ S.f = v
  rw [← S.toCycles_i, ← Category.assoc, ha, S.liftCycles_i]

/-- For two projective differentials, the degree-one homotopy boundary is
surjective exactly when precomposition into the second cokernel is surjective. -/
theorem surjective_boundary_iff_surjective_precompose (P Q : TwoTerm R) :
    Function.Surjective (homotopyBoundary P Q) ↔ Function.Surjective (P.precompose (cokernel Q.differential)) := by
  let _ := P.projective_source
  let _ := P.projective_target
  let q := cokernel.π Q.differential
  constructor
  · intro h f
    obtain ⟨w, hw⟩ := FGModuleCat.exists_lift_of_projective q f
    obtain ⟨⟨a, b⟩, hab⟩ := h w
    refine ⟨-(b ≫ q), ?_⟩
    have hc : Q.differential ≫ q = 0 := cokernel.condition _
    change a ≫ Q.differential - P.differential ≫ b = w at hab
    rw [← hw, ← hab, Preadditive.sub_comp, Category.assoc a, hc, comp_zero, zero_sub,
      Category.assoc]
    change P.differential ≫ (-(b ≫ q)) = -(P.differential ≫ b ≫ q)
    exact Preadditive.comp_neg _ _
  · intro h w
    obtain ⟨c, hc⟩ := h (w ≫ q)
    obtain ⟨b, hb⟩ := FGModuleCat.exists_lift_of_projective q c
    have hv : (w - P.differential ≫ b) ≫ q = 0 := by
      change P.differential ≫ c = w ≫ q at hc
      rw [Preadditive.sub_comp, Category.assoc, hb, hc, sub_self]
    obtain ⟨a, ha⟩ := exists_lift_of_exact (cokernel.condition Q.differential)
      (ShortComplex.exact_cokernel Q.differential) _ hv
    refine ⟨(a, -b), ?_⟩
    change a ≫ Q.differential - P.differential ≫ (-b) = w
    rw [ha, Preadditive.comp_neg, sub_neg_eq_add, sub_add_cancel]

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- The Nakayama kernel represents the obstruction to surjectivity on Hom. -/
theorem surjective_precompose_iff_no_hom_nakayamaKernel (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    Function.Surjective (P.precompose M) ↔ Subsingleton (M ⟶ P.nakayamaKernel k) := by
  change Function.Surjective (Linear.leftComp k M P.differential) ↔ _
  rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (P.dualKerEquiv k M).toEquiv.subsingleton_congr

include k in
/-- A two-term projective complex is presilting precisely when the Hom
from its cokernel to its Nakayama kernel vanishes. -/
theorem isPresilting_iff_no_hom_nakayamaKernel (P : TwoTerm R) :
    P.IsPresilting ↔ Subsingleton (cokernel P.differential ⟶ P.nakayamaKernel k) :=
  (surjective_boundary_iff_surjective_precompose P P).trans
    (surjective_precompose_iff_no_hom_nakayamaKernel k P _)

end EFiniteCharacterizations.TwoTerm
