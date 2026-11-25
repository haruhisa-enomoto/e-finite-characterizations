module

public import EFiniteCharacterizations.Modules.ProjectiveBiproducts
public import EFiniteCharacterizations.Presentations.ProjectiveHomWeight

/-! # The Euler pairing on the integral projective group -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

theorem Weight.ext_eval {a b : Weight (FGModuleCat.{u} R)}
    (h : ∀ M : FGModuleCat.{u} R, a.eval M = b.eval M) : a = b := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply AddMonoidHom.ext
  intro z
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp
  | of M => exact h M
  | neg M ih => simpa only [map_neg] using congrArg Neg.neg ih
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Maps out of a binary biproduct are pairs of maps from its summands. -/
noncomputable def homFromBiprodEquiv (P Q M : FGModuleCat.{u} R) :
    ((P ⊞ Q) ⟶ M) ≃ₗ[k] (P ⟶ M) × (Q ⟶ M) where
  toFun f := (biprod.inl ≫ f, biprod.inr ≫ f)
  invFun f := biprod.desc f.1 f.2
  left_inv f := biprod.hom_ext' _ _ (by simp) (by simp)
  right_inv f := Prod.ext (by simp) (by simp)
  map_add' f g := Prod.ext (Preadditive.comp_add _ _ _ _ _ _) (Preadditive.comp_add _ _ _ _ _ _)
  map_smul' a f := Prod.ext (Linear.comp_smul _ _ _ _ _ _) (Linear.comp_smul _ _ _ _ _ _)

include k in
/-- Pair a split projective class with the exact classes of modules. -/
noncomputable def projectiveClassWeight :
    ProjectiveClass R →+ Weight (FGModuleCat.{u} R) := by
  refine ProjectiveClass.lift (fun P ↦ let _ := P.property; projectiveHomWeight k P.val) ?_ ?_
  · intro P Q e
    let _ := P.property
    let _ := Q.property
    apply Weight.ext_eval
    intro M
    simp only [projectiveHomWeight_eval, homFinrank_eq_finrank]
    exact_mod_cast (Linear.homCongr k e (Iso.refl M)).finrank_eq
  · intro P Q T e
    let _ := P.property
    let _ := Q.property
    let _ := T.property
    let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
    let e' := F.preimageIso (e.trans (FGModuleCat.forgetBiprodIso P.val Q.val).symm)
    apply Weight.ext_eval
    intro M
    change (projectiveHomWeight k T.val).eval M =
      (projectiveHomWeight k P.val).eval M + (projectiveHomWeight k Q.val).eval M
    simp only [projectiveHomWeight_eval, homFinrank_eq_finrank, ← Nat.cast_add]
    have := finiteModuleHom_isFinite k P.val M
    have := finiteModuleHom_isFinite k Q.val M
    exact_mod_cast (Linear.homCongr k e' (Iso.refl M)).finrank_eq.trans
      ((homFromBiprodEquiv k P.val Q.val M).finrank_eq.trans Module.finrank_prod)

@[simp] theorem projectiveClassWeight_of (P : FiniteProjective R) :
    projectiveClassWeight k (ProjectiveClass.of P) =
      (letI := P.property; projectiveHomWeight k P.val) :=
  ProjectiveClass.lift_of _ _ _ P

theorem TwoTerm.projectiveClassWeight_eq_eulerWeight (P : TwoTerm R) :
    projectiveClassWeight k P.projectiveClass = P.eulerWeight k := by
  rw [TwoTerm.projectiveClass, map_sub, projectiveClassWeight_of, projectiveClassWeight_of]
  rfl

end EFiniteCharacterizations
