module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionHom
public import EFiniteCharacterizations.Presentations.IntegralEulerWeights
public import Mathlib.RingTheory.TensorProduct.Free

/-! # The Euler pairing under a finite extension of the ground field -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F]

local notation "R₊" => ExtendedAlgebra k F R

/-- The extension field action on an extended module is the tensor-product
vector space action. -/
def extendVectorSpaceEquiv (M : FGModuleCat.{u} R) :
    (extendObj k F R M).obj ≃ₗ[F] (F ⊗[k] (M.obj : Type u)) where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl
  map_smul' c z := congrArg (fun g : Module.End F (F ⊗[k] (M.obj : Type u)) ↦ g z)
    ((representation k F R M).commutes c)

omit [Module.Finite k F] in
/-- Field extension preserves dimension when the scalar field changes. -/
theorem finrank_extendObj (M : FGModuleCat.{u} R) :
    Module.finrank F ((extendObj k F R M).obj : Type u) = Module.finrank k (M.obj : Type u) := by
  let _ : Module.Finite k (M.obj : Type u) := Module.Finite.trans R _
  let b := Module.finBasis k (M.obj : Type u)
  exact (extendVectorSpaceEquiv k F R M).finrank_eq.trans
    ((Module.finrank_eq_card_basis (Algebra.TensorProduct.basis F b)).trans (Fintype.card_fin _))

/-- The ground dimension of a restricted module is its dimension over the
extension multiplied by the extension degree. -/
theorem finrank_restrictObj (M : FGModuleCat.{u} R₊) :
    Module.finrank k ((restrictObj k F R M).obj : Type u) =
      Module.finrank k F * Module.finrank F (M.obj : Type u) := by
  let _ := isScalarTower_ground_extension k F R M.obj
  exact (restrictVectorSpaceEquiv k F R M.obj).finrank_eq.trans
    (Module.finrank_mul_finrank k F (M.obj : Type u)).symm

/-- Scalar restriction multiplies the dimension of the adjoint Hom space
by the degree of the field extension. -/
theorem homFinrank_restrictObj (P : FGModuleCat.{u} R) (M : FGModuleCat.{u} R₊) :
    homFinrank k P (restrictObj k F R M) =
      Module.finrank k F * homFinrank F (extendObj k F R P) M := by
  let X := extendObj k F R P
  change homFinrank k P (restrictObj k F R M) =
    Module.finrank k F * homFinrank F X M
  let _ := isScalarTower_ground_extension_hom k F R X M
  rw [homFinrank_eq_finrank, homFinrank_eq_finrank, Module.finrank_mul_finrank k F (X ⟶ M)]
  exact (homLinearEquiv k F R P M).finrank_eq.symm

/-- Extending a two-term projective complex extends its two terms and differential. -/
def extendTwoTerm (P : TwoTerm R) : TwoTerm R₊ where
  source := extendObj k F R P.source
  target := extendObj k F R P.target
  projective_source := let _ := P.projective_source; projective_extendObj k F R P.source
  projective_target := let _ := P.projective_target; projective_extendObj k F R P.target
  differential := extendMap k F R P.differential

variable [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k F R)]

/-- Evaluation on a restricted module equals evaluation at the extended
Euler weight, multiplied by the degree. -/
theorem eulerWeight_eval_restrictObj (P : TwoTerm R) (M : FGModuleCat.{u} R₊) :
    (P.eulerWeight k).eval (restrictObj k F R M) =
      (Module.finrank k F : ℤ) * ((extendTwoTerm k F R P).eulerWeight F).eval M := by
  rw [TwoTerm.eulerWeight_eval, TwoTerm.eulerWeight_eval, homFinrank_restrictObj, homFinrank_restrictObj]
  change (↑(Module.finrank k F * homFinrank F (extendObj k F R P.target) M) : ℤ) -
    ↑(Module.finrank k F * homFinrank F (extendObj k F R P.source) M) =
    (Module.finrank k F : ℤ) * ((homFinrank F (extendObj k F R P.target) M : ℤ) -
      homFinrank F (extendObj k F R P.source) M)
  simp only [Nat.cast_mul, mul_sub]

/-- A linear combination of an Euler weight and ground dimension extends
with the same coefficients when it has a projective representative. -/
theorem eulerWeight_extend_eq_of_eulerWeight_eq (P Q : TwoTerm R) (a b : ℤ)
    (h : Q.eulerWeight k = a • P.eulerWeight k - b • dimensionWeight (R := R) k) :
    (extendTwoTerm k F R Q).eulerWeight F =
      a • (extendTwoTerm k F R P).eulerWeight F - b • dimensionWeight (R := R₊) F := by
  apply Weight.ext_eval
  intro M
  let d := (Module.finrank k F : ℤ)
  have hd : d ≠ 0 := Int.natCast_ne_zero.mpr (Nat.ne_of_gt Module.finrank_pos)
  have hdim : (dimensionWeight (R := R) k).eval (restrictObj k F R M) =
      d * (dimensionWeight (R := R₊) F).eval M := by
    rw [dimensionWeight_eval, dimensionWeight_eval, finrank_restrictObj k F R M, Nat.cast_mul]
  apply mul_left_cancel₀ hd
  calc
    d * ((extendTwoTerm k F R Q).eulerWeight F).eval M =
        (Q.eulerWeight k).eval (restrictObj k F R M) := (eulerWeight_eval_restrictObj k F R Q M).symm
    _ = (a • P.eulerWeight k - b • dimensionWeight (R := R) k).eval (restrictObj k F R M) :=
      congrArg (fun w : Weight (FGModuleCat.{u} R) ↦ w.eval (restrictObj k F R M)) h
    _ = d * (a • (extendTwoTerm k F R P).eulerWeight F -
        b • dimensionWeight (R := R₊) F).eval M := by
      simp only [Weight.eval, AddMonoidHom.sub_apply, AddMonoidHom.zsmul_apply, zsmul_eq_mul, Int.cast_id]
      change a * (P.eulerWeight k).eval (restrictObj k F R M) -
        b * (dimensionWeight (R := R) k).eval (restrictObj k F R M) =
        d * (a * ((extendTwoTerm k F R P).eulerWeight F).eval M -
          b * (dimensionWeight (R := R₊) F).eval M)
      rw [eulerWeight_eval_restrictObj k F R P M, hdim]
      ring

end

end EFiniteCharacterizations.FieldExtension
