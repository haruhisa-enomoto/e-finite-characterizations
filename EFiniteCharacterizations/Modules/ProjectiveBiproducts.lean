module

public import EFiniteCharacterizations.Presentations.ProjectiveClasses
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.Finiteness.Prod

/-! # Binary direct sums of finite projective modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

namespace FGModuleCat

variable {R : Type u} [Ring R]

instance : HasFiniteBiproducts (FGModuleCat.{u} R) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

noncomputable instance : HasBinaryBiproducts (FGModuleCat.{u} R) :=
  HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The forgetful functor preserves the chosen finite-module binary biproduct. -/
noncomputable def forgetBiprodIso (P Q : FGModuleCat.{u} R) :
    (P ⊞ Q : FGModuleCat.{u} R).obj ≅ P.obj ⊞ Q.obj := by
  let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact F.mapBiprod P Q

/-- A direct sum of finite projectives is projective. -/
theorem projective_biprod (P Q : FGModuleCat.{u} R) [Module.Projective R P] [Module.Projective R Q] :
    Module.Projective R (P ⊞ Q : FGModuleCat.{u} R) := by
  let e := (forgetBiprodIso P Q).trans (ModuleCat.biprodIsoProd P.obj Q.obj)
  exact Module.Projective.of_equiv' e.symm.toLinearEquiv

end FGModuleCat

namespace ProjectiveClass

variable {R : Type u} [Ring R]

/-- A zero finite projective module. -/
def zeroProjective (R : Type u) [Ring R] : FiniteProjective R :=
  ⟨FGModuleCat.of R PUnit, inferInstance⟩

/-- The finite projective obtained as the direct sum of two finite projectives. -/
noncomputable def biprod (P Q : FiniteProjective R) : FiniteProjective R :=
  let _ : Module.Projective R P.val := P.property
  let _ : Module.Projective R Q.val := Q.property
  ⟨P.val ⊞ Q.val, FGModuleCat.projective_biprod P.val Q.val⟩

@[simp] theorem of_biprod (P Q : FiniteProjective R) : of (biprod P Q) = of P + of Q :=
  of_eq_add_of_biprod P Q _ (FGModuleCat.forgetBiprodIso P.val Q.val)

end ProjectiveClass

end EFiniteCharacterizations
