/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
Ported from Tau Ceti (TauCeti.Algebra.Module.Opposite, commit 02160f039476c36211f34cf7cb338272193a0ab6, Apache 2.0).
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Tower

/-!
# Double opposite module structures

A left module is a module over the double opposite ring. The transport
respects the scalar tower and linear maps.
-/

public section

namespace EFiniteCharacterizations

open MulOpposite

section OpOp

/-- A left `A`-module, seen as a module over the double opposite `Aᵐᵒᵖᵐᵒᵖ`. -/
abbrev opOpModule (A N : Type*) [Semiring A] [AddCommMonoid N] [Module A N] : Module Aᵐᵒᵖᵐᵒᵖ N :=
  Module.compHom N (RingEquiv.opOp A).symm.toRingHom

attribute [local instance] opOpModule RingHomInvPair.of_ringEquiv

/-- The action of `Aᵐᵒᵖᵐᵒᵖ` on a left `A`-module is compatible with the action of the base. -/
theorem isScalarTower_opOpModule {R A N : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N] :
    IsScalarTower R Aᵐᵒᵖᵐᵒᵖ N :=
  IsScalarTower.of_algebraMap_smul fun r x => algebraMap_smul A r x

/-- A left `A`-module is semilinearly identified with itself over the double opposite `Aᵐᵒᵖᵐᵒᵖ`. -/
def opOpSemilinearEquiv {A N : Type*} [Semiring A] [AddCommMonoid N] [Module A N] :
    N ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A)] N :=
  { Equiv.refl N with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
theorem opOpSemilinearEquiv_apply {A N : Type*} [Semiring A] [AddCommMonoid N] [Module A N]
    (x : N) : opOpSemilinearEquiv (A := A) x = x :=
  (rfl)

@[simp]
theorem opOpSemilinearEquiv_symm_apply {A N : Type*} [Semiring A] [AddCommMonoid N] [Module A N]
    (x : N) : (opOpSemilinearEquiv (A := A)).symm x = x :=
  (rfl)

end OpOp

end EFiniteCharacterizations
