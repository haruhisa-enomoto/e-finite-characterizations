module

public import EFiniteCharacterizations.LinearAlgebra.DimensionDefect
public import EFiniteCharacterizations.Presentations.HomKernels
public import EFiniteCharacterizations.Presentations.NakayamaPairing
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! # The Euler identity for two-term projective complexes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

/-- The dual kernel of the Hom differential consists of the maps to the Nakayama kernel. -/
noncomputable def dualKerEquiv (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    LinearMap.ker (Linear.leftComp k M P.differential).dualMap ≃ₗ[k]
      (M ⟶ P.nakayamaKernel k) := by
  have : Module.Projective R P.source := P.projective_source
  have : Module.Projective R P.target := P.projective_target
  let e := nakayamaPairing k P.source M
  let n := nakayamaMorphism k P.differential
  let K := LinearMap.ker (Linear.rightComp k M n)
  have h : LinearMap.ker (Linear.leftComp k M P.differential).dualMap =
      K.comap e.toLinearMap := by
    ext χ
    change (Linear.leftComp k M P.differential).dualMap χ = 0 ↔ e χ ≫ n = 0
    rw [← nakayamaPairing_dual_leftComp k P.differential χ]
    exact ⟨fun hχ ↦ by rw [hχ, map_zero],
      fun hχ ↦ (nakayamaPairing k P.target M).injective (hχ.trans (map_zero _).symm)⟩
  exact (LinearEquiv.ofEq _ _ h).trans
    ((e.ofSubmodule' K).trans (homKernelLinearEquiv k n M).symm)

/-- Evaluate a projective differential by the difference of its two Hom dimensions. -/
theorem euler_eq_hom_difference (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    (homFinrank k P.target M : ℤ) - homFinrank k P.source M =
      (homFinrank k (cokernel P.differential) M : ℤ) - homFinrank k M (P.nakayamaKernel k) := by
  have := finiteModuleHom_isFinite k P.target M
  have := finiteModuleHom_isFinite k P.source M
  simp only [homFinrank_eq_finrank]
  rw [finrank_sub_eq_ker_sub_dualKer (Linear.leftComp k M P.differential),
    ← (cokernelHomLinearEquiv k P.differential M).finrank_eq,
    (P.dualKerEquiv k M).finrank_eq]

end EFiniteCharacterizations.TwoTerm
