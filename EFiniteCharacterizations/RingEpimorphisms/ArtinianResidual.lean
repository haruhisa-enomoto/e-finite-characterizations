module

public import EFiniteCharacterizations.RingEpimorphisms.FiniteDimensionalResidual
public import Mathlib.Algebra.Algebra.Prod

/-! # Finite-dimensional residual quotients of Artinian rings -/

@[expose] public section

universe u
namespace EFiniteCharacterizations

variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- The intersection of the kernels of finite-dimensional representations of
an Artinian algebra is already the kernel of one such representation. -/
theorem finite_quotient_residual_of_artinian [IsArtinianRing B] :
    Module.Finite k (B ⧸ finiteDimensionalResidual k B) := by
  classical
  let K : Set (Ideal B) := {I | ∃ (D : Type u) (_ : Ring D) (_ : Algebra k D)
    (_ : Module.Finite k D) (a : B →ₐ[k] D), RingHom.ker a.toRingHom = I}
  let π := Ideal.Quotient.mkₐ k (⊤ : Ideal B)
  have nonempty : K.Nonempty := ⟨_, _, inferInstance, inferInstance, inferInstance, π, rfl⟩
  obtain ⟨_, ⟨D, _, _, _, a, rfl⟩, hmin⟩ := wellFounded_lt.has_min K nonempty
  have eqn : RingHom.ker a.toRingHom = finiteDimensionalResidual k B := by
    apply le_antisymm
    · intro x hx E _ _ _ b
      let c := a.prod b
      have small : RingHom.ker c.toRingHom ≤ RingHom.ker a.toRingHom :=
        fun z hz ↦ congrArg Prod.fst (show c z = 0 from hz)
      have hm := hmin _ (show RingHom.ker c.toRingHom ∈ K from
        ⟨_, inferInstance, inferInstance, inferInstance, c, rfl⟩)
      exact congrArg Prod.snd (show c x = 0 from (le_of_eq (eq_of_le_of_not_lt small hm).symm) hx)
    · exact fun x hx ↦ hx D a
  have := Module.Finite.of_injective (Ideal.kerLiftAlg a).toLinearMap (Ideal.kerLiftAlg_injective a)
  rwa [← eqn]

end EFiniteCharacterizations
