module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.AlgebraTower

/-! # Iterating compatible semilinear maps after field extension -/

@[expose] public section

open scoped TensorProduct

namespace EFiniteCharacterizations

variable {k E L V : Type*} [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra k L] [Algebra E L] [IsScalarTower k E L]
  [AddCommGroup V] [Module k V]

/-- If the original semilinear map and the larger field automorphism both
have period dividing `n`, then the extended semilinear map does too. -/
theorem semilinear_pow_eq_one_of_compatible (σ : L ≃ₐ[k] L)
    (t : AddMonoid.End (E ⊗[k] V)) (u : AddMonoid.End (L ⊗[k] V))
    (hs : ∀ (c : L) (z : L ⊗[k] V), u (c • z) = σ c • u z)
    (hc : ∀ z : E ⊗[k] V,
      u (TensorProduct.map (IsScalarTower.toAlgHom k E L).toLinearMap LinearMap.id z) =
        TensorProduct.map (IsScalarTower.toAlgHom k E L).toLinearMap LinearMap.id (t z))
    {n : ℕ} (ht : t ^ n = 1) (hσ : σ ^ n = 1) : u ^ n = 1 := by
  let i : E ⊗[k] V →ₗ[k] L ⊗[k] V :=
    TensorProduct.map (IsScalarTower.toAlgHom k E L).toLinearMap LinearMap.id
  have hι (c : L) (v : V) : c • i ((1 : E) ⊗ₜ[k] v) = c ⊗ₜ[k] v := by
    change c • TensorProduct.map (IsScalarTower.toAlgHom k E L).toLinearMap LinearMap.id
      ((1 : E) ⊗ₜ[k] v) = _
    rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hp (c : L) (v : V) (m : ℕ) :
      (u ^ m) (c ⊗ₜ[k] v) = (σ ^ m) c • i ((t ^ m) ((1 : E) ⊗ₜ[k] v)) := by
    induction m with
    | zero =>
      simp only [pow_zero]
      exact (hι c v).symm
    | succ m ih =>
      rw [pow_succ', pow_succ', pow_succ']
      change u ((u ^ m) (c ⊗ₜ[k] v)) =
        σ ((σ ^ m) c) • i (t ((t ^ m) ((1 : E) ⊗ₜ[k] v)))
      rw [ih, hs, hc]
  have h (z : L ⊗[k] V) : (u ^ n) z = z := by
    refine TensorProduct.inductionOn (motive := fun z ↦ (u ^ n) z = z) z ?_ ?_
    · intro c v
      refine (hp c v n).trans ?_
      rw [ht, hσ]
      exact hι c v
    · intro z w hz hw
      exact ((u ^ n).map_add z w).trans (congrArg₂ (· + ·) hz hw)
  exact AddMonoidHom.ext h

end EFiniteCharacterizations
