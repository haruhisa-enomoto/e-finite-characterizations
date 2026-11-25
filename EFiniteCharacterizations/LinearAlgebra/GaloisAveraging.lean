module

public import EFiniteCharacterizations.LinearAlgebra.GaloisComponents

/-! # The linear component of the Galois decomposition -/

@[expose] public section
open Module
universe u
namespace EFiniteCharacterizations

variable {k F : Type u} [Field k] [Field F] [Algebra k F] [Module.Finite k F] [IsGalois k F]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι k F)

/-- The trace-dual Casimir element multiplies to one in the field. -/
theorem traceDual_mul_sum_one : ∑ j, b.traceDual j * b j = 1 := by
  classical
  let z (σ : Gal(F/k)) := ∑ j, σ (b.traceDual j) * b j
  have hz (σ : Gal(F/k)) : galoisComponent b (LinearMap.id : F →ₗ[k] F) σ 1 = z σ := by
    simp [galoisComponent,z,smul_eq_mul]
  have hv (σ : Gal(F/k)) (c : F) :
      galoisComponent b (LinearMap.id : F →ₗ[k] F) σ c = z σ * c := by
    simp [galoisComponent,z,smul_eq_mul,Finset.sum_mul,mul_assoc]
  have h0 (σ : Gal(F/k)) (hn : σ ≠ 1) : z σ = 0 := by
    by_contra hnz
    apply hn
    ext c
    have eq := galoisComponent_smul b (LinearMap.id : F →ₗ[k] F) σ c 1
    rw [hz,smul_eq_mul,mul_one,hv,smul_eq_mul,mul_comm (z σ)] at eq
    exact (mul_right_cancel₀ hnz eq).symm
  have h := sum_galoisComponent b (LinearMap.id : F →ₗ[k] F) 1
  simp_rw [hz] at h
  rw [Finset.sum_eq_single 1 (fun σ _ hn ↦ h0 _ hn) (by simp)] at h
  exact h

end EFiniteCharacterizations
