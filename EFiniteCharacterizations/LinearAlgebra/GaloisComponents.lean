module

public import Mathlib.RingTheory.Trace.Basic

/-! # Semilinear components of a ground-linear map over a Galois extension -/

@[expose] public section
open Module
universe u
namespace EFiniteCharacterizations

variable {k F : Type u} [Field k] [Field F] [Algebra k F] [Module.Finite k F] [IsGalois k F]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι k F)
  {U V : Type*} [AddCommGroup U] [AddCommGroup V] [Module k U] [Module k V]
  [Module F U] [Module F V] [IsScalarTower k F U] [IsScalarTower k F V]

/-- Projection onto the component transforming by a fixed automorphism. -/
noncomputable def galoisComponent (f : U →ₗ[k] V) (σ : Gal(F/k)) (x : U) : V :=
  ∑ i, σ (b.traceDual i) • f ((b i) • x)

private theorem repr_by_trace (c : F) (j : ι) : b.repr c j = Algebra.trace k F (c * b.traceDual j) := by
  have h := b.traceDual.traceDual_repr_apply c j
  simpa only [Basis.traceDual_traceDual,Algebra.traceForm_apply] using h

private theorem traceDual_mul (c : F) (j : ι) :
    ∑ i, b.repr (b i * c) j • b.traceDual i = c * b.traceDual j := by
  calc
    _ = ∑ i, b.traceDual.repr (c * b.traceDual j) i • b.traceDual i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [repr_by_trace,Basis.traceDual_repr_apply,Algebra.traceForm_apply,
        show b i * c * b.traceDual j = c * b.traceDual j * b i by ac_rfl]
    _ = _ := b.traceDual.sum_repr _

theorem galoisComponent_smul (f : U →ₗ[k] V) (σ : Gal(F/k)) (c : F) (x : U) :
    galoisComponent b f σ (c • x) = σ c • galoisComponent b f σ x := by
  classical
  have expand (v : F) : f (v • x) = ∑ j, b.repr v j • f ((b j) • x) := by
    conv_lhs => rw [← b.sum_repr v,Finset.sum_smul,map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_assoc,map_smul]
  unfold galoisComponent
  simp only [← mul_smul,Finset.smul_sum]
  conv_lhs => arg 2; ext i; rw [expand,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (∑ i, σ (b.repr (b i * c) j • b.traceDual i)) • f ((b j) • x) := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      let a := b.repr (b i * c) j
      rw [show σ (a • b.traceDual i) = a • σ (b.traceDual i) from σ.toLinearEquiv.map_smul a _,smul_assoc,smul_comm (σ _)]
    _ = _ := by rw [← map_sum,traceDual_mul,map_mul,mul_smul]

/-- Summing the semilinear components recovers the original map. -/
theorem sum_galoisComponent (f : U →ₗ[k] V) (x : U) :
    ∑ σ : Gal(F/k), galoisComponent b f σ x = f x := by
  classical
  simp only [galoisComponent]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, b.repr 1 i • f ((b i) • x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_smul,← trace_eq_sum_automorphisms,algebraMap_smul,repr_by_trace,one_mul]
    _ = f x := by
      simp_rw [← map_smul,← smul_assoc]
      rw [← map_sum,← Finset.sum_smul,b.sum_repr,one_smul]

end EFiniteCharacterizations
