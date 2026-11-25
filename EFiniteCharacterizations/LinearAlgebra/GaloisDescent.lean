module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Descent of a vector space with a semilinear Galois action -/

@[expose] public section

open scoped BigOperators TensorProduct

namespace EFiniteCharacterizations.GaloisDescent

variable {k L V : Type*} [Field k] [Field L] [Algebra k L]
  [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
  (ρ : Gal(L/k) →* AddMonoid.End V)
  (hρ : ∀ σ : Gal(L/k), ∀ (a : L) (v : V), ρ σ (a • v) = σ a • ρ σ v)

/-- Vectors fixed by the semilinear action form a ground-field subspace. -/
def fixedSubmodule : Submodule k V where
  carrier := {v | ∀ σ, ρ σ v = v}
  zero_mem' := fun σ ↦ map_zero (ρ σ)
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  smul_mem' c v hv σ := by
    change ρ σ (c • v) = c • v
    rw [← algebraMap_smul L c v, hρ, AlgEquiv.commutes, hv σ]

variable [FiniteDimensional k L]

/-- The invariant vectors span the space after extending scalars. -/
theorem span_fixedSubmodule :
    Submodule.span L (fixedSubmodule ρ hρ : Set V) = ⊤ := by
  classical
  let _ := Fintype.ofFinite Gal(L/k)
  by_contra hn
  obtain ⟨f, hf, hvan⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hn)
  have hind : LinearIndependent L (fun σ : Gal(L/k) ↦ σ.toAlgHom.toLinearMap) :=
    (linearIndependent_algHom_toLinearMap k L L).comp _ AlgEquiv.coe_toAlgHom_injective
  apply hf
  ext v
  have hsum : ∀ a : L, ∑ σ : Gal(L/k), σ a * f (ρ σ v) = 0 := by
    intro a
    have hfixed : (∑ σ : Gal(L/k), ρ σ (a • v)) ∈ fixedSubmodule ρ hρ := by
      intro τ
      rw [map_sum]
      have hcomp (σ : Gal(L/k)) : ρ τ (ρ σ (a • v)) = ρ (τ * σ) (a • v) :=
        (DFunLike.congr_fun (map_mul ρ τ σ) (a • v)).symm
      simp only [hcomp]
      exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun _ ↦ rfl)
    have he := hvan (Submodule.subset_span hfixed)
    rw [LinearMap.mem_ker, map_sum] at he
    simpa only [hρ, map_smul, smul_eq_mul] using he
  have heq : ∑ σ : Gal(L/k), f (ρ σ v) • σ.toAlgHom.toLinearMap = 0 := by
    ext a
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, AlgHom.toLinearMap_apply,
      AlgEquiv.coe_toAlgHom, smul_eq_mul, mul_comm] using hsum a
  have h₁ := (Fintype.linearIndependent_iff.mp hind) _ heq 1
  simpa using h₁

variable [IsGalois k L] [FiniteDimensional L V]

/-- Base change of the fixed vectors recovers the original vector space. -/
theorem bijective_liftBaseChange_fixedSubmodule :
    Function.Bijective (LinearMap.liftBaseChange L (fixedSubmodule ρ hρ).subtype) := by
  classical
  let A := fixedSubmodule ρ hρ
  let b := Module.Basis.ofSpan (span_fixedSubmodule ρ hρ).ge
  let I := (linearIndepOn_empty L id).extend (Set.empty_subset (A : Set V))
  let _ : Fintype I := Fintype.ofFinite _
  have hb (σ : Gal(L/k)) (i : I) : ρ σ (b i) = b i :=
    Module.Basis.ofSpan_subset (span_fixedSubmodule ρ hρ).ge ⟨i, rfl⟩ σ
  let a (i : I) : A := ⟨b i, fun σ ↦ hb σ i⟩
  have hrepr (σ : Gal(L/k)) (v : V) (j : I) :
      b.equivFun (ρ σ v) j = σ (b.equivFun v j) := by
    have hs := congrArg (ρ σ) (b.sum_equivFun v)
    rw [map_sum] at hs
    simp only [hρ, hb] at hs
    have he := congrArg (fun x : V ↦ b.equivFun x j) hs
    rw [map_sum] at he
    simpa [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_apply] using he.symm
  have hspan : ⊤ ≤ Submodule.span k (Set.range a) := by
    intro v _
    have hc (i : I) : b.equivFun v.val i ∈ Set.range (algebraMap k L) :=
      (IsGalois.mem_range_algebraMap_iff_fixed _).2 (fun σ ↦ by rw [← hrepr, v.property σ])
    choose d hd using hc
    have hv : (∑ i, d i • a i) = v := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      calc
        ∑ i, ((d i • a i : A) : V) = ∑ i, b.equivFun v.val i • b i := by
          apply Finset.sum_congr rfl
          intro i _
          change d i • b i = b.equivFun v.val i • b i
          rw [← algebraMap_smul L (d i) (b i), hd]
        _ = v.val := b.sum_equivFun v.val
    rw [← hv]
    exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hind : LinearIndependent k a := by
    apply (A.subtype.linearIndependent_iff (Submodule.ker_subtype A)).1
    exact b.linearIndependent.restrict_scalars' k
  let bA : Module.Basis I k A := Module.Basis.mk hind hspan
  let e := LinearMap.liftBaseChange L A.subtype
  have he : e = ((bA.baseChange L).equivFun.trans b.equivFun.symm).toLinearMap := by
    apply (bA.baseChange L).ext
    intro i
    rw [Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul, one_smul]
    change (bA i : V) = b.equivFun.symm ((bA.baseChange L).equivFun ((1 : L) ⊗ₜ[k] bA i))
    rw [← Module.Basis.baseChange_apply]
    have hbase : (bA i : V) = b i := congrArg Subtype.val (Module.Basis.mk_apply hind hspan i)
    rw [hbase]
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext j
    rw [Module.Basis.equivFun_self, Module.Basis.equivFun_self]
  change Function.Bijective e
  rw [he]
  exact LinearEquiv.bijective _

end EFiniteCharacterizations.GaloisDescent
