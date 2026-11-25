module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The dimension difference of a linear map -/

@[expose] public section

open Module

namespace EFiniteCharacterizations

/-- The difference between the dimensions of the source and target is the
difference between the dimensions of the kernel and of the dual kernel. -/
theorem finrank_sub_eq_ker_sub_dualKer {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] (f : V →ₗ[k] W) :
    (finrank k V : ℤ) - finrank k W =
      (finrank k (LinearMap.ker f) : ℤ) - finrank k (LinearMap.ker f.dualMap) := by
  have h := f.finrank_range_add_finrank_ker
  have hd := f.dualMap.finrank_range_add_finrank_ker
  rw [f.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at hd
  omega

end EFiniteCharacterizations
