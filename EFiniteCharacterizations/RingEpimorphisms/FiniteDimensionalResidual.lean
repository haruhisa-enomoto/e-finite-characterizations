module

public import EFiniteCharacterizations.RingEpimorphisms.ResiduallyFiniteTargets
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The quotient detected by finite-dimensional representations -/

@[expose] public section
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] (B : Type u) [Ring B] [Algebra k B]

/-- The intersection of the kernels of maps into finite-dimensional algebras. -/
def finiteDimensionalResidual : Ideal B where
  carrier := {b | ∀ (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] (f : B →ₐ[k] A), f b = 0}
  zero_mem' := fun _ _ _ _ f ↦ f.map_zero
  add_mem' := fun hx hy _ _ _ _ f ↦ by rw [map_add,hx _ f,hy _ f,zero_add]
  smul_mem' := fun b a ha _ _ _ _ f ↦ by change f (b*a) = 0; rw [map_mul,ha _ f,mul_zero]

instance : (finiteDimensionalResidual k B).IsTwoSided where
  mul_mem_of_left a hx := fun _ _ _ _ f ↦ by rw [map_mul,hx _ f,zero_mul]

/-- Equivalently, the residual ideal is the common annihilator of all
finite-dimensional modules. -/
theorem mem_finiteDimensionalResidual_iff (b : B) : b ∈ finiteDimensionalResidual k B ↔
    ∀ M : ModuleCat.{u} B, Module.Finite k M → ∀ x : M, b • x = 0 := by
  constructor
  · intro h M fin x
    exact DFunLike.congr_fun (h (Module.End k M) (Algebra.lsmul k k M)) x
  · intro h A _ _ _ f
    let N := (ModuleCat.restrictScalars f.toRingHom).obj (ModuleCat.of A A)
    let e : N ≃ₗ[k] A :=
      { toEquiv := Equiv.refl _
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun c x ↦ by
          change f (algebraMap k B c) * (show A from x) = c • (show A from x)
          rw [f.commutes,Algebra.smul_def] }
    simpa only [mul_one] using (show f b * 1 = 0 from h N (Module.Finite.equiv e.symm) (1 : A))

/-- Passing to the opposite ring identifies the residual ideals. -/
theorem op_mem_finiteDimensionalResidual_iff (b : B) :
    MulOpposite.op b ∈ finiteDimensionalResidual k Bᵐᵒᵖ ↔ b ∈ finiteDimensionalResidual k B := by
  constructor
  · intro h A _ _ _ f
    exact congrArg MulOpposite.unop (h Aᵐᵒᵖ (AlgHom.op f))
  · intro h A _ _ _ f
    exact congrArg MulOpposite.unop (h Aᵐᵒᵖ ((AlgHom.op f).comp (AlgEquiv.opOp k B).toAlgHom))

/-- Finite-dimensional left and right modules detect the same elements. -/
theorem residuallyFiniteDimensional_iff_opposite :
    IsResiduallyFiniteDimensional k B ↔ IsResiduallyFiniteDimensional k Bᵐᵒᵖ := by
  simp only [IsResiduallyFiniteDimensional, ← mem_finiteDimensionalResidual_iff]
  constructor
  · intro h b hb
    exact congrArg MulOpposite.op (h b.unop ((op_mem_finiteDimensionalResidual_iff k B b.unop).1 hb))
  · intro h b hb
    exact congrArg MulOpposite.unop (h (MulOpposite.op b) ((op_mem_finiteDimensionalResidual_iff k B b).2 hb))

theorem quotient_residuallyFiniteDimensional :
    IsResiduallyFiniteDimensional k (B ⧸ finiteDimensionalResidual k B) := by
  let I := finiteDimensionalResidual k B
  intro z hz
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective k I z
  apply (Ideal.Quotient.eq_zero_iff_mem).2
  intro A _ _ _ f
  let g := Ideal.Quotient.liftₐ I f (fun x hx ↦ hx A f)
  exact ((mem_finiteDimensionalResidual_iff k _ _).2 hz) A g

/-- A representation with finite-dimensional image factors through the residual quotient. -/
noncomputable def liftFiniteImage {C : Type u} [Ring C] [Algebra k C] (f : B →ₐ[k] C)
    [Module.Finite k f.range] : (B ⧸ finiteDimensionalResidual k B) →ₐ[k] C :=
  Ideal.Quotient.liftₐ _ f fun x hx ↦ congrArg Subtype.val (hx f.range f.rangeRestrict)

end EFiniteCharacterizations
