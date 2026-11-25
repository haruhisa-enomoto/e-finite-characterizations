module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Prod

/-! # Ring epimorphisms and restricted module maps -/

@[expose] public section

universe u

namespace EFiniteCharacterizations

variable {R B : Type u} [Ring R] [Ring B]

/-- Right cancellation against arbitrary unital ring homomorphisms. -/
def IsRingEpimorphism (f : R →+* B) : Prop :=
  ∀ (T : Type u) [Ring T] (g h : B →+* T), g.comp f = h.comp f → g = h

/-- Conjugating the action on a direct sum by a shear shows that maps
linear over the source of a ring epimorphism are linear over its target. -/
theorem IsRingEpimorphism.map_smul {f : R →+* B} (hf : IsRingEpimorphism f)
    {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] :
    letI := Module.compHom M f
    letI := Module.compHom N f
    ∀ (p : M →ₗ[R] N) (b : B) (x : M), p (b • x) = b • p x := by
  let := Module.compHom M f
  let := Module.compHom N f
  intro p b x
  let shear : (M × N) ≃ₗ[ℤ] (M × N) :=
    { toFun := fun (x,y) ↦ (x, y + p x)
      invFun := fun (x,y) ↦ (x, y - p x)
      left_inv := fun (x,y) ↦ by simp
      right_inv := fun (x,y) ↦ by simp
      map_add' := fun (x,y) (z,w) ↦ by simp [add_add_add_comm]
      map_smul' := fun r (x,y) ↦ by simp }
  let ρ : B →+* Module.End ℤ (M × N) := Module.toModuleEnd ℤ _
  have eqn := hf _ ((shear.conjRingEquiv.toRingHom).comp ρ) ρ (by
    apply RingHom.ext
    intro r
    apply LinearMap.ext
    intro v
    change (f r • v.1, f r • (v.2 - p v.1) + p (f r • v.1)) = _
    rw [show p (f r • v.1) = f r • p v.1 from p.map_smul r _, smul_sub, sub_add_cancel]
    rfl)
  have he := LinearMap.congr_fun (DFunLike.congr_fun eqn b) (x,0)
  have h := congrArg Prod.snd he
  change b • (0 - p x) + p (b • x) = b • (0 : N) at h
  apply sub_eq_zero.mp
  simpa [add_comm, ← sub_eq_add_neg] using h

/-- Fullness of restriction also implies cancellation of ring maps. -/
theorem isRingEpimorphism_of_map_smul (f : R →+* B)
    (h : ∀ (M N : Type u) [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N],
      letI := Module.compHom M f
      letI := Module.compHom N f
      ∀ (p : M →ₗ[R] N) (b : B) (x : M), p (b • x) = b • p x) : IsRingEpimorphism f := by
  intro T _ g g' he
  let M := (ModuleCat.restrictScalars g).obj (ModuleCat.of T T)
  let N := (ModuleCat.restrictScalars g').obj (ModuleCat.of T T)
  let := Module.compHom M f
  let := Module.compHom N f
  let p : M →ₗ[R] N :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change @HMul.hMul T T T _ (g (f r)) x = @HMul.hMul T T T _ (g' (f r)) x
        exact congrArg (fun t : T ↦ @HMul.hMul T T T _ t x) (DFunLike.congr_fun he r) }
  ext b
  have hb := h M N p b (1 : T)
  change g b * 1 = g' b * 1 at hb
  simpa using hb

theorem IsRingEpimorphism.op {f : R →+* B} (hf : IsRingEpimorphism f) :
    IsRingEpimorphism (RingHom.op f) := by
  intro T _ g h he
  let g' := (RingHom.op g).comp (RingEquiv.opOp B).toRingHom
  let h' := (RingHom.op h).comp (RingEquiv.opOp B).toRingHom
  have eqn := hf Tᵐᵒᵖ g' h' (RingHom.ext fun x ↦
    congrArg MulOpposite.op (DFunLike.congr_fun he (MulOpposite.op x)))
  exact RingHom.ext fun y ↦ MulOpposite.op_injective (DFunLike.congr_fun eqn y.unop)

/-- Central scalars of the source stay central in an epic target. -/
theorem IsRingEpimorphism.commutes {f : R →+* B} (hf : IsRingEpimorphism f)
    {c : R} (hc : ∀ r : R, c * r = r * c) (b : B) : f c * b = b * f c := by
  let := Module.compHom B f
  let p : B →ₗ[R] B :=
    { toFun := fun x ↦ f c * x
      map_add' := mul_add _
      map_smul' := fun r x ↦ by
        change f c * (f r * x) = f r * (f c * x)
        rw [← mul_assoc, ← mul_assoc, ← map_mul, hc, map_mul] }
  have he := hf.map_smul (M := B) (N := B) p b 1
  change f c * (b * 1) = b * (f c * 1) at he
  simpa using he

/-- The ground algebra structure on the target of an arbitrary ring epimorphism. -/
@[instance_reducible] def IsRingEpimorphism.targetAlgebra (k : Type u) [Field k] [Algebra k R]
    {f : R →+* B} (hf : IsRingEpimorphism f) : Algebra k B :=
  (f.comp (algebraMap k R)).toAlgebra' fun c ↦ hf.commutes (Algebra.commutes c)

end EFiniteCharacterizations
