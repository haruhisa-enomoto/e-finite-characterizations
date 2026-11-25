module

public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar extension of a bilinear map -/

@[expose] public section

open scoped TensorProduct

namespace EFiniteCharacterizations

variable {k : Type*} [CommRing k] (S : Type*) [CommRing S] [Algebra k S]
  {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [Module k U] [Module k V] [Module k W]

/-- Extend a bilinear map to the tensor products with a commutative scalar algebra. -/
def baseChangeBilinear (f : U →ₗ[k] V →ₗ[k] W) :
    (S ⊗[k] U) →ₗ[S] (S ⊗[k] V) →ₗ[S] (S ⊗[k] W) :=
  ((LinearMap.baseChangeHom k S V W).comp f).liftBaseChange S

@[simp] theorem baseChangeBilinear_tmul (f : U →ₗ[k] V →ₗ[k] W) (r s : S) (u : U) (v : V) :
    baseChangeBilinear S f (r ⊗ₜ[k] u) (s ⊗ₜ[k] v) = (r * s) ⊗ₜ[k] f u v := by
  simp [baseChangeBilinear, LinearMap.liftBaseChange_tmul, TensorProduct.smul_tmul']

@[simp] theorem baseChangeBilinear_one_tmul_left (f : U →ₗ[k] V →ₗ[k] W)
    (u : U) (v : S ⊗[k] V) : baseChangeBilinear S f (1 ⊗ₜ[k] u) v = (f u).baseChange S v := by
  simp [baseChangeBilinear, LinearMap.liftBaseChange_tmul]

@[simp] theorem baseChangeBilinear_one_tmul_right (f : U →ₗ[k] V →ₗ[k] W)
    (u : S ⊗[k] U) (v : V) : baseChangeBilinear S f u (1 ⊗ₜ[k] v) = (f.flip v).baseChange S u := by
  refine TensorProduct.inductionOn u (fun r a ↦ by simp) ?_
  intro a b ha hb
  simp [ha, hb]

/-- Applying an algebra homomorphism to the coefficients commutes with an
extended bilinear map. -/
theorem map_baseChangeBilinear {T : Type*} [CommRing T] [Algebra k T]
    (e : S →ₐ[k] T) (f : U →ₗ[k] V →ₗ[k] W) (u : S ⊗[k] U) (v : S ⊗[k] V) :
    TensorProduct.map e.toLinearMap LinearMap.id (baseChangeBilinear S f u v) =
      baseChangeBilinear T f (TensorProduct.map e.toLinearMap LinearMap.id u)
        (TensorProduct.map e.toLinearMap LinearMap.id v) := by
  revert v
  refine TensorProduct.inductionOn u ?_ ?_
  · intro r a v
    refine TensorProduct.inductionOn v (fun s b ↦ by simp) ?_
    intro b b' hb hb'
    simp only [map_add, hb, hb']
  · intro a a' ha ha' v
    simp only [map_add, LinearMap.add_apply, ha v, ha' v]

end EFiniteCharacterizations
