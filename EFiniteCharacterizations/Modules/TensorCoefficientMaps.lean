module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic

/-! # Coefficients of maps between tensor products with a vector space -/

@[expose] public section

open scoped TensorProduct
open TensorProduct

universe u
namespace EFiniteCharacterizations

noncomputable section

variable {k R D : Type u} [Field k] [Ring R] [Algebra k R] [AddCommGroup D] [Module k D]
variable {I J : Type u} [AddCommGroup I] [Module k I] [Module R I] [IsScalarTower k R I]
  [AddCommGroup J] [Module k J] [Module R J] [IsScalarTower k R J]

/-- Coordinates in the vector-space factor, linear over the ground algebra. -/
def tensorCoordinates {ι : Type u} [DecidableEq ι] (e : Module.Basis ι k D) :
    J ⊗[k] D ≃ₗ[R] ι →₀ J :=
  (AlgebraTensorModule.congr (.refl R J) e.repr).trans (finsuppScalarRight k R J ι)

private theorem tensorCoordinates_tmul {ι : Type u} [DecidableEq ι] (e : Module.Basis ι k D)
    (y : J) (v : D) (i : ι) : tensorCoordinates (R := R) e (y ⊗ₜ[k] v) i = e.repr v i • y := by
  simp [tensorCoordinates]

/-- Tensoring an injective module with a vector space preserves injectivity
over a Noetherian algebra, even for an infinite-dimensional vector space. -/
theorem injective_tensor_vectorSpace [IsNoetherianRing R] (inj : Module.Injective R J) :
    Module.Injective R (J ⊗[k] D) := by
  classical
  let e := Module.Free.chooseBasis k D
  let coord := tensorCoordinates (R := R) (J := J) e
  apply Module.Baer.injective
  apply Module.Baer.of_equiv coord.symm
  intro L f
  obtain ⟨c,hc⟩ := (LinearMap.finsuppLinearMap_bijective_of_moduleFinite R L J _ k).2 f
  choose lift hlift using fun i ↦ Module.Baer.of_injective inj L (c i)
  refine ⟨∑ i ∈ c.support, (Finsupp.lsingle i).comp (lift i),fun x hx ↦ ?_⟩
  ext i
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    Finsupp.finsetSum_apply, hlift _ x hx]
  rw [← hc]
  by_cases hi : i ∈ c.support
  · simp [Finsupp.single_apply,hi]
  · simp [Finsupp.single_apply,hi,Finsupp.notMem_support_iff.mp hi]

/-- Hom out of a finitely generated module commutes with tensoring its target
by a ground vector space. -/
def tensorHomAddEquiv [Module.Finite R I] :
    ((I →ₗ[R] J) ⊗[k] D) ≃+ (I →ₗ[R] J ⊗[k] D) := by
  classical
  let e := Module.Free.chooseBasis k D
  let c := tensorCoordinates (R := R) (J := J) e
  let coeff := LinearEquiv.ofBijective (LinearMap.finsuppLinearMap k)
    (LinearMap.finsuppLinearMap_bijective_of_moduleFinite R I J (Module.Free.ChooseBasisIndex k D) k)
  exact (tensorCoordinates (R := k) (J := I →ₗ[R] J) e).toAddEquiv.trans
    (coeff.toAddEquiv.trans (LinearEquiv.arrowCongrAddEquiv (.refl R I) c.symm))

omit [Module k I] [IsScalarTower k R I] in
@[simp] theorem tensorHomAddEquiv_tmul [Module.Finite R I] (f : I →ₗ[R] J) (v : D) (x : I) :
    tensorHomAddEquiv (k := k) (f ⊗ₜ[k] v) x = f x ⊗ₜ[k] v := by
  classical
  let e := Module.Free.chooseBasis k D
  apply (tensorCoordinates (R := R) (J := J) e).injective
  ext i
  change tensorCoordinates (R := R) e ((tensorCoordinates (R := R) e).symm _) i = _
  rw [LinearEquiv.apply_symm_apply,tensorCoordinates_tmul]
  change (tensorCoordinates (R := k) e (f ⊗ₜ[k] v) i) x = _
  rw [tensorCoordinates_tmul]
  rfl

/-- A map between tensor products of finite modules with an arbitrary vector space
expands in a basis of ground module maps, with linear operators as coefficients. -/
theorem exists_tensor_operator_coefficients [Module.Finite R I] {n : Type u} [Fintype n]
    (h : Module.Basis n k (I →ₗ[R] J)) (f : I ⊗[k] D →ₗ[R] J ⊗[k] D) :
    ∃ b : n → Module.End k D, ∀ x v, f (x ⊗ₜ[k] v) = ∑ j, h j x ⊗ₜ[k] b j v := by
  classical
  let e := Module.Free.chooseBasis k D
  let coord := tensorCoordinates (R := R) (J := J) e
  let coeff := LinearEquiv.ofBijective (LinearMap.finsuppLinearMap k)
    (LinearMap.finsuppLinearMap_bijective_of_moduleFinite R I J (Module.Free.ChooseBasisIndex k D) k)
  let column (v : D) : I →ₗ[R] _ :=
    coord.toLinearMap.comp (f.comp ((AlgebraTensorModule.mk k R I D).flip v))
  let q : D →ₗ[k] _ :=
    { toFun := fun v ↦ coeff.symm (column v)
      map_add' := fun v w ↦ by apply coeff.injective; ext x; simp [column]
      map_smul' := fun c v ↦ by
        apply coeff.injective
        ext x i
        simp [column]
        exact congrArg (fun z ↦ z i) ((coord.restrictScalars k).map_smul c _) }
  let b (j : n) : Module.End k D :=
    e.repr.symm.toLinearMap.comp ((Finsupp.mapRange.linearMap (h.coord j)).comp q)
  refine ⟨b,fun x v ↦ ?_⟩
  apply coord.injective
  ext i
  have hc : LinearMap.finsuppLinearMap k (q v) = column v := coeff.apply_symm_apply _
  have hv := congrArg (fun t : I →ₗ[R] _ ↦ (t x) i) hc
  change (q v i) x = coord (f (x ⊗ₜ[k] v)) i at hv
  rw [map_sum,Finsupp.finsetSum_apply,← hv]
  simp only [coord,tensorCoordinates_tmul]
  have hb (j : n) : e.repr (b j v) i = h.repr (q v i) j := by simp [b,Module.Basis.coord_apply]
  simp_rw [hb]
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply] using (congrArg (fun t : I →ₗ[R] J ↦ t x) (h.sum_repr (q v i))).symm

end
end EFiniteCharacterizations
