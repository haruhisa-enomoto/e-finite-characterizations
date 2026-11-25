module

public import EFiniteCharacterizations.DivisionRings.FreeTensorBoundary
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Detecting the tensor boundary by free-group coefficients -/

@[expose] public section

open scoped TensorProduct
open TensorProduct
namespace EFiniteCharacterizations
namespace FreeGroupCoefficients

variable {ι k : Type*} [Field k]

/-- Every labeling of the oriented generator edges of a free group is the
difference of a vertex function. Lift the translations with their increments
to permutations of the product of the group with the additive coefficient group. -/
private theorem exists_potential (b : ι → FreeGroup ι → k) :
    ∃ P : FreeGroup ι → k, ∀ i w, P (FreeGroup.of i * w) - P w = b i w := by
  let step (i : ι) : Equiv.Perm (FreeGroup ι × k) :=
    { toFun := fun z ↦ (FreeGroup.of i * z.1,z.2 + b i z.1)
      invFun := fun z ↦ ((FreeGroup.of i)⁻¹ * z.1,z.2 - b i ((FreeGroup.of i)⁻¹ * z.1))
      left_inv := fun z ↦ by simp
      right_inv := fun z ↦ by simp }
  let ρ := FreeGroup.lift step
  have pr (w : FreeGroup ι) (z : FreeGroup ι × k) : (ρ w z).1 = w*z.1 := by
    induction w generalizing z with
    | one => simp [ρ]
    | of i => simp [ρ,step]
    | inv_of i ih =>
      rw [map_inv]
      change ((ρ (FreeGroup.of i)).symm z).1 = _
      simp [ρ,step]
    | mul x y hx hy =>
      rw [map_mul]
      change (ρ x (ρ y z)).1 = _
      rw [hx,hy,mul_assoc]
  refine ⟨fun w ↦ (ρ w (1,0)).2,fun i w ↦ ?_⟩
  change (ρ (FreeGroup.of i * w) (1,0)).2 - _ = _
  rw [map_mul]
  change (ρ (FreeGroup.of i) (ρ w (1,0))).2 - _ = _
  rw [show ρ (FreeGroup.of i) = step i from FreeGroup.lift_apply_of]
  change _ + b i (ρ w (1,0)).1 - _ = _
  simp [pr]

/-- A finite flow on generator edges with zero boundary vanishes. -/
private theorem edge_flow_zero [Fintype ι] (s : ι → FreeGroup ι →₀ k)
    (hs : ∑ i, ((s i).mapDomain (FreeGroup.of i * ·) - s i) = 0) : ∀ i, s i = 0 := by
  classical
  intro j
  ext w
  let b (i : ι) (v : FreeGroup ι) : k := if i = j ∧ v = w then 1 else 0
  obtain ⟨P,hP⟩ := exists_potential b
  let L := Finsupp.linearCombination k P
  have step (i : ι) : L ((s i).mapDomain (FreeGroup.of i * ·) - s i) = (s i).sum (fun v a ↦ a * b i v) := by
    rw [map_sub]
    change (Finsupp.mapDomain _ _).sum _ - (s i).sum _ = _
    rw [Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ ↦ by simp [add_mul])]
    simp [Finsupp.sum,LinearMap.smulRight_apply,← Finset.sum_sub_distrib,← mul_sub,hP]
  have h := congrArg L hs
  rw [map_sum,map_zero] at h
  simp_rw [step] at h
  rw [Finset.sum_eq_single j] at h
  · by_cases hw : w ∈ (s j).support
    · simpa [b,Finsupp.sum,mul_ite,hw] using h
    · exact Finsupp.notMem_support_iff.mp hw
  · intro i _ hi
    simp [b,hi]
  · simp

variable {D : Type*} [DivisionRing D] [Algebra k D]

/-- A coefficient pairing on a tensor, evaluated independently on its two factors. -/
private def pair (c : FreeGroup ι → D →ₗ[k] k) (g h : FreeGroup ι) : D ⊗[k] D →ₗ[k] k :=
  TensorProduct.lift ((LinearMap.toSpanSingleton k (D →ₗ[k] k) (c h)).comp (c g))

private theorem pair_tmul (c : FreeGroup ι → D →ₗ[k] k) (g h : FreeGroup ι) (u v : D) :
    pair c g h (u ⊗ₜ[k] v) = c g u * c h v := rfl

/-- Coefficients separating each factor also separate tensors in the algebraic
tensor product. Only finite sums of pure tensors occur here. -/
private theorem tensor_eq_zero (c : FreeGroup ι → D →ₗ[k] k)
    (hc : ∀ u, (∀ g, c g u = 0) → u = 0) (t : D ⊗[k] D)
    (ht : ∀ g h, pair c g h t = 0) : t = 0 := by
  let B := Module.Free.chooseBasis k D
  let E := TensorProduct.equivFinsuppOfBasisRight (M := D) B
  let L (g : FreeGroup ι) := (TensorProduct.lid k D).toLinearMap.comp ((c g).rTensor D)
  have eval (g h : FreeGroup ι) (z : D ⊗[k] D) : c h (L g z) = pair c g h z := by
    induction z with
    | tmul u v => simp [L,pair_tmul]
    | add u v hu hv => simp [map_add,hu,hv]
  have zero (g : FreeGroup ι) : L g t = 0 := hc _ fun h ↦ (eval g h t).trans (ht g h)
  apply E.injective
  rw [map_zero]
  ext i
  apply hc
  intro g
  have swap (z : D ⊗[k] D) : c g (E z i) = B.coord i (L g z) := by
    induction z with
    | tmul u v =>
      simp [E,L,mul_comm]
    | add u v hu hv => simp [hu,hv]
  rw [swap,zero,map_zero]

variable (c : FreeGroup ι → D →ₗ[k] k)
    (hf : ∀ (z : FreeGroup ι) (u v : D), (fun w ↦ c (z*w⁻¹) u * c w v).HasFiniteSupport)

include hf

private theorem finite_slice (z : FreeGroup ι) (t : D ⊗[k] D) :
    (fun w ↦ pair c (z*w⁻¹) w t).HasFiniteSupport := by
  induction t with
  | tmul u v => exact hf z u v
  | add t s ht hs =>
    exact (ht.union hs).subset (fun w hw ↦ by
      contrapose! hw
      simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hw
      simp [Function.mem_support,hw.1,hw.2])

private noncomputable def slice (z : FreeGroup ι) : D ⊗[k] D →ₗ[k] (FreeGroup ι →₀ k) where
  toFun t := Finsupp.ofSupportFinite _ (finite_slice c hf z t)
  map_add' u v := Finsupp.ext fun w ↦ (pair c (z*w⁻¹) w).map_add u v
  map_smul' r u := Finsupp.ext fun w ↦ (pair c (z*w⁻¹) w).map_smul r u

/-- Suppose elements of D have separating free-group coefficients for which
products have finite supports on each multiplication fiber. If the designated
elements translate coefficients on the left and right, their tensor boundary
is injective. -/
theorem injective_boundary [Fintype ι] (a : ι → D)
    (hc : ∀ u, (∀ g, c g u = 0) → u = 0)
    (left : ∀ i w v, c w (a i * v) = c ((FreeGroup.of i)⁻¹ * w) v)
    (right : ∀ i w v, c w (v * a i) = c (w * (FreeGroup.of i)⁻¹) v) :
    Function.Injective (freeTensorBoundary k a) := by
  classical
  let L (i : ι) : Module.End D (D ⊗[k] D) := AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft k (a i))
  let R (i : ι) : Module.End D (D ⊗[k] D) := AlgebraTensorModule.map (LinearMap.toSpanSingleton D D (a i)) LinearMap.id
  have shift (z : FreeGroup ι) (i : ι) (t : D ⊗[k] D) :
      slice c hf z (L i t) = (slice c hf z (R i t)).mapDomain (FreeGroup.of i * ·) := by
    ext w
    change _ = Finsupp.mapDomain (Equiv.mulLeft (FreeGroup.of i)) _ w
    rw [Finsupp.mapDomain_equiv_apply (f := Equiv.mulLeft (FreeGroup.of i))]
    change pair c (z*w⁻¹) w (L i t) = pair c (z*((FreeGroup.of i)⁻¹*w)⁻¹) ((FreeGroup.of i)⁻¹*w) (R i t)
    induction t with
    | tmul u v =>
      change c _ u * c _ (a i * v) = c _ (u * a i) * c _ v
      rw [left,right]
      simp [mul_assoc]
    | add u v hu hv => simp [hu,hv]
  apply (injective_iff_map_eq_zero _).2
  intro t ht
  have flow (z : FreeGroup ι) : ∀ i, slice c hf z (R i (t i)) = 0 := by
    apply edge_flow_zero
    have e := congrArg (slice c hf z) ht
    rw [freeTensorBoundary,LinearMap.lsum_apply,LinearMap.sum_apply] at e
    change slice c hf z (∑ i, (L i (t i) - R i (t i))) = slice c hf z 0 at e
    simpa only [map_sum,map_sub,map_zero,shift] using e
  funext i
  apply tensor_eq_zero c hc
  intro g h
  let z := g * FreeGroup.of i * h
  have eq := DFunLike.congr_fun (flow z i) h
  change pair c (z*h⁻¹) h (R i (t i)) = 0 at eq
  have eta (u : D ⊗[k] D) : pair c (z*h⁻¹) h (R i u) = pair c g h u := by
    induction u with
    | tmul v w =>
      change c _ (v * a i) * c _ w = c _ v * c _ w
      simp [right,z,mul_assoc]
    | add v w hv hw => simp [hv,hw]
  rwa [eta] at eq

end FreeGroupCoefficients
end EFiniteCharacterizations
