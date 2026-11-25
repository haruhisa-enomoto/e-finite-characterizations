module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Pi

/-! # The tensor boundary for a family of elements of a division ring -/

@[expose] public section

open scoped TensorProduct
open TensorProduct

namespace EFiniteCharacterizations

variable (k : Type*) [Field k] {D ι : Type*} [DivisionRing D] [Algebra k D] [Fintype ι]

/-- Surjectivity of the map sending T to its commutators with left
multiplication by the coefficients of the generic differential. -/
def HasSurjectiveCommutators (a : ι → D) : Prop :=
  ∀ b : ι → Module.End k D, ∃ T : Module.End k D,
    ∀ i x, b i x = T (a i * x) - a i * T x

/-- On the i-th summand the two terms move the generator to opposite sides
of the tensor sign. The map is linear for multiplication on the first factor. -/
noncomputable def freeTensorBoundary (a : ι → D) :
    (ι → D ⊗[k] D) →ₗ[D] D ⊗[k] D := by
  classical
  exact LinearMap.lsum D (fun _ : ι ↦ D ⊗[k] D) ℕ (fun i ↦
    AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft k (a i)) -
    AlgebraTensorModule.map (LinearMap.toSpanSingleton D D (a i)) LinearMap.id)

open Classical in
theorem freeTensorBoundary_single (a : ι → D) (i : ι) (u v : D) :
    freeTensorBoundary k a (Pi.single i (u ⊗ₜ[k] v)) =
      u ⊗ₜ[k] (a i * v) - (u * a i) ⊗ₜ[k] v := by
  rw [freeTensorBoundary,LinearMap.lsum_piSingle]
  rfl

/-- Injectivity of the tensor boundary gives simultaneous commutator solutions
for arbitrary ground-field linear operators, without a localization hypothesis. -/
theorem simultaneous_commutators_of_injective_boundary (a : ι → D)
    (ha : Function.Injective (freeTensorBoundary k a)) : HasSurjectiveCommutators k a := by
  classical
  intro b
  obtain ⟨s,hs⟩ := (freeTensorBoundary k a).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr ha)
  let B (i : ι) : D ⊗[k] D →ₗ[D] D :=
    AlgebraTensorModule.lift (LinearMap.toSpanSingleton D (Module.End k D) (b i))
  let F := LinearMap.lsum D (fun _ : ι ↦ D ⊗[k] D) ℕ B
  let L := F.comp s
  let T : Module.End k D := (L.restrictScalars k).comp (TensorProduct.mk k D D 1)
  refine ⟨T,fun i x ↦ ?_⟩
  let z : ι → D ⊗[k] D := Pi.single i ((1 : D) ⊗ₜ[k] x)
  have eq : L (freeTensorBoundary k a z) = F z := congrArg F (LinearMap.congr_fun hs z)
  change L (freeTensorBoundary k a (Pi.single i (1 ⊗ₜ[k] x))) = F (Pi.single i (1 ⊗ₜ[k] x)) at eq
  rw [freeTensorBoundary_single,one_mul,map_sub,show F (Pi.single i (1 ⊗ₜ[k] x)) = B i (1 ⊗ₜ[k] x) from
    LinearMap.lsum_piSingle ..] at eq
  have hmul : (a i) ⊗ₜ[k] x = a i • (1 ⊗ₜ[k] x) := by
    change _ = (a i * 1) ⊗ₜ[k] x
    rw [mul_one]
  rw [hmul,L.map_smul] at eq
  simpa [T,B] using eq.symm

end EFiniteCharacterizations
