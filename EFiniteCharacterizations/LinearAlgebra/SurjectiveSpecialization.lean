module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Specializing a surjective linear family to an infinite ground field -/

@[expose] public section

namespace EFiniteCharacterizations

/-- If a linear family contains a surjection over an extension field, its
coefficients may be chosen in any infinite ground field. -/
theorem exists_surjective_ground_coefficients (k F : Type*) [Field k] [Infinite k]
    [Field F] [Algebra k F] {ι V W : Type*} [Fintype ι] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    (D : ι → V →ₗ[F] W) (a : ι → F) (ha : Function.Surjective (∑ i, a i • D i : V →ₗ[F] W)) :
    ∃ c : ι → k, Function.Surjective (∑ i, algebraMap k F (c i) • D i : V →ₗ[F] W) := by
  classical
  obtain ⟨s,hs⟩ := (∑ i, a i • D i).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr ha)
  let b := Module.finBasis F W
  let M i := LinearMap.toMatrix b b ((D i).comp s)
  let A := Matrix.of fun j l ↦ ∑ i, MvPolynomial.C (M i j l) * MvPolynomial.X i
  have eval (v : ι → F) : MvPolynomial.eval v A.det =
      LinearMap.det ((∑ i, v i • D i).comp s) := by
    rw [RingHom.map_det, ← LinearMap.det_toMatrix b]
    congr 1
    ext j l
    simp [A,M,LinearMap.toMatrix_apply,mul_comm]
  have hn : A.det ≠ 0 := by
    intro h
    have he := eval a
    rw [h,map_zero,hs,LinearMap.det_id] at he
    exact zero_ne_one he
  by_contra! h
  apply hn
  apply MvPolynomial.funext_set (fun _ ↦ Set.range (algebraMap k F))
    (fun _ ↦ Set.infinite_range_of_injective (algebraMap k F).injective)
  intro v hv
  choose c hc using fun i ↦ hv i (Set.mem_univ i)
  have he : (fun i ↦ algebraMap k F (c i)) = v := funext hc
  rw [← he,eval,map_zero,LinearMap.det_eq_zero_iff_ker_ne_bot]
  intro hker
  exact h c (Function.Surjective.of_comp
    (LinearMap.surjective_of_injective (LinearMap.ker_eq_bot.mp hker)))

end EFiniteCharacterizations
