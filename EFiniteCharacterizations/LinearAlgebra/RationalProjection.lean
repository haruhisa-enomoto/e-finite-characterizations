module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Monoid

/-! # Rational linear functionals positive on prescribed real numbers -/

@[expose] public section

open scoped BigOperators

namespace EFiniteCharacterizations

/-- A rational-linear functional from `ℝ` to `ℚ` can preserve strict
positivity on any prescribed finite list of positive real numbers. -/
theorem exists_rat_linear_pos_on_finset (s : Finset ℝ) (hs : ∀ x ∈ s, 0 < x) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, ∀ x ∈ s, 0 < f x := by
  classical
  let I := Module.Basis.ofVectorSpaceIndex ℚ ℝ
  let b : Module.Basis I ℚ ℝ := Module.Basis.ofVectorSpace ℚ ℝ
  let eval (x : ℝ) (v : I → ℝ) : ℝ :=
    (b.repr x).sum (fun i q ↦ (q : ℝ) * v i)
  have heval (x : ℝ) : eval x b = x := by
    have h := b.linearCombination_repr x
    rw [Finsupp.linearCombination_apply] at h
    simpa only [eval, Rat.smul_def] using h
  have hc (x : ℝ) : Continuous (eval x) := by
    change Continuous (fun v : I → ℝ ↦ ∑ i ∈ (b.repr x).support, ((b.repr x i : ℚ) : ℝ) * v i)
    exact continuous_finsetSum _ (fun i _ ↦ continuous_const.mul (continuous_apply i))
  let U := ⋂ x ∈ s, {v : I → ℝ | 0 < eval x v}
  have hU : IsOpen U := isOpen_biInter_finset (fun x _ ↦ isOpen_lt continuous_const (hc x))
  have hb : (b : I → ℝ) ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_ofPred_eq, heval]
    exact hs
  have hd : DenseRange (fun v : I → ℚ ↦ fun i ↦ (v i : ℝ)) :=
    DenseRange.piMap (f := fun _ ↦ ((↑) : ℚ → ℝ)) (fun _ ↦ Rat.denseRange_cast)
  obtain ⟨v, hv⟩ := hd.exists_mem_open hU ⟨_, hb⟩
  let f := (Finsupp.linearCombination ℚ v).comp b.repr.toLinearMap
  refine ⟨f, fun x hx ↦ ?_⟩
  have hw : 0 < eval x (fun i ↦ (v i : ℝ)) := by
    have h := Set.mem_iInter.mp hv x
    exact Set.mem_iInter.mp h hx
  have he : (f x : ℝ) = eval x (fun i ↦ (v i : ℝ)) := by
    simp [f, Finsupp.linearCombination_apply, Finsupp.sum, eval, smul_eq_mul]
  rw [← he] at hw
  exact_mod_cast hw

/-- Two nonnegative real coefficients can be sent to nonnegative rational
coefficients by a rational-linear functional that is positive on `1`. -/
theorem exists_rat_linear_nonneg_pair {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, 0 < f 1 ∧ 0 ≤ f a ∧ 0 ≤ f b := by
  classical
  let s : Finset ℝ := ({1, a, b} : Finset ℝ).filter (0 < ·)
  obtain ⟨f, hf⟩ := exists_rat_linear_pos_on_finset s (fun x hx ↦ (Finset.mem_filter.mp hx).2)
  have h (x : ℝ) (hx : x ∈ ({1, a, b} : Finset ℝ)) (h₀ : 0 ≤ x) : 0 ≤ f x := by
    rcases h₀.eq_or_lt with hzero | hpos
    · simp [← hzero]
    · exact (hf x (Finset.mem_filter.mpr ⟨hx, hpos⟩)).le
  exact ⟨f, hf 1 (by simp [s]), h a (by simp) ha, h b (by simp) hb⟩

end EFiniteCharacterizations
