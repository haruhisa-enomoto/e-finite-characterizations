module

public import EFiniteCharacterizations.Stability.DivisionEuler
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Real separating weights on modules over a commuting division ring -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

private theorem real_nonpos_of_integral_tests {I J : Type*} [Fintype I]
    (a : I → ℝ) (d : J → I → ℕ) (b : I → ℕ)
    (ha : ∀ j, ∑ i, a i * d j i ≤ 0)
    (h : ∀ c : I → ℤ, (∀ j, ∑ i, c i * (d j i : ℤ) ≤ 0) → ∑ i, c i * (b i : ℤ) ≤ 0) :
    ∑ i, a i * b i ≤ 0 := by
  by_contra! hp
  obtain ⟨n,hn⟩ := exists_nat_gt ((∑ i, (b i : ℝ)) / (∑ i, a i * b i))
  let c (i : I) := ⌊(n : ℝ) * a i⌋
  have hc := h c (fun j ↦ by
    have he : ∑ i, (c i : ℝ) * d j i ≤ (n : ℝ) * ∑ i, a i * d j i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (Int.floor_le _) (Nat.cast_nonneg _)
    exact_mod_cast he.trans (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (ha j)))
  have he : (n : ℝ) * (∑ i, a i * b i) ≤ (∑ i, (c i : ℝ) * b i) + ∑ i, (b i : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hf := Int.sub_one_lt_floor ((n : ℝ) * a i)
    have hle : (n : ℝ) * a i ≤ (c i : ℝ) + 1 := by dsimp [c]; linarith
    simpa [add_mul,mul_assoc] using mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg (b i) : (0:ℝ) ≤ _)
  have hreal : (∑ i, (c i : ℝ) * b i) ≤ 0 := by exact_mod_cast hc
  linarith [(div_lt_iff₀ hp).mp hn]

variable {R : Type u} [Ring R] (k : Type u) [Field k] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R] (D : Type u) [DivisionRing D]
  (M : ModuleCat.{u} R) [Module D M] [SMulCommClass R D M] [Module.Finite D M]
  {I : Type*} [Fintype I] (P : I → FiniteProjective R) (a : I → ℝ)

private theorem eval_projective_sum (c : I → ℤ) (N : FGModuleCat.{u} R) :
    (projectiveClassWeight k (∑ i, c i • ProjectiveClass.of (P i))).eval N =
      ∑ i, c i * homFinrank k (P i).val N := by
  simp only [Weight.eval,map_sum,map_zsmul,AddMonoidHom.finsetSum_apply,AddMonoidHom.zsmul_apply,
    projectiveClassWeight_of,zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  let := (P i).property
  exact congrArg (c i * ·) (projectiveHomWeight_eval k (P i).val N)

/-- Real weights nonpositive on finite submodules give the same inequality
when Hom dimensions are measured over the commuting division ring. -/
theorem divisionEuler_real_nonpos_of_submodule_tests (hR : IsEFinite R)
    (ha : ∀ (N : FGModuleCat.{u} R) (i : N.obj ⟶ M), Function.Injective i.hom →
      ∑ t, a t * homFinrank k (P t).val N ≤ 0) :
    ∑ t, a t * Module.finrank D ((P t).val →ₗ[R] M) ≤ 0 := by
  let J := {N : FGModuleCat.{u} R // ∃ i : N.obj ⟶ M, Function.Injective i.hom}
  apply real_nonpos_of_integral_tests a (fun (j : J) t ↦ homFinrank k (P t).val j.val) _
    (fun j ↦ by obtain ⟨i,hi⟩ := j.property; exact ha _ i hi)
  intro c hc
  obtain ⟨Q,hQ,he⟩ := hR (∑ t, c t • ProjectiveClass.of (P t))
  have hn := divisionEuler_nonpos_of_submodule_tests D M k Q hQ (by
    intro N i hi
    rw [← Q.projectiveClassWeight_eq_eulerWeight k,he,eval_projective_sum]
    exact hc ⟨N,i,hi⟩)
  simpa only [he,map_sum,map_zsmul,divisionEuler_of,zsmul_eq_mul,Int.cast_id] using hn

/-- The quotient tests give the opposite inequality over the division ring. -/
theorem divisionEuler_real_nonneg_of_quotient_tests (hR : IsEFinite R)
    (ha : ∀ (N : FGModuleCat.{u} R) (q : M ⟶ N.obj), Function.Surjective q.hom →
      0 ≤ ∑ t, a t * homFinrank k (P t).val N) :
    0 ≤ ∑ t, a t * Module.finrank D ((P t).val →ₗ[R] M) := by
  let J := {N : FGModuleCat.{u} R // ∃ q : M ⟶ N.obj, Function.Surjective q.hom}
  let d (j : J) (t : I) := homFinrank k (P t).val j.val
  let b (t : I) := Module.finrank D ((P t).val →ₗ[R] M)
  have hs (j : J) : ∑ t, (-a t) * (d j t : ℝ) ≤ 0 := by
    obtain ⟨q,hq⟩ := j.property
    rw [show (∑ t, -a t * (d j t : ℝ)) = -(∑ t, a t * (d j t : ℝ)) by
      simp only [neg_mul,Finset.sum_neg_distrib], neg_nonpos]
    exact ha _ q hq
  have hi (c : I → ℤ) (hc : ∀ j, ∑ t, c t * (d j t : ℤ) ≤ 0) :
      ∑ t, c t * (b t : ℤ) ≤ 0 := by
    let g := ∑ t, c t • ProjectiveClass.of (P t)
    obtain ⟨Q,hQ,he⟩ := hR (-g)
    have hb := divisionEuler_nonneg_of_quotient_tests D M k Q hQ (by
      intro N q hq
      rw [← Q.projectiveClassWeight_eq_eulerWeight k,he,map_neg]
      change 0 ≤ -((projectiveClassWeight k g).eval N)
      rw [neg_nonneg]
      exact (eval_projective_sum k P c N).trans_le (hc ⟨N,q,hq⟩))
    simpa only [he,g,map_neg,map_sum,map_zsmul,divisionEuler_of,zsmul_eq_mul,Int.cast_id,neg_nonneg,b] using hb
  simpa only [neg_mul,Finset.sum_neg_distrib,neg_nonpos,b] using
    real_nonpos_of_integral_tests (fun t ↦ -a t) d b hs hi

end EFiniteCharacterizations
