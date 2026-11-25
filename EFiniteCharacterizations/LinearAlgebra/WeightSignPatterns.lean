module

public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Polynomial bounds on strict sign patterns of integral weights -/

@[expose] public section

namespace EFiniteCharacterizations

variable {G I : Type*} [AddCommGroup G] [Fintype I]

/-- Subsets of the tests on which an integral weight is strictly negative. -/
noncomputable def negativePatterns (v : I → G) : Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun s ↦ ∃ w : G →+ ℤ, ∀ i, i ∈ s ↔ w (v i) < 0

private theorem independent_of_shattered {v : I → G} {s : Finset I} [DecidableEq I]
    (hs : (negativePatterns v).Shatters s) : LinearIndependent ℤ (fun i : s ↦ v i.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have noPos (a : s → ℤ) (hz : ∑ i, a i • v i.val = 0) (i₀ : s) : ¬ 0 < a i₀ := by
    intro hp
    let t := s.attach.filter fun i ↦ 0 < a i
    let u := t.image Subtype.val
    have hu : u ⊆ s := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact j.property
    obtain ⟨p, hmem, he⟩ := hs hu
    obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hmem).2
    have sign (i : s) : w (v i.val) < 0 ↔ 0 < a i := by
      have hm := Finset.ext_iff.mp he i.val
      simpa [i.property, u, t, ← hw] using hm
    have hzero := congrArg w hz
    simp only [map_sum, map_zsmul, zsmul_eq_mul, map_zero] at hzero
    apply (Finset.sum_neg' (f := fun i : s ↦ a i * w (v i.val)) _ ⟨i₀, Finset.mem_univ _, mul_neg_of_pos_of_neg hp ((sign i₀).2 hp)⟩).ne hzero
    intro i _
    by_cases h : 0 < a i
    · exact mul_nonpos_of_nonneg_of_nonpos h.le ((sign i).2 h).le
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (le_of_not_gt (mt (sign i).1 h))
  intro i
  have h₁ := noPos c hc i
  have h₂ := noPos (fun i ↦ -c i) (by simp only [neg_smul, Finset.sum_neg_distrib, hc, neg_zero]) i
  omega

/-- For a group with at most `n` independent elements, the number of
strict negative patterns on a finite collection of tests is polynomial. -/
theorem card_negativePatterns_le (v : I → G) (n : ℕ)
    (h : ∀ s : Finset I, LinearIndependent ℤ (fun i : s ↦ v i.val) → s.card ≤ n) :
    (negativePatterns v).card ≤ (n + 1) * (Fintype.card I + 1) ^ n := by
  classical
  let A := negativePatterns v
  have hd : A.vcDim ≤ n := Finset.sup_le fun s hs ↦ h s (independent_of_shattered (Finset.mem_shatterer.mp hs))
  refine (A.card_le_card_shatterer.trans A.card_shatterer_le_sum_vcDim).trans ?_
  calc
    _ ≤ ∑ _j ∈ Finset.Iic A.vcDim, (Fintype.card I + 1) ^ n := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) ((Finset.mem_Iic.mp hj).trans hd)))
    _ ≤ _ := by simpa using hd

end EFiniteCharacterizations
