module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Recovery of central coefficients by two-sided multiplication -/

@[expose] public section

namespace EFiniteCharacterizations

/-- Two-sided operators isolating the members of a basis recover the
coefficients of a relation in any target ring. The coefficients need only
commute with the left multipliers. -/
theorem coefficients_zero_of_sandwich_separation {T ι J : Type*} [Ring T] [Fintype ι]
    [DecidableEq ι] [Fintype J] (b d : ι → T) (u v : ι → J → T)
    (hcomm : ∀ i l j, Commute (u l j) (d i))
    (hsep : ∀ l i, ∑ j, u l j * b i * v l j = if i = l then 1 else 0)
    (h : ∑ i, d i * b i = 0) : ∀ i, d i = 0 := by
  classical
  intro l
  calc
    d l = ∑ i, d i * (if i = l then 1 else 0) := by simp
    _ = ∑ i, ∑ j, d i * (u l j * b i * v l j) := by
      simp only [← hsep, Finset.mul_sum]
    _ = ∑ j, ∑ i, u l j * (d i * b i) * v l j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, ← mul_assoc, ← (hcomm i l j).eq]
      simp only [mul_assoc]
    _ = ∑ j, u l j * (∑ i, d i * b i) * v l j := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = 0 := by simp [h]

/-- Agreement on a linear combination and the basis elements forces
agreement on the coefficients when two-sided operators isolate each basis
element and the maps agree on their left multipliers. -/
theorem ringHom_agree_on_separated_coefficients {A T ι J : Type*} [Ring A] [Ring T]
    [Fintype ι] [DecidableEq ι] [Fintype J] (f g : A →+* T)
    (b c : ι → A) (u v : ι → J → A)
    (hb : ∀ i, f (b i) = g (b i)) (hu : ∀ l j, f (u l j) = g (u l j))
    (hc : ∀ i l j, Commute (u l j) (c i))
    (hsep : ∀ l i, ∑ j, u l j * b i * v l j = if i = l then 1 else 0)
    (h : f (∑ i, c i * b i) = g (∑ i, c i * b i)) : ∀ i, f (c i) = g (c i) := by
  classical
  have hcomm (i l j) : Commute (f (u l j)) (f (c i) - g (c i)) := by
    apply Commute.sub_right
    · simpa only [Commute, SemiconjBy, map_mul] using congrArg f (hc i l j).eq
    · rw [hu]
      simpa only [Commute, SemiconjBy, map_mul] using congrArg g (hc i l j).eq
  have hs (l i) : ∑ j, f (u l j) * f (b i) * f (v l j) = if i = l then 1 else 0 := by
    simpa only [map_sum,map_mul,apply_ite,map_one,map_zero] using congrArg f (hsep l i)
  have hz : ∑ i, (f (c i) - g (c i)) * f (b i) = 0 := by
    simp only [sub_mul,Finset.sum_sub_distrib,sub_eq_zero]
    simpa only [map_sum,map_mul,← hb] using h
  exact fun i ↦ sub_eq_zero.mp (coefficients_zero_of_sandwich_separation _ _ _ _ hcomm hs hz i)

end EFiniteCharacterizations
