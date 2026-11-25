module

public import EFiniteCharacterizations.LinearAlgebra.Farkas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-! # Integral separation of finite families of class vectors -/

@[expose] public section

namespace EFiniteCharacterizations.Farkas

theorem common_denominator {I : Type*} [Fintype I] (v : I → ℚ) :
    ∃ (d : ℚ) (w : I → ℤ), 0 < d ∧ ∀ i, (w i : ℚ) = d * v i := by
  classical
  let D := ∏ i, (v i).den
  let P (i : I) := ∏ j ∈ Finset.univ.erase i, (v j).den
  have hd : 0 < D := Finset.prod_pos fun i _ ↦ (v i).den_pos
  refine ⟨D, fun i ↦ (P i : ℤ) * (v i).num, by exact_mod_cast hd, fun i ↦ ?_⟩
  have he : P i * (v i).den = D := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have hv := (div_eq_iff (by exact_mod_cast (v i).den_ne_zero)).mp (v i).num_div_den
  rw [← he]
  push_cast
  rw [hv]
  ring

private theorem scaled_dot {I : Type*} [Fintype I] (v : I → ℤ) {w : I → ℤ} {q : I → ℚ}
    {d : ℚ} (hw : ∀ i, (w i : ℚ) = d * q i) :
    ((∑ i, v i * w i : ℤ) : ℚ) = d * ∑ i, (v i : ℚ) * q i := by
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hw]; ring

/-- The alternative for integral rows has an integral separating functional
or an integral certificate with nonnegative test-row coefficients. -/
theorem integral_separation_or_relation {n : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (B : I → Fin n → ℤ) (U : J → Fin n → ℤ) :
    (∃ w : Fin n → ℤ, (∀ i, ∑ t, B i t * w t = 0) ∧ ∀ j, ∑ t, U j t * w t < 0) ∨
    ∃ (a : J → ℤ) (c : I → ℤ), (∀ j, 0 ≤ a j) ∧ 0 < ∑ j, a j ∧
      ∀ t, ∑ j, a j * U j t = ∑ i, c i * B i t := by
  rcases separation_or_relation (fun i t ↦ (B i t : ℚ)) (fun j t ↦ (U j t : ℚ)) with
    ⟨q, hB, hU⟩ | ⟨a, c, ha, hp, he⟩
  · obtain ⟨d, w, hd, hw⟩ := common_denominator q
    left
    refine ⟨w, fun i ↦ ?_, fun j ↦ ?_⟩
    · have h := scaled_dot (B i) hw
      rw [hB, mul_zero] at h
      exact_mod_cast h
    · have h := (scaled_dot (U j) hw).trans_lt (mul_neg_of_pos_of_neg hd (hU j))
      exact_mod_cast h
  · obtain ⟨d, w, hd, hw⟩ := common_denominator (Sum.elim a c)
    have hw₁ (j : J) : (w (.inl j) : ℚ) = d * a j := hw _
    have hw₂ (i : I) : (w (.inr i) : ℚ) = d * c i := hw _
    right
    refine ⟨fun j ↦ w (.inl j), fun i ↦ w (.inr i), fun j ↦ ?_, ?_, fun t ↦ ?_⟩
    · exact_mod_cast (hw₁ j).symm ▸ mul_nonneg hd.le (ha j)
    · have h : (0 : ℚ) < ∑ j, (w (.inl j) : ℚ) := by
        simpa only [hw₁, Finset.mul_sum] using mul_pos hd hp
      exact_mod_cast h
    · have h := (scaled_dot (fun j ↦ U j t) hw₁).trans
        ((congrArg (d * ·) (by simpa only [mul_comm] using he t)).trans
          (scaled_dot (fun i ↦ B i t) hw₂).symm)
      simpa only [mul_comm] using (Int.cast_injective (α := ℚ) h)

/-- A finite separating family of integer coordinates lifts the alternative
to the original abelian group. The separating weight is an integral
combination of the given coordinates. -/
theorem integral_separation_of_injective_coordinates {G : Type*} [AddCommGroup G]
    {n : ℕ} (v : Fin n → G →+ ℤ) (hv : Function.Injective (fun x t ↦ v t x))
    {I J : Type*} [Fintype I] [Fintype J] (B : I → G) (U : J → G) :
    (∃ w : Fin n → ℤ, (∀ i, (∑ t, w t • v t : G →+ ℤ) (B i) = 0) ∧
      ∀ j, (∑ t, w t • v t : G →+ ℤ) (U j) < 0) ∨
    ∃ (a : J → ℤ) (c : I → ℤ), (∀ j, 0 ≤ a j) ∧ 0 < ∑ j, a j ∧
      ∑ j, a j • U j = ∑ i, c i • B i := by
  rcases integral_separation_or_relation (fun i t ↦ v t (B i)) (fun j t ↦ v t (U j)) with
    ⟨w, hB, hU⟩ | ⟨a, c, ha, hp, he⟩
  · left
    exact ⟨w, fun i ↦ by simpa [AddMonoidHom.finsetSum_apply, mul_comm] using hB i,
      fun j ↦ by simpa [AddMonoidHom.finsetSum_apply, mul_comm] using hU j⟩
  · right
    refine ⟨a, c, ha, hp, hv (funext fun t ↦ ?_)⟩
    simpa [map_sum, map_zsmul] using he t

end EFiniteCharacterizations.Farkas
