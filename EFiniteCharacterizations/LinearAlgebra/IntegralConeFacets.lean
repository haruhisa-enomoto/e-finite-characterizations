module

public import EFiniteCharacterizations.LinearAlgebra.IntegralSeparation

/-! # Finite integral halfspace tests for a rational cone -/

@[expose] public section

namespace EFiniteCharacterizations.Farkas

/-- With the coefficient matrix fixed, elimination gives a single finite list
of tests that decides feasibility for every right-hand side. -/
theorem finite_feasibility_tests (n : ℕ) {I : Type*} [Fintype I] (A : I → Fin n → ℚ) :
    ∃ S : Finset (I → ℚ), ∀ b, Feasible A b ↔ ∀ s ∈ S, ∑ i, s i * b i ≤ 0 := by
  classical
  induction n generalizing I with
  | zero =>
    refine ⟨Finset.univ.image (fun i : I ↦ Pi.single i 1), fun b ↦ ?_⟩
    simp [Feasible, Pi.single_apply]
  | succ n ih =>
    obtain ⟨S, hS⟩ := ih (elimA A)
    let lift (s : ElimRow A → ℚ) (i : I) := ∑ r, s r * coef A r i
    refine ⟨S.image lift, fun b ↦ ?_⟩
    have hf : Feasible A b ↔ Feasible (elimA A) (elimB A b) := by
      refine ⟨fun h ↦ ?_, feasible_of_elim A b⟩
      exact (farkas n _ _).resolve_right fun hc ↦ not_feasible_and_certificate A b ⟨h, certificate_of_elim A b hc⟩
    rw [hf, hS]
    simp only [Finset.forall_mem_image, lift, sum_comb, elimB]

/-- A finite system of rational linear inequalities recognizes the nonnegative
rational span of a finite list of integral vectors. -/
theorem finite_cone_tests {n m : ℕ} (V : Fin m → Fin n → ℤ) :
    ∃ H : Finset (Fin n → ℤ), ∀ z : Fin n → ℤ,
      (∀ h ∈ H, 0 ≤ ∑ t, h t * z t) ↔
      ∃ a : Fin m → ℚ, (∀ i, 0 ≤ a i) ∧ ∀ t, (z t : ℚ) = ∑ i, a i * V i t := by
  classical

  let A : (Fin m ⊕ (Fin n ⊕ Fin n)) → Fin m → ℚ := Sum.elim (fun i ↦ Pi.single i 1)
    (Sum.elim (fun t i ↦ (V i t : ℚ)) (fun t i ↦ -(V i t : ℚ)))
  let b (z : Fin n → ℤ) : (Fin m ⊕ (Fin n ⊕ Fin n)) → ℚ := Sum.elim (fun _ ↦ 0) (Sum.elim (fun t ↦ (z t : ℚ)) (fun t ↦ -(z t : ℚ)))
  obtain ⟨S, hS⟩ := finite_feasibility_tests m A
  let coeff (s : S) (t : Fin n) := s.val (.inr (.inr t)) - s.val (.inr (.inl t))
  choose d w hd hw using fun s : S ↦ common_denominator (coeff s)
  refine ⟨Finset.univ.image w, fun z ↦ ?_⟩
  have dot (s : S) : (∑ t, w s t * z t : ℤ) = -(d s * ∑ i, s.val i * b z i : ℚ) := by
    push_cast
    simp only [hw, coeff, b, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
      Finset.sum_const_zero, zero_add, mul_neg, Finset.sum_neg_distrib]
    simp only [mul_assoc, ← Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
    ring
  have ht : (∀ h ∈ Finset.univ.image w, 0 ≤ ∑ t, h t * z t) ↔ Feasible A (b z) := by
    rw [hS]
    simp only [Finset.forall_mem_image, Finset.mem_univ, true_implies]
    constructor
    · intro h s hs
      let j : S := ⟨s,hs⟩
      have hj : (0 : ℚ) ≤ (∑ t, w j t * z t : ℤ) := by exact_mod_cast @h j
      rw [dot] at hj
      exact nonpos_of_mul_nonpos_right (neg_nonneg.mp hj) (hd j)
    · intro h j
      have hj := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hd j).le (h j.val j.property))
      rw [← dot] at hj
      exact_mod_cast hj
  rw [ht]
  constructor
  · rintro ⟨a, h⟩
    refine ⟨a, fun i ↦ ?_, fun t ↦ le_antisymm ?_ ?_⟩
    · simpa [A,b,Pi.single_apply] using h (.inl i)
    · simpa [A,b,mul_comm] using h (.inr (.inl t))
    · simpa [A,b,mul_comm,Finset.sum_neg_distrib] using h (.inr (.inr t))
  · rintro ⟨a, ha, he⟩
    refine ⟨a, fun i ↦ ?_⟩
    rcases i with i | (t | t)
    · simpa [A,b,Pi.single_apply] using ha i
    · simpa [A,b,mul_comm] using (he t).le
    · simpa [A,b,mul_comm,Finset.sum_neg_distrib] using (he t).ge

/-- On an integral lattice the same tests detect a relation after clearing
one positive denominator on the class being tested. -/
theorem finite_lattice_cone_tests {G : Type*} [AddCommGroup G] {n m : ℕ}
    (v : Fin n → G →+ ℤ) (hv : Function.Injective (fun z t ↦ v t z)) (X : Fin m → G) :
    ∃ H : Finset (Fin n → ℤ), ∀ z : G, (∀ h ∈ H, 0 ≤ (∑ t, h t • v t : G →+ ℤ) z) ↔
      ∃ (p : ℤ) (a : Fin m → ℤ), 0 < p ∧ (∀ i, 0 ≤ a i) ∧ p • z = ∑ i, a i • X i := by
  obtain ⟨H,hH⟩ := finite_cone_tests (fun i t ↦ v t (X i))
  refine ⟨H, fun z ↦ ?_⟩
  simp only [AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply, zsmul_eq_mul, Int.cast_id]
  rw [hH (fun t ↦ v t z)]
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨d, w, hd, hw⟩ := common_denominator (Fin.cons 1 a)
    have hw₀ : (w 0 : ℚ) = d := by simpa using hw 0
    have hw' (i : Fin m) : (w i.succ : ℚ) = d * a i := by simpa using hw i.succ
    refine ⟨w 0, fun i ↦ w i.succ, by exact_mod_cast hw₀.symm ▸ hd, fun i ↦ ?_, hv (funext fun t ↦ ?_)⟩
    · exact_mod_cast (hw' i).symm ▸ mul_nonneg hd.le (ha i)
    · simp only [map_zsmul, map_sum, zsmul_eq_mul]
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [hw₀, he t, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hw']; ring
  · rintro ⟨p,a,hp,ha,he⟩
    refine ⟨fun i ↦ (p : ℚ)⁻¹ * a i, fun i ↦ mul_nonneg (inv_nonneg.mpr (by exact_mod_cast hp.le))
      (by exact_mod_cast ha i), fun t ↦ ?_⟩
    have ht := congrArg (v t) he
    simp only [map_zsmul, map_sum, zsmul_eq_mul] at ht
    have ht' : (p : ℚ) * v t z = ∑ i, (a i : ℚ) * v t (X i) := by exact_mod_cast ht
    simp only [mul_assoc, ← Finset.mul_sum, ← ht', inv_mul_cancel_left₀ (show (p : ℚ) ≠ 0 by exact_mod_cast hp.ne')]

end EFiniteCharacterizations.Farkas
