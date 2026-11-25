module

public import EFiniteCharacterizations.LinearAlgebra.WeightSignPatterns

/-! # Sign patterns on one side of a hyperplane in the weight space -/

@[expose] public section

namespace EFiniteCharacterizations

variable {G I : Type*} [AddCommGroup G] [Fintype I]

/-- Negative tests for weights vanishing on a prescribed class and positive on a pivot. -/
noncomputable def normalizedPatterns (v : I → G) (z p : G) : Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun s ↦ ∃ w : G →+ ℤ, w z = 0 ∧ 0 < w p ∧
    ∀ i, i ∈ s ↔ w (v i) < 0

/-- A relation on a shattered set and the two distinguished classes has
zero pivot coefficient. -/
theorem normalizedPatterns_pivot_eq_zero {v : I → G} {z p : G} {s : Finset I}
    [DecidableEq I] (hs : (normalizedPatterns v z p).Shatters s)
    (c : s → ℤ) (a b : ℤ) (he : (∑ i, c i • v i.val) + a • z + b • p = 0) : b = 0 := by
  classical
  have nonpos (d : s → ℤ) (t u : ℤ) (hd : (∑ i, d i • v i.val) + t • z + u • p = 0) : u ≤ 0 := by
    by_contra! hu
    let A := (s.attach.filter fun i ↦ d i < 0).image Subtype.val
    have hA : A ⊆ s := by
      intro x hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
      exact j.property
    obtain ⟨S,hS,hAS⟩ := hs hA
    obtain ⟨w,hz,hp,hw⟩ := (Finset.mem_filter.mp hS).2
    have sign (i : s) : w (v i.val) < 0 ↔ d i < 0 := by
      simpa [← hw, i.property, A] using Finset.ext_iff.mp hAS i.val
    have hsum : 0 ≤ ∑ i, d i * w (v i.val) := by
      apply Finset.sum_nonneg
      intro i _
      by_cases hi : d i < 0
      · exact mul_nonneg_of_nonpos_of_nonpos hi.le ((sign i).2 hi).le
      · exact mul_nonneg (le_of_not_gt hi) (le_of_not_gt (mt (sign i).1 hi))
    have hh := congrArg w hd
    simp only [map_add, map_sum, map_zsmul, zsmul_eq_mul, hz, mul_zero, add_zero, map_zero] at hh
    have hpos := mul_pos hu hp
    exact (add_pos_of_nonneg_of_pos hsum hpos).ne' hh
  have h₁ := nonpos c a b he
  have h₂ := nonpos (fun i ↦ -c i) (-a) (-b) (by
    simp only [neg_smul, Finset.sum_neg_distrib, ← neg_add, he, neg_zero])
  omega

/-- All test coefficients in a relation vanish, even when the relation also
involves the prescribed class and the pivot. -/
theorem normalizedPatterns_tests_eq_zero {v : I → G} {z p : G} {s : Finset I}
    [DecidableEq I] (hs : (normalizedPatterns v z p).Shatters s)
    (c : s → ℤ) (a b : ℤ) (he : (∑ i, c i • v i.val) + a • z + b • p = 0) :
    ∀ i, c i = 0 := by
  classical
  have hb := normalizedPatterns_pivot_eq_zero hs c a b he
  subst b
  simp only [zero_smul, add_zero] at he
  have noPos (d : s → ℤ) (t : ℤ) (hd : (∑ i, d i • v i.val) + t • z = 0)
      (i₀ : s) : ¬ 0 < d i₀ := by
    intro hp
    let A := (s.attach.filter fun i ↦ 0 < d i).image Subtype.val
    have hA : A ⊆ s := by
      intro x hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
      exact j.property
    obtain ⟨S,hS,hAS⟩ := hs hA
    obtain ⟨w,hz,_,hw⟩ := (Finset.mem_filter.mp hS).2
    have sign (i : s) : w (v i.val) < 0 ↔ 0 < d i := by
      simpa [← hw, i.property, A] using Finset.ext_iff.mp hAS i.val
    have hh := congrArg w hd
    simp only [map_add, map_sum, map_zsmul, zsmul_eq_mul, hz, mul_zero, add_zero, map_zero] at hh
    apply (Finset.sum_neg' (f := fun i : s ↦ d i * w (v i.val)) _
      ⟨i₀, Finset.mem_univ _, mul_neg_of_pos_of_neg hp ((sign i₀).2 hp)⟩).ne hh
    intro i _
    by_cases hi : 0 < d i
    · exact mul_nonpos_of_nonneg_of_nonpos hi.le ((sign i).2 hi).le
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hi) (le_of_not_gt (mt (sign i).1 hi))
  intro i
  have h₁ := noPos c a he i
  have h₂ := noPos (fun j ↦ -c j) (-a) (by
    simp only [neg_smul, Finset.sum_neg_distrib, ← neg_add, he, neg_zero]) i
  omega

/-- A shattered family together with the class and pivot is linearly independent
when the prescribed class has infinite order. -/
theorem normalizedPatterns_independent {v : I → G} {z p : G} {s : Finset I}
    [DecidableEq I] (hs : (normalizedPatterns v z p).Shatters s)
    (hz : ∀ a : ℤ, a • z = 0 → a = 0) :
    LinearIndependent ℤ (Sum.elim (fun i : s ↦ v i.val) (fun t : Bool ↦ if t then p else z)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have he : (∑ i : s, c (.inl i) • v i.val) + c (.inr false) • z + c (.inr true) • p = 0 := by
    simpa [Fintype.sum_sum_type, Fintype.sum_bool, add_assoc, add_left_comm, add_comm]
      using hc
  have hb := normalizedPatterns_pivot_eq_zero hs _ _ _ he
  have hd := normalizedPatterns_tests_eq_zero hs _ _ _ he
  have ha := hz (c (.inr false)) (by simpa [hd, hb] using he)
  rintro (i | t)
  · exact hd i
  · cases t <;> assumption

/-- On either side of the pivot the sign-pattern count has degree at most n−2
in the number of tests. -/
theorem card_normalizedPatterns_le (v : I → G) (z p : G) (r N : ℕ)
    (hz : ∀ a : ℤ, a • z = 0 → a = 0) (hN : Fintype.card I ≤ N) (hp : 0 < N)
    (hr : ∀ s : Finset I,
      LinearIndependent ℤ (Sum.elim (fun i : s ↦ v i.val) (fun t : Bool ↦ if t then p else z)) →
        s.card + 2 ≤ r + 2) :
    (normalizedPatterns v z p).card ≤ (r + 1) * N ^ r := by
  classical
  let A := normalizedPatterns v z p
  have hd : A.vcDim ≤ r := Finset.sup_le fun s hs ↦ by
    have h := hr s (normalizedPatterns_independent (Finset.mem_shatterer.mp hs) hz)
    omega
  refine (A.card_le_card_shatterer.trans A.card_shatterer_le_sum_vcDim).trans ?_
  calc
    _ ≤ ∑ _j ∈ Finset.Iic A.vcDim, N ^ r := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left hN _).trans
        (Nat.pow_le_pow_right hp ((Finset.mem_Iic.mp hj).trans hd)))
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (N ^ r) (Nat.succ_le_succ hd)

/-- Perturbing an integral weight within the class hyperplane preserves every
strict negative inequality on a finite set and avoids the pivot hyperplane. -/
theorem exists_weight_nonzero_on_pivot (v : I → G) (z p : G) (w δ : G →+ ℤ)
    (hw : w z = 0) (hδ : δ z = 0) (hp : δ p ≠ 0) :
    ∃ u : G →+ ℤ, u z = 0 ∧ u p ≠ 0 ∧ ∀ i, w (v i) < 0 → u (v i) < 0 := by
  classical
  by_cases h : w p = 0
  · let N : ℤ := (∑ i, (δ (v i)).natAbs : ℕ) + 1
    refine ⟨N • w + δ, by simp [hw,hδ], by simpa [h], fun i hi ↦ ?_⟩
    have hle := Finset.single_le_sum (f := fun i ↦ (δ (v i)).natAbs)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hlt : δ (v i) < N := by
      dsimp [N]
      have hh : δ (v i) ≤ ((δ (v i)).natAbs : ℤ) := Int.le_natAbs
      omega
    have hN : 0 ≤ N := by dsimp [N]; omega
    have hm := mul_le_mul_of_nonneg_left (show w (v i) ≤ -1 by omega) hN
    simp only [AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, zsmul_eq_mul]
    change N * w (v i) + δ (v i) < 0
    simp only [mul_neg, mul_one] at hm
    omega
  · exact ⟨w,hw,h,fun _ hi ↦ hi⟩

/-- Count disjoint systems of strict negative inequalities in the class
hyperplane by assigning a normalized sign pattern to each system. -/
theorem card_disjoint_weight_systems_le {X : Type*} [Fintype X] (v : I → G) (z : G)
    (r N : ℕ) (hz : ∀ a : ℤ, a • z = 0 → a = 0) (hN : Fintype.card I ≤ N) (hp : 0 < N)
    (hr : ∀ (p : G) (s : Finset I),
      LinearIndependent ℤ (Sum.elim (fun i : s ↦ v i.val) (fun t : Bool ↦ if t then p else z)) →
        s.card + 2 ≤ r + 2)
    (w : X → G →+ ℤ) (hw : ∀ x, w x z = 0)
    (hdis : ∀ x y (u : G →+ ℤ), u z = 0 →
      (∀ i, w x (v i) < 0 → u (v i) < 0) → (∀ i, w y (v i) < 0 → u (v i) < 0) → x = y) :
    Fintype.card X ≤ 2 * (r + 1) * N ^ r := by
  classical
  by_cases hex : ∃ (x : X) (p : G), w x p ≠ 0
  · obtain ⟨a,p,ha⟩ := hex
    choose u hu hne hpres using fun x ↦ exists_weight_nonzero_on_pivot v z p (w x) (w a)
      (hw x) (hw a) ha
    let signs (x : X) := Finset.univ.filter fun i ↦ u x (v i) < 0
    have hs (x : X) (q : G) (hq : 0 < u x q) : signs x ∈ normalizedPatterns v z q := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u x, hu x, hq, fun i ↦ by simp [signs]⟩
    let f (x : X) : ↥(normalizedPatterns v z p) ⊕ ↥(normalizedPatterns v z (-p)) :=
      if hx : 0 < u x p then .inl ⟨_,hs x p hx⟩ else
        .inr ⟨_,hs x (-p) (by rw [map_neg]; have := hne x; omega)⟩
    have recover (x : X) : Sum.elim Subtype.val Subtype.val (f x) = signs x := by
      dsimp [f]
      split <;> rfl
    have hinj : Function.Injective f := by
      intro x y hxy
      have he : signs x = signs y := by rw [← recover x, ← recover y, hxy]
      apply hdis x y (u x) (hu x) (hpres x)
      intro i hi
      have hy : i ∈ signs y := by simp [signs, hpres y i hi]
      exact (Finset.mem_filter.mp (he.symm ▸ hy : i ∈ signs x)).2
    have hcard := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_sum, Fintype.card_coe] at hcard
    have h₁ := card_normalizedPatterns_le v z p r N hz hN hp (hr p)
    have h₂ := card_normalizedPatterns_le v z (-p) r N hz hN hp (hr (-p))
    rw [mul_assoc, two_mul]
    omega
  · have : Subsingleton X := ⟨fun x y ↦ hdis x y 0 rfl
        (fun i hi ↦ (hex ⟨x,v i,hi.ne⟩).elim) (fun i hi ↦ (hex ⟨y,v i,hi.ne⟩).elim)⟩
    exact (Fintype.card_le_one_iff_subsingleton.mpr inferInstance).trans (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) (Nat.pow_pos hp))

end EFiniteCharacterizations
