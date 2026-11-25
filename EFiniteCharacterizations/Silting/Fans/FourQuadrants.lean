module

public import EFiniteCharacterizations.Silting.Fans.SectorSubdivision

/-! # A finite cover of the plane by compatible sectors -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R]

/-- The two-term complex concentrated in degree −1 at one finite projective. -/
abbrev inDegreeMinusOne (P : FiniteProjective R) : TwoTerm R :=
  ⟨P.val, (ProjectiveClass.zeroProjective R).val, P.property,
    (ProjectiveClass.zeroProjective R).property, 0⟩

@[simp] theorem projectiveClass_inDegreeMinusOne (P : FiniteProjective R) :
    (inDegreeMinusOne P).projectiveClass = -ProjectiveClass.of P := by
  change ProjectiveClass.of (ProjectiveClass.zeroProjective R) - ProjectiveClass.of P = _
  simp

@[simp] theorem projectiveClass_inDegreeZero (P : FiniteProjective R) :
    ((let _ := P.property; inDegreeZero P.val) : TwoTerm R).projectiveClass = ProjectiveClass.of P := by
  change ProjectiveClass.of P - ProjectiveClass.of (ProjectiveClass.zeroProjective R) = _
  simp

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

theorem shiftedHomFinrank_eq_zero_of_isZero_source {P Q : TwoTerm R} (h : IsZero P.source) :
    P.shiftedHomFinrank k Q = 0 := by
  apply (shiftedHomFinrank_eq_zero_iff k P Q).2
  intro f
  exact ⟨0, (map_zero (P.homotopyBoundary Q)).trans (h.eq_of_src 0 f)⟩

theorem shiftedHomFinrank_eq_zero_of_isZero_target {P Q : TwoTerm R} (h : IsZero Q.target) :
    P.shiftedHomFinrank k Q = 0 := by
  apply (shiftedHomFinrank_eq_zero_iff k P Q).2
  intro f
  exact ⟨0, (map_zero (P.homotopyBoundary Q)).trans (h.eq_of_tgt 0 f)⟩

include k in
theorem isPresilting_inDegreeMinusOne (P : FiniteProjective R) : (inDegreeMinusOne P).IsPresilting := by
  apply (shiftedHomFinrank_eq_zero_iff k _ _).1
  exact shiftedHomFinrank_eq_zero_of_isZero_target k ProjectiveClass.zeroProjective_isZero

omit [Module.Finite k R] in
/-- The reverse shifted Hom between opposite stalks is the ordinary Hom
between their projective terms. -/
theorem shiftedHomFinrank_opposite_stalks (P Q : FiniteProjective R) :
    (inDegreeMinusOne P).shiftedHomFinrank k (let _ := Q.property; inDegreeZero Q.val) =
      Module.finrank k (P.val ⟶ Q.val) := by
  unfold shiftedHomFinrank
  apply LinearEquiv.finrank_eq
  apply Submodule.quotEquivOfEqBot
  rw [LinearMap.range_eq_bot]
  apply LinearMap.ext
  intro f
  change f.1 ≫ 0 - (0 : P.val ⟶ _) ≫ f.2 = 0
  simp

/-- The finite test in the two mixed-sign quadrants. -/
def ProjectiveMediantsCovered (P Q : FiniteProjective R) : Prop :=
  ∀ c ∈ sternBrocotMediants (Module.finrank k (Q.val ⟶ P.val))
      (ProjectiveClass.of P) (-ProjectiveClass.of Q) ∪
    sternBrocotMediants (Module.finrank k (P.val ⟶ Q.val))
      (ProjectiveClass.of Q) (-ProjectiveClass.of P),
    ∃ Z : TwoTerm R, Z.IsPresilting ∧ Z.projectiveClass = c

include k in
/-- The two finite mediant tests cover the plane by at most the sum of the
two mixed-quadrant bounds and the two same-sign quadrants. -/
theorem exists_bounded_plane_cover_of_mediants {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : ProjectiveClass R →+ V) (P Q : FiniteProjective R) (hc : ProjectiveMediantsCovered k P Q)
    (hspan : ∀ v : V, ∃ a b : ℝ, a • g (ProjectiveClass.of P) + b • g (ProjectiveClass.of Q) = v) :
    ∃ s : List (TwoTerm R × TwoTerm R),
      s.length ≤ 2 ^ Module.finrank k (Q.val ⟶ P.val) + 2 ^ Module.finrank k (P.val ⟶ Q.val) + 2 ∧
      (∀ p ∈ s, (p.1.directSum p.2).IsPresilting) ∧
      ∀ v : V, ∃ p ∈ s, v ∈ sectorBetween (g p.1.projectiveClass) (g p.2.projectiveClass) := by
  let _ := P.property
  let _ := Q.property
  let A := inDegreeZero P.val
  let B := inDegreeZero Q.val
  let A' := inDegreeMinusOne P
  let B' := inDegreeMinusOne Q
  have pa : A.projectiveClass = ProjectiveClass.of P := projectiveClass_inDegreeZero P
  have pb : B.projectiveClass = ProjectiveClass.of Q := projectiveClass_inDegreeZero Q
  have pa' : A'.projectiveClass = -ProjectiveClass.of P := projectiveClass_inDegreeMinusOne P
  have pb' : B'.projectiveClass = -ProjectiveClass.of Q := projectiveClass_inDegreeMinusOne Q
  have hA : A.IsPresilting := isPresilting_inDegreeZero _
  have hB : B.IsPresilting := isPresilting_inDegreeZero _
  have hA' : A'.IsPresilting := isPresilting_inDegreeMinusOne k P
  have hB' : B'.IsPresilting := isPresilting_inDegreeMinusOne k Q
  have hzero : IsZero (ProjectiveClass.zeroProjective R).val := ProjectiveClass.zeroProjective_isZero
  have ha (U : TwoTerm R) : A.shiftedHomFinrank k U = 0 := shiftedHomFinrank_eq_zero_of_isZero_source k hzero
  have hb (U : TwoTerm R) : B.shiftedHomFinrank k U = 0 := shiftedHomFinrank_eq_zero_of_isZero_source k hzero
  have ha' (U : TwoTerm R) : U.shiftedHomFinrank k A' = 0 := shiftedHomFinrank_eq_zero_of_isZero_target k hzero
  have hb' (U : TwoTerm R) : U.shiftedHomFinrank k B' = 0 := shiftedHomFinrank_eq_zero_of_isZero_target k hzero
  obtain ⟨s, hslen, hs, hsc⟩ := exists_presilting_sector_cover_of_mediants k g _ A B' hA hB' (ha B')
    (shiftedHomFinrank_opposite_stalks k Q P).le (by
      rw [pa, pb']
      exact fun c h ↦ hc c (Or.inl h))
  obtain ⟨t, htlen, ht, htc⟩ := exists_presilting_sector_cover_of_mediants k g _ B A' hB hA' (hb A')
    (shiftedHomFinrank_opposite_stalks k P Q).le (by
      rw [pb, pa']
      exact fun c h ↦ hc c (Or.inr h))
  refine ⟨(A, B) :: (A', B') :: (s ++ t), ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_append]
    omega
  · simp only [List.mem_cons, List.mem_append]
    intro p hp
    rcases hp with rfl | rfl | hp | hp
    · exact (isPresilting_directSum_iff k A B).2 ⟨hA, hB, ha B, hb A⟩
    · exact (isPresilting_directSum_iff k A' B').2 ⟨hA', hB', hb' A', ha' B'⟩
    · exact hs p hp
    · exact ht p hp
  · intro v
    obtain ⟨a, b, hv⟩ := hspan v
    rcases le_total 0 a with ha₀ | ha₀ <;> rcases le_total 0 b with hb₀ | hb₀
    · refine ⟨(A, B), by simp, a, b, ha₀, hb₀, ?_⟩
      simpa only [pa, pb] using hv
    · have hv' : v ∈ sectorBetween (g A.projectiveClass) (g B'.projectiveClass) :=
        ⟨a, -b, ha₀, neg_nonneg.mpr hb₀, by simpa only [pa, pb', map_neg, neg_smul, smul_neg, neg_neg] using hv⟩
      rw [hsc] at hv'
      obtain ⟨p, hp, hvp⟩ := hv'
      exact ⟨p, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hp)), hvp⟩
    · have hv' : v ∈ sectorBetween (g B.projectiveClass) (g A'.projectiveClass) :=
        ⟨b, -a, hb₀, neg_nonneg.mpr ha₀, by simpa only [pb, pa', map_neg, neg_smul, smul_neg, neg_neg, add_comm] using hv⟩
      rw [htc] at hv'
      obtain ⟨p, hp, hvp⟩ := hv'
      exact ⟨p, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hp)), hvp⟩
    · refine ⟨(A', B'), by simp, -a, -b, neg_nonneg.mpr ha₀, neg_nonneg.mpr hb₀, ?_⟩
      simpa only [pa', pb', map_neg, neg_smul, smul_neg, neg_neg] using hv

include k in
/-- If two projective classes span the space, E-finiteness gives a finite
cover of that whole space by sectors of compatible presilting pairs. -/
theorem exists_presilting_plane_cover (hR : IsEFinite R) {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : ProjectiveClass R →+ V) (P Q : FiniteProjective R)
    (hspan : ∀ v : V, ∃ a b : ℝ, a • g (ProjectiveClass.of P) + b • g (ProjectiveClass.of Q) = v) :
    ∃ s : List (TwoTerm R × TwoTerm R),
      (∀ p ∈ s, (p.1.directSum p.2).IsPresilting) ∧
      ∀ v : V, ∃ p ∈ s, v ∈ sectorBetween (g p.1.projectiveClass) (g p.2.projectiveClass) := by
  obtain ⟨s, _, hs, hcov⟩ := exists_bounded_plane_cover_of_mediants k g P Q (fun c _ ↦ hR c) hspan
  exact ⟨s, hs, hcov⟩

end EFiniteCharacterizations.TwoTerm
