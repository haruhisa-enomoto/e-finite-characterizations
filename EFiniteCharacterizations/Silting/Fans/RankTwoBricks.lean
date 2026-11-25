module

public import EFiniteCharacterizations.Presentations.CokernelGenerators
public import EFiniteCharacterizations.Characterizations.FixedClassFiniteness

/-! # Stable bricks in a finite rank-two sector cover -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace EFiniteCharacterizations

namespace TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

private theorem retract_comp {C : Type*} [Category* C] {D F G : C} (a : D ⟶ F) (b : F ⟶ D)
      (c : F ⟶ G) (d : G ⟶ F) (h : a ≫ b = 𝟙 _) (h' : c ≫ d = 𝟙 _) :
      (a ≫ c) ≫ (d ≫ b) = 𝟙 _ := by rw [Category.assoc, ← Category.assoc c, h', Category.id_comp, h]

private theorem nonpos_of_arrow_retract {P Q : TwoTerm R} (hP : P.IsPresilting) (hQ : Q.IsPresilting)
    (a : P.asArrow ⟶ Q.asArrow) (b : Q.asArrow ⟶ P.asArrow) (hab : a ≫ b = 𝟙 _)
    {X : FGModuleCat.{u} R} (hx : (Q.eulerWeight k).IsSemistable X) :
    ∀ {U : FGModuleCat.{u} R} (i : U ⟶ X) [Mono i], (P.eulerWeight k).eval U ≤ 0 := by
  apply (P.nonpos_eulerWeight_all_subobjects_iff k hP X).2
  have hz := ((Q.isSemistable_eulerWeight_iff_perpendicular k hQ X).1 hx).1
  let F := arrowCokernel (FGModuleCat.{u} R)
  have h : F.map a ≫ F.map b = 𝟙 _ := by rw [← F.map_comp, hab, F.map_id]
  change Subsingleton (F.obj P.asArrow ⟶ X)
  refine ⟨fun f g ↦ ?_⟩
  change Subsingleton (F.obj Q.asArrow ⟶ X) at hz
  have hf := hz.elim (F.map b ≫ f) (F.map b ≫ g)
  calc
    f = (F.map a ≫ F.map b) ≫ f := by rw [h, Category.id_comp]
    _ = (F.map a ≫ F.map b) ≫ g := by rw [Category.assoc, hf, Category.assoc]
    _ = g := by rw [h, Category.id_comp]

/-- Positive multiplicities on a compatible pair can both be replaced by one
without losing any stable brick. -/
private theorem stable_sum_of_positive_copies (E L : TwoTerm R)
    (hEL : (E.directSum L).IsPresilting) (m n : ℕ) {X : FGModuleCat.{u} R}
    (hs : ((m+1) • E.eulerWeight k + (n+1) • L.eulerWeight k).IsStable X) :
    (E.eulerWeight k + L.eulerWeight k).IsStable X := by
  obtain ⟨hE, hL, h₁, h₂⟩ := (isPresilting_directSum_iff k E L).1 hEL
  let A := E.copies (m+1)
  let B := L.copies (n+1)
  let Y := A.directSum B
  have hy : Y.IsPresilting := by
    apply (isPresilting_directSum_iff k A B).2
    refine ⟨isPresilting_copies k hE _, isPresilting_copies k hL _, ?_, ?_⟩ <;>
      simp only [A, B, shiftedHomFinrank_copies_source, shiftedHomFinrank_copies_target, h₁, h₂, Nat.mul_zero]
  have hwt : Y.eulerWeight k = (m+1) • E.eulerWeight k + (n+1) • L.eulerWeight k := by
    rw [← Y.projectiveClassWeight_eq_eulerWeight k, ← E.projectiveClassWeight_eq_eulerWeight k,
      ← L.projectiveClassWeight_eq_eulerWeight k]
    simp [Y,A,B]
  have hY : (Y.eulerWeight k).IsSemistable X := hwt.symm ▸ hs.isSemistable
  have we {U : FGModuleCat R} (i : U ⟶ X) [Mono i] := nonpos_of_arrow_retract k hE hy _ _
    (retract_comp _ _ _ _ (inlDirectSum_fstDirectSum E (E.copies m)) (inlDirectSum_fstDirectSum A B)) hY i
  have wl {U : FGModuleCat R} (i : U ⟶ X) [Mono i] := nonpos_of_arrow_retract k hL hy _ _
    (retract_comp _ _ _ _ (inlDirectSum_fstDirectSum L (L.copies n)) (inrDirectSum_sndDirectSum A B)) hY i
  have nonpos (a : ℕ) (z : ℤ) (hz : z ≤ 0) : (a : ℤ) * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hz
  refine ⟨hs.1, ?_, fun {U} i hi hn hp ↦ ?_⟩
  · have h₀ := hs.2.1
    have he := we (𝟙 X)
    have hl := wl (𝟙 X)
    simp only [Weight.eval, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, add_mul, one_mul] at h₀ ⊢
    dsimp only [Weight.eval] at he hl
    exact le_antisymm (add_nonpos he hl) (by linarith [nonpos m _ he, nonpos n _ hl])
  · change (E.eulerWeight k).eval U + (L.eulerWeight k).eval U < 0
    by_contra! hn'
    have he := we i
    have hl := wl i
    have h₀ : (E.eulerWeight k).eval U = 0 := by omega
    have h₁ : (L.eulerWeight k).eval U = 0 := by omega
    have hlt := hs.2.2 i hn hp
    change (m+1) • (E.eulerWeight k).eval U + (n+1) • (L.eulerWeight k).eval U < 0 at hlt
    simp [h₀, h₁] at hlt

/-- Each sector contributes at most four integral weights for testing stability,
including the origin and both boundary rays. -/
private theorem stable_in_sector {g : ProjectiveClass R} {E L : TwoTerm R}
    (hEL : (E.directSum L).IsPresilting) {X : FGModuleCat.{u} R}
    (hX : (projectiveClassWeight k g).IsStable X)
    (hg : realProjectiveClass R g ∈ sectorBetween (realProjectiveClass R E.projectiveClass)
      (realProjectiveClass R L.projectiveClass)) :
    ∃ q ∈ [0, E.projectiveClass, L.projectiveClass, E.projectiveClass + L.projectiveClass],
      (projectiveClassWeight k q).IsStable X := by
  obtain ⟨a, b, ha, hb, hab⟩ := hg
  change a • ((1 : ℝ) ⊗ₜ[ℤ] E.projectiveClass) + b • ((1 : ℝ) ⊗ₜ[ℤ] L.projectiveClass) =
    (1 : ℝ) ⊗ₜ[ℤ] g at hab
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at hab
  obtain ⟨m, n, p, hp, he⟩ := exists_nat_relation_of_real_tensor_relation _ _ _ ha hb hab
  have h := (stable_nsmul_iff _ X hp).2 hX
  have hw := congrArg (projectiveClassWeight (R := R) k) he
  simp only [map_add, map_nsmul] at hw
  rw [← hw] at h
  cases m with
  | zero =>
    simp only [zero_smul, zero_add] at h
    cases n with
    | zero => exact ⟨0, by simp, by simpa using h⟩
    | succ n => exact ⟨_, by simp, (stable_nsmul_iff _ X (Nat.succ_pos n)).1 h⟩
  | succ m =>
    cases n with
    | zero =>
      simp only [zero_smul, add_zero] at h
      exact ⟨_, by simp, (stable_nsmul_iff _ X (Nat.succ_pos m)).1 h⟩
    | succ n =>
      simp only [projectiveClassWeight_eq_eulerWeight] at h
      refine ⟨E.projectiveClass + L.projectiveClass, by simp, ?_⟩
      simpa only [map_add, projectiveClassWeight_eq_eulerWeight] using stable_sum_of_positive_copies k E L hEL m n h

end TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

include k in
/-- To test E-finiteness one may cover any positive multiple of each integral
class. Stability is constant along a positive ray. -/
theorem isEFinite_iff_positive_multiples_covered :
    IsEFinite R ↔ ∀ g : ProjectiveClass R, ∃ (p : ℕ) (P : TwoTerm R),
      0 < p ∧ P.IsPresilting ∧ P.projectiveClass = p • g := by
  constructor
  · intro h g
    obtain ⟨P,hP,hg⟩ := h g
    exact ⟨1,P,Nat.one_pos,hP,by simpa using hg⟩
  · intro h
    apply isEFinite_of_finite_stableClassesOfEndolength_allFields k
    intro g r _
    obtain ⟨p,P,hp,hP,he⟩ := h g
    apply (P.finite_stableClasses_eulerWeight k hP).subset
    intro x hx
    have hs := stableClassesOfEndolength_subset_stableClasses k _ r hx
    rw [← P.projectiveClassWeight_eq_eulerWeight k, he, map_nsmul]
    exact (stable_nsmul_iff _ _ hp).2 hs

include k in
/-- A real sector cover by compatible pairs detects E-finiteness as soon as
it contains the images of the integral classes. -/
theorem isEFinite_of_integral_classes_in_presilting_sectors
    (hc : ∀ g : ProjectiveClass R, ∃ E L : TwoTerm R, (E.directSum L).IsPresilting ∧
      realProjectiveClass R g ∈ sectorBetween (realProjectiveClass R E.projectiveClass)
        (realProjectiveClass R L.projectiveClass)) : IsEFinite R := by
  apply (isEFinite_iff_positive_multiples_covered k).2
  intro g
  obtain ⟨E,L,hEL,a,b,ha,hb,hab⟩ := hc g
  change a • ((1 : ℝ) ⊗ₜ[ℤ] E.projectiveClass) + b • ((1 : ℝ) ⊗ₜ[ℤ] L.projectiveClass) =
    (1 : ℝ) ⊗ₜ[ℤ] g at hab
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at hab
  obtain ⟨m,n,p,hp,he⟩ := exists_nat_relation_of_real_tensor_relation _ _ _ ha hb hab
  obtain ⟨hE,hL,h₁,h₂⟩ := (TwoTerm.isPresilting_directSum_iff k E L).1 hEL
  refine ⟨p,(E.copies m).directSum (L.copies n),hp,?_,by simpa using he⟩
  apply (TwoTerm.isPresilting_directSum_iff k _ _).2
  refine ⟨TwoTerm.isPresilting_copies k hE _,TwoTerm.isPresilting_copies k hL _,?_,?_⟩ <;>
    simp [TwoTerm.shiftedHomFinrank_copies_source,TwoTerm.shiftedHomFinrank_copies_target,h₁,h₂]

include k in
/-- In a real projective class space of dimension at most one, the signed
projective rays cover every integral class. -/
theorem isEFinite_of_projective_rank_le_one (hr : Module.finrank ℝ (RealProjectiveSpace R) ≤ 1) : IsEFinite R := by
  have := (realProjectiveSpace_rank_bound (R := R) k).1
  apply isEFinite_of_integral_classes_in_presilting_sectors k
  intro g
  let φ := realProjectiveClass R
  have line : ∃ (P : FiniteProjective R) (c : ℝ), c • φ (ProjectiveClass.of P) = φ g := by
    obtain ⟨A,B,h⟩ := ProjectiveClass.exists_sub g
    by_cases ha : φ (ProjectiveClass.of A) = 0
    · exact ⟨B,-1,by simp [← h,ha]⟩
    have hp : 0 < Module.finrank ℝ (RealProjectiveSpace R) := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_,ha⟩
    obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one (K := ℝ) (by omega) ha (φ g)
    exact ⟨A,c,hc⟩
  obtain ⟨P,c,hc⟩ := line
  let _ := P.property
  have ray (A : TwoTerm R) (hA : A.IsPresilting) (t : ℝ) (ht : 0 ≤ t)
      (he : t • φ A.projectiveClass = φ g) :
      ∃ E L : TwoTerm R, (E.directSum L).IsPresilting ∧
        φ g ∈ sectorBetween (φ E.projectiveClass) (φ L.projectiveClass) := by
    have hz := (TwoTerm.shiftedHomFinrank_eq_zero_iff k A A).2 hA
    exact ⟨A,A,(TwoTerm.isPresilting_directSum_iff k A A).2 ⟨hA,hA,hz,hz⟩,
      t,0,ht,le_rfl,by simpa using he⟩
  rcases le_total 0 c with ht | ht
  · apply ray (TwoTerm.inDegreeZero P.val) (TwoTerm.isPresilting_inDegreeZero _) c ht
    rwa [TwoTerm.projectiveClass_inDegreeZero P]
  · apply ray (TwoTerm.inDegreeMinusOne P) (TwoTerm.isPresilting_inDegreeMinusOne k P) (-c) (neg_nonneg.2 ht)
    simpa using hc

include k in
theorem isEFinite_of_rank_le_one (hr : (simpleIsomorphismClasses R).ncard ≤ 1) : IsEFinite R :=
  isEFinite_of_projective_rank_le_one k ((realProjectiveSpace_rank_bound (R := R) k).2.trans hr)

include k in
theorem finite_brickClasses_of_rank_le_two_of_isEFinite
    (hr : (simpleIsomorphismClasses R).ncard ≤ 2) (h : IsEFinite R) :
    (brickClasses (C := FGModuleCat.{u} R)).Finite := by
  classical
  obtain ⟨s, hs, hcover⟩ := exists_presilting_cover_of_simple_rank_le_two k hr h
  let weights (p : TwoTerm R × TwoTerm R) :=
    [0, p.1.projectiveClass, p.2.projectiveClass, p.1.projectiveClass + p.2.projectiveClass]
  let T := (s.flatMap weights).toFinset
  apply (Set.finite_iUnion (fun q : T ↦ stableFiniteAtAllIntegralWeights_of_isEFinite k h q.val)).subset
  intro x hx
  obtain ⟨g, hg⟩ := exists_projective_weight_stable_of_isEFinite k h hx
  obtain ⟨p, hp, hcone⟩ := hcover (realProjectiveClass R g)
  obtain ⟨q, hq, hst⟩ := TwoTerm.stable_in_sector k (hs p hp) hg hcone
  have hq' : q ∈ T := List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨p, hp, hq⟩)
  exact Set.mem_iUnion.mpr ⟨⟨q,hq'⟩, hst⟩

include k in
theorem isEFinite_iff_brickFinite_of_rank_le_two (hr : (simpleIsomorphismClasses R).ncard ≤ 2) :
    IsEFinite R ↔ (brickClasses (C := FGModuleCat.{u} R)).Finite :=
  ⟨finite_brickClasses_of_rank_le_two_of_isEFinite k hr, isEFinite_of_finite_brickClasses_allFields k⟩

omit [IsNoetherianRing R] [IsArtinianRing R] in
include k in
theorem isEFinite_iff_brickFinite_right_of_rank_le_two (hr : (simpleIsomorphismClasses Rᵐᵒᵖ).ncard ≤ 2) :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    IsEFinite Rᵐᵒᵖ ↔ (brickClasses (C := FGModuleCat.{u} Rᵐᵒᵖ)).Finite := by
  let _ := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let _ := IsArtinianRing.of_finite k Rᵐᵒᵖ
  exact isEFinite_iff_brickFinite_of_rank_le_two k hr

end EFiniteCharacterizations
