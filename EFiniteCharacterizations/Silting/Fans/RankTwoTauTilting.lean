module

public import EFiniteCharacterizations.Silting.Fans.RankTwoTauCompletion
public import EFiniteCharacterizations.LinearAlgebra.FiniteSectorCover

/-!
# Theorem B: E-finiteness, brick-finiteness, and `τ`-tilting finiteness in rank at most two

Section 8 of the manuscript (`intro:rank-two` and `thm:rank-two`). For a
finite-dimensional algebra of rank `n ≤ 2` over an arbitrary field `k`:

* `RankTwoBricks.lean` proves `(E-fin) ⇔ brick-finite` via Stern–Brocot mediant
  subdivision of the two mixed-sign quadrants (`SectorSubdivision.lean`), producing
  finitely many compatible presilting sectors whose boundary weights detect all bricks;
* this file completes the cycle `(E-fin) ⇔ τ-tilting finite` (`rankTwoEquivalences`)
  by bounding indecomposable `τ`-rigid modules from the finite sector cover in the
  forward direction and covering the plane from finitely many `τ`-rigid rays in the
  converse direction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

theorem moduleProjectiveClass_projective (K : FiniteProjective R) :
    moduleProjectiveClass k K.val = ProjectiveClass.of K := by
  rw [moduleProjectiveClass_of_projective_epi k K (𝟙 _),
    projectiveCoverClass_iso k ((isZero_kernel_of_mono (𝟙 K.val)).iso ProjectiveClass.zeroProjective_isZero),
    projectiveCoverClass_projective,ProjectiveClass.of_zeroProjective,sub_zero]

private theorem tauRigid_projective (K : FiniteProjective R) : IsTauRigid k K.val := by
  let _ := K.property
  exact (isTauRigid_iff_exists_presilting_cokernel k K.val).2 ⟨TwoTerm.inDegreeZero K.val,
    TwoTerm.isPresilting_inDegreeZero _,⟨cokernelZeroIsoTarget ..⟩⟩

/-- Classes of minimal presentations of indecomposable tau-rigid modules and
of indecomposable projectives placed in degree minus one. -/
private def rayClasses : Set (ProjectiveClass R) :=
  {c | (∃ X : FGModuleCat.{u} R, Indecomposable X ∧ IsTauRigid k X ∧ moduleProjectiveClass k X = c) ∨
       ∃ K : FiniteProjective R, Indecomposable K.val ∧ -ProjectiveClass.of K = c}

private theorem finite_rayClasses (h : (indecomposableTauRigidClasses (R := R) k).Finite) :
    (rayClasses (R := R) k).Finite := by
  let f (c : Skeleton (FGModuleCat.{u} R)) := moduleProjectiveClass k ((fromSkeleton _).obj c)
  apply ((h.image f).union (h.image (fun c ↦ -f c))).subset
  rintro c (⟨X,hX,hτ,rfl⟩ | ⟨K,hK,rfl⟩)
  · exact Or.inl ⟨toSkeleton X,⟨X,hX,hτ,rfl⟩,moduleProjectiveClass_iso k (fromSkeletonToSkeletonIso X)⟩
  · refine Or.inr ⟨toSkeleton K.val,⟨K.val,hK,tauRigid_projective k K,rfl⟩,?_⟩
    exact congrArg Neg.neg ((moduleProjectiveClass_iso k (fromSkeletonToSkeletonIso K.val)).trans
      (moduleProjectiveClass_projective k K))

private theorem exists_presilting_of_rayClass {c : ProjectiveClass R} (h : c ∈ rayClasses k) :
    ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = c := by
  rcases h with ⟨X,_,⟨p,hp⟩,rfl⟩ | ⟨K,_,rfl⟩
  · exact ⟨p.twoTerm,(TwoTerm.surjective_boundary_iff_surjective_precompose _ _).2
      (p.twoTerm.surjective_precompose_of_iso p.cokernelIso.symm
        ((p.twoTerm.surjective_precompose_iff_no_hom_nakayamaKernel k X).2 hp)),p.projectiveClass_eq k⟩
  · exact ⟨TwoTerm.inDegreeMinusOne K,TwoTerm.isPresilting_inDegreeMinusOne k K,TwoTerm.projectiveClass_inDegreeMinusOne K⟩

omit [IsNoetherianRing R] in
private theorem surjective_precompose_retract (P : TwoTerm R) {M X : FGModuleCat.{u} R}
    (i : M ⟶ X) (r : X ⟶ M) (h : i ≫ r = 𝟙 M) (hs : Function.Surjective (P.precompose X)) :
    Function.Surjective (P.precompose M) := by
  intro t
  obtain ⟨v,hv⟩ := hs (t ≫ i)
  change P.differential ≫ v = t ≫ i at hv
  exact ⟨v ≫ r,by change P.differential ≫ v ≫ r = t; rw [← Category.assoc,hv,Category.assoc,h,Category.comp_id]⟩

/-- If a compatible complex lies in an open linear half-space, then one
indecomposable module summand or shifted projective summand already lies there. -/
private theorem exists_positive_compatible_ray (P Q : TwoTerm R) (hc : (P.directSum Q).IsPresilting)
    (f : ProjectiveClass R →+ ℝ) (hq : 0 < f Q.projectiveClass) :
    ∃ L : TwoTerm R, L.projectiveClass ∈ rayClasses k ∧ (P.directSum L).IsPresilting ∧ 0 < f L.projectiveClass := by
  classical
  obtain ⟨hp,hQ,h₁,h₂⟩ := (TwoTerm.isPresilting_directSum_iff k _ _).1 hc
  have hPQ := (TwoTerm.surjective_boundary_iff_surjective_precompose P Q).1
    ((TwoTerm.shiftedHomFinrank_eq_zero_iff k P Q).1 h₁)
  have hQP := (TwoTerm.surjective_boundary_iff_surjective_precompose Q P).1
    ((TwoTerm.shiftedHomFinrank_eq_zero_iff k Q P).1 h₂)
  obtain ⟨K,j,s,hjs,hj,he⟩ := Q.exists_projectiveClass_cokernel_sub k
  rw [he,map_sub] at hq
  let X := cokernel Q.differential
  by_cases hX : 0 < f (moduleProjectiveClass k X)
  · let W : AddSubmonoid (ProjectiveClass R) := {
      carrier := {v | f v ≤ 0}, zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by change f (a+b) ≤ 0; rw [map_add]; exact add_nonpos ha hb }
    obtain ⟨D,hD,i,r,hir,hd⟩ : ∃ (D : FGModuleCat.{u} R), Indecomposable D ∧
        ∃ (i : D ⟶ X) (r : X ⟶ D), i ≫ r = 𝟙 _ ∧ 0 < f (moduleProjectiveClass k D) := by
      by_contra! hn
      exact hX.not_ge (moduleProjectiveClass_mem_of_retracts k X W hn)
    let p := (MinimalPresentation.nonempty_minimalPresentation k D).some
    have hτ := Q.isTauRigid_of_cokernel_retract k hQ i r hir
    have hm {N : FGModuleCat R} (hN : Function.Surjective (Q.precompose N)) :=
      p.surjective_precompose_of_presentation_retract i r hir Q (cokernel.π _) (cokernel.condition _)
        (ShortComplex.exact_cokernel _) hN
    refine ⟨p.twoTerm,Or.inl ⟨D,hD,hτ,(p.projectiveClass_eq k).symm⟩,?_,by rwa [p.projectiveClass_eq k]⟩
    apply TwoTerm.compatible_of_precompose k hp
    · exact P.surjective_precompose_of_iso p.cokernelIso.symm (surjective_precompose_retract P i r hir hPQ)
    · exact hm hQP
    · apply p.twoTerm.surjective_precompose_of_iso p.cokernelIso.symm
      exact hm (surjective_precompose_retract Q i r hir ((TwoTerm.surjective_boundary_iff_surjective_precompose Q Q).1 hQ))
  · have hK : f (moduleProjectiveClass k K.val) < 0 := by
      rw [moduleProjectiveClass_projective]
      change ¬ 0 < f (moduleProjectiveClass k (cokernel Q.differential)) at hX
      linarith
    let W : AddSubmonoid (ProjectiveClass R) := {
      carrier := {v | 0 ≤ f v}, zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by change 0 ≤ f (a+b); rw [map_add]; exact add_nonneg ha hb }
    obtain ⟨D,hD,i,r,hir,hd⟩ : ∃ (D : FGModuleCat.{u} R), Indecomposable D ∧
        ∃ (i : D ⟶ K.val) (r : K.val ⟶ D), i ≫ r = 𝟙 _ ∧ f (moduleProjectiveClass k D) < 0 := by
      by_contra! hn
      exact hK.not_ge (moduleProjectiveClass_mem_of_retracts k K.val W hn)
    let _ := K.property
    let A : FiniteProjective R := ⟨D,Module.Projective.of_split i.hom.hom r.hom.hom
      (congrArg (fun t : D ⟶ D ↦ t.hom.hom) hir)⟩
    let L := TwoTerm.inDegreeMinusOne A
    have hl := TwoTerm.projectiveClass_inDegreeMinusOne A
    refine ⟨L,Or.inr ⟨A,hD,hl.symm⟩,?_,?_⟩
    · apply (TwoTerm.isPresilting_directSum_iff k _ _).2
      refine ⟨hp,TwoTerm.isPresilting_inDegreeMinusOne k A,TwoTerm.shiftedHomFinrank_eq_zero_of_isZero_target k
        ProjectiveClass.zeroProjective_isZero,?_⟩
      apply (TwoTerm.shiftedHomFinrank_eq_zero_iff k _ _).2
      apply (TwoTerm.surjective_boundary_iff_surjective_precompose L P).2
      intro t
      obtain ⟨v,hv⟩ := hQP (s ≫ r ≫ t)
      change Q.differential ≫ v = s ≫ r ≫ t at hv
      have hh := congrArg (fun z ↦ i ≫ j ≫ z) hv
      have ht : t = 0 := by
        rw [← Category.assoc j, hj,zero_comp,comp_zero,← Category.assoc j,hjs,Category.id_comp,← Category.assoc,hir,Category.id_comp] at hh
        exact hh.symm
      exact ⟨0,by rw [ht,map_zero]⟩
    · rw [hl,map_neg,neg_pos,← moduleProjectiveClass_projective k A]
      exact hd

/-- Any open half-plane bounded by the line of a presilting class contains
a compatible indecomposable direction. -/
private theorem exists_ray_in_halfspace (P : TwoTerm R) (hp : P.IsPresilting)
    (l : RealProjectiveSpace R →ₗ[ℝ] ℝ) (hl : l ≠ 0)
    (hz : l (realProjectiveClass R P.projectiveClass) = 0) :
    ∃ Q : TwoTerm R, Q.projectiveClass ∈ rayClasses k ∧ (P.directSum Q).IsPresilting ∧
      0 < l (realProjectiveClass R Q.projectiveClass) := by
  classical
  let f := l.toAddMonoidHom.comp (realProjectiveClass R)
  obtain ⟨G,hG⟩ : ∃ G : FiniteProjective R, f (ProjectiveClass.of G) ≠ 0 := by
    by_contra! hn
    apply hl
    apply LinearMap.ker_eq_top.1
    apply top_unique
    rw [← span_realProjectiveClasses R]
    exact Submodule.span_le.2 (by rintro _ ⟨G,rfl⟩; exact hn G)
  change f P.projectiveClass = 0 at hz
  rcases lt_or_gt_of_ne hG with h | h
  · obtain ⟨Q,hc,he⟩ := P.exists_compatible_sub_projective k hp G
    exact exists_positive_compatible_ray k P Q hc f (by simp [he,hz,h])
  · obtain ⟨Q,hc,he⟩ := P.exists_compatible_add_projective k hp G
    exact exists_positive_compatible_ray k P Q hc f (by simp [he,hz,h])

variable [IsArtinianRing R]

include k in
theorem isEFinite_of_tauTiltingFinite_of_rank_le_two
    (hr : (simpleIsomorphismClasses R).ncard ≤ 2) (ht : IsTauTiltingFinite (R := R) k) : IsEFinite R := by
  classical
  obtain ⟨hfin,hd⟩ := realProjectiveSpace_rank_bound k (R := R)
  by_cases hsmall : Module.finrank ℝ (RealProjectiveSpace R) ≤ 1
  · exact isEFinite_of_projective_rank_le_one k hsmall
  have hdim : Module.finrank ℝ (RealProjectiveSpace R) = 2 := by omega
  let φ := realProjectiveClass R
  let s := φ '' rayClasses (R := R) k
  have hs : s.Finite := (finite_rayClasses k ((isTauTiltingFinite_iff_finite_indecomposable_of_rank_le_two k hr).1 ht)).image φ
  let C (v w : RealProjectiveSpace R) := ∃ P Q : TwoTerm R, (P.directSum Q).IsPresilting ∧
    φ P.projectiveClass = v ∧ φ Q.projectiveClass = w
  let Z := TwoTerm.contractible (ProjectiveClass.zeroProjective R)
  have hZ : Z.IsPresilting := (TwoTerm.shiftedHomFinrank_eq_zero_iff k Z Z).1
    (TwoTerm.shiftedHomFinrank_contractible_source k _ _)
  have hz : φ Z.projectiveClass = 0 := by simp [Z,TwoTerm.projectiveClass]
  apply isEFinite_of_integral_classes_in_presilting_sectors k
  intro g
  by_cases h : φ g = 0
  · have htt := (TwoTerm.shiftedHomFinrank_eq_zero_iff k Z Z).2 hZ
    refine ⟨Z,Z,(TwoTerm.isPresilting_directSum_iff k Z Z).2 ⟨hZ,hZ,htt,htt⟩,0,0,le_rfl,le_rfl,?_⟩
    simpa using h.symm
  obtain ⟨v,w,⟨P,Q,hPQ,hv,hw⟩,hsec⟩ := mem_sector_of_finite_directions hdim s hs C
    (fun l hl ↦ by
      obtain ⟨Q,hQ,_,hq⟩ := exists_ray_in_halfspace k Z hZ l hl (by change l (φ _) = _; rw [hz,map_zero])
      exact ⟨_,⟨_,hQ,rfl⟩,hq⟩)
    (fun v hv l hl hzero ↦ by
      obtain ⟨c,hc,rfl⟩ := hv
      obtain ⟨P,hp,rfl⟩ := exists_presilting_of_rayClass k hc
      obtain ⟨Q,hQ,hPQ,hq⟩ := exists_ray_in_halfspace k P hp l hl hzero
      exact ⟨_,⟨_,hQ,rfl⟩,⟨P,Q,hPQ,rfl,rfl⟩,hq⟩) (φ g) h
  exact ⟨P,Q,hPQ,by change φ g ∈ sectorBetween (φ _) (φ _); rwa [hv,hw]⟩

include k in
theorem isEFinite_iff_tauTiltingFinite_of_rank_le_two (hr : (simpleIsomorphismClasses R).ncard ≤ 2) :
    IsEFinite R ↔ IsTauTiltingFinite (R := R) k :=
  ⟨isTauTiltingFinite_of_isEFinite_of_rank_le_two k hr, isEFinite_of_tauTiltingFinite_of_rank_le_two k hr⟩

omit [IsNoetherianRing R] [IsArtinianRing R] in
include k in
/-- Theorem B, for right modules over a finite-dimensional algebra of rank at
most two over an arbitrary field. -/
theorem rankTwoEquivalences (hr : (simpleIsomorphismClasses Rᵐᵒᵖ).ncard ≤ 2) :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    (IsEFinite Rᵐᵒᵖ ↔ IsTauTiltingFinite (R := Rᵐᵒᵖ) k) ∧
      (IsEFinite Rᵐᵒᵖ ↔ (brickClasses (C := FGModuleCat.{u} Rᵐᵒᵖ)).Finite) := by
  let _ := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let _ := IsArtinianRing.of_finite k Rᵐᵒᵖ
  exact ⟨isEFinite_iff_tauTiltingFinite_of_rank_le_two k hr,isEFinite_iff_brickFinite_of_rank_le_two k hr⟩

end EFiniteCharacterizations
