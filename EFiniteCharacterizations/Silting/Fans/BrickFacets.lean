module

public import EFiniteCharacterizations.Silting.Fans.PresiltingConeWalls
public import EFiniteCharacterizations.Silting.Reduction.BongartzStableQuotients
public import EFiniteCharacterizations.Stability.MinimalStableWeights
public import EFiniteCharacterizations.Silting.Fans.RankTwoTauCompletion

/-! # Presilting facets in brick walls -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

abbrev TwoTerm.gVectorConeSpan (P : TwoTerm R) :=
  Submodule.span ℝ (P.gVectorCone : Set (RealProjectiveSpace R))

private abbrev RightMinimal (P : TwoTerm R) :=
  ∀ a, a ≫ P.differential = P.differential → IsIso a

private theorem exists_max_stable_cone (hR : IsEFinite R) {B : FGModuleCat.{u} R} (hb : IsBrick B) :
    ∃ P : TwoTerm R, P.IsPresilting ∧ RightMinimal P ∧ (P.eulerWeight k).IsStable B ∧
      ∀ Q : TwoTerm R, Q.IsPresilting → RightMinimal Q → (Q.eulerWeight k).IsStable B →
        Module.finrank ℝ (Q.gVectorConeSpan) ≤ Module.finrank ℝ (P.gVectorConeSpan) := by
  classical
  have := (realProjectiveSpace_rank_bound (R := R) k).1
  obtain ⟨g,hg⟩ := exists_projective_weight_stable_of_isEFinite k hR hb
  obtain ⟨T,ht,rfl⟩ := hR g
  rw [T.projectiveClassWeight_eq_eulerWeight k] at hg
  obtain ⟨p⟩ := MinimalPresentation.nonempty_minimalPresentation k (cokernel T.differential)
  obtain ⟨hp,hs⟩ := T.minimalPresentation_stable k ht p hg
  let A (n : ℕ) := ∃ P : TwoTerm R, P.IsPresilting ∧ RightMinimal P ∧ (P.eulerWeight k).IsStable B ∧
    Module.finrank ℝ (P.gVectorConeSpan) = n
  have h₀ : A (Module.finrank ℝ (p.twoTerm.gVectorConeSpan)) := ⟨_,hp,p.rightMinimal,hs,rfl⟩
  obtain ⟨P,hP,hm,hB,he⟩ := Nat.findGreatest_spec (Submodule.finrank_le (p.twoTerm.gVectorConeSpan)) h₀
  refine ⟨P,hP,hm,hB,fun Q hQ hq hs ↦ he ▸ ?_⟩
  exact Nat.le_findGreatest (Submodule.finrank_le (Q.gVectorConeSpan)) (show A _ from ⟨Q,hQ,hq,hs,rfl⟩)

omit [IsNoetherianRing R] [IsArtinianRing R] in
theorem TwoTerm.gVectorConeSpan_le_directSum (P Q : TwoTerm R) : P.gVectorConeSpan ≤ (P.directSum Q).gVectorConeSpan := by
  apply Submodule.span_mono
  apply Submodule.span_mono
  rintro v ⟨T,hT,rfl⟩
  exact ⟨T,hT.trans (IsInAdd.of_retraction _ _ (TwoTerm.inlDirectSum_fstDirectSum P Q)),rfl⟩

omit [IsArtinianRing R] in
private theorem mem_span_of_max {P V : TwoTerm R} {B : FGModuleCat.{u} R}
    (hm : RightMinimal P) (hV : RightMinimal V) (hB : (P.eulerWeight k).IsStable B)
    (hmax : ∀ Q : TwoTerm R, Q.IsPresilting → RightMinimal Q → (Q.eulerWeight k).IsStable B →
      Module.finrank ℝ (Q.gVectorConeSpan) ≤ Module.finrank ℝ (P.gVectorConeSpan))
    (hc : (P.directSum V).IsPresilting) (hs : (V.eulerWeight k).IsSemistable B) :
    realProjectiveClass R V.projectiveClass ∈ P.gVectorConeSpan := by
  have := (realProjectiveSpace_rank_bound (R := R) k).1
  have hmin : RightMinimal (P.directSum V) := by
    change ∀ a : P.source ⊞ V.source ⟶ P.source ⊞ V.source, a ≫ blockDifferential P.differential V.differential 0 = blockDifferential P.differential V.differential 0 → IsIso a
    rw [blockDifferential_zero]
    exact rightMinimal_biprod_map _ _ hm hV
  have hst := hB.add_of_semistable hs
  have hs' : ((P.directSum V).eulerWeight k).IsStable B := by
    simpa only [← TwoTerm.projectiveClassWeight_eq_eulerWeight k,TwoTerm.projectiveClass_directSum,map_add] using hst
  rw [Submodule.eq_of_le_of_finrank_le (P.gVectorConeSpan_le_directSum V) (hmax _ hc hmin hs')]
  apply Submodule.subset_span
  exact PointedCone.subset_hull ⟨V,IsInAdd.of_retraction _ _ (TwoTerm.inrDirectSum_sndDirectSum P V),rfl⟩

private def RelativeSummand (P : TwoTerm R) (D : FGModuleCat.{u} R) : Prop :=
  Indecomposable D ∧ P.LiftsOverWeakTorsion D ∧ Function.Surjective (P.precompose D)

omit [IsArtinianRing R] in
private theorem one_exceptional_class {P : TwoTerm R} (hp : P.IsPresilting)
    {B : FGModuleCat.{u} R} (hb : (P.eulerWeight k).IsStable B) :
    ∃ e : RealProjectiveSpace R, ∀ D : FGModuleCat.{u} R, RelativeSummand P D →
      ∀ f : D ⟶ B, f ≠ 0 → realProjectiveClass R (moduleProjectiveClass k D) = e := by
  classical
  by_cases hex : ∃ E : FGModuleCat.{u} R, RelativeSummand P E ∧ ∃ q : E ⟶ B, q ≠ 0
  · obtain ⟨E,hE,q,hq⟩ := hex
    refine ⟨realProjectiveClass R (moduleProjectiveClass k E),fun D hD f hf ↦ ?_⟩
    obtain ⟨i⟩ := P.iso_of_common_stable_quotient k hp hD.1 hE.1 hD.2.1 hE.2.1 hD.2.2 hE.2.2 hb f q hf hq
    exact congrArg _ (moduleProjectiveClass_iso k i)
  · exact ⟨0,fun D hD f hf ↦ (hex ⟨D,hD,f,hf⟩).elim⟩

omit [IsArtinianRing R] in
private theorem span_with_one_class {P : TwoTerm R} (hp : P.IsPresilting) (hm : RightMinimal P)
    {B : FGModuleCat.{u} R} (hb : (P.eulerWeight k).IsStable B)
    (hmax : ∀ Q : TwoTerm R, Q.IsPresilting → RightMinimal Q → (Q.eulerWeight k).IsStable B →
      Module.finrank ℝ (Q.gVectorConeSpan) ≤ Module.finrank ℝ (P.gVectorConeSpan)) :
    ∃ e : RealProjectiveSpace R, P.gVectorConeSpan ⊔ Submodule.span ℝ {e} = ⊤ := by
  classical
  obtain ⟨e,he⟩ := one_exceptional_class k hp hb
  let W := P.gVectorConeSpan ⊔ Submodule.span ℝ {e}
  have hinc : P.gVectorConeSpan ≤ W := le_sup_left
  let φ := realProjectiveClass R
  refine ⟨e,top_unique ?_⟩
  rw [← span_realProjectiveClasses R]
  apply Submodule.span_le.2
  rintro _ ⟨G,rfl⟩
  let := G.property
  obtain ⟨Q,_,hmin,hg,hPQ,hQ,_⟩ := P.exists_bongartz_at_projective_rightMinimal k hp G.val
  let Z := cokernel Q.differential
  have hZ : φ (moduleProjectiveClass k Z) ∈ W := by
    apply moduleProjectiveClass_mem_of_retracts k Z (W.toAddSubmonoid.comap φ)
    intro D hD i r hir
    have : Epi r := epi_of_epi_fac hir
    have hperp := (P.surjective_precompose_iff_no_hom_nakayamaKernel k Z).1 hPQ
    have hsD := (P.surjective_precompose_iff_no_hom_nakayamaKernel k D).2
      ⟨fun f g ↦ (cancel_epi r).1 (hperp.elim _ _)⟩
    have hrel : RelativeSummand P D :=
      ⟨hD,P.liftsOverWeakTorsion_of_bongartz_retract Q hQ i r hir,hsD⟩
    change φ (moduleProjectiveClass k D) ∈ W
    by_cases hex : ∃ f : D ⟶ B, f ≠ 0
    · obtain ⟨f,hf⟩ := hex
      rw [show φ (moduleProjectiveClass k D) = e from he D hrel f hf]
      exact (show Submodule.span ℝ {e} ≤ W from le_sup_right) (Submodule.subset_span (Set.mem_singleton _))
    push Not at hex
    obtain ⟨p⟩ := MinimalPresentation.nonempty_minimalPresentation k D
    let V := p.twoTerm
    have hV {M : FGModuleCat.{u} R} (hs : Function.Surjective (P.precompose M)) :
        Function.Surjective (V.precompose M) := p.surjective_precompose_of_presentation_retract i r hir Q
          (cokernel.π _) (cokernel.condition _) (ShortComplex.exact_cokernel _) (hQ _ hs)
    have hPV := P.surjective_precompose_of_iso p.cokernelIso.symm hsD
    have hPP := (TwoTerm.surjective_boundary_iff_surjective_precompose P P).1 hp
    have hc := TwoTerm.compatible_of_precompose k hp hPV (hV hPP) (hV hPV)
    have hv := (TwoTerm.surjective_boundary_iff_surjective_precompose V V).2 (hV hPV)
    have hBs := ((P.isSemistable_eulerWeight_iff_perpendicular k hp B).1 hb.isSemistable).2
    have hs : (V.eulerWeight k).IsSemistable B := by
      refine (V.isSemistable_eulerWeight_iff_perpendicular k hv B).2 ⟨?_,
        (V.surjective_precompose_iff_no_hom_nakayamaKernel k B).1
          (hV ((P.surjective_precompose_iff_no_hom_nakayamaKernel k B).2 hBs))⟩
      exact ⟨fun f g ↦ (cancel_epi p.cokernelIso.inv).1
        ((hex (p.cokernelIso.inv ≫ f)).trans (hex (p.cokernelIso.inv ≫ g)).symm)⟩
    rw [← p.projectiveClass_eq k]
    exact hinc (mem_span_of_max k hm p.rightMinimal hb hmax hc hs)
  have heq := congrArg φ ((Q.projectiveClass_eq_of_rightMinimal k (hmin hm)).symm.trans hg)
  rw [map_add,map_nsmul] at heq
  rw [heq] at hZ
  exact (W.add_mem_iff_left (W.nsmul_mem (hinc (Submodule.subset_span P.class_mem_gVectorCone)) _)).mp hZ

omit [IsArtinianRing R] in
private theorem evaluation_kernel (P : TwoTerm R) (hp : P.IsPresilting) {Y : FGModuleCat.{u} R}
    (hy : (P.eulerWeight k).IsStable Y) :
    P.gVectorConeSpan ≤ LinearMap.ker (realEulerForm k (GrothendieckGroup.of Y)) ∧
    LinearMap.ker (realEulerForm k (GrothendieckGroup.of Y)) ≠ ⊤ := by
  refine ⟨Submodule.span_le.2 (fun v hv ↦ (P.gVectorCone_subset_wall_of_semistable k hp Y hy.isSemistable hv).1),?_⟩
  let A : FiniteProjective R := ⟨FGModuleCat.of R R,inferInstance⟩
  intro he
  have hz : realProjectiveClass R (ProjectiveClass.of A) ∈ LinearMap.ker (realEulerForm k (GrothendieckGroup.of Y)) :=
    he.symm ▸ Submodule.mem_top
  change realEulerEvaluation k _ _ = 0 at hz
  rw [realEulerEvaluation_integral,Int.cast_eq_zero,projectiveClassWeight_of] at hz
  exact (dimensionWeight_pos k Y hy.1).ne' hz

/-- A largest-dimensional cone at which a given brick is stable has
codimension one. All stable modules there have its isomorphism type. -/
theorem exists_unique_stable_presilting_facet (hR : IsEFinite R) {B : FGModuleCat.{u} R} (hB : IsBrick B) :
    ∃ P : TwoTerm R, P.IsPresilting ∧
      Module.finrank ℝ (Submodule.span ℝ (P.gVectorCone : Set (RealProjectiveSpace R))) + 1 =
        Module.finrank ℝ (RealProjectiveSpace R) ∧
      (P.eulerWeight k).IsStable B ∧ ∀ Y : FGModuleCat.{u} R, (P.eulerWeight k).IsStable Y → Nonempty (B ≅ Y) := by
  classical
  have := (realProjectiveSpace_rank_bound (R := R) k).1
  obtain ⟨P,hp,hm,hb,hmax⟩ := exists_max_stable_cone k hR hB
  obtain ⟨e,he⟩ := span_with_one_class k hp hm hb hmax
  have ⟨hBker,hBprop⟩ := evaluation_kernel k P hp hb
  have hproper : P.gVectorConeSpan ≠ ⊤ := fun h ↦ hBprop (top_unique (h ▸ hBker))
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)
  rw [finrank_top] at hlt
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (P.gVectorConeSpan) (Submodule.span ℝ {e})
  rw [he,finrank_top] at hd
  have hs := finrank_span_le_card (R := ℝ) ({e} : Set (RealProjectiveSpace R))
  simp only [Set.toFinset_singleton,Finset.card_singleton] at hs
  have hcodim : Module.finrank ℝ (P.gVectorConeSpan) + 1 = Module.finrank ℝ (RealProjectiveSpace R) := by omega
  refine ⟨P,hp,hcodim,hb,fun Y hy ↦ ?_⟩
  obtain ⟨hYker,hYprop⟩ := evaluation_kernel k P hp hy
  have hk := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hYprop)
  rw [finrank_top] at hk
  have heq := Submodule.eq_of_le_of_finrank_le hYker (by omega)
  by_contra hne
  obtain ⟨g,hpos,hzero⟩ := P.exists_stable_separating_projective_weight k hp hb
  have hz : realProjectiveClass R g ∈ LinearMap.ker (realEulerForm k (GrothendieckGroup.of Y)) := by
    change realEulerEvaluation k _ _ = 0
    rw [realEulerEvaluation_integral,Int.cast_eq_zero]
    exact hzero Y hy hne
  have h := hBker (heq.symm ▸ hz)
  change realEulerEvaluation k _ _ = 0 at h
  rw [realEulerEvaluation_integral,Int.cast_eq_zero] at h
  exact hpos.ne' h

/-- The real wall-face criterion of Theorems A and A′ over every field. -/
theorem isEFinite_iff_wall_face : IsEFinite R ↔ BrickWallFaces (R := R) k :=
  ⟨fun h ↦ (wall_face_iff_unique_stable_presilting_facet k).2
    (fun _ hb ↦ exists_unique_stable_presilting_facet k h hb),isEFinite_of_wall_face k⟩

end EFiniteCharacterizations
