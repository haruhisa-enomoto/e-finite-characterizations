module

public import EFiniteCharacterizations.Presentations.PresiltingCompletions
public import EFiniteCharacterizations.Presentations.TauTilting
public import EFiniteCharacterizations.Silting.Fans.RankTwoBricks

/-! # Completing an indecomposable tau-rigid module in rank two -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

/-- An additive condition on integral g-vectors can be tested on
indecomposable direct summands of the given module. -/
theorem moduleProjectiveClass_mem_of_retracts (Y : FGModuleCat.{u} R) (W : AddSubmonoid (ProjectiveClass R))
    (h : ∀ D : FGModuleCat.{u} R, Indecomposable D → ∀ (i : D ⟶ Y) (r : Y ⟶ D),
      i ≫ r = 𝟙 _ → moduleProjectiveClass k D ∈ W) : moduleProjectiveClass k Y ∈ W := by
  generalize hn : Module.finrank k (Y.obj : Type u) = n
  induction n using Nat.strong_induction_on generalizing Y with
  | h n ih =>
    by_cases hz : IsZero Y
    · have he := (moduleProjectiveClass_iso k (isoBiprodZero (X := Y) hz)).trans (moduleProjectiveClass_biprod k Y Y)
      have hzero := add_eq_left.mp he.symm
      rw [hzero]; exact W.zero_mem
    by_cases hy : Indecomposable Y
    · exact h Y hy (𝟙 _) (𝟙 _) (Category.id_comp _)
    have hs : ¬ ∀ U V : FGModuleCat.{u} R, (Y ≅ U ⊞ V) → IsZero U ∨ IsZero V := fun hs ↦ hy ⟨hz,hs⟩
    push Not at hs
    obtain ⟨U,V,e,hu,hv⟩ := hs
    have hd := ((FGModuleCat.isoToLinearEquiv e).restrictScalars k).finrank_eq.trans (FGModuleCat.finrank_biprod k U V)
    change Module.finrank k (Y.obj : Type u) = Module.finrank k (U.obj : Type u) + Module.finrank k (V.obj : Type u) at hd
    have h₁ := dimensionWeight_pos k U hu
    have h₂ := dimensionWeight_pos k V hv
    rw [dimensionWeight_eval, Int.natCast_pos] at h₁ h₂
    rw [moduleProjectiveClass_iso k e, moduleProjectiveClass_biprod]
    apply W.add_mem
    · apply ih _ (by omega) U _ rfl
      intro D hD i r hr
      exact h D hD (i ≫ biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst ≫ r) (by simp [hr])
    · apply ih _ (by omega) V _ rfl
      intro D hD i r hr
      exact h D hD (i ≫ biprod.inr ≫ e.inv) (e.hom ≫ biprod.snd ≫ r) (by simp [hr])

noncomputable def cokernelBiprodMapIso {C : Type*} [Category* C] [Abelian C]
    {A B X Y : C} (p : A ⟶ X) (q : B ⟶ Y) :
    cokernel (biprod.map p q) ≅ cokernel p ⊞ cokernel q := by
  let d := biprod.map p q
  let a := cokernel.desc p (biprod.inl ≫ cokernel.π d) (by
    rw [← Category.assoc, ← biprod.inl_map, Category.assoc, cokernel.condition, comp_zero])
  let b := cokernel.desc q (biprod.inr ≫ cokernel.π d) (by
    rw [← Category.assoc, ← biprod.inr_map, Category.assoc, cokernel.condition, comp_zero])
  let j := cokernel.desc d (biprod.map (cokernel.π p) (cokernel.π q)) (by ext <;> simp [d])
  refine ⟨j,biprod.desc a b,?_,?_⟩
  · apply (cancel_epi (cokernel.π d)).1
    apply biprod.hom_ext' <;> simp [a,b,j,← Category.assoc] <;> simp [Category.assoc,d]
  · apply biprod.hom_ext'
    · apply (cancel_epi (cokernel.π p)).1
      simp [a,j,← Category.assoc]; simp [Category.assoc]
    · apply (cancel_epi (cokernel.π q)).1
      simp [b,j,← Category.assoc]; simp [Category.assoc]

noncomputable def TwoTerm.cokernelDirectSumIso (P Q : TwoTerm R) :
    cokernel (P.directSum Q).differential ≅ cokernel P.differential ⊞ cokernel Q.differential :=
  (cokernelIsoOfEq (blockDifferential_zero _ _)) ≪≫ cokernelBiprodMapIso _ _

/-- In a projective class space of dimension at least two, an indecomposable
tau-rigid module has a distinct compatible indecomposable module. -/
theorem exists_second_tauRigid_summand (hd : 2 ≤ Module.finrank ℝ (RealProjectiveSpace R))
    (X : FGModuleCat.{u} R) (hx : IsTauRigid k X) :
    ∃ Y : FGModuleCat.{u} R, Indecomposable Y ∧ ¬ Nonempty (X ≅ Y) ∧ IsTauRigid k (X ⊞ Y) := by
  classical
  obtain ⟨p,hp⟩ := hx
  let P := p.twoTerm
  have hr : P.IsPresilting := (TwoTerm.surjective_boundary_iff_surjective_precompose _ _).2
    (P.surjective_precompose_of_iso p.cokernelIso.symm ((P.surjective_precompose_iff_no_hom_nakayamaKernel k X).2 hp))
  let φ := realProjectiveClass R
  let W := Submodule.span ℝ {φ (moduleProjectiveClass k X)}
  have hw : W ≠ ⊤ := by
    intro he
    have hb := finrank_span_le_card (R := ℝ) ({φ (moduleProjectiveClass k X)} : Set _)
    change Module.finrank ℝ W ≤ _ at hb
    rw [he,finrank_top] at hb
    simp at hb
    omega
  obtain ⟨G,hG⟩ : ∃ G : FiniteProjective R, φ (ProjectiveClass.of G) ∉ W := by
    by_contra! hn
    apply hw
    apply top_unique
    rw [← span_realProjectiveClasses R]
    exact Submodule.span_le.2 (by rintro _ ⟨G,rfl⟩; exact hn G)
  obtain ⟨Q,hPQ,he⟩ := P.exists_compatible_cokernel_add_projective k hr p.rightMinimal G
  let Z := cokernel Q.differential
  let T := W.toAddSubmonoid.comap φ
  have hxW : moduleProjectiveClass k X ∈ T := Submodule.subset_span (Set.mem_singleton _)
  have hZ : moduleProjectiveClass k Z ∉ T := by
    intro hz
    have he' := congrArg φ he
    rw [map_add,map_nsmul,p.projectiveClass_eq k] at he'
    change φ (moduleProjectiveClass k (cokernel Q.differential)) ∈ W at hz
    exact hG ((W.add_mem_iff_right (W.nsmul_mem (by exact hxW) _)).1 (he' ▸ hz))
  obtain ⟨Y,hY,i,r,hir,hy⟩ : ∃ (Y : FGModuleCat.{u} R), Indecomposable Y ∧
      ∃ (i : Y ⟶ Z) (r : Z ⟶ Y), i ≫ r = 𝟙 _ ∧ moduleProjectiveClass k Y ∉ T := by
    by_contra! hn
    exact hZ (moduleProjectiveClass_mem_of_retracts k Z T hn)
  refine ⟨Y,hY,fun ⟨e⟩ ↦ hy (moduleProjectiveClass_iso k e ▸ hxW),?_⟩
  let e := P.cokernelDirectSumIso Q
  apply (P.directSum Q).isTauRigid_of_cokernel_retract k hPQ
    (biprod.map p.cokernelIso.inv i ≫ e.inv) (e.hom ≫ biprod.map p.cokernelIso.hom r)
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  apply biprod.hom_ext' <;> simp [← Category.assoc] <;> simp [Category.assoc]
  rw [← Category.assoc,hir,Category.id_comp]

private noncomputable def finTwoBiprodIso {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] [HasBinaryBiproducts C] (Z : Fin 2 → C) :
    (⨁ Z) ≅ Z 0 ⊞ Z 1 := by
  let h := biprod.lift (biproduct.π Z 0) (biproduct.π Z 1)
  let g := biprod.desc (biproduct.ι Z 0) (biproduct.ι Z 1)
  have h₀ : biproduct.ι Z 0 ≫ h = biprod.inl := by apply biprod.hom_ext <;> simp [h]
  have h₁ : biproduct.ι Z 1 ≫ h = biprod.inr := by apply biprod.hom_ext <;> simp [h]
  refine ⟨h,g,?_,?_⟩
  · apply biproduct.hom_ext'
    intro i
    fin_cases i
    · change biproduct.ι Z 0 ≫ h ≫ g = _
      rw [← Category.assoc,h₀,biprod.inl_desc,Category.comp_id]
      rfl
    · change biproduct.ι Z 1 ≫ h ≫ g = _
      rw [← Category.assoc,h₁,biprod.inr_desc,Category.comp_id]
      rfl
  · apply biprod.hom_ext'
    · rw [← Category.assoc,biprod.inl_desc,h₀,Category.comp_id]
    · rw [← Category.assoc,biprod.inr_desc,h₁,Category.comp_id]

omit [IsNoetherianRing R] in
private theorem basicDecomposition_pair {X Y : FGModuleCat.{u} R}
    (hx : Indecomposable X) (hy : Indecomposable Y) (hne : ¬ Nonempty (X ≅ Y)) :
    HasBasicDecomposition 2 (X ⊞ Y) := by
  classical
  let Z : Fin 2 → FGModuleCat.{u} R := ![X,Y]
  have hne' : toSkeleton X ≠ toSkeleton Y := fun h ↦ hne (toSkeleton_eq_toSkeleton_iff.1 h)
  refine ⟨Z,?_,?_,?_⟩
  · intro i; fin_cases i <;> first | exact hx | exact hy
  · intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hne' he)
    · exact False.elim (hne' he.symm)
    · rfl
  · exact ⟨finTwoBiprodIso Z⟩

variable [IsArtinianRing R]

/-- When there are two simple modules and the real projective class space
has dimension at least two, tau-tilting finiteness bounds all indecomposable
tau-rigid modules by the summands of the basic tau-tilting modules. -/
theorem finite_indecomposableTauRigidClasses_of_tauTiltingFinite_rank_two
    (hr : (simpleIsomorphismClasses R).ncard = 2) (hd : 2 ≤ Module.finrank ℝ (RealProjectiveSpace R))
    (ht : IsTauTiltingFinite (R := R) k) : (indecomposableTauRigidClasses (R := R) k).Finite := by
  classical
  let T := basicTauRigidClasses (R := R) k 2
  have hT : T.Finite := by simpa [IsTauTiltingFinite,hr,T] using ht
  have : Finite T := hT
  let F := fromSkeleton (FGModuleCat.{u} R)
  choose l hl using fun c : T ↦ FGModuleCat.exists_list_indecomposable_isInAdd k (F.obj c.val)
  apply (Set.finite_iUnion (fun c : T ↦ ((l c).map toSkeleton).toFinset.finite_toSet)).subset
  rintro _ ⟨X,hX,hτ,rfl⟩
  obtain ⟨Y,hY,hne,hxy⟩ := exists_second_tauRigid_summand k hd X hτ
  let c : T := ⟨toSkeleton (X ⊞ Y),X ⊞ Y,hxy,basicDecomposition_pair hX hY hne,rfl⟩
  let e := fromSkeletonToSkeletonIso (X ⊞ Y)
  obtain ⟨A,hA,hi⟩ := hl c X hX (IsInAdd.of_retraction (biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst) (by simp))
  exact Set.mem_iUnion.mpr ⟨c,List.mem_toFinset.mpr (List.mem_map.mpr ⟨A,hA,(toSkeleton_eq_toSkeleton_iff.2 hi).symm⟩)⟩

include k in
theorem isTauTiltingFinite_iff_finite_indecomposable_of_rank_le_two
    (hr : (simpleIsomorphismClasses R).ncard ≤ 2) :
    IsTauTiltingFinite (R := R) k ↔ (indecomposableTauRigidClasses (R := R) k).Finite := by
  refine ⟨fun h ↦ ?_, finite_basicTauRigidClasses_of_finite_indecomposable k _⟩
  by_cases h₂ : (simpleIsomorphismClasses R).ncard = 2
  · by_cases hd : 2 ≤ Module.finrank ℝ (RealProjectiveSpace R)
    · exact finite_indecomposableTauRigidClasses_of_tauTiltingFinite_rank_two k h₂ hd h
    · exact finite_indecomposableTauRigidClasses_of_rank_le_two k hr (isEFinite_of_projective_rank_le_one k (by omega))
  · exact finite_indecomposableTauRigidClasses_of_rank_le_two k hr (isEFinite_of_rank_le_one k (by omega))

end EFiniteCharacterizations
