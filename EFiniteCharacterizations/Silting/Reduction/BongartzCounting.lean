module

public import EFiniteCharacterizations.Silting.Reduction.PerpendicularReduction
public import EFiniteCharacterizations.Subcategories.WidePerpendicular
public import EFiniteCharacterizations.Presentations.BasicSummandClasses
public import EFiniteCharacterizations.Presentations.FinitePresiltingCokernels

/-!
# Spanning projective classes from a presilting complex and its perpendicular simples

Proves the lower rank inequality `n ≤ r + |sim J(P)|` of Lemma 2.2 (`lem:perpendicular`)
over any field by showing that `K₀(proj R)` is spanned by the classes of the `r`
basic summands of `P` together with at most one class per simple object of `J(P)`
(`exists_spanning_weights_for_perpendicular`).
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped EFiniteCharacterizations.IsWideClass

universe u
namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

private theorem generated_of_no_stable_quotient (P : TwoTerm R) (hp : P.IsPresilting)
    (D : FGModuleCat.{u} R) (hd : Function.Surjective (P.precompose D))
    (h : ∀ S : FGModuleCat.{u} R, (P.eulerWeight k).IsStable S → ∀ f : D ⟶ S, f = 0) :
    IsGeneratedBy (cokernel P.differential) D := by
  let θ := P.eulerWeight k
  let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let _ : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
  have all {X : FGModuleCat.{u} R} (hx : W X) : ∀ f : D ⟶ X, f = 0 := by
    apply θ.isWideClass_semistable.extension_induction (fun X ↦ ∀ f : D ⟶ X, f = 0) _ _ hx
    · exact fun X hz f ↦ hz.eq_of_tgt _ _
    · intro row hr hs _ ih f
      let _ := hr.mono_f
      obtain ⟨a,rfl⟩ := hr.exact.lift' f (ih (f ≫ row.g))
      have hS := (θ.isStable_iff_simple ⟨_,hs.1⟩).2 ((IsWideClass.simple_iff_simpleMember (W := W) _).2 hs)
      rw [h _ hS a,zero_comp]
  obtain ⟨T,i,_,hT,hs⟩ := P.exists_semistable_quotient_of_no_hom_nakayamaKernel k hp D
    ((P.surjective_precompose_iff_no_hom_nakayamaKernel k _).1 hd)
  let _ : Epi i := Abelian.epi_of_cokernel_π_eq_zero _ (all hs (cokernel.π i))
  exact hT.of_epi i

private theorem class_mem_of_no_stable_quotient (P Q : TwoTerm R) (hp : P.IsPresilting)
    (hQ : ∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) → Function.Surjective (Q.precompose M))
    (W : Submodule ℤ (ProjectiveClass R)) (hW : ∀ X : TwoTerm R, IsInAdd X.asArrow P.asArrow → X.projectiveClass ∈ W)
    {D : FGModuleCat.{u} R} (hD : Indecomposable D) (hd : Function.Surjective (P.precompose D))
    (i : D ⟶ cokernel Q.differential) (r : cokernel Q.differential ⟶ D) (hir : i ≫ r = 𝟙 _)
    (h : ∀ S : FGModuleCat.{u} R, (P.eulerWeight k).IsStable S → ∀ f : D ⟶ S, f = 0) :
    moduleProjectiveClass k D ∈ W := by
  let C := cokernel P.differential
  obtain ⟨n,a,b,hab⟩ := factor_to_generated_from_bongartz k P Q hp hQ (generated_of_no_stable_quotient k P hp D hd h) r
  let A := fun _ : Fin n ↦ C
  have hadd : IsInAdd D C := by
    refine ⟨List.ofFn (fun j ↦ ((i ≫ a) ≫ biproduct.π A j,biproduct.ι A j ≫ b)),?_⟩
    rw [List.map_ofFn,Fin.sum_ofFn]
    have eq := congrArg (fun z : (⨁ A) ⟶ (⨁ A) ↦ (i ≫ a) ≫ z ≫ b) (biproduct.total (f := A))
    refine Eq.trans ?_ ((congrArg ((i ≫ a) ≫ ·) (Category.id_comp b)).trans ((Category.assoc i a b).trans
      ((congrArg (i ≫ ·) hab).trans hir)))
    simpa only [Function.comp_apply,Preadditive.sum_comp,Preadditive.comp_sum,Category.assoc] using eq
  obtain ⟨j,s,hjs⟩ := FGModuleCat.exists_retraction_of_isInAdd hD hadd
  obtain ⟨p⟩ := MinimalPresentation.nonempty_minimalPresentation k D
  obtain ⟨f,g,c,d,hc,hd,hfg,hcd⟩ := p.exists_split_presentation_maps j s hjs P (cokernel.π _)
    (cokernel.condition _) (ShortComplex.exact_cokernel _)
  rw [← p.projectiveClass_eq k]
  apply hW
  let x : p.twoTerm.asArrow ⟶ P.asArrow := Arrow.homMk c f hc
  let y : P.asArrow ⟶ p.twoTerm.asArrow := Arrow.homMk d g hd
  exact IsInAdd.of_retraction x y (Arrow.hom_ext _ _ hcd hfg)

omit [IsNoetherianRing R] [IsArtinianRing R] in
private theorem shifted_class_mem (P : TwoTerm R) (K : FiniteProjective R)
    {n : ℕ} (a : Fin n → (K.val ⟶ P.source)) (b : Fin n → (P.source ⟶ K.val))
    (ha : ∀ j, a j ≫ P.differential = 0) (hs : ∑ j, a j ≫ b j = 𝟙 _) (W : Submodule ℤ (ProjectiveClass R))
    (hW : ∀ X : TwoTerm R, IsInAdd X.asArrow P.asArrow → X.projectiveClass ∈ W) :
    ProjectiveClass.of K ∈ W := by
  let L := inDegreeMinusOne K
  let x (j) : L.asArrow ⟶ P.asArrow := Arrow.homMk (a j) 0 (by change a j ≫ P.differential = 0 ≫ 0; rw [ha j,zero_comp])
  let y (j) : P.asArrow ⟶ L.asArrow := Arrow.homMk (b j) 0 (by change b j ≫ 0 = P.differential ≫ 0; rw [comp_zero,comp_zero])
  have hL : IsInAdd L.asArrow P.asArrow := by
    refine ⟨List.ofFn (fun j ↦ (x j,y j)),?_⟩
    rw [List.map_ofFn,Fin.sum_ofFn]
    apply Arrow.hom_ext
    · change Arrow.leftFunc.map (∑ j, x j ≫ y j) = _
      rw [Functor.map_sum]
      exact hs
    · exact ProjectiveClass.zeroProjective_isZero.eq_of_src _ _
  simpa only [L,projectiveClass_inDegreeMinusOne,neg_mem_iff] using hW L hL

/-- All ambient projective classes lie in the span of the classes of basic
summands and at most one additional class per stable simple. -/
theorem exists_spanning_weights_for_perpendicular (P : TwoTerm R) (hp : P.IsPresilting) {l}
    (hl : BasicDecomposition P l) :
    ∃ w : Fin l.length ⊕ ↥(stableClasses (P.eulerWeight k)) → ProjectiveClass R,
      ∀ G : FiniteProjective R, ProjectiveClass.of G ∈ Submodule.span ℤ (Set.range w) := by
  classical
  let J := ↥(stableClasses (P.eulerWeight k))
  let S (j : J) := (fromSkeleton _).obj j.val
  let rel (D : FGModuleCat.{u} R) := Indecomposable D ∧ P.LiftsOverWeakTorsion D ∧ Function.Surjective (P.precompose D)
  let hits (j : J) (D : FGModuleCat.{u} R) := rel D ∧ ∃ f : D ⟶ S j, f ≠ 0
  let e (j : J) := if h : ∃ D, hits j D then moduleProjectiveClass k h.choose else 0
  obtain ⟨v,hv⟩ := exists_basic_summand_coordinates k P hl
  let w := Sum.elim v e
  let W := Submodule.span ℤ (Set.range w)
  have hW (X : TwoTerm R) (hX : IsInAdd X.asArrow P.asArrow) : X.projectiveClass ∈ W := by
    apply (Submodule.span_mono (show Set.range v ⊆ Set.range w from ?_)) (hv X hX)
    rintro _ ⟨j,rfl⟩
    exact ⟨Sum.inl j,rfl⟩
  refine ⟨w,fun G ↦ ?_⟩
  let _ := G.property
  obtain ⟨Q,_,hshift,_,hg,hPQ,hQ,_⟩ := exists_bongartz_at_projective_with_source k P hp G.val
  let Z := cokernel Q.differential
  have hZ : moduleProjectiveClass k Z ∈ W := by
    apply moduleProjectiveClass_mem_of_retracts k Z W.toAddSubmonoid
    intro D hD i r hir
    let _ : Epi r := epi_of_epi_fac hir
    have orth := (P.surjective_precompose_iff_no_hom_nakayamaKernel k Z).1 hPQ
    have hd := (P.surjective_precompose_iff_no_hom_nakayamaKernel k D).2
      ⟨fun f g ↦ (cancel_epi r).1 (orth.elim _ _)⟩
    have hr : rel D := ⟨hD,P.liftsOverWeakTorsion_of_bongartz_retract Q hQ i r hir,hd⟩
    by_cases hex : ∃ j, hits j D
    · obtain ⟨j,hj⟩ := hex
      have ex : ∃ E, hits j E := ⟨D,hj⟩
      obtain ⟨d,hd'⟩ := hj.2
      obtain ⟨hr',q,hq⟩ := ex.choose_spec
      obtain ⟨u⟩ := P.iso_of_common_stable_quotient k hp hD hr'.1 hr.2.1 hr'.2.1 hd hr'.2.2
        (show (P.eulerWeight k).IsStable (S j) from j.property) d q hd' hq
      apply Submodule.subset_span
      refine ⟨Sum.inr j,?_⟩
      change e j = _
      rw [show e j = moduleProjectiveClass k ex.choose from dite_eq_left ex]
      exact moduleProjectiveClass_iso k u.symm
    · apply class_mem_of_no_stable_quotient k P Q hp hQ W hW hD hd i r hir
      intro B hb f
      by_contra hf
      let j : J := ⟨toSkeleton B,hb.of_iso (fromSkeletonToSkeletonIso B).symm⟩
      exact hex ⟨j,hr,f ≫ (fromSkeletonToSkeletonIso B).inv,fun h ↦ hf ((cancel_mono _).1 (h.trans zero_comp.symm))⟩
  obtain ⟨K,i,r,hir,hkill,hclass⟩ := Q.exists_projectiveClass_cokernel_sub k
  obtain ⟨m,a,b,ha,hs⟩ := hshift K.val i r hir hkill
  have hC : Q.projectiveClass ∈ W := hclass ▸ W.sub_mem hZ (shifted_class_mem P K a b ha hs W hW)
  rw [hg] at hC
  exact (W.add_mem_iff_left (W.nsmul_mem (hW P (.refl _)) _)).1 hC

end EFiniteCharacterizations.TwoTerm
