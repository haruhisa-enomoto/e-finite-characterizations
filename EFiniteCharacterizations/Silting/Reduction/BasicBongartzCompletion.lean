module

public import EFiniteCharacterizations.Stability.ConeTorsionPairs
public import EFiniteCharacterizations.Presentations.SiltingPresentation
public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickGeneration

/-! # The torsion class of the basic Bongartz completion -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe u
namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

include k in
private theorem transfer_precompose {A B : TwoTerm R}
    (test : ∀ Y : TwoTerm R, Function.Surjective (homotopyBoundary A Y) →
      Function.Surjective (homotopyBoundary B Y)) {M : FGModuleCat.{u} R}
    (h : Function.Surjective (A.precompose M)) : Function.Surjective (B.precompose M) := by
  obtain ⟨m⟩ := MinimalPresentation.nonempty_minimalPresentation k M
  apply B.surjective_precompose_of_iso m.cokernelIso
  apply (surjective_boundary_iff_surjective_precompose B m.twoTerm).1
  exact test _ ((surjective_boundary_iff_surjective_precompose A m.twoTerm).2
    (A.surjective_precompose_of_iso m.cokernelIso.symm h))

include k in
private theorem transfer_precompose_add {A B : TwoTerm R} (ha : IsInAdd B.homotopyObject A.homotopyObject)
    {M : FGModuleCat.{u} R} (h : Function.Surjective (A.precompose M)) : Function.Surjective (B.precompose M) := by
  apply transfer_precompose k _ h
  intro Y hY
  exact (surjective_boundary_iff_homotopy ..).2 fun n hn ↦ subsingleton_from_add ha
    ((surjective_boundary_iff_homotopy ..).1 hY n hn)

theorem isZero_semistable_of_silting (T : TwoTerm R) (ht : T.IsPresilting)
    (gen : ∀ X : TwoTerm R, InThick T X) (Y : FGModuleCat.{u} R) (hY : (T.eulerWeight k).IsSemistable Y) :
    IsZero Y := by
  let G : FiniteProjective R := ⟨FGModuleCat.of R R,inferInstance⟩
  let _ := G.property
  let Q := inDegreeZero G.val
  have inv := invertedOn_of_inThick (gen Q) Y.obj ((T.invertedOn_iff_semistable k ht Y).2 hY)
  have hz := ((Q.invertedOn_iff_semistable k (isPresilting_inDegreeZero G.val) Y).1 inv).1
  rw [← projectiveClassWeight_eq_eulerWeight,projectiveClass_inDegreeZero G,projectiveClassWeight_of] at hz
  by_contra hn
  exact (dimensionWeight_pos k Y hn).ne' hz

include k in
private theorem generated_iff_precompose_silting (T : TwoTerm R) (ht : T.IsPresilting)
    (gen : ∀ X : TwoTerm R, InThick T X) (M : FGModuleCat.{u} R) :
    IsGeneratedBy (cokernel T.differential) M ↔ Function.Surjective (T.precompose M) := by
  constructor
  · exact T.surjective_precompose_of_generatedBy ((surjective_boundary_iff_surjective_precompose T T).1 ht)
  intro hs
  obtain ⟨D,i,_,hD,hY⟩ := T.exists_semistable_quotient_of_no_hom_nakayamaKernel k ht M
    ((T.surjective_precompose_iff_no_hom_nakayamaKernel k M).1 hs)
  let Y := cokernel i
  have zero := isZero_semistable_of_silting k T ht gen Y hY
  let _ : Epi i := Abelian.epi_of_cokernel_π_eq_zero _ (zero.eq_of_tgt _ _)
  exact hD.of_epi i

/-- There is a basic two-term silting completion containing the original
complex in its additive closure, and its cokernel generates precisely the
left Hom-perpendicular of the original Nakayama kernel. -/
theorem exists_basic_bongartz_completion (P : TwoTerm R) (hp : P.IsPresilting) :
    ∃ (T : TwoTerm R), ∃ l, BasicDecomposition T l ∧ T.IsPresilting ∧
      IsInAdd P.homotopyObject T.homotopyObject ∧ (∀ X : TwoTerm R, InThick T X) ∧
      ∀ M : FGModuleCat.{u} R, IsGeneratedBy (cokernel T.differential) M ↔
        Subsingleton (M ⟶ P.nakayamaKernel k) := by
  obtain ⟨B,hs,gen,orth⟩ := exists_bongartz_generator k P hp
  let U := P.directSum B
  obtain ⟨T,l,hl,hTU,hUT⟩ := exists_basic_add_generator k U hs
  have ht := isPresilting_of_homotopy_isInAdd hs hTU
  have hPU : IsInAdd P.homotopyObject U.homotopyObject :=
    (IsInAdd.of_retraction _ _ (inlDirectSum_fstDirectSum P B)).map (doubleFunctor ⋙ HomotopyCategory.quotient _ _)
  have genT (X : TwoTerm R) : InThick T X := by
    have hu := inThick_of_isInAdd T U hUT
    exact (ObjectProperty.triangEnvelope_le_iff _ (Q := (ObjectProperty.singleton T.homotopyObject).triangEnvelope)).2
      (ObjectProperty.singleton_le_iff.2 hu) _ (gen X)
  refine ⟨T,l,hl,ht,hPU.trans hUT,genT,fun M ↦ ?_⟩
  rw [generated_iff_precompose_silting k T ht genT,← surjective_precompose_iff_no_hom_nakayamaKernel]
  exact ⟨transfer_precompose_add k (hPU.trans hUT),fun h ↦ transfer_precompose_add k hTU
    (transfer_precompose k orth h)⟩

end EFiniteCharacterizations.TwoTerm
